#include <dirent.h>
#include <getopt.h>
#include <inttypes.h>
#include <pwd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#define NS_PER_SEC ((uint64_t)1000000000)
#define CMDLINE_MAX 4096
#define LINE_MAX_LEN (CMDLINE_MAX + 256)
#define MAX_COLUMNS 32

#define CMP(a, b) (((a) > (b)) - ((a) < (b)))

struct proc {
    pid_t pid;
    pid_t ppid;
    char user[9];
    uint64_t start_ns;   /* since boot; only precise to 1/100 s */
    uint64_t cpu_ns;
    uint64_t sample_ns;  /* CLOCK_BOOTTIME right after cpu_ns was read */
    uint64_t elapsed_ns;
    double pcpu;         /* cpu_ns / elapsed_ns: average over the whole life */
    double now;          /* usage during the -c interval */
    uint64_t rss;        /* bytes */
    char *cmd;
};

enum column { COL_PID, COL_PPID, COL_USER, COL_ELAPSED, COL_CPU, COL_PCPU, COL_NOW, COL_RSS, COL_PMEM,
              COL_CMD, COL_COUNT };

static const struct {
    const char *name;
    const char *header;
    int width;  /* negative: left-aligned, 0: no padding */
    const char *desc;
} columns[COL_COUNT] = {
    [COL_PID]     = {"pid",     "PID",      7, "process ID"},
    [COL_PPID]    = {"ppid",    "PPID",     7, "parent process ID"},
    [COL_USER]    = {"user",    "USER",    -8, "owner (effective user)"},
    [COL_ELAPSED] = {"elapsed", "ELAPSED", 13, "time since start, seconds"},
    [COL_CPU]     = {"cpu",     "CPU",     16, "CPU time used, seconds"},
    [COL_PCPU]    = {"pcpu",    "%CPU",    11, "CPU time / elapsed time"},
    [COL_NOW]     = {"now",     "%NOW",    11, "CPU usage during the -c interval"},
    [COL_RSS]     = {"rss",     "RSS",     10, "resident memory, MiB"},
    [COL_PMEM]    = {"pmem",    "%MEM",     7, "RSS / total RAM"},
    [COL_CMD]     = {"cmd",     "CMD",      0, "command line"},
};

static long ticks_per_sec;
static long page_size;
static uint64_t total_ram;

static enum column sort_col = COL_PID;
static int sort_desc;

static uint64_t clock_ns(clockid_t clock) {
    struct timespec ts;
    clock_gettime(clock, &ts);
    return (uint64_t)ts.tv_sec * NS_PER_SEC + ts.tv_nsec;
}

/* Reads /proc/<pid>/<file> into buf, NUL-terminated; returns its length or -1. */
static long read_proc_file(pid_t pid, const char *file, char *buf, size_t size) {
    char path[64];
    snprintf(path, sizeof path, "/proc/%d/%s", (int)pid, file);
    FILE *f = fopen(path, "r");
    if (!f)
        return -1;
    size_t n = fread(buf, 1, size - 1, f);
    fclose(f);
    buf[n] = 0;
    return n;
}

/* Start time (field 22 of stat) and CPU time, and the moment CPU time was
 * read. This is all that is needed for each of the two -c samples. */
static int read_sample(struct proc *p) {
    char buf[1024];
    if (read_proc_file(p->pid, "stat", buf, sizeof buf) <= 0)
        return -1;

    /* Field 2 is "(comm)" and comm may contain spaces and ')', so fields
     * 3 onwards start after the last ')'. */
    char *s = strrchr(buf, ')');
    if (!s)
        return -1;
    s++;
    for (int field = 3; field < 22; field++) {
        while (*s == ' ')
            s++;
        if (field == 4)
            p->ppid = strtol(s, NULL, 10);
        while (*s && *s != ' ')
            s++;
    }
    char *end;
    uint64_t start_ticks = strtoull(s, &end, 10);
    if (end == s)
        return -1;
    p->start_ns = start_ticks * NS_PER_SEC / ticks_per_sec;

    /* Whole process in ns, including threads that have already exited. */
    /* For another process the kernel doesn't add the time its threads have
     * been running since the last scheduler tick (1 ms at HZ=1000), so each
     * reading can lag by up to a tick. */
    clockid_t clock;
    struct timespec ts;
    if (clock_getcpuclockid(p->pid, &clock) != 0 || clock_gettime(clock, &ts) < 0)
        return -1;
    p->cpu_ns = (uint64_t)ts.tv_sec * NS_PER_SEC + ts.tv_nsec;
    p->sample_ns = clock_ns(CLOCK_BOOTTIME);
    return 0;
}

static const char *user_name(uid_t uid) {
    static uid_t cached_uid = (uid_t)-1;
    static char name[32];

    if (uid != cached_uid) {
        struct passwd *pw = getpwuid(uid);
        if (pw)
            snprintf(name, sizeof name, "%s", pw->pw_name);
        else
            snprintf(name, sizeof name, "%u", (unsigned)uid);
        /* Like ps: names longer than 8 characters become 7 + "+". */
        if (strlen(name) > 8) {
            name[7] = '+';
            name[8] = 0;
        }
        cached_uid = uid;
    }
    return name;
}

static char *read_cmdline(pid_t pid) {
    char buf[CMDLINE_MAX];
    long n = read_proc_file(pid, "cmdline", buf, sizeof buf);
    if (n > 0) {
        while (n > 0 && buf[n - 1] == 0)
            n--;
        /* NULs separate arguments; other control characters (e.g. a newline
         * inside an argument) would break the one-line-per-process layout. */
        for (long i = 0; i < n; i++)
            if (buf[i] == 0)
                buf[i] = ' ';
            else if ((unsigned char)buf[i] < 0x20 || buf[i] == 0x7f)
                buf[i] = '?';
        buf[n] = 0;
        return strdup(buf);
    }

    /* Kernel threads have no cmdline: show [comm] like ps does. */
    char comm[32];
    n = read_proc_file(pid, "comm", comm, sizeof comm);
    if (n > 0 && comm[n - 1] == '\n')
        comm[n - 1] = 0;
    snprintf(buf, sizeof buf, "[%s]", n > 0 ? comm : "?");
    return strdup(buf);
}

/* Second field of statm: resident pages. */
static uint64_t read_rss(pid_t pid) {
    char buf[256];
    if (read_proc_file(pid, "statm", buf, sizeof buf) <= 0)
        return 0;
    char *s = buf;
    strtoull(s, &s, 10);
    return strtoull(s, NULL, 10) * page_size;
}

static int read_proc(struct proc *p) {
    char path[64];
    struct stat st;
    snprintf(path, sizeof path, "/proc/%d", (int)p->pid);
    if (stat(path, &st) < 0 || read_sample(p) < 0)
        return -1;

    snprintf(p->user, sizeof p->user, "%s", user_name(st.st_uid));
    p->elapsed_ns = p->sample_ns - p->start_ns;
    p->pcpu = p->elapsed_ns ? 100.0 * p->cpu_ns / p->elapsed_ns : 0;
    p->rss = read_rss(p->pid);
    p->cmd = read_cmdline(p->pid);
    return 0;
}

static int is_pid(const char *s) {
    if (!*s)
        return 0;
    for (; *s; s++)
        if (*s < '0' || *s > '9')
            return 0;
    return 1;
}

static int compare_pid(const void *a, const void *b) {
    return CMP(((const struct proc *)a)->pid, ((const struct proc *)b)->pid);
}

/* All PIDs in /proc, sorted. Only pid is filled in. */
static size_t scan_pids(struct proc **out) {
    DIR *dir = opendir("/proc");
    if (!dir) {
        perror("/proc");
        exit(1);
    }

    size_t n = 0, cap = 0;
    struct proc *procs = NULL;
    struct dirent *de;
    while ((de = readdir(dir))) {
        if (!is_pid(de->d_name))
            continue;
        if (n == cap) {
            cap = cap ? cap * 2 : 512;
            procs = realloc(procs, cap * sizeof *procs);
            if (!procs) {
                perror("realloc");
                exit(1);
            }
        }
        memset(&procs[n], 0, sizeof *procs);
        procs[n++].pid = atoi(de->d_name);
    }
    closedir(dir);

    qsort(procs, n, sizeof *procs, compare_pid);
    *out = procs;
    return n;
}

static int compare_procs(const void *a, const void *b) {
    const struct proc *p = a, *q = b;
    int r = 0;
    switch (sort_col) {
    case COL_PID:     r = CMP(p->pid, q->pid); break;
    case COL_PPID:    r = CMP(p->ppid, q->ppid); break;
    case COL_USER:    r = strcmp(p->user, q->user); break;
    case COL_ELAPSED: r = CMP(p->elapsed_ns, q->elapsed_ns); break;
    case COL_CPU:     r = CMP(p->cpu_ns, q->cpu_ns); break;
    case COL_PCPU:    r = CMP(p->pcpu, q->pcpu); break;
    case COL_NOW:     r = CMP(p->now, q->now); break;
    case COL_RSS:
    case COL_PMEM:    r = CMP(p->rss, q->rss); break;
    case COL_CMD:     r = strcmp(p->cmd, q->cmd); break;
    case COL_COUNT:   break;
    }
    if (sort_desc)
        r = -r;
    return r ? r : CMP(p->pid, q->pid);
}

static void format_value(char *buf, size_t size, const struct proc *p, enum column col) {
    switch (col) {
    case COL_PID:
        snprintf(buf, size, "%d", (int)p->pid);
        break;
    case COL_PPID:
        snprintf(buf, size, "%d", (int)p->ppid);
        break;
    case COL_USER:
        snprintf(buf, size, "%s", p->user);
        break;
    case COL_ELAPSED:
        /* Start time comes from stat in 1/100 s, so 2 decimals. */
        snprintf(buf, size, "%" PRIu64 ".%02" PRIu64 "s",
                 p->elapsed_ns / NS_PER_SEC, p->elapsed_ns % NS_PER_SEC / 10000000);
        break;
    case COL_CPU:
        snprintf(buf, size, "%" PRIu64 ".%06" PRIu64 "s",
                 p->cpu_ns / NS_PER_SEC, p->cpu_ns % NS_PER_SEC / 1000);
        break;
    case COL_PCPU:
        snprintf(buf, size, "%.5f", p->pcpu);
        break;
    case COL_NOW:
        snprintf(buf, size, "%.5f", p->now);
        break;
    case COL_RSS:
        snprintf(buf, size, "%.2fM", p->rss / 1048576.0);
        break;
    case COL_PMEM:
        snprintf(buf, size, "%.3f", total_ram ? 100.0 * p->rss / total_ram : 0);
        break;
    case COL_CMD:
        snprintf(buf, size, "%s", p->cmd);
        break;
    case COL_COUNT:
        buf[0] = 0;
        break;
    }
}

/* Prints s, but at most cols characters (cols < 0: no limit). Counts UTF-8
 * characters rather than bytes so a multi-byte character is never split. */
static void print_cut(const char *s, int cols) {
    const char *end = s;
    for (; *end; end++) {
        if (((unsigned char)*end & 0xc0) == 0x80)
            continue;
        if (cols-- == 0)
            break;
    }
    fwrite(s, 1, end - s, stdout);
    putchar('\n');
}

/* One output line; p == NULL prints the header. */
static void print_line(const struct proc *p, const enum column *cols, int ncols, int term_cols) {
    char line[LINE_MAX_LEN], value[CMDLINE_MAX];
    size_t pos = 0;

    for (int i = 0; i < ncols && pos < sizeof line; i++) {
        if (p)
            format_value(value, sizeof value, p, cols[i]);
        else
            snprintf(value, sizeof value, "%s", columns[cols[i]].header);
        int n = snprintf(line + pos, sizeof line - pos, "%s%*s",
                         i ? " " : "", columns[cols[i]].width, value);
        if (n > 0)
            pos += n;
    }
    print_cut(line, term_cols);
}

static enum column find_column(const char *name) {
    for (int c = 0; c < COL_COUNT; c++)
        if (strcmp(columns[c].name, name) == 0)
            return c;
    fprintf(stderr, "minips: unknown column '%s' (see --help)\n", name);
    exit(2);
}

static int parse_delay(const char *s, double *out) {
    char *end;
    double d = strtod(s, &end);
    if (end == s || *end || !(d > 0))
        return -1;
    *out = d;
    return 0;
}

static void usage(FILE *f) {
    fprintf(f,
            "Usage: minips [-c [SEC]] [-o COLUMNS] [-s [-]COLUMN] [-r]\n"
            "\n"
            "  -c, --current[=SEC]  measure current CPU usage over SEC seconds (default 1);\n"
            "                       adds the 'now' column and sorts by it (busiest last)\n"
            "  -o, --columns=LIST   comma-separated columns to show\n"
            "  -s, --sort=[-]COL    sort by COL, '-' for descending (default: pid)\n"
            "  -r, --reverse        reverse the sort order\n"
            "  -h, --help           show this help\n"
            "\n"
            "Columns:\n");
    for (int c = 0; c < COL_COUNT; c++)
        fprintf(f, "  %-8s %s\n", columns[c].name, columns[c].desc);
}

int main(int argc, char **argv) {
    static const struct option long_options[] = {
        {"current", optional_argument, NULL, 'c'},
        {"columns", required_argument, NULL, 'o'},
        {"sort",    required_argument, NULL, 's'},
        {"reverse", no_argument,       NULL, 'r'},
        {"help",    no_argument,       NULL, 'h'},
        {NULL, 0, NULL, 0},
    };

    double delay = 0;  /* 0: no current-usage measurement */
    const char *columns_arg = NULL;
    const char *sort_arg = NULL;
    int reverse = 0;

    int opt;
    while ((opt = getopt_long(argc, argv, "c::o:s:rh", long_options, NULL)) != -1) {
        switch (opt) {
        case 'c':
            delay = 1;
            /* Also accept "-c 0.5", not only "-c0.5" / "--current=0.5". */
            if (!optarg && optind < argc && parse_delay(argv[optind], &delay) == 0)
                optind++;
            else if (optarg && parse_delay(optarg, &delay) < 0) {
                fprintf(stderr, "minips: invalid delay '%s'\n", optarg);
                return 2;
            }
            break;
        case 'o':
            columns_arg = optarg;
            break;
        case 's':
            sort_arg = optarg;
            break;
        case 'r':
            reverse = 1;
            break;
        case 'h':
            usage(stdout);
            return 0;
        default:
            usage(stderr);
            return 2;
        }
    }
    if (optind < argc) {
        fprintf(stderr, "minips: unexpected argument '%s'\n", argv[optind]);
        return 2;
    }

    enum column cols[MAX_COLUMNS];
    int ncols = 0;
    char *list = strdup(columns_arg ? columns_arg
                        : delay ? "pid,ppid,user,elapsed,cpu,now,pcpu,rss,cmd"
                                : "pid,ppid,user,elapsed,cpu,pcpu,rss,cmd");
    for (char *name = strtok(list, ","); name; name = strtok(NULL, ",")) {
        if (ncols == MAX_COLUMNS) {
            fprintf(stderr, "minips: too many columns\n");
            return 2;
        }
        cols[ncols++] = find_column(name);
    }
    free(list);

    if (sort_arg) {
        sort_desc = sort_arg[0] == '-';
        sort_col = find_column(sort_arg + (sort_arg[0] == '-' || sort_arg[0] == '+'));
    } else if (delay) {
        sort_col = COL_NOW;  /* ascending: busiest last, next to the prompt */
    }
    sort_desc ^= reverse;

    int uses_now = sort_col == COL_NOW;
    for (int i = 0; i < ncols; i++)
        uses_now |= cols[i] == COL_NOW;
    if (uses_now && !delay) {
        fprintf(stderr, "minips: the 'now' column needs -c\n");
        return 2;
    }

    ticks_per_sec = sysconf(_SC_CLK_TCK);
    page_size = sysconf(_SC_PAGESIZE);
    total_ram = (uint64_t)sysconf(_SC_PHYS_PAGES) * page_size;

    /* Cut lines to the terminal width; when piped, print everything. */
    int tty = isatty(STDOUT_FILENO);
    struct winsize ws;
    int term_cols = -1;
    if (tty && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
        term_cols = ws.ws_col;

    struct proc *first = NULL;
    size_t nfirst = 0;
    uint64_t interval_start_ns = 0;
    if (delay) {
        interval_start_ns = clock_ns(CLOCK_BOOTTIME);
        nfirst = scan_pids(&first);
        for (size_t i = 0; i < nfirst; i++)
            if (read_sample(&first[i]) < 0)
                first[i].sample_ns = 0;  /* gone already */

        struct timespec ts = {(time_t)delay, (long)((delay - (time_t)delay) * NS_PER_SEC)};
        while (nanosleep(&ts, &ts) < 0)
            ;
    }

    struct proc *procs;
    size_t n = scan_pids(&procs), shown = 0;
    for (size_t i = 0; i < n; i++) {
        struct proc *p = &procs[i];
        if (read_proc(p) < 0)
            continue;

        if (delay) {
            struct proc *prev = bsearch(p, first, nfirst, sizeof *first, compare_pid);
            if (prev && prev->sample_ns && prev->start_ns == p->start_ns)
                p->now = 100.0 * (p->cpu_ns - prev->cpu_ns) / (p->sample_ns - prev->sample_ns);
            else
                /* Started during the interval (or the PID was reused), so all
                 * of its CPU time was used within the interval. */
                p->now = 100.0 * p->cpu_ns / (p->sample_ns - interval_start_ns);
        }
        procs[shown++] = *p;
    }

    qsort(procs, shown, sizeof *procs, compare_procs);

    print_line(NULL, cols, ncols, term_cols);
    for (size_t i = 0; i < shown; i++)
        print_line(&procs[i], cols, ncols, term_cols);
    /* The top header has scrolled away by now; repeat it next to the prompt.
     * Not when piped, where it would just be an extra line to filter out. */
    if (tty)
        print_line(NULL, cols, ncols, term_cols);

    return 0;
}
