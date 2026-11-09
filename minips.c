#define _GNU_SOURCE

#include <dirent.h>
#include <ctype.h>
#include <getopt.h>
#include <inttypes.h>
#include <pwd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
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
    uid_t uid;
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

typedef struct proc proc_t;

/* In display order: a column added with +name goes to its place in this order. */
enum column { COL_PID, COL_PPID, COL_USER, COL_TIME, COL_CPU, COL_PCPU, COL_NOW, COL_RSS, COL_PMEM,
              COL_CMD, COL_COUNT };

static const struct {
    const char *name;
    const char *header;
    int left;  /* left-aligned (text) rather than right-aligned (numbers) */
    const char *desc;
} columns[COL_COUNT] = {
    [COL_PID]  = {"pid",  "pid",  0, "process ID"},
    [COL_PPID] = {"ppid", "ppid", 0, "parent process ID"},
    [COL_USER] = {"user", "user", 1, "owner (effective user)"},
    [COL_TIME] = {"time", "time", 0, "time since start (elapsed), HH:MM:SS"},
    [COL_CPU]  = {"cpu",  "cpu",  0, "CPU time used, seconds"},
    [COL_PCPU] = {"avg",  "%avg",     0, "average CPU usage: CPU time / elapsed time"},
    [COL_NOW]  = {"now",  "%cpu",     0, "current CPU usage, during the -c interval"},
    [COL_RSS]  = {"rss",  "rss",  0, "resident memory, MiB"},
    [COL_PMEM] = {"pmem", "%mem", 0, "RSS / total RAM"},
    [COL_CMD]  = {"cmd",  "cmd",  1, "command line"},
};

static long ticks_per_sec;
static long page_size;
static uint64_t total_ram;

static enum column sort_col = COL_PID;
static int sort_desc;

static int precise;    /* -p: full precision instead of human-friendly values */
static char mem_unit;  /* -B/-K/-M/-G, 0: pick per value */
static int color;      /* highlight the leading part of numbers (terminal only) */

#define BOLD "\033[1m"
#define DIM "\033[2m"
#define RESET "\033[0m"

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
static int read_sample(proc_t *p) {
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

static int read_proc(proc_t *p) {
    char path[64];
    struct stat st;
    snprintf(path, sizeof path, "/proc/%d", (int)p->pid);
    if (stat(path, &st) < 0 || read_sample(p) < 0)
        return -1;

    p->uid = st.st_uid;
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
    return CMP(((const proc_t *)a)->pid, ((const proc_t *)b)->pid);
}

/* All PIDs in /proc, sorted. Only pid is filled in. */
static size_t scan_pids(proc_t **out) {
    DIR *dir = opendir("/proc");
    if (!dir) {
        perror("/proc");
        exit(1);
    }

    size_t n = 0, cap = 0;
    proc_t *procs = NULL;
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
    const proc_t *p = a, *q = b;
    int r = 0;
    switch (sort_col) {
    case COL_PID:     r = CMP(p->pid, q->pid); break;
    case COL_PPID:    r = CMP(p->ppid, q->ppid); break;
    case COL_USER:    r = strcmp(p->user, q->user); break;
    /* By start time: elapsed_ns also depends on when each process was read. */
    case COL_TIME:    r = CMP(q->start_ns, p->start_ns); break;
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

/* head + tail into buf; head bold and tail dim, so the magnitude stands out. */
static void emit(char *buf, size_t size, const char *head, const char *tail) {
    if (color)
        snprintf(buf, size, BOLD "%s" RESET DIM "%s" RESET, head, tail);
    else
        snprintf(buf, size, "%s%s", head, tail);
}

/* A number with the part before the decimal point highlighted, e.g. "12.345s". */
static void emit_number(char *buf, size_t size, const char *num, const char *unit) {
    char head[64], tail[64];
    size_t n = strcspn(num, ".");
    snprintf(head, sizeof head, "%.*s", (int)n, num);
    snprintf(tail, sizeof tail, "%s%s", num + n, unit);
    emit(buf, size, head, tail);
}

/* Human-friendly: one decimal fewer from 10 up, and another from 100 up. */
static void emit_human(char *buf, size_t size, double v, int decimals, const char *unit) {
    char num[64];
    if (v >= 10)
        decimals--;
    if (v >= 100)
        decimals--;
    snprintf(num, sizeof num, "%.*f", decimals > 0 ? decimals : 0, v);
    emit_number(buf, size, num, unit);
}

/* Fixed number of significant digits, the decimal point moving as the value
 * grows: 1.23456, 12.3456, 123.456, ... */
static void emit_digits(char *buf, size_t size, double v, int digits, const char *unit) {
    char num[64];
    int decimals = digits - 1;
    for (double limit = 10; v >= limit && decimals > 0; limit *= 10)
        decimals--;
    snprintf(num, sizeof num, "%.*f", decimals, v);
    emit_number(buf, size, num, unit);
}

static void format_time(char *buf, size_t size, uint64_t ns) {
    char num[64];
    if (precise) {
        /* Start time comes from stat in 1/100 s, so 2 decimals. */
        snprintf(num, sizeof num, "%" PRIu64 ".%02" PRIu64, ns / NS_PER_SEC,
                 ns % NS_PER_SEC / 10000000);
        emit_number(buf, size, num, "s");
        return;
    }

    /* HH:MM:SS (hours keep counting past a day), leading zero fields dimmed:
     * 00:05:23 shows "00:" dim, so only the significant part stands out. */
    uint64_t sec = ns / NS_PER_SEC;
    snprintf(num, sizeof num, "%02" PRIu64 ":%02" PRIu64 ":%02" PRIu64, sec / 3600,
             sec / 60 % 60, sec % 60);
    size_t lead = 0;
    while (strncmp(num + lead, "00:", 3) == 0)
        lead += 3;
    if (color && lead)
        snprintf(buf, size, DIM "%.*s" RESET "%s", (int)lead, num, num + lead);
    else
        snprintf(buf, size, "%s", num);
}

static void format_cpu(char *buf, size_t size, uint64_t ns) {
    if (precise) {
        char num[64];
        snprintf(num, sizeof num, "%" PRIu64 ".%06" PRIu64, ns / NS_PER_SEC,
                 ns % NS_PER_SEC / 1000);
        emit_number(buf, size, num, "s");
    } else {
        emit_digits(buf, size, (double)ns / NS_PER_SEC, 6, "s");
    }
}

static void format_percent(char *buf, size_t size, double v, int precise_decimals) {
    if (precise) {
        char num[64];
        snprintf(num, sizeof num, "%.*f", precise_decimals, v);
        emit_number(buf, size, num, "");
    } else {
        emit_digits(buf, size, v, 6, "");
    }
}

/* End of the word starting at s (spaces separate words). */
static const char *word_end(const char *s) {
    return s + strcspn(s, " ");
}

static const char *skip_spaces(const char *s) {
    return s + strspn(s, " ");
}

/* Start of the program name in the word s..end: after the last '/'. */
static const char *base_name(const char *s, const char *end) {
    const char *base = s;
    for (; s < end; s++)
        if (*s == '/')
            base = s + 1;
    return base;
}

/* The command with only the program name normal; its directory and the
 * arguments are dimmed. After sudo (and its options), the name of the command
 * it runs stays normal too: "sudo -u bob /usr/bin/vim x.txt". Kernel threads,
 * shown as "[name]", are dimmed entirely. */
static void format_cmd(char *buf, size_t size, const char *cmd) {
    if (!color) {
        snprintf(buf, size, "%s", cmd);
        return;
    }
    if (cmd[0] == '[') {
        snprintf(buf, size, DIM "%s" RESET, cmd);
        return;
    }

    /* Up to two names to keep normal: sudo's and the command's. */
    const char *names[2][2];
    int nnames = 0;
    const char *end = word_end(cmd);
    const char *base = base_name(cmd, end);
    names[nnames][0] = base;
    names[nnames++][1] = end;
    if (end - base == 4 && strncmp(base, "sudo", 4) == 0) {
        const char *s = skip_spaces(end);
        while (*s == '-') {
            /* Options that take a value: -u USER, -g GROUP, ... */
            int value = strchr("ughpCDTrt", s[1]) && s[1] && s[2] == ' ';
            s = skip_spaces(word_end(s));
            if (value)
                s = skip_spaces(word_end(s));
        }
        if (*s) {
            end = word_end(s);
            names[nnames][0] = base_name(s, end);
            names[nnames++][1] = end;
        }
    }

    size_t pos = 0;
    const char *s = cmd;
    for (int i = 0; i <= nnames && pos < size; i++) {
        const char *from = i < nnames ? names[i][0] : s + strlen(s);
        if (from > s)
            pos += snprintf(buf + pos, size - pos, DIM "%.*s" RESET, (int)(from - s), s);
        if (i < nnames && pos < size)
            pos += snprintf(buf + pos, size - pos, "%.*s", (int)(names[i][1] - from), from);
        if (i < nnames)
            s = names[i][1];
    }
}

static void format_mem(char *buf, size_t size, uint64_t bytes) {
    char unit = mem_unit;
    if (!unit)
        unit = precise ? 'M' : bytes < (1 << 20) ? 'K' : bytes < (1 << 30) ? 'M' : 'G';

    char num[64], suffix[2] = {unit, 0};
    switch (unit) {
    case 'B':
    case 'K':
        /* Whole kilobytes are exact: memory comes in pages. */
        snprintf(num, sizeof num, "%" PRIu64, unit == 'B' ? bytes : bytes >> 10);
        emit_number(buf, size, num, suffix);
        break;
    default: {
        double v = (double)bytes / (unit == 'M' ? 1 << 20 : 1 << 30);
        if (precise) {
            snprintf(num, sizeof num, "%.*f", unit == 'M' ? 2 : 3, v);
            emit_number(buf, size, num, suffix);
        } else if (unit == 'M') {
            snprintf(num, sizeof num, "%.0f", v);
            emit_number(buf, size, num, suffix);
        } else {
            emit_human(buf, size, v, 2, suffix);
        }
    }
    }
}

static void format_value(char *buf, size_t size, const proc_t *p, enum column col) {
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
    case COL_TIME:
        format_time(buf, size, p->elapsed_ns);
        break;
    case COL_CPU:
        format_cpu(buf, size, p->cpu_ns);
        break;
    case COL_PCPU:
        format_percent(buf, size, p->pcpu, 5);
        break;
    case COL_NOW:
        format_percent(buf, size, p->now, 5);
        break;
    case COL_RSS:
        format_mem(buf, size, p->rss);
        break;
    case COL_PMEM: {
        double v = total_ram ? 100.0 * p->rss / total_ram : 0;
        if (precise)
            format_percent(buf, size, v, 3);
        else
            emit_human(buf, size, v, 2, "");
        break;
    }
    case COL_CMD:
        format_cmd(buf, size, p->cmd);
        break;
    case COL_COUNT:
        buf[0] = 0;
        break;
    }
}

/* Skips a color escape sequence ("\033[...m") starting at s, if any. */
static const char *skip_escape(const char *s) {
    if (*s != '\033')
        return s;
    while (*s && *s != 'm')
        s++;
    return *s ? s + 1 : s;
}

/* Prints s, but at most cols characters (cols < 0: no limit). Counts UTF-8
 * characters rather than bytes so a multi-byte character is never split,
 * and color escapes take no space. */
static void print_cut(const char *s, int cols) {
    const char *end = s;
    while (*end) {
        const char *next = skip_escape(end);
        if (next != end) {
            end = next;
            continue;
        }
        if (((unsigned char)*end & 0xc0) != 0x80 && cols-- == 0)
            break;
        end++;
    }
    fwrite(s, 1, end - s, stdout);
    if (color)
        fputs(RESET, stdout);  /* in case the cut fell inside highlighted text */
    putchar('\n');
}

/* Display width of a UTF-8 string: characters, not bytes, without escapes. */
static int text_width(const char *s) {
    int n = 0;
    while (*s) {
        const char *next = skip_escape(s);
        if (next != s) {
            s = next;
            continue;
        }
        if (((unsigned char)*s & 0xc0) != 0x80)
            n++;
        s++;
    }
    return n;
}

/* Value of a column; p == NULL gives the header. */
static void column_text(char *buf, size_t size, const proc_t *p, enum column col) {
    if (p)
        format_value(buf, size, p, col);
    else
        snprintf(buf, size, "%s", columns[col].header);
}

static void print_line(const proc_t *p, const enum column *cols, const int *widths,
                       int ncols, int term_cols) {
    char line[LINE_MAX_LEN], value[CMDLINE_MAX];
    size_t pos = 0;

    for (int i = 0; i < ncols; i++) {
        column_text(value, sizeof value, p, cols[i]);
        int pad = widths[i] - text_width(value);
        int left = columns[cols[i]].left;
        if (left && i == ncols - 1)
            pad = 0;  /* no trailing spaces after the last column */
        int n = snprintf(line + pos, sizeof line - pos, "%s%*s%s%*s", i ? "  " : "",
                         left ? 0 : pad, "", value, left ? pad : 0, "");
        if (n < 0 || (pos += n) >= sizeof line) {
            pos = sizeof line - 1;
            break;
        }
    }
    print_cut(line, term_cols);
}

static int lookup_column(const char *name) {
    for (int c = 0; c < COL_COUNT; c++)
        if (strcasecmp(columns[c].name, name) == 0)
            return c;
    return -1;
}

static enum column find_column(const char *name) {
    int c = lookup_column(name);
    if (c < 0) {
        fprintf(stderr, "minips: unknown column '%s' (see --help)\n", name);
        exit(2);
    }
    return c;
}

/* Whether a short-option argument like "-rs" leaves its value in the next
 * argument, which then must not be taken for a "-col" toggle (-s -cpu). */
static int value_in_next_arg(const char *arg) {
    if (strcmp(arg, "--sort") == 0 || strcmp(arg, "--columns") == 0)
        return 1;
    if (arg[0] != '-' || arg[1] == '-')
        return 0;
    for (const char *s = arg + 1; *s; s++) {
        if (*s == 'c')
            return 0;  /* optional value, only ever attached */
        if (*s == 's' || *s == 'o')
            return s[1] == 0;
    }
    return 0;
}

/* Length of the "-c" option at the start of a short-option cluster like
 * "-acr", up to and including the 'c', when what follows is more options
 * rather than a delay (as in "-c0.5"); 0 if there's nothing to split. */
static size_t split_after_c(const char *arg) {
    if (arg[0] != '-' || arg[1] == '-')
        return 0;
    for (const char *s = arg + 1; *s; s++) {
        if (*s == 's' || *s == 'o')
            return 0;  /* the rest is their value */
        if (*s == 'c')
            return s[1] && !isdigit((unsigned char)s[1]) && s[1] != '.' ? s + 1 - arg : 0;
    }
    return 0;
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
            "Usage: minips [OPTIONS] [+COLUMN] [-COLUMN] [FILTER...]\n"
            "\n"
            "Shows your processes; FILTER shows only those whose command line contains\n"
            "any of the given texts (ignoring case).\n"
            "\n"
            "  +COL, -COL           add / remove a column (to the defaults or the -o list)\n"
            "  -a, --all            show processes of all users\n"
            "  -p, --precise        full precision (times in s, CPU time in us)\n"
            "  -B, -K, -M, -G       memory in bytes / KiB / MiB / GiB (default: per value)\n"
            "  -c, --current[=SEC]  measure current CPU usage over SEC seconds (default 1);\n"
            "                       adds the 'now' (%%CPU) column and sorts by it (busiest last)\n"
            "  -o, --columns=LIST   comma-separated columns to show\n"
            "  -s, --sort=[-]COL    sort by COL, '-' for descending (default: pid)\n"
            "  -m, --mem            sort by memory (rss), biggest last\n"
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
        {"mem",     no_argument,       NULL, 'm'},
        {"reverse", no_argument,       NULL, 'r'},
        {"all",     no_argument,       NULL, 'a'},
        {"precise", no_argument,       NULL, 'p'},
        {"help",    no_argument,       NULL, 'h'},
        {NULL, 0, NULL, 0},
    };

    double delay = 0;  /* 0: no current-usage measurement */
    const char *columns_arg = NULL;
    const char *sort_arg = NULL;
    int reverse = 0;
    int all = 0;

    /* "+col" / "-col" add or remove columns. Take them out before getopt,
     * which would read "-rss" as "-r -s s". */
    enum column toggle_col[MAX_COLUMNS];
    int toggle_add[MAX_COLUMNS], ntoggles = 0;
    /* Room for splitting "-cr" into "-c" "-r": at most one extra per character. */
    size_t room = argc + 1;
    for (int i = 1; i < argc; i++)
        room += strlen(argv[i]);
    char **args = malloc(room * sizeof *args);
    args[0] = argv[0];
    int kept = 1;
    for (int i = 1; i < argc; i++) {
        const char *arg = argv[i];
        int col;
        if (strcmp(arg, "--") == 0) {
            while (i < argc)
                args[kept++] = argv[i++];
            break;
        }
        if (arg[0] == '+' && arg[1])
            find_column(arg + 1);  /* exits on an unknown name */
        if ((arg[0] == '+' || arg[0] == '-') && (col = lookup_column(arg + 1)) >= 0) {
            if (ntoggles == MAX_COLUMNS) {
                fprintf(stderr, "minips: too many columns\n");
                return 2;
            }
            toggle_col[ntoggles] = col;
            toggle_add[ntoggles++] = arg[0] == '+';
            continue;
        }
        /* "-c" takes an optional attached delay, so "-cr" would read "r" as
         * the delay: split it into "-c" "-r". */
        for (size_t n; (n = split_after_c(arg)); ) {
            args[kept++] = strndup(arg, n);
            char *rest = malloc(strlen(arg + n) + 2);
            rest[0] = '-';
            strcpy(rest + 1, arg + n);
            arg = rest;
        }
        args[kept++] = (char *)arg;
        if (value_in_next_arg(arg) && i + 1 < argc)
            args[kept++] = argv[++i];
    }
    argc = kept;
    args[argc] = NULL;
    argv = args;

    int opt;
    while ((opt = getopt_long(argc, argv, "c::o:s:mraphBKMG", long_options, NULL)) != -1) {
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
        case 'm':
            sort_arg = "rss";  /* ascending: biggest last, next to the prompt */
            break;
        case 'r':
            reverse = 1;
            break;
        case 'a':
            all = 1;
            break;
        case 'p':
            precise = 1;
            break;
        case 'B':
        case 'K':
        case 'M':
        case 'G':
            mem_unit = opt;
            break;
        case 'h':
            usage(stdout);
            return 0;
        default:
            usage(stderr);
            return 2;
        }
    }
    char **filters = argv + optind;
    int nfilters = argc - optind;

    enum column cols[MAX_COLUMNS];
    int ncols = 0;
    char *list = strdup(columns_arg ? columns_arg
                        : delay ? "pid,user,time,cpu,avg,now,rss,cmd"
                                : "pid,user,time,cpu,avg,rss,cmd");
    for (char *name = strtok(list, ","); name; name = strtok(NULL, ",")) {
        if (ncols == MAX_COLUMNS) {
            fprintf(stderr, "minips: too many columns\n");
            return 2;
        }
        cols[ncols++] = find_column(name);
    }
    free(list);

    for (int t = 0; t < ntoggles; t++) {
        enum column col = toggle_col[t];
        int at = 0, present = 0;
        for (int i = 0; i < ncols; i++)
            present |= cols[i] == col;
        if (!toggle_add[t]) {
            for (int i = 0; i < ncols; i++)
                if (cols[i] != col)
                    cols[at++] = cols[i];
            ncols = at;
        } else if (!present) {
            if (ncols == MAX_COLUMNS) {
                fprintf(stderr, "minips: too many columns\n");
                return 2;
            }
            /* Before the first column that comes later in display order. */
            while (at < ncols && cols[at] < col)
                at++;
            memmove(&cols[at + 1], &cols[at], (ncols - at) * sizeof *cols);
            cols[at] = col;
            ncols++;
        }
    }

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
        fprintf(stderr, "minips: the 'now' (%%CPU) column needs -c\n");
        return 2;
    }

    ticks_per_sec = sysconf(_SC_CLK_TCK);
    page_size = sysconf(_SC_PAGESIZE);
    total_ram = (uint64_t)sysconf(_SC_PHYS_PAGES) * page_size;

    /* Cut lines to the terminal width; when piped, print everything. */
    int tty = isatty(STDOUT_FILENO);
    color = tty && !getenv("NO_COLOR");
    struct winsize ws;
    int term_cols = -1;
    if (tty && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
        term_cols = ws.ws_col;

    proc_t *first = NULL;
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

    proc_t *procs;
    size_t n = scan_pids(&procs), shown = 0;
    for (size_t i = 0; i < n; i++) {
        proc_t *p = &procs[i];
        if (read_proc(p) < 0)
            continue;
        if (!all && p->uid != geteuid())
            continue;
        if (nfilters) {
            if (p->pid == getpid())
                continue;  /* our own command line contains the filter */
            int match = 0;
            for (int f = 0; f < nfilters && !match; f++)
                match = strcasestr(p->cmd, filters[f]) != NULL;
            if (!match)
                continue;
        }

        if (delay) {
            proc_t *prev = bsearch(p, first, nfirst, sizeof *first, compare_pid);
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

    /* Each column as wide as its widest value (or header). */
    int widths[MAX_COLUMNS];
    char value[CMDLINE_MAX];
    for (int i = 0; i < ncols; i++) {
        widths[i] = text_width(columns[cols[i]].header);
        for (size_t j = 0; j < shown; j++) {
            format_value(value, sizeof value, &procs[j], cols[i]);
            int w = text_width(value);
            if (w > widths[i])
                widths[i] = w;
        }
    }

    // print_line(NULL, cols, widths, ncols, term_cols);
    for (size_t i = 0; i < shown; i++)
        print_line(&procs[i], cols, widths, ncols, term_cols);
    /* The top header has scrolled away by now; repeat it next to the prompt.
     * Not when piped, where it would just be an extra line to filter out. */
    if (tty)
        print_line(NULL, cols, widths, ncols, term_cols);

    return 0;
}
