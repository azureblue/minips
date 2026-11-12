#define _GNU_SOURCE

#include <dirent.h>
#include <fcntl.h>
#include <ctype.h>
#include <getopt.h>
#include <minicell.h>
#include <inttypes.h>
#include <pwd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
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
    double now;          /* usage during the -c interval; -1: not measured yet */
    uint64_t rss;        /* bytes */
    char *cmd;
    char comm[32];       /* name from stat, for "[comm]" without a cmdline */
    int kthread;
    /* /proc/<pid>/stat and cmdline, kept open and re-read with pread, so a
     * refresh needs no open/close. -1: not open. */
    int stat_fd;
    int statm_fd;
    int cmdline_fd;
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
    int stat_field;  /* the last field of /proc/<pid>/stat the column needs */
} columns[COL_COUNT] = {
    [COL_PID]  = {"pid",  "pid",  0, "process ID", 0},
    [COL_PPID] = {"ppid", "ppid", 0, "parent process ID", 4},
    [COL_USER] = {"user", "user", 1, "owner (effective user)", 0},
    [COL_TIME] = {"time", "time", 0, "time since start (elapsed), HH:MM:SS", 22},
    [COL_CPU]  = {"cpu",  "cpu",  0, "CPU time used, seconds", 0},
    [COL_PCPU] = {"avg",  "%avg",     0, "average CPU usage: CPU time / elapsed time", 22},
    /* Start time tells a reused PID from the process sampled before. */
    [COL_NOW]  = {"now",  "%cpu",     0, "current CPU usage, during the -c interval", 22},
    /* RSS from statm: the one in stat is a quick, approximate read. */
    [COL_RSS]  = {"rss",  "rss",  0, "resident memory, MiB", 0},
    [COL_PMEM] = {"pmem", "%mem", 0, "RSS / total RAM", 0},
    [COL_CMD]  = {"cmd",  "cmd",  1, "command line", 9},  /* flags: kernel thread */
};

/* What has to be read for the columns shown and sorted by: stat up to
 * stat_fields, statm for memory, and the command line only if it is shown
 * or filtered on. */
static int stat_fields = 22;
static int need_rss = 1;
static int need_cmd = 1;

static long ticks_per_sec;
static long page_size;
static uint64_t total_ram;

static enum column sort_col = COL_PID;
static int sort_desc;

static int precise;    /* -p: full precision instead of human-friendly values */
static char mem_unit;  /* -B/-K/-M/-G, 0: pick per value */
static int color;      /* highlight the leading part of numbers (terminal only) */
static int live;       /* -t: the live view */

static int show_all;     /* -a: all users' processes, not only ours */
static char **filters;   /* show only commands containing one of these */
static int nfilters;

#define BOLD "\033[1m"
#define DIM "\033[2m"
#define RESET "\033[0m"

static uint64_t clock_ns(clockid_t clock) {
    struct timespec ts;
    clock_gettime(clock, &ts);
    return (uint64_t)ts.tv_sec * NS_PER_SEC + ts.tv_nsec;
}

static int proc_fd = -1;  /* /proc, for openat */

/* Reads /proc/<pid>/<file> into buf, NUL-terminated, at most size - 1 bytes
 * (these files are produced whole, so one read is enough). The file stays
 * open in *fd and is re-read from the start next time. Returns the length,
 * or -1 if the process is gone. */
static long read_proc_file(pid_t pid, const char *file, int *fd, char *buf, size_t size) {
    if (*fd < 0) {
        char path[64];
        snprintf(path, sizeof path, "%d/%s", (int)pid, file);
        *fd = openat(proc_fd, path, O_RDONLY | O_CLOEXEC);
        if (*fd < 0)
            return -1;
    }
    ssize_t n = pread(*fd, buf, size - 1, 0);
    if (n < 0)
        return -1;  /* ESRCH: the process has exited */
    buf[n] = 0;
    return n;
}

static void close_proc_files(proc_t *p) {
    if (p->stat_fd >= 0)
        close(p->stat_fd);
    if (p->statm_fd >= 0)
        close(p->statm_fd);
    if (p->cmdline_fd >= 0)
        close(p->cmdline_fd);
    p->stat_fd = p->statm_fd = p->cmdline_fd = -1;
}

/* What clock_getcpuclockid() returns (MAKE_PROCESS_CPUCLOCK in the kernel),
 * without its clock_getres() call to check the process exists. */
static clockid_t process_cpu_clock(pid_t pid) {
    return (clockid_t)((~(unsigned)pid << 3) | 2);  /* 2: CPUCLOCK_SCHED */
}

/* From stat: comm, ppid, flags and start time, as far as needed; then the
 * CPU time and the moment it was read. All a -c sample needs. */
static int read_sample(proc_t *p) {
    char buf[1024];
    if (read_proc_file(p->pid, "stat", &p->stat_fd, buf, sizeof buf) <= 0)
        return -1;

    /* Field 2 is "(comm)" and comm may contain spaces and ')', so fields
     * 3 onwards start after the last ')'. */
    char *open = strchr(buf, '('), *s = strrchr(buf, ')');
    if (!open || !s)
        return -1;
    snprintf(p->comm, sizeof p->comm, "%.*s", (int)(s - open - 1), open + 1);
    s++;
    uint64_t field_value[23] = {0};
    for (int field = 3; field <= stat_fields; field++) {
        while (*s == ' ')
            s++;
        field_value[field] = strtoull(s, NULL, 10);  /* 0 for field 3, the state letter */
        while (*s && *s != ' ')
            s++;
    }
    p->ppid = field_value[4];
    p->kthread = (field_value[9] & 0x00200000) != 0;  /* PF_KTHREAD */
    p->start_ns = field_value[22] * NS_PER_SEC / ticks_per_sec;

    /* Whole process in ns, including threads that have already exited. */
    /* For another process the kernel doesn't add the time its threads have
     * been running since the last scheduler tick (1 ms at HZ=1000), so each
     * reading can lag by up to a tick. */
    struct timespec ts;
    if (clock_gettime(process_cpu_clock(p->pid), &ts) < 0)
        return -1;
    p->cpu_ns = (uint64_t)ts.tv_sec * NS_PER_SEC + ts.tv_nsec;
    p->sample_ns = clock_ns(CLOCK_BOOTTIME);
    return 0;
}

/* Name of uid, cached for every uid seen. */
static const char *user_name(uid_t uid) {
    static struct {
        uid_t uid;
        char name[9];
    } *cache;
    static size_t n, cap;

    for (size_t i = 0; i < n; i++)
        if (cache[i].uid == uid)
            return cache[i].name;
    if (n == cap) {
        cap = cap ? cap * 2 : 16;
        cache = realloc(cache, cap * sizeof *cache);
        if (!cache) {
            perror("realloc");
            exit(1);
        }
    }
    char name[64];
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
    cache[n].uid = uid;
    snprintf(cache[n].name, sizeof cache[n].name, "%s", name);
    return cache[n++].name;
}

/* Second field of statm: resident pages. */
static uint64_t read_rss(proc_t *p) {
    char buf[256];
    if (read_proc_file(p->pid, "statm", &p->statm_fd, buf, sizeof buf) <= 0)
        return 0;
    char *s = buf;
    strtoull(s, &s, 10);
    return strtoull(s, NULL, 10) * page_size;
}

static char *read_cmdline(proc_t *p) {
    char buf[CMDLINE_MAX];
    /* Kernel threads have no cmdline: show [comm] like ps does. */
    long n = p->kthread ? 0 : read_proc_file(p->pid, "cmdline", &p->cmdline_fd, buf, sizeof buf);
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
    snprintf(buf, sizeof buf, "[%s]", p->comm);
    return strdup(buf);
}

static int read_proc(proc_t *p) {
    if (read_sample(p) < 0)
        return -1;

    /* The owner of /proc/<pid> is the effective user (its files belong to
     * root if the process isn't dumpable). Read once, when the files are
     * opened; a later setuid() isn't noticed. */
    if (!p->user[0]) {
        char name[16];
        struct stat st;
        snprintf(name, sizeof name, "%d", (int)p->pid);
        if (fstatat(proc_fd, name, &st, 0) < 0)
            return -1;
        p->uid = st.st_uid;
        snprintf(p->user, sizeof p->user, "%s", user_name(st.st_uid));
    }
    p->elapsed_ns = p->sample_ns - p->start_ns;
    p->pcpu = p->elapsed_ns ? 100.0 * p->cpu_ns / p->elapsed_ns : 0;
    p->rss = need_rss ? read_rss(p) : 0;
    p->cmd = need_cmd ? read_cmdline(p) : strdup("");
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
    /* Opened once; each scan rewinds it, which re-reads the listing. */
    static DIR *dir;
    if (!dir) {
        dir = opendir("/proc");
        if (!dir) {
            perror("/proc");
            exit(1);
        }
        proc_fd = dirfd(dir);
    }
    rewinddir(dir);

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
        procs[n].stat_fd = procs[n].statm_fd = procs[n].cmdline_fd = -1;
        procs[n++].pid = atoi(de->d_name);
    }

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
    /* Before the first measurement (-t starting), by the average instead. */
    case COL_NOW:     r = p->now < 0 && q->now < 0 ? CMP(p->pcpu, q->pcpu)
                                                   : CMP(p->now, q->now); break;
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
        if (live) {
            /* Fixed "ddd.dd", so it doesn't jump around between refreshes; the
             * whole value plain, or dim if it didn't run at all. Before the
             * first measurement, the average stands in for it, dim too. */
            double v = p->now < 0 ? p->pcpu : p->now;
            snprintf(buf, size, color && p->now <= 0 ? DIM "%6.2f" RESET : "%6.2f", v);
        } else if (precise) {
            format_percent(buf, size, p->now, 5);
        } else {
            char num[64];
            snprintf(num, sizeof num, "%.2f", p->now);
            emit_number(buf, size, num, "");
        }
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

/* One line of the table into line (LINE_MAX_LEN); p == NULL gives the header. */
static void build_line(char *line, const proc_t *p, const enum column *cols, const int *widths,
                       int ncols) {
    char value[CMDLINE_MAX];
    size_t pos = 0;

    line[0] = 0;

    for (int i = 0; i < ncols; i++) {
        column_text(value, sizeof value, p, cols[i]);
        int pad = widths[i] - text_width(value);
        int left = columns[cols[i]].left;
        if (left && i == ncols - 1)
            pad = 0;  /* no trailing spaces after the last column */
        int n = snprintf(line + pos, LINE_MAX_LEN - pos, "%s%*s%s%*s", i ? "  " : "",
                         left ? 0 : pad, "", value, left ? pad : 0, "");
        if (n < 0 || (pos += n) >= LINE_MAX_LEN)
            break;
    }
}

static void print_line(const proc_t *p, const enum column *cols, const int *widths,
                       int ncols, int term_cols) {
    char line[LINE_MAX_LEN];
    build_line(line, p, cols, widths, ncols);
    print_cut(line, term_cols);
}

/* Widens each column to its widest value (or header); never narrows it. */
static void fit_widths(const proc_t *procs, size_t n, const enum column *cols, int ncols,
                       int *widths) {
    char value[CMDLINE_MAX];
    for (int i = 0; i < ncols; i++) {
        int w = text_width(columns[cols[i]].header);
        if (w > widths[i])
            widths[i] = w;
        for (size_t j = 0; j < n; j++) {
            format_value(value, sizeof value, &procs[j], cols[i]);
            w = text_width(value);
            if (w > widths[i])
                widths[i] = w;
        }
    }
}

static void free_procs(proc_t *procs, size_t n) {
    for (size_t i = 0; i < n; i++) {
        free(procs[i].cmd);
        close_proc_files(&procs[i]);
    }
    free(procs);
}

/* All processes that can be read, sorted by pid. If measure, also %NOW: the
 * CPU usage since prev (sorted by pid), sampled from interval_start_ns on. */
static size_t collect(proc_t **out, proc_t *prev, size_t nprev,
                      uint64_t interval_start_ns, int measure) {
    proc_t *procs;
    size_t n = scan_pids(&procs), kept = 0;
    for (size_t i = 0; i < n; i++) {
        proc_t *p = &procs[i];
        proc_t *before = bsearch(p, prev, nprev, sizeof *prev, compare_pid);

        /* Take over the files kept open since before, and what never changes. */
        if (before && before->stat_fd >= 0) {
            p->stat_fd = before->stat_fd;
            p->statm_fd = before->statm_fd;
            p->cmdline_fd = before->cmdline_fd;
            before->stat_fd = before->statm_fd = before->cmdline_fd = -1;
            p->uid = before->uid;
            memcpy(p->user, before->user, sizeof p->user);
        }
        if (read_proc(p) < 0 && p->user[0]) {
            /* The files were of a process that has exited; its PID may have
             * been reused by a new one. */
            close_proc_files(p);
            p->user[0] = 0;
            read_proc(p);
        }
        if (!p->cmd) {
            close_proc_files(p);
            continue;
        }
        if (measure) {
            if (before && before->sample_ns && before->start_ns == p->start_ns)
                p->now = 100.0 * (p->cpu_ns - before->cpu_ns) /
                         (p->sample_ns - before->sample_ns);
            else
                /* Started during the interval (or the PID was reused), so all
                 * of its CPU time was used within the interval. */
                p->now = 100.0 * p->cpu_ns / (p->sample_ns - interval_start_ns);
        } else {
            p->now = -1;
        }
        procs[kept++] = *p;
    }
    *out = procs;
    return kept;
}

/* First sample for %NOW: only start and CPU time. */
static size_t sample_all(proc_t **out) {
    size_t n = scan_pids(out);
    for (size_t i = 0; i < n; i++)
        if (read_sample(&(*out)[i]) < 0)
            (*out)[i].sample_ns = 0;  /* gone already */
    return n;
}

/* Whether p passes -a and the command filters. */
static int wanted(const proc_t *p) {
    if (!show_all && p->uid != geteuid())
        return 0;
    if (!nfilters)
        return 1;
    if (p->pid == getpid())
        return 0;  /* our own command line contains the filter */
    for (int f = 0; f < nfilters; f++)
        if (strcasestr(p->cmd, filters[f]))
            return 1;
    return 0;
}

/* Keeps the wanted processes of procs, in order; returns how many. */
static size_t filter_procs(proc_t *procs, size_t n) {
    size_t kept = 0;
    for (size_t i = 0; i < n; i++)
        if (wanted(&procs[i])) {
            procs[kept++] = procs[i];
        } else {
            free(procs[i].cmd);
            close_proc_files(&procs[i]);
        }
    return kept;
}

/* --- Live view (-t) ------------------------------------------------------- */

static volatile sig_atomic_t quit;

static void on_signal(int sig) {
    (void)sig;
    quit = 1;
}

/* Draws s from x up to (not including) column max_x, turning the BOLD, DIM
 * and RESET escapes that format_value() writes into styles. */
static void put_styled(mc_screen *scr, int x, int y, int max_x, const char *s, mc_style base) {
    mc_style style = base;
    while (*s && x < max_x) {
        if (*s == '\033') {
            if (strncmp(s, BOLD, strlen(BOLD)) == 0)
                style.attrs |= MC_AttrBold;
            else if (strncmp(s, DIM, strlen(DIM)) == 0)
                style.attrs |= MC_AttrDim;
            else
                style = base;
            s = skip_escape(s);
            continue;
        }
        s = mc_screen_put(scr, x++, y, s, style);
        if (!s)
            break;
    }
}

/* --- CPU and memory summary (-t) --- */

#define MAX_CPUS 1024

/* Cumulative times from /proc/stat, in ticks. */
struct cpu_times {
    uint64_t user;   /* user + nice */
    uint64_t sys;    /* system + irq + softirq + steal */
    uint64_t total;  /* the above + idle + iowait; 0: CPU offline */
};

/* Index 0 is all CPUs together, i + 1 is cpu i. */
static struct cpu_times cpu_before[MAX_CPUS + 1];
static double cpu_user[MAX_CPUS + 1], cpu_sys[MAX_CPUS + 1];  /* fractions, last interval */
static int ncpus;
static int cpu_measured;  /* cpu_user / cpu_sys hold a measurement */

/* CPUs grouped by core: core_cpus[core_first[c] .. core_first[c + 1]). */
static int core_cpus[MAX_CPUS], core_first[MAX_CPUS + 1], ncores;

static uint64_t mem_total, mem_used, swap_total, swap_used;  /* bytes */

static void read_cpu_times(struct cpu_times *t) {
    memset(t, 0, (MAX_CPUS + 1) * sizeof *t);
    FILE *f = fopen("/proc/stat", "r");
    if (!f)
        return;
    char line[512];
    while (fgets(line, sizeof line, f) && strncmp(line, "cpu", 3) == 0) {
        char *s = line + 3;
        int i = 0;
        if (*s != ' ') {
            i = strtol(s, &s, 10) + 1;
            if (i > MAX_CPUS)
                continue;
            if (i > ncpus)
                ncpus = i;
        }
        uint64_t v[8] = {0};
        for (int k = 0; k < 8; k++)
            v[k] = strtoull(s, &s, 10);
        /* user nice system idle iowait irq softirq steal */
        t[i].user = v[0] + v[1];
        t[i].sys = v[2] + v[5] + v[6] + v[7];
        t[i].total = t[i].user + t[i].sys + v[3] + v[4];
    }
    fclose(f);
}

/* Usage of each CPU since the last call. */
static void update_cpu_usage(void) {
    static struct cpu_times now[MAX_CPUS + 1];
    static int calls;
    read_cpu_times(now);
    for (int i = 0; i <= ncpus; i++) {
        uint64_t total = now[i].total - cpu_before[i].total;
        int valid = now[i].total && cpu_before[i].total && total;
        cpu_user[i] = valid ? (double)(now[i].user - cpu_before[i].user) / total : 0;
        cpu_sys[i] = valid ? (double)(now[i].sys - cpu_before[i].sys) / total : 0;
        cpu_before[i] = now[i];
    }
    cpu_measured = calls++ > 0;
}

static int read_topology_id(int cpu, const char *name) {
    char path[128], buf[32];
    snprintf(path, sizeof path, "/sys/devices/system/cpu/cpu%d/topology/%s", cpu, name);
    FILE *f = fopen(path, "r");
    if (!f)
        return -1;
    int id = fgets(buf, sizeof buf, f) ? atoi(buf) : -1;
    fclose(f);
    return id;
}

/* Groups the CPUs (hyperthreads) by core, cores in order of their first CPU. */
static void read_topology(void) {
    int package[MAX_CPUS], core[MAX_CPUS], done[MAX_CPUS] = {0};
    for (int c = 0; c < ncpus; c++) {
        package[c] = read_topology_id(c, "physical_package_id");
        core[c] = read_topology_id(c, "core_id");
    }
    int n = 0;
    ncores = 0;
    for (int c = 0; c < ncpus; c++) {
        if (done[c])
            continue;
        core_first[ncores++] = n;
        for (int d = c; d < ncpus; d++)
            if (!done[d] && (d == c || (core[c] >= 0 && package[d] == package[c] &&
                                        core[d] == core[c]))) {
                core_cpus[n++] = d;
                done[d] = 1;
            }
    }
    core_first[ncores] = n;
}

static void read_meminfo(void) {
    FILE *f = fopen("/proc/meminfo", "r");
    if (!f)
        return;
    char line[256];
    uint64_t available = 0, swap_free = 0;
    while (fgets(line, sizeof line, f)) {
        char *colon = strchr(line, ':');
        if (!colon)
            continue;
        uint64_t kb = strtoull(colon + 1, NULL, 10);
        *colon = 0;
        if (strcmp(line, "MemTotal") == 0)
            mem_total = kb << 10;
        else if (strcmp(line, "MemAvailable") == 0)
            available = kb << 10;
        else if (strcmp(line, "SwapTotal") == 0)
            swap_total = kb << 10;
        else if (strcmp(line, "SwapFree") == 0)
            swap_free = kb << 10;
    }
    fclose(f);
    mem_used = mem_total - available;
    swap_used = swap_total - swap_free;
}

static int put_text(mc_screen *scr, int x, int y, const char *text, mc_style style) {
    int n = mc_screen_put_str_styled(scr, x, y, text, style);
    return n > 0 ? x + n : x;
}

/* One cell per CPU, its usage as the height of a block; dim ▁ when idle.
 * The CPUs of a core touch, so every other one is gray instead of white. */
static int draw_cpu_cell(mc_screen *scr, int x, int y, int cpu, int gray) {
    static const char *const levels[] = {"▁", "▂", "▃", "▄", "▅", "▆", "▇", "█"};
    double used = cpu_user[cpu] + cpu_sys[cpu];
    int level = (int)(used * 8 + 0.5);
    mc_style style = mc_style_default();
    if (level == 0)
        style = mc_style_attributes(style, MC_AttrDim);
    else if (mc_screen_colors(scr) >= 256)
        style = mc_style_foreground(style, gray ? 245 : 15);
    else if (mc_screen_colors(scr) >= 16)
        style = mc_style_foreground(style, gray ? 7 : 15);
    mc_screen_put(scr, x, y, levels[level ? level - 1 : 0], style);
    return x + 1;
}

/* Draws the summary at the top: total CPU usage, a cell per CPU (a space
 * between cores), then memory and swap.
 * Returns the number of lines used. */
static double refresh_delay;  /* seconds */
static int paused;            /* space: no refreshing */

static int draw_summary(mc_screen *scr, int width) {
    char text[64];
    mc_style plain = mc_style_default();
    mc_style dim = mc_style_attributes(plain, MC_AttrDim);
    int x = 0, y = 0;

    x = put_text(scr, x, y, "cpu  ", dim);
    if (cpu_measured)
        snprintf(text, sizeof text, "%3.0f%%  ", 100 * (cpu_user[0] + cpu_sys[0]));
    else
        snprintf(text, sizeof text, "  -   ");
    int indent = put_text(scr, x, y, text, cpu_measured ? plain : dim);
    x = indent;
    for (int c = 0; c < ncores; c++) {
        int cells = core_first[c + 1] - core_first[c] + 1;
        if (x > indent && x + cells > width) {
            x = indent;  /* wrap, under the first core */
            y++;
        } else if (c) {
            x++;
        }
        for (int k = core_first[c]; k < core_first[c + 1]; k++)
            x = draw_cpu_cell(scr, x, y, core_cpus[k] + 1, (k - core_first[c]) % 2);
    }

    /* Memory after the CPUs, or on its own line if it doesn't fit. */
    snprintf(text, sizeof text, "%.1f/%.1fG", mem_used / 1073741824.0, mem_total / 1073741824.0);
    int mem_width = 5 + (int)strlen(text);
    x += 4;
    if (x + mem_width > width) {
        x = 0;
        y++;
    }
    x = put_text(scr, x, y, "mem  ", dim);
    x = put_text(scr, x, y, text, plain);
    if (swap_total) {
        x = put_text(scr, x + 4, y, "swap  ", dim);
        snprintf(text, sizeof text, "%.1f/%.1fG", swap_used / 1073741824.0,
                 swap_total / 1073741824.0);
        x = put_text(scr, x, y, text, plain);
    }

    /* At the right end of the first line: the refresh interval, or paused. */
    if (paused)
        snprintf(text, sizeof text, " paused ");
    else
        snprintf(text, sizeof text, "every %gs", refresh_delay);
    int len = (int)strlen(text);
    if ((y > 0 || x + 4 + len <= width) && len <= width)
        put_text(scr, width - len, 0, text,
                 paused ? mc_style_attributes(plain, MC_AttrReverse | MC_AttrBold) : dim);
    return y + 1;
}

static int visible_rows;  /* process lines on the screen, for PgUp / PgDn */

static void draw_top(mc_screen *scr, const proc_t *procs, size_t n, const enum column *cols,
                     int ncols, int *widths, int *scroll) {
    char line[LINE_MAX_LEN];
    int width, height;
    mc_screen_size(scr, &width, &height);
    mc_screen_clear(scr);

    int top = draw_summary(scr, width) + 1;  /* and an empty line */
    int rows = height - top - 1;
    visible_rows = rows;
    if (*scroll > (int)n - rows)
        *scroll = (int)n - rows;
    if (*scroll < 0)
        *scroll = 0;

    fit_widths(procs, n, cols, ncols, widths);
    mc_style header = mc_style_attributes(mc_style_default(), MC_AttrReverse);
    for (int x = 0; x < width; x++)
        mc_screen_set_content(scr, x, top, ' ', header);
    build_line(line, NULL, cols, widths, ncols);
    put_styled(scr, 0, top, width, line, header);

    for (int i = 0; i < rows && *scroll + i < (int)n; i++) {
        build_line(line, &procs[*scroll + i], cols, widths, ncols);
        put_styled(scr, 0, top + 1 + i, width, line, mc_style_default());
    }
    mc_screen_show(scr);
}

/* Like top: refreshes every delay seconds until q. */
static int run_top(const enum column *cols, int ncols, double delay) {
    mc_screen *scr = mc_screen_init(NULL);
    if (!scr) {
        perror("minips: mc_screen_init");
        return 1;
    }
    struct sigaction sa = {0};
    sa.sa_handler = on_signal;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGHUP, &sa, NULL);

    /* prev: every process at the last refresh, by pid, for %NOW.
     * view: the wanted ones, sorted for display (sharing prev's cmd). */
    proc_t *prev = NULL, *view = NULL;
    size_t nprev = 0, nview = 0;
    /* The first screen comes at once, without %CPU (nothing to compare with
     * yet); the first measurement after a shorter interval than the rest. */
    uint64_t interval_start_ns = clock_ns(CLOCK_BOOTTIME), next_ns = interval_start_ns;
    int first = 1;
    int widths[MAX_COLUMNS] = {0};
    refresh_delay = delay;
    int scroll = 0, redraw = 0;

    while (!quit) {
        uint64_t now_ns = clock_ns(CLOCK_BOOTTIME);
        if (!paused && now_ns >= next_ns) {
            proc_t *procs;
            size_t n = collect(&procs, prev, nprev, interval_start_ns, !first);
            free_procs(prev, nprev);
            prev = procs;
            nprev = n;
            interval_start_ns = now_ns;
            update_cpu_usage();
            if (first)
                read_topology();  /* needs ncpus, from the first update */
            read_meminfo();
            next_ns = now_ns + (uint64_t)((first && delay > 0.5 ? 0.5 : delay) * NS_PER_SEC);
            first = 0;

            free(view);
            view = malloc((n ? n : 1) * sizeof *view);
            nview = 0;
            for (size_t i = 0; i < n; i++)
                if (wanted(&procs[i]))
                    view[nview++] = procs[i];
            redraw = 1;
        }
        if (redraw) {
            qsort(view, nview, sizeof *view, compare_procs);
            draw_top(scr, view, nview, cols, ncols, widths, &scroll);
            redraw = 0;
        }

        int page = visible_rows > 1 ? visible_rows - 1 : 1;
        uint64_t wait_ns = next_ns - clock_ns(CLOCK_BOOTTIME);
        if ((int64_t)wait_ns < 0)
            wait_ns = 0;
        mc_event ev;
        int r = mc_screen_poll_event(scr, &ev, paused ? -1 : (int)(wait_ns / 1000000) + 1);
        if (r < 0)
            break;
        if (r == 0)
            continue;
        redraw = 1;
        if (ev.type != MC_EventKey)
            continue;  /* resize: just redraw */
        int ch = ev.key == MC_KeyRune ? (int)ev.rune : 0;
        if (ch == 'q' || ev.key == MC_KeyEscape || ev.key == MC_KeyCtrlC)
            break;
        else if (ev.key == MC_KeyUp)
            scroll--;
        else if (ev.key == MC_KeyDown)
            scroll++;
        else if (ev.key == MC_KeyPgUp)
            scroll -= page;
        else if (ev.key == MC_KeyPgDn)
            scroll += page;
        else if (ev.key == MC_KeyHome)
            scroll = 0;
        else if (ev.key == MC_KeyEnd)
            scroll = (int)nview;  /* draw_top clamps it */
        else if (ch == 'r')
            sort_desc = !sort_desc;
        else if (ch == ' ') {
            /* Resuming refreshes at once; that %CPU covers the pause too. */
            paused = !paused;
            next_ns = clock_ns(CLOCK_BOOTTIME);
        } else if (ch > 0 && ch < 128 && strchr("catemp", ch)) {
            static const char keys[] = "catemp";
            static const enum column by_key[] = {COL_NOW, COL_PCPU, COL_CPU, COL_TIME,
                                                 COL_RSS, COL_PID};
            sort_col = by_key[strchr(keys, ch) - keys];
            sort_desc = ch != 'p';  /* biggest (or longest running) on top */
            scroll = 0;
        }
    }

    mc_screen_fini(scr);
    free(view);
    free_procs(prev, nprev);
    return 0;
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
            "  -t, --top            live view like top, refreshed every -c SEC (default 1),\n"
            "                       busiest on top; keys: q quit, space pause, arrows/PgUp/\n"
            "                       PgDn/Home/End scroll, sort by c %%CPU, a average, t CPU\n"
            "                       time, e elapsed, m memory, p pid; r reverse\n"
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
        {"top",     no_argument,       NULL, 't'},
        {"all",     no_argument,       NULL, 'a'},
        {"precise", no_argument,       NULL, 'p'},
        {"help",    no_argument,       NULL, 'h'},
        {NULL, 0, NULL, 0},
    };

    double delay = 0;  /* 0: no current-usage measurement */
    const char *columns_arg = NULL;
    const char *sort_arg = NULL;
    int reverse = 0;
    int by_mem = 0;
    int top = 0;

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
    while ((opt = getopt_long(argc, argv, "c::o:s:mrtaphBKMG", long_options, NULL)) != -1) {
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
            by_mem = 1;
            break;
        case 't':
            top = 1;
            break;
        case 'r':
            reverse = 1;
            break;
        case 'a':
            show_all = 1;
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
    filters = argv + optind;
    nfilters = argc - optind;
    if (top && !delay)
        delay = 1;

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
    /* -c and -m put the biggest last, next to the prompt; on a live screen
     * the top is where you look. */
    if (top && (!sort_arg || by_mem))
        sort_desc = 1;
    sort_desc ^= reverse;

    int uses_now = sort_col == COL_NOW;
    for (int i = 0; i < ncols; i++)
        uses_now |= cols[i] == COL_NOW;
    if (uses_now && !delay) {
        fprintf(stderr, "minips: the 'now' (%%CPU) column needs -c\n");
        return 2;
    }

    /* Read only what is shown or sorted by; the live view can be re-sorted
     * by any of its keys. */
    stat_fields = columns[sort_col].stat_field;
    need_cmd = nfilters || sort_col == COL_CMD;
    need_rss = sort_col == COL_RSS || sort_col == COL_PMEM;
    for (int i = 0; i < ncols; i++) {
        if (columns[cols[i]].stat_field > stat_fields)
            stat_fields = columns[cols[i]].stat_field;
        need_cmd |= cols[i] == COL_CMD;
        need_rss |= cols[i] == COL_RSS || cols[i] == COL_PMEM;
    }
    if (top) {
        stat_fields = 22;  /* any key can sort by time, memory, ... */
        need_rss = 1;
    }

    /* Three files are kept open per process; allow as many as we may. */
    struct rlimit rl;
    if (getrlimit(RLIMIT_NOFILE, &rl) == 0 && rl.rlim_cur < rl.rlim_max) {
        rl.rlim_cur = rl.rlim_max;
        setrlimit(RLIMIT_NOFILE, &rl);
    }

    ticks_per_sec = sysconf(_SC_CLK_TCK);
    page_size = sysconf(_SC_PAGESIZE);
    total_ram = (uint64_t)sysconf(_SC_PHYS_PAGES) * page_size;

    if (top) {
        color = !getenv("NO_COLOR");
        live = 1;
        return run_top(cols, ncols, delay);
    }

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
        nfirst = sample_all(&first);

        struct timespec ts = {(time_t)delay, (long)((delay - (time_t)delay) * NS_PER_SEC)};
        while (nanosleep(&ts, &ts) < 0)
            ;
    }

    proc_t *procs;
    size_t shown = collect(&procs, first, nfirst, interval_start_ns, delay != 0);
    shown = filter_procs(procs, shown);
    qsort(procs, shown, sizeof *procs, compare_procs);

    int widths[MAX_COLUMNS] = {0};
    fit_widths(procs, shown, cols, ncols, widths);

    // print_line(NULL, cols, widths, ncols, term_cols);
    for (size_t i = 0; i < shown; i++)
        print_line(&procs[i], cols, widths, ncols, term_cols);
    /* The top header has scrolled away by now; repeat it next to the prompt.
     * Not when piped, where it would just be an extra line to filter out. */
    if (tty)
        print_line(NULL, cols, widths, ncols, term_cols);

    return 0;
}
