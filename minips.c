#include "read_buffer.h"

#include <dirent.h>
#include <fcntl.h>
#include <pwd.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#define CMDLINE_MAX 4096
/* /proc/<pid>/<file>, with d_name up to 255 chars */
#define PATH_LEN 300

static int is_pid(const char *s) {
    if (!*s)
        return 0;
    for (; *s; s++)
        if (*s < '0' || *s > '9')
            return 0;
    return 1;
}

static int open_proc(const char *pid, const char *file) {
    char path[PATH_LEN];
    snprintf(path, sizeof path, "/proc/%s/%s", pid, file);
    return open(path, O_RDONLY);
}

/* Field 22 of /proc/<pid>/stat: start time in clock ticks since boot.
 * Field 2 is "(comm)", which may contain spaces, so we skip past ')'. */
static int read_starttime(const char *pid, uint64_t *out) {
    int fd = open_proc(pid, "stat");
    if (fd < 0)
        return -1;

    int ok = read_start(fd) == read_result_ok && skip_past(')') == read_result_ok;
    for (int field = 3; ok && field < 22; field++)
        ok = skip_next() == read_result_ok;
    ok = ok && read_next_uint64(out) == read_result_ok;

    close(fd);
    return ok ? 0 : -1;
}

/* CPU time of the whole process in nanoseconds, including threads that
 * have already exited. */
static int read_cputime_ns(const char *pid, uint64_t *out) {
    pid_t p = 0;
    for (; *pid; pid++)
        p = p * 10 + (*pid - '0');

    clockid_t clock;
    struct timespec ts;
    if (clock_getcpuclockid(p, &clock) != 0 || clock_gettime(clock, &ts) < 0)
        return -1;

    *out = (uint64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
    return 0;
}

/* cmdline is NUL-separated raw bytes, not whitespace-separated tokens,
 * so it is read directly rather than through read_buffer. */
static ssize_t read_raw(const char *pid, const char *file, char *buf, size_t size) {
    int fd = open_proc(pid, file);
    if (fd < 0)
        return -1;

    size_t total = 0;
    ssize_t n;
    while (total < size - 1 && (n = read(fd, buf + total, size - 1 - total)) > 0)
        total += n;
    close(fd);
    buf[total] = 0;
    return total;
}

static void read_cmdline(const char *pid, char *buf, size_t size) {
    ssize_t n = read_raw(pid, "cmdline", buf, size);
    if (n > 0) {
        while (n > 0 && buf[n - 1] == 0)
            n--;
        /* NULs separate arguments; other control characters (e.g. a newline
         * inside an argument) would break the one-line-per-process layout. */
        for (ssize_t i = 0; i < n; i++)
            if (buf[i] == 0)
                buf[i] = ' ';
            else if ((unsigned char)buf[i] < 0x20 || buf[i] == 0x7f)
                buf[i] = '?';
        buf[n] = 0;
        return;
    }

    /* Kernel threads have no cmdline: show [comm] like ps does. */
    char comm[32];
    n = read_raw(pid, "comm", comm, sizeof comm);
    if (n > 0 && comm[n - 1] == '\n')
        comm[n - 1] = 0;
    snprintf(buf, size, "[%s]", n > 0 ? comm : "?");
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

static uint64_t clock_ns(clockid_t clock) {
    struct timespec ts;
    clock_gettime(clock, &ts);
    return (uint64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
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

static void print_process(const char *pid, long ticks_per_sec, int term_cols) {
    char path[PATH_LEN];
    struct stat st;
    snprintf(path, sizeof path, "/proc/%s", pid);
    if (stat(path, &st) < 0)
        return;

    uint64_t start_ticks;
    if (read_starttime(pid, &start_ticks) < 0)
        return;
    uint64_t start_ns = start_ticks * 1000000000 / ticks_per_sec;

    uint64_t cpu_ns;
    if (read_cputime_ns(pid, &cpu_ns) < 0)
        return;
    /* Read right after the CPU time so both describe the same moment. */
    uint64_t elapsed_ns = clock_ns(CLOCK_BOOTTIME) - start_ns;
    double cpu_percent = elapsed_ns ? 100.0 * cpu_ns / elapsed_ns : 0;

    static char cmdline[CMDLINE_MAX];
    read_cmdline(pid, cmdline, sizeof cmdline);

    /* Elapsed time is only precise to 1/100 s (ticks in stat), CPU time is
     * shown to the microsecond. */
    int used = printf("%7s %-8s %9" PRIu64 ".%02" PRIu64 "s %8" PRIu64 ".%06" PRIu64 "s %11.5f ",
                      pid, user_name(st.st_uid),
                      elapsed_ns / 1000000000, elapsed_ns % 1000000000 / 10000000,
                      cpu_ns / 1000000000, cpu_ns % 1000000000 / 1000,
                      cpu_percent);
    print_cut(cmdline, term_cols < 0 ? -1 : (term_cols > used ? term_cols - used : 0));
}

int main(void) {
    long ticks_per_sec = sysconf(_SC_CLK_TCK);

    /* Cut lines to the terminal width; when piped, print everything. */
    struct winsize ws;
    int term_cols = -1;
    if (isatty(STDOUT_FILENO) && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
        term_cols = ws.ws_col;

    DIR *proc = opendir("/proc");
    if (!proc) {
        perror("/proc");
        return 1;
    }

    printf("%7s %-8s %13s %16s %11s %s\n",
           "PID", "USER", "ELAPSED", "CPU", "%CPU", "CMD");

    struct dirent *de;
    while ((de = readdir(proc)))
        if (is_pid(de->d_name))
            print_process(de->d_name, ticks_per_sec, term_cols);

    closedir(proc);
    return 0;
}
