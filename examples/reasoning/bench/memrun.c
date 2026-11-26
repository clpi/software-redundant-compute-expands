/* memrun: run a command, print its peak resident memory (KiB) and exit status on stderr's last line.
   A forked child inherits its parent's peak RSS across exec on Linux, so the measuring parent must
   itself be tiny; this one is a few hundred KiB, so small solver runs are not floored by Python. */
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
int main(int argc, char **argv) {
    if (argc < 2) return 2;
    pid_t pid = fork();
    if (pid == 0) { setsid(); execvp(argv[1], argv + 1); _exit(127); }
    int st; struct rusage ru;
    wait4(pid, &st, 0, &ru);
    fprintf(stderr, "\n@@memrun maxrss_kib=%ld exit=%d\n", ru.ru_maxrss, WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st));
    return WIFEXITED(st) ? WEXITSTATUS(st) : 1;
}
