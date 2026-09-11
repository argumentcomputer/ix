#include <errno.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* Fork from this small image: Linux preserves a process's pre-exec RSS
 * high-water mark, which would otherwise include the Lean runner's memory.
 * The child starts with this launcher's current resident set. Startup and
 * this fork are outside every recorded native timing interval. */
int main(int argc, char **argv) {
  if (argc < 2) return 2;
  pid_t child = fork();
  if (child < 0) { perror("benchmark worker fork"); return 2; }
  if (child == 0) {
    execv(argv[1], argv + 1);
    perror("benchmark worker exec");
    _exit(127);
  }
  int status;
  while (waitpid(child, &status, 0) < 0) {
    if (errno == EINTR) continue;
    perror("benchmark worker wait");
    return 2;
  }
  if (WIFEXITED(status)) return WEXITSTATUS(status);
  if (WIFSIGNALED(status)) return 128 + WTERMSIG(status);
  return 2;
}
