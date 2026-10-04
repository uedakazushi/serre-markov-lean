#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
  ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
  char self_numeric[64];
  snprintf(self_numeric, sizeof self_numeric, "/proc/%d/exe", (int)getpid());
  if (strcmp(path, self_numeric) == 0) path = "/proc/self/exe";
  return original(path, buf, size);
}
