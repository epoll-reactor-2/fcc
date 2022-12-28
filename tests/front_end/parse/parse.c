/* parse.c - Test case for parser.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "utility/alloc.h"
#include <dirent.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

static bool is_directory(const char *path) {
    return strcmp(path,  ".") == 0
        || strcmp(path, "..") == 0;
}

int main() {
    char cwd[512];
    if (getcwd(cwd, sizeof(cwd)) == NULL) {
        perror("getcwd()");
        return 1;
    }

    sprintf(cwd + strlen(cwd), "/parser");

    DIR *dir_iterator = opendir(cwd);
    struct dirent *dir;

    if (!dir_iterator) {
        perror("opendir()");
        return -1;
    }

    while ((dir = readdir(dir_iterator)) != NULL) {
        if (is_directory(dir->d_name)) {
            continue;
        }

        char buf[1024];
        sprintf(buf, "%s/%s", cwd, dir->d_name);
        yyin = fopen(buf, "r");
        if (yyin == NULL) {
            perror("fopen()");
            return -1;
        }
        yylex();
        yylex_destroy();
    }

    closedir(dir_iterator);
}