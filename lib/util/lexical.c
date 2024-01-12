/* lexical.c - Text formatting and so on.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/lexical.h"
#include <assert.h>
#include <ctype.h>
#include <stdio.h>

void ordinal_numeral(uint64_t num, char *out)
{
    assert(out && "Received NULL buffer");
    assert(num != 0 && "Ordinal numeral of 0 makes no sence");
    char *postfix = NULL;
    uint8_t n = num % 100;
    if (3 < n && n < 21) {
        postfix = "th";
    } else {
        switch (n % 10) {
        case 1:  postfix = "st"; break;
        case 2:  postfix = "nd"; break;
        case 3:  postfix = "rd"; break;
        default: postfix = "th"; break;
        }
    }
    sprintf(out, "%lu'%s", num, postfix);
}

int istrcmp(const char *l, const char *r)
{
    while (*l && *r) {
        while (isspace(*l)) ++l;
        while (isspace(*r)) ++r;

        if (*l != *r)
            return *l - *r;

        ++l; ++r;
    }

    while (isspace(*l)) ++l;
    while (isspace(*r)) ++r;

    return *l - *r;
}