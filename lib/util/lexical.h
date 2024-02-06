/* lexical.h - Text formatting and so on.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_LEXICAL_H
#define WEAK_COMPILER_UTIL_LEXICAL_H

#include <stdint.h>
#include "util/compiler.h"

unused static char color_red[]    = "\33[0;31m";
unused static char color_green[]  = "\33[0;32m";
unused static char color_yellow[] = "\33[0;33m";
unused static char color_blue[]   = "\33[1;34m";
unused static char color_purple[] = "\33[1;35m";
unused static char color_cyan[]   = "\33[0;36m";
unused static char color_end[]    = "\33[0m";

/** Convert integer to string in format "%d'postfix'.
  
    http://www.lifeprint.com/asl101/pages-signs/n/numbersordianlandcardinal.htm
  
    \param[out] out Requiers at most (sizeof (uint64_t) * CHAR_BIT + 4) bytes */
void ordinal_numeral(uint64_t num, char *out);

/** Like strcmp but ignore spaces. */
int istrcmp(const char *l, const char *r);

#endif // WEAK_COMPILER_UTIL_LEXICAL_H