/* tok.h - Definition of token.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_TOK_H
#define WEAK_COMPILER_FRONTEND_LEX_TOK_H

#include "front_end/lex/tok_type.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct {
    char       *data;
    tok_type_e  type;
    uint16_t    line_no;
    uint16_t    col_no;
} tok_t;

bool tok_is(const tok_t *tok, char symbol);

#endif // WEAK_COMPILER_FRONTEND_LEX_TOK_H