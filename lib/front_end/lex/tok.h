/* tok.h - Definition of token.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_FRONTEND_LEX_TOK_H
#define FCC_FRONTEND_LEX_TOK_H

#include "front_end/lex/tok_type.h"
#include "util/compiler.h"
#include <stdbool.h>
#include <stdint.h>

struct token {
    char            *data;
    enum token_type  type;
    uint16_t         line_no;
    uint16_t         col_no;
};

wur bool tok_is(const struct token *tok, char symbol);

#endif // FCC_FRONTEND_LEX_TOK_H