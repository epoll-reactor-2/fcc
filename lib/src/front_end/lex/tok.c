/* tok.c - Definition of token.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/tok.h"

bool tok_is(const tok_t *tok, char symbol)
{
    return tok->type == tok_char_to_tok(symbol);
}