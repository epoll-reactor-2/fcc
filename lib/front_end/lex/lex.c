/* lex.c - flex-based lexical analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include <stdio.h>
#include <stdlib.h>

static tok_array_t tokens = {0};

void lex_consume_token(tok_t *tok)
{
    vector_push_back(tokens, *tok);
}

tok_array_t *lex_consumed_tokens()
{
    return &tokens;
}

void lex_init_state()
{
    vector_init(tokens);
}

void lex_reset_state()
{
    vector_free(tokens);
}