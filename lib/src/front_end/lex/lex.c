/* lex.c - flex-based lexical analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include <stdio.h>
#include <stdlib.h>

static tok_array_t consumed_tokens = {0};

void lex_consume_token(tok_t *tok)
{
    vector_push_back(consumed_tokens, *tok);
}

tok_array_t *lex_consumed_tokens()
{
    return &consumed_tokens;
}

void lex_init_global_state()
{
    vector_init(consumed_tokens);
}

void lex_cleanup_global_state()
{
    vector_free(consumed_tokens);
}