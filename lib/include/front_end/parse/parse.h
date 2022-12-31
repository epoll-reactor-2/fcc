/* parse.h - Syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_PARSE_PARSE_H
#define WEAK_COMPILER_FRONTEND_PARSE_PARSE_H

#include "front_end/ast/ast_compound.h"
#include "front_end/lex/tok.h"

ast_node_t *parse(const tok_t *begin, const tok_t *end);

#endif // WEAK_COMPILER_FRONTEND_PARSE_PARSE_H