/* sema.h - Semantic AST passes.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_FRONTEND_SEMA_H
#define FCC_FRONTEND_SEMA_H

struct ast_node;

/** Decrease abstraction level of AST.
   
    1. Replace range-based for loop with usual. */
void sema_lower(struct ast_node **ast);

/** Supplement AST with implicit type
    conversions. */
void sema_type(struct ast_node **ast);

#endif // FCC_FRONTEND_SEMA_H