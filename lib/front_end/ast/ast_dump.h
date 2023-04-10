/* ast_dump.h - AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H
#define WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H

#include "front_end/ast/ast_node.h"
#include <stdio.h>

/// Write AST represented as string to given file or memory stream.
///
/// \return 0 on success
///         1 on following errors:
///           - memory stream is NULL
///           - ast is NULL
///           - any required non-NULL AST node is NULL
int32_t ast_dump(FILE *mem, ast_node_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H
