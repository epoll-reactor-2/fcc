/* analysis.h - All analyzers based on AST traversal.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H

typedef struct ast_node_t ast_node_t;

void analysis_variable_use_analysis(ast_node_t *root);
void analysis_functions_analysis(ast_node_t *root);
void analysis_type_analysis(ast_node_t *root);

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H