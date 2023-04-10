/* analysis.h - All analyzers based on AST traversal.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H

typedef struct ast_node_t ast_node_t;

/// \brief Variable usage analyzer.
///
/// Asserts listed below conditions.
///   - Function is unused.
///   - Variable is unused.
///   - Variable is written, but not read.
void analysis_variable_use_analysis(ast_node_t *root);

/// \brief Function analyzer.
///
/// \note Should be called after variable use analysis.
///
/// Asserts listed below conditions.
///   - Arguments size and types matches called function prototype.
///   - Return value matches its function return type.
void analysis_functions_analysis(ast_node_t *root);

/// \brief Type checker.
///
/// Asserts listed below conditions.
///
/// \note Should be called after variable use analysis and functions analysis.
///
/// <table>
///   <tr>
///     <th>Expression</th>
///     <th>Semantic</th>
///   </tr>
///   <tr>
///     <th>x + y</th>
///     <td>Same operand types (int, char, float, bool).</td>
///   </tr>
///   <tr>
///     <th>++x</th>
///     <td>Int or char operand type.</td>
///   </tr>
///   <tr>
///     <th>int f() { return 1; }</th>
///     <td>Return value is of function return type.</td>
///   </tr>
///   <tr>
///     <th>void f(int arg) {}, f(0)</th>
///     <td>Function argument is of type in signature.</td>
///   </tr>
///   <tr>
///     <th>mem[1] | mem[var]</th>
///     <td>Integer as array index.</td>
///   </tr>
/// </table>

void analysis_type_analysis(ast_node_t *root);

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USAGE_H