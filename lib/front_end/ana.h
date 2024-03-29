/* ana.h - All analyzers based on AST traversal.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_FRONTEND_ANA_H
#define FCC_FRONTEND_ANA_H

struct ast_node;

/** \brief Variable usage analyzer.
  
    Asserts listed below conditions.
      - Function is unused.
      - Variable is unused.
      - Variable is written, but not read. */
void ana_var_usage(struct ast_node *root);

/** \brief Function analyzer.
   
    Asserts listed below conditions.
   
    \note Should be called after variable use analysis.
   
    <table>
      <tr>
        <th>Expression</th>
        <th>Semantic</th>
      </tr>
      <tr>
        <th>int f() { return 1; }</th>
        <td>Return value is of function return type.</td>
      </tr>
      <tr>
        <th>void f(int arg) {}, f(0)</th>
        <td>Function argument is of type in signature.</td>
      </tr>
    </table> */
void ana_fn(struct ast_node *root);

/** \brief Type checker.
   
    Asserts listed below conditions.
   
    \note Should be called after variable use analysis and functions analysis.
   
    <table>
      <tr>
        <th>Expression</th>
        <th>Semantic</th>
      </tr>
      <tr>
        <th>x + y</th>
        <td>Same integral or pointer types (int, char, float, bool).</td>
      </tr>
      <tr>
        <th>x <op> y</th>
        <td>Allowed operator applied to the operands.</td>
      </tr>
      <tr>
        <th>++x</th>
        <td>Int or char operand type.</td>
      </tr>
      <tr>
        <th>*x</th>
        <td>Pointer type with depth >= 1.</td>
      </tr>
      <tr>
        <th>mem[1] | mem[var]</th>
        <td>Integer as array index.</td>
      </tr>
    </table> */
void ana_type(struct ast_node *root);

#endif // FCC_FRONTEND_ANA_H