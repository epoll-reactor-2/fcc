/* ast_storage.h - Storage for declarations being AST nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H

#include "front_end/ast/ast.h"
#include "front_end/lex/data_type.h"
#include "utility/vector.h"

typedef struct {
    ast_node_t  *ast;
    data_type_e  data_type;
    char        *name;
    uint16_t     read_uses; /// How many times variable was accessed.
    uint16_t     write_uses; /// How many times value was written to variable.
    uint16_t     depth; /// How much variable is nested.
} ast_storage_decl_t;

typedef vector_t(ast_storage_decl_t *) ast_storage_decl_array_t;

/// Initialize internal data, needed for correct scope depth
/// resolution.
void ast_storage_init_state();

/// Reset all internal data.
void ast_storage_reset_state();

/// Increment scope depth.
void ast_storage_start_scope();

/// Decrement scope depth, cleanup all most top scope records.
void ast_storage_end_scope();

/// Add record at current depth.
void ast_storage_push(const char *var_name, ast_node_t *ast);

/// \copydoc ast_storage_push(const char *, ast_node_t *)
void ast_storage_push_typed(const char *var_name, data_type_e dt, ast_node_t *ast);

/// Find storage by name.
///
/// \return Corresponding record if found, NULL otherwise.
ast_storage_decl_t *ast_storage_lookup(const char *var_name);

/// Add read use.
///
/// \pre Variable as declared before.
/// \pre Variable depth is <= current depth.
void ast_storage_add_read_use(const char *var_name);

/// Add read use.
///
/// \pre Variable as declared before.
/// \pre Variable depth is <= current depth.
void ast_storage_add_write_use(const char *var_name);

/// Collect all variable usages in current scope. Don't care
/// about reads and writes, though.
///
/// \todo  Order of output uses is undefined, since it operates on
///        hashmap, hence we don't have properly sorted by occurrence
///        warnings. Maybe, just sort result array?
void ast_storage_current_scope_uses(ast_storage_decl_array_t *out_set);

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H