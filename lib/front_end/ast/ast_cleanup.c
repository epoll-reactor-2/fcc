/* ast_cleanup.h - Cleanup functions for the root AST type.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_float.h"
#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_bool.h"
#include "front_end/ast/ast_break.h"
#include "front_end/ast/ast_char.h"
#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_continue.h"
#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_node.h"
#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_string.h"
#include "front_end/ast/ast_struct_decl.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_while.h"
#include "utility/alloc.h"
#include "utility/unreachable.h"

void ast_node_cleanup(ast_node_t *ast)
{
    if (!ast) return;
    switch (ast->type) {
    case AST_CHAR_LITERAL:
        ast_char_cleanup(ast->ast);
        break;
    case AST_INTEGER_LITERAL:
        ast_num_cleanup(ast->ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        ast_float_cleanup(ast->ast);
        break;
    case AST_STRING_LITERAL:
        ast_string_cleanup(ast->ast);
        break;
    case AST_BOOLEAN_LITERAL:
        ast_bool_cleanup(ast->ast);
        break;
    case AST_SYMBOL:
        ast_symbol_cleanup(ast->ast);
        break;
    case AST_VAR_DECL:
        ast_var_decl_cleanup(ast->ast);
        break;
    case AST_ARRAY_DECL:
        ast_array_decl_cleanup(ast->ast);
        break;
    case AST_STRUCT_DECL:
        ast_struct_decl_cleanup(ast->ast);
        break;
    case AST_BREAK_STMT:
        ast_break_cleanup(ast->ast);
        break;
    case AST_CONTINUE_STMT:
        ast_continue_cleanup(ast->ast);
        break;
    case AST_BINARY:
        ast_binary_cleanup(ast->ast);
        break;
    case AST_PREFIX_UNARY:
        ast_unary_cleanup(ast->ast);
        break;
    case AST_POSTFIX_UNARY:
        ast_unary_cleanup(ast->ast);
        break;
    case AST_ARRAY_ACCESS:
        ast_array_access_cleanup(ast->ast);
        break;
    case AST_MEMBER:
        ast_member_cleanup(ast->ast);
        break;
    case AST_IF_STMT:
        ast_if_cleanup(ast->ast);
        break;
    case AST_FOR_STMT:
        ast_for_cleanup(ast->ast);
        break;
    case AST_WHILE_STMT:
        ast_while_cleanup(ast->ast);
        break;
    case AST_DO_WHILE_STMT:
        ast_do_while_cleanup(ast->ast);
        break;
    case AST_RETURN_STMT:
        ast_return_cleanup(ast->ast);
        break;
    case AST_COMPOUND_STMT:
        ast_compound_cleanup(ast->ast);
        break;
    case AST_FUNCTION_DECL:
        ast_function_decl_cleanup(ast->ast);
        break;
    case AST_FUNCTION_CALL:
        ast_function_call_cleanup(ast->ast);
        break;
    default:
        weak_unreachable("Should not reach here.");
    }
    weak_free(ast);
}