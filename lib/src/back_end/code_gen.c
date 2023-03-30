/* code_gen.c - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

/////////////////////////////
/// Super important note. ///
/////////////////////////////
///
/// This is a junk. Will be in git history but actually to throw out.

#include "back_end/code_gen.h"
#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_node.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_var_decl.h"
#include "utility/alloc.h"
#include "utility/crc32.h"
#include "utility/hashmap.h"
#include "utility/unreachable.h"
#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

/// Function argument to refer to.
typedef struct stack_arg_t {
    int32_t     offset;
    int32_t     instr_size;
    const char *name;
} stack_arg_t;

static FILE *emit_file;
static hashmap_t stack_args;
static stack_arg_t *stack_last_arg;
static int32_t stack_offset = 0;

static void code_gen_init_state()
{
    emit_file = fopen("/tmp/__code_dump.s", "w");
    if (!emit_file) {
        perror("fopen()");
        exit(0);
    }
}

static void code_gen_reset_state()
{
    fclose(emit_file);
}

static void func_init_state()
{
    hashmap_init(&stack_args, 100);
    stack_offset = 0;
}

static void func_reset_state()
{
    hashmap_foreach(&stack_args, var_hash, arg_addr) {
        (void)var_hash;
        weak_free((void *)arg_addr);
    }
    hashmap_destroy(&stack_args);
    stack_offset = 0;
}

static stack_arg_t *stack_arg_get(const char *name)
{
    size_t addr = hashmap_get(&stack_args, crc32_string(name));
    return addr ? (stack_arg_t *)addr : NULL;
}

static void emit(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(emit_file, fmt, args);
    va_end(args);
    fputc('\n', emit_file);
}

static uint32_t decl_bytes_size(ast_var_decl_t *decl)
{
    /// Pointer.
    if (decl->indirection_lvl > 0)
        return 8;

    switch (decl->dt) {
    case D_T_BOOL:   return 1;
    case D_T_CHAR:   return 1;
    case D_T_INT:    return 4;
    case D_T_FLOAT:  return 4;
    case D_T_STRUCT: return 8; /// I don't give a fuck.
                               /// \todo: Calculate size of structure.
    default: weak_unreachable("Invalid data type");
    }
}

static int32_t num_align_to(int32_t num, int32_t to)
{
    int mask = to - 1;
    return num + (-num & mask);
}

static void visit_ast_node(ast_node_t *ast);

static void visit_ast_char(ast_node_t *ast) {}
static void visit_ast_num(ast_node_t *ast) {}
static void visit_ast_float(ast_node_t *ast) {}
static void visit_ast_string(ast_node_t *ast) {}
static void visit_ast_bool(ast_node_t *ast) {}
static void visit_ast_struct_decl(ast_node_t *ast) {}
static void visit_ast_break(ast_node_t *ast) {}
static void visit_ast_continue(ast_node_t *ast) {}

static void visit_ast_symbol(ast_node_t *ast)
{
    ast_symbol_t *stmt = ast->ast;
    stack_last_arg = stack_arg_get(stmt->value);

    printf(
        "Argument: %s, offset: -%d, instr size: %d\n",
        stack_last_arg->name,
        stack_last_arg->offset,
        stack_last_arg->instr_size
    );
    fflush(stdout);
}

static void visit_ast_var_decl(ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    int32_t size = decl_bytes_size(decl);

    printf("Size: %d\n", size);
    printf("Stack offset before: %d\n", stack_offset);
    stack_offset += size;
    stack_offset = num_align_to(stack_offset, size);
    printf("Stack offset after:  %d\n", stack_offset);

    stack_arg_t *arg = weak_calloc(1, sizeof( stack_arg_t));
    arg->offset = stack_offset;
    arg->instr_size = size;
    arg->name = decl->name;

    hashmap_put(&stack_args, crc32_string(decl->name), (size_t)arg);
    printf("Push `%s`\n", decl->name);
    fflush(stdout);

    /// \todo: Other types.
    if (decl->dt == D_T_INT) {
        /// \todo: Not 1, just constant or something else.
        emit("\tmovl    $1, -%d(%%rbp)", stack_offset);
    }
}

static void visit_ast_array_decl(ast_node_t *ast) {}

static char solve_instr_size_postfix(int32_t instr_size)
{
    switch (instr_size) {
    case 1: return 'b';
    case 4: return 'l';
    case 8: return 'q';
    default: weak_unreachable("Wrong type size");
    }
}

static char *solve_opcode(tok_type_e op, int32_t instr_size)
{
    char size = solve_instr_size_postfix(instr_size);
    static char opcode[32];
    switch (op) {
    case TOK_PLUS:  sprintf(opcode, "add%c",  size); break;
    case TOK_MINUS: sprintf(opcode, "sub%c",  size); break;
    case TOK_STAR:  sprintf(opcode, "imul%c", size); break;
    case TOK_SLASH: sprintf(opcode, "div%c",  size); break;
    default: weak_unreachable("Todo other operations. Not urgent.");
    }

    return opcode;
}

static void visit_ast_binary(ast_node_t *ast)
{
    ast_binary_t *stmt = ast->ast;

    visit_ast_node(stmt->lhs);
    stack_arg_t *l_arg = stack_last_arg;
    visit_ast_node(stmt->rhs);
    stack_arg_t *r_arg = stack_last_arg;

    printf(
        "Binary (`%s`, -%d(%%rbp)), (`%s`, -%d(%%rbp))\n",
        l_arg->name,
        l_arg->offset,
        r_arg->name,
        r_arg->offset
    );
    fflush(stdout);

    /// \todo: Store two values in two any free registers,
    ///        then do operation, e.g.
    ///
    ///        ... move to eax ...
    ///        ... move to ebx ...
    ///        addl %eax, %ebx
    ///

    char size = solve_instr_size_postfix(l_arg->instr_size);
    char *opcode = solve_opcode(stmt->operation, l_arg->instr_size);

    /// \todo: Not eax, ebx but corresponding size registers.
    emit("\tmov%c   -%d(%%rbp), %%eax", size, l_arg->offset);
    emit("\tmov%c   -%d(%%rbp), %%ebx", size, r_arg->offset);
    emit("\t%-5s  %%ebx, %%eax", opcode);
}

static void visit_ast_unary(ast_node_t *ast) {}
static void visit_ast_array_access(ast_node_t *ast) {}
static void visit_ast_member(ast_node_t *ast) {}
static void visit_ast_if(ast_node_t *ast) {}
static void visit_ast_for(ast_node_t *ast) {}
static void visit_ast_while(ast_node_t *ast) {}
static void visit_ast_do_while(ast_node_t *ast) {}

static void visit_ast_return(ast_node_t *ast)
{
    ast_return_t *stmt = ast->ast;
    if (stmt->operand)
        visit_ast_node(stmt->operand);
    /// \todo: Determine where result of any operation
    ///        (unary, binary, function call) will be
    ///        stored. Now assume that is %...ax
    emit("\tcltq"); /// eax to rax
    emit("\tmovq   %%rax, %%rdi"); /// exit()
}

static void visit_ast_compound(ast_node_t *ast)
{
    ast_compound_t *stmt = ast->ast;
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_ast_node(stmt->stmts[i]);
}

/// State for function call. Stores information about
/// occupied by parameters registers.
///
/// \todo: Function to select first free register.
typedef struct {
    struct {
        bool ah : 1;
        bool al : 1;
        bool bh : 1;
        bool bl : 1;
        bool ch : 1;
        bool cl : 1;
        bool dh : 1;
        bool dl : 1;
    } _8_bit;

    struct {
        bool eax : 1;
        bool ebx : 1;
        bool ecx : 1;
        bool edx : 1;
    } _32_bit;

    struct {
        bool rax : 1;
        bool rbx : 1;
        bool rcx : 1;
        bool rdx : 1;
    } _64_bit;
} reg_state_t;

static const char *reg_first_8_bit(reg_state_t *state)
{
    if (!state->_8_bit.ah) { state->_8_bit.ah = 1; return "al"; }
    if (!state->_8_bit.al) { state->_8_bit.al = 1; return "ah"; }
    if (!state->_8_bit.bh) { state->_8_bit.bh = 1; return "bl"; }
    if (!state->_8_bit.bl) { state->_8_bit.bl = 1; return "bh"; }
    if (!state->_8_bit.ch) { state->_8_bit.ch = 1; return "cl"; }
    if (!state->_8_bit.cl) { state->_8_bit.cl = 1; return "ch"; }
    if (!state->_8_bit.dh) { state->_8_bit.dh = 1; return "dl"; }
    if (!state->_8_bit.dl) { state->_8_bit.dl = 1; return "dh"; }
    return NULL;
}

static const char *reg_first_32_bit(reg_state_t *state)
{
    if (!state->_32_bit.eax) { state->_32_bit.eax = 1; return "eax"; }
    if (!state->_32_bit.ebx) { state->_32_bit.ebx = 1; return "ebx"; }
    if (!state->_32_bit.ecx) { state->_32_bit.ecx = 1; return "ecx"; }
    if (!state->_32_bit.edx) { state->_32_bit.edx = 1; return "edx"; }
    return NULL;
}

static const char *reg_first_64_bit(reg_state_t *state)
{
    if (!state->_64_bit.rax) { state->_64_bit.rax = 1; return "rax"; }
    if (!state->_64_bit.rbx) { state->_64_bit.rbx = 1; return "rbx"; }
    if (!state->_64_bit.rcx) { state->_64_bit.rcx = 1; return "rcx"; }
    if (!state->_64_bit.rdx) { state->_64_bit.rdx = 1; return "rdx"; }
    return NULL;
}

/// \param reg_postfix b -  8 bits
///                    l - 32 bits
///                    q - 64 bits
static void emit_arg(int32_t instr_size, const char *name, const char *reg, int32_t frame_ptr_offset)
{
    char size = solve_instr_size_postfix(instr_size);
    if (reg) {
        /// \todo: Push arguments to some storage in order
        ///        to refer later.
        ///
        ///        { - stack offset
        ///            -N(%rbp),
        ///          - string variable name }
        emit("\tmov%c   %%%s, -%d(%%rbp)", size, reg, frame_ptr_offset);
        stack_arg_t *arg = weak_calloc(1, sizeof( stack_arg_t));
        arg->offset = frame_ptr_offset;
        arg->instr_size = instr_size;
        arg->name = name;
        hashmap_put(&stack_args, crc32_string(name), (size_t)arg);
    } else
        /// No more registers. Push onto stack.
        /// ...
        ///
        ///
        ;
}

static void emit_var_fun_arg(ast_var_decl_t *decl, reg_state_t *reg_state, int32_t *frame_ptr_offset)
{
    uint32_t size = decl_bytes_size(decl);
    *frame_ptr_offset += size;
    int off = num_align_to(*frame_ptr_offset, size);

    switch (size) {
    case 1: {
        const char *reg = reg_first_8_bit(reg_state);
        emit_arg(1, decl->name, reg, off);
        break;
    }
    case 4: {
        const char *reg = reg_first_32_bit(reg_state);
        emit_arg(4, decl->name, reg, off);
        break;
    }
    case 8: {
        const char *reg = reg_first_64_bit(reg_state);
        emit_arg(8, decl->name, reg, off);
        break;
    }
    }
}

static void emit_fun_args(ast_compound_t *args)
{
    reg_state_t reg_state = {0};
    int32_t frame_ptr_offset = 0;

    for (uint64_t i = 0; i < args->size; ++i) {
        ast_node_t *stmt = args->stmts[i];
        ast_type_e t = stmt->type;
        switch (t) {
        case AST_VAR_DECL:
            emit_var_fun_arg(stmt->ast, &reg_state, &frame_ptr_offset);
            break;
        case AST_ARRAY_DECL:
            weak_unreachable(
                "Arrays as function arguments are not supported. "
                "Use pointers instead."
            );
        default: break;
        }
    }
}

static void visit_ast_function_decl(ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    bool is_main = !strcmp(decl->name, "main");

    func_init_state();

    if (is_main)
        emit("_start:");
    else
        emit("%s:", decl->name);

    emit("\tpushq  %rbp");
    emit("\tmovq   %rsp, %rbp");
    /// \todo: This is for empty functions without any
    ///        instructions. Throw out if isn't needed.
    emit("\tnop");

    /// \todo: This is actually isn't needed?
    ///        Arguments are already on stack. Don't
    ///        occupy all registers at one needlessly.
    ast_compound_t *args = decl->args->ast;
    emit_fun_args(args);

    visit_ast_node(decl->body);

    if (is_main) {
        /// Return value in %rdi will determined
        /// in return AST visitor.
        emit("\tmov    $60, %rax"); /// exit()
        /// emit("\txor    %rdi, %rdi");
        emit("\tsyscall");
    } else {
        emit("\tpopq   %rbp");
        emit("\tret");
    }
    func_reset_state();

    ///\todo: Collect all string literals and emit at the end
    ///       of the file.
    ///
    /// emit("message:");
    /// emit("\t.ascii \"Hello, World\"");
}

static void visit_ast_function_call(ast_node_t *ast) {}

void visit_ast_node(ast_node_t *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL:
        visit_ast_char(ast);
        break;
    case AST_INTEGER_LITERAL:
        visit_ast_num(ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_ast_float(ast);
        break;
    case AST_STRING_LITERAL:
        visit_ast_string(ast);
        break;
    case AST_BOOLEAN_LITERAL:
        visit_ast_bool(ast);
        break;
    case AST_STRUCT_DECL:
        visit_ast_struct_decl(ast);
        break;
    case AST_BREAK_STMT:
        visit_ast_break(ast);
        break;
    case AST_CONTINUE_STMT:
        visit_ast_continue(ast);
        break;
    case AST_SYMBOL:
        visit_ast_symbol(ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(ast);
        break;
    case AST_BINARY:
        visit_ast_binary(ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(ast);
        break;
    case AST_MEMBER:
        visit_ast_member(ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(ast);
        break;
    default:
        weak_unreachable("Wrong AST type");
    }
}

void code_gen(ast_node_t *root)
{
    code_gen_init_state();
    emit("\t.global _start");
    emit("\t.text");
    visit_ast_node(root);
    code_gen_reset_state();
}