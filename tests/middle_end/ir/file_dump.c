/* file_dump.c - Generate binary files with weak IR.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "utils/test_utils.h"
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

#if 1
#define DUMP(x, bytes) \
    { for (uint64_t i = 0; i < bytes; ++i) { \
        printf("%X ", ((char *)(x))[i]); \
      } puts(""); }
#else
#define DUMP(...)
#endif

/* TODO: Extract binary file and verify. */
#define IR_FWRITE(x) \
    { fwrite (&(x), sizeof ((x)), 1, mem); \
      DUMP (&(x), sizeof ((x))); \
    }

#define IR_FWRITE_PTR(x) \
    { fwrite ((x), sizeof (*(x)), 1, mem); \
      DUMP ((x), sizeof (*(x))); \
    }

/**********************************************
 **               Binary dump                **
 **********************************************/
void dump_node(FILE *mem, struct ir_node *ir);

void dump_alloca(FILE *mem, struct ir_node *ir)
{
    struct ir_alloca *alloca = ir->ir;
    puts("dump_alloca");

    IR_FWRITE(ir->type);
    IR_FWRITE_PTR(alloca);
}

void dump_alloca_array(FILE *mem, struct ir_node *ir)
{
    struct ir_alloca_array *alloca = ir->ir;
    puts("dump_alloca_array");

    IR_FWRITE(ir->type);
    IR_FWRITE_PTR(alloca);
}

void dump_imm(FILE *mem, struct ir_node *ir)
{
    struct ir_imm *imm = ir->ir;
    puts("dump_imm");

    IR_FWRITE(ir->type);
    // IR_FWRITE_PTR(imm);
    IR_FWRITE(imm->type);
    IR_FWRITE(imm->imm);
}

void dump_string(FILE *mem, struct ir_node *ir)
{
    (void) mem; (void) ir;
}

void dump_sym(FILE *mem, struct ir_node *ir)
{
    struct ir_sym *sym = ir->ir;
    puts("dump_sym");

    IR_FWRITE(ir->type);
    IR_FWRITE(sym->deref);
    IR_FWRITE(sym->addr_of);
    IR_FWRITE(sym->idx);
    IR_FWRITE(sym->ssa_idx);
}

void dump_store(FILE *mem, struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    puts("dump_store");

    IR_FWRITE(ir->type);
    dump_node(mem, store->idx);
    dump_node(mem, store->body);
}

void dump_bin(FILE *mem, struct ir_node *ir)
{
    struct ir_bin *bin = ir->ir;
    puts("dump_bin");

    IR_FWRITE(ir->type);
    IR_FWRITE(bin->op);
    dump_node(mem, bin->lhs);
    dump_node(mem, bin->rhs);
}

void dump_jump(FILE *mem, struct ir_node *ir)
{
    struct ir_jump *jump = ir->ir;
    puts("dump_jump");

    IR_FWRITE(ir->type);
    IR_FWRITE(jump->idx);
    dump_node(mem, jump->target);
}

void dump_cond(FILE *mem, struct ir_node *ir)
{
    struct ir_cond *cond = ir->ir;
    puts("dump_cond");

    IR_FWRITE(ir->type);
    dump_node(mem, cond->cond);
    IR_FWRITE(cond->goto_label);
    dump_node(mem, cond->target);
}

void dump_ret(FILE *mem, struct ir_node *ir)
{
    struct ir_ret *ret = ir->ir;
    puts("dump_ret");

    IR_FWRITE(ir->type);
    dump_node(mem, ret->body);
}

void dump_member(FILE *mem, struct ir_node *ir)
{
    (void) mem; (void) ir;
}

void dump_type_decl(FILE *mem, struct ir_node *ir)
{
    (void) mem; (void) ir;
}

void dump_fn_call(FILE *mem, struct ir_node *ir)
{
    struct ir_fn_call *call = ir->ir;
    puts("dump_fn_call");

    IR_FWRITE(ir->type);
    (void) call;
}

void dump_phi(FILE *mem, struct ir_node *ir)
{
    (void) mem; (void) ir;
}

void dump_fn_decl(FILE *mem, struct ir_node *ir)
{
    struct ir_fn_decl *decl = ir->ir;
    struct ir_node *it = decl->args;
    while (it) {
        dump_alloca(mem, it);
        it = it->next;
    }

    it = decl->body;
    while (it) {
        dump_node(mem, it);
        it = it->next;
    }
}

void dump_node(FILE *mem, struct ir_node *ir)
{
    if (!ir) {
        /* TODO: Write NULL. */
        return;
    }

    switch (ir->type) {
    case IR_ALLOCA:       dump_alloca(mem, ir); break;
    case IR_ALLOCA_ARRAY: dump_alloca_array(mem, ir); break;
    case IR_IMM:          dump_imm(mem, ir); break;
    case IR_STRING:       dump_string(mem, ir); break;
    case IR_SYM:          dump_sym(mem, ir); break;
    case IR_STORE:        dump_store(mem, ir); break;
    case IR_BIN:          dump_bin(mem, ir); break;
    case IR_JUMP:         dump_jump(mem, ir); break;
    case IR_COND:         dump_cond(mem, ir); break;
    case IR_RET:          dump_ret(mem, ir); break;
    case IR_MEMBER:       dump_member(mem, ir); break;
    case IR_TYPE_DECL:    dump_type_decl(mem, ir); break;
    case IR_FN_DECL:      dump_fn_decl(mem, ir); break;
    case IR_FN_CALL:      dump_fn_call(mem, ir); break;
    case IR_PHI:          dump_phi(mem, ir); break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}
 
void dump_unit(FILE *mem, struct ir_unit *ir)
{
    struct ir_node *it = ir->fn_decls;
    while (it) {
        dump_fn_decl(mem, it);
        it = it->next;
    }}

/**********************************************
 **              Driver code                 **
 **********************************************/
void dump_binary(struct ir_unit *ir, const char *filename)
{
    char out_path[256] = {0};

    snprintf(out_path, 255, "binary_dumps/%s.dot", filename);

    FILE *out_stream   = fopen(out_path, "w");

    dump_unit(out_stream, ir);

    fclose(out_stream);
}

int dump(const char *path, unused const char *filename)
{
    struct ir_unit ir = gen_ir(path);
    dump_binary(&ir, filename);
    ir_unit_cleanup(&ir);

    return 0;
}

void configure()
{
    create_dir("binary_dumps");
}

int run()
{
    return do_on_each_file("ir_gen", dump);
}

int main()
{
    configure();

    return run();
}