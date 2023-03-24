/* ir_dump.c - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_dump.h"

void ir_dump_alloca(ir_alloca_t *ir) {}
void ir_dump_store(ir_store_t *ir) {}
void ir_dump_binary(ir_binary_t *ir) {}
void ir_dump_label(ir_label_t *ir) {}
void ir_dump_jump(ir_jump_t *ir) {}
void ir_dump_cond(ir_cond_t *ir) {}
void ir_dump_ret(ir_ret_t *ir) {}
void ir_dump_ret_void(ir_ret_t *ir) {}
void ir_dump_member(ir_member_t *ir) {}
void ir_dump_array_access(ir_array_access_t *ir) {}
void ir_dump_type_decl(ir_type_decl_t *ir) {}
void ir_dump_func_decl(ir_func_decl_t *ir) {}
void ir_dump_func_call(ir_func_call_t *ir) {}

int32_t ir_dump(FILE *mem, ir_node_t *ir, uint64_t ir_size)
{
    if (mem == NULL || ir == NULL) return -1;

    /// \todo Organize only function decls as global IR objects.
    ///       No unneeded checks
    ///         (ir_it.type != IR_FUNC_DECL)
    ///       for each stmt (waste of CPU time).
    for (uint64_t i = 0; i < ir_size; ++i) {
        ir_node_t ir_it = *(ir + i);
        if (ir_it.type != IR_FUNC_DECL)
            fprintf(mem, "    ");

        switch (ir->type) {
        case IR_ALLOCA: ir_dump_alloca(ir_it.ir); break;
        case IR_STORE: ir_dump_store(ir_it.ir); break;
        case IR_BINARY: ir_dump_binary(ir_it.ir); break;
        case IR_LABEL: ir_dump_label(ir_it.ir); break;
        case IR_JUMP: ir_dump_jump(ir_it.ir); break;
        case IR_COND: ir_dump_cond(ir_it.ir); break;
        case IR_RET: ir_dump_ret(ir_it.ir); break;
        case IR_RET_VOID: ir_dump_ret_void(ir_it.ir); break;
        case IR_MEMBER: ir_dump_member(ir_it.ir); break;
        case IR_ARRAY_ACCESS: ir_dump_array_access(ir_it.ir); break;
        case IR_TYPE_DECL: ir_dump_type_decl(ir_it.ir); break;
        case IR_FUNC_DECL: ir_dump_func_decl(ir_it.ir); break;
        case IR_FUNC_CALL: ir_dump_func_call(ir_it.ir); break;
        }
    }

    return 0;
}