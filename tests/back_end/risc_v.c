/* risc_v.c - Test cases for RISC-V codegen.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "back_end/elf.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include "utils/test_utils.h"
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int risc_v_test(const char *path, unused const char *filename)
{
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    struct  ir_node    *it   = NULL;

    if (!setjmp(weak_fatal_error_buf)) {
        struct ir_unit unit = gen_ir(path);
        ir_type_pass(&unit);

        get_init_comment(yyin, expected_stream, NULL);

        /* ir_dump_unit(stdout, ir); */

        it = unit.fn_decls;
        while (it) {
            struct ir_fn_decl *decl = it->ir;
            /* Reordering before building CFG links. */
            ir_opt_reorder(decl);
            ir_opt_arith(decl);

            ir_cfg_build(decl);

            puts("");
            ir_dump(stdout, decl);

            /* Wrong
               ir_opt_unreachable_code(decl); */

            /* There is some trouble with
               data flow of input function
               parameters.

               ir_opt_data_flow(decl); */

            /* ir_dump_cfg(tmp_cfg, decl); */
            /* ir_dump(stdout, decl); */
            /* cfg_edges_dump(stdout, decl); */
            it = it->next;
        }

        struct codegen_output codegen_ctx = {0};

        struct elf_entry elf = {
            .arch     = ARCH_RISC_V,
            .filename = "__risc_v_gen.o"
        };
        elf_init(&elf);

        risc_v_gen(&codegen_ctx, &unit);

        // unused uint8_t risc_v_code[] = {
        //     0x41, 0x11, 0x22, 0xe4,
        //     0x81, 0x47,
        //     0x3e, 0x85, 0x22, 0x64,
        //     0x41, 0x01, 0x82, 0x80,
        // };

        // uint8_t  *code = (uint8_t *) codegen_ctx.instrs.data;
        // uint64_t  siz  = codegen_ctx.instrs.count;
        // elf_put_code(code, siz);

        /* TODO: Strings, other sections must be written to ELF file. */
        elf_exit();
        ir_unit_cleanup(&unit);
    } else {
        /* Error, will be printed in main. */
        return -1;
    }

    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);

    return 0;
}

int main()
{
    // do_on_each_file("risc_v", risc_v_test);
    return 0;
}
