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

char current_output_dir[128];

int risc_v_test(const char *path, unused const char *filename)
{
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    struct  ir_node    *it   = NULL;
    char    out_path[256]    = {0};

    snprintf(out_path, 255, "%s/%s.o", current_output_dir, filename);

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

        struct codegen_output output = {0};
        hashmap_init(&output.fn_offsets, 512);

        risc_v_gen(&output, &unit);

        struct elf_entry elf = {
            .arch     = ARCH_RISC_V,
            .filename = out_path,
            .output   = output
        };
        elf_init(&elf);
        elf_exit();

        hashmap_destroy(&output.fn_offsets);
        vector_free(output.instrs);

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
    cfg_dir("risc_v", current_output_dir);
    do_on_each_file("risc_v", risc_v_test);
    return 0;
}
