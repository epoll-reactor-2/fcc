/* ast_storage.с - Storage for declarations being AST nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast.h"
#include "utils/test_utils.h"
#include <time.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

/// Slow as fuck.
void generate_random_string(char *out, uint64_t len)
{
    static const char alphabet[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    struct timespec ts;

    for (uint64_t i = 0; i < len; ++i) {
        timespec_get(&ts, TIME_UTC);
        srand(ts.tv_nsec);
        out[i] = alphabet[rand() % sizeof alphabet - 1];
    }
}

int main() {
    {
        ast_node_t *ast = ast_num_init(1, 2, 3);

        ast_storage_init_state();
        ASSERT_FALSE(ast_storage_lookup("var"));
        ast_storage_push("var", ast);
        ASSERT_TRUE(ast_storage_lookup("var"));
        ast_storage_reset_state();
        ast_node_cleanup(ast);
    }

    {
        /// Loop to check proper internal states handling.
        for (uint64_t i = 0; i < 5; ++i) {
            ast_node_t *ast = ast_num_init(1, 2, 3);

            ast_storage_init_state();
            ast_storage_start_scope();
            ast_storage_push("var", ast);

            ast_storage_decl_t *record = ast_storage_lookup("var");
            ASSERT_TRUE(record->read_uses == 0);
            ASSERT_TRUE(record->write_uses == 0);
            ASSERT_TRUE(record->depth == 1);
            ast_storage_add_read_use("var");
            ast_storage_add_write_use("var");
            ast_storage_add_write_use("var");
            ASSERT_TRUE(record->read_uses == 1);
            ASSERT_TRUE(record->write_uses == 2);

            ast_storage_end_scope();
            ast_storage_reset_state();
            ast_node_cleanup(ast);
        }
    }

    {
        ast_node_t *ast = ast_num_init(1, 2, 3);
        ast_storage_init_state();

        ast_storage_start_scope();
        ast_storage_start_scope();
        ast_storage_push_typed("var", D_T_BOOL, ast);

        ast_storage_decl_t *record = ast_storage_lookup("var");
        ASSERT_TRUE(record);
        ASSERT_TRUE(record->depth == 2);
        ASSERT_TRUE(record->data_type == D_T_BOOL);

        ast_storage_end_scope();

        ast_storage_push("var2", ast);
        ast_storage_decl_t *second_record = ast_storage_lookup("var2");
        ASSERT_TRUE(second_record);
        ASSERT_TRUE(second_record->depth == 1);

        ast_storage_end_scope();
        ASSERT_FALSE(ast_storage_lookup("var"));

        ast_storage_reset_state();
        ast_node_cleanup(ast);
    }

    {
        ast_storage_init_state();
        ast_node_t *ast = ast_num_init(1, 2, 3);

        char rand_string[32];
        for (uint64_t i = 0; i < 1000; ++i) {
            memset(rand_string, 0, 32);
            generate_random_string(rand_string, 32);
            ast_storage_push(rand_string, ast);
            ASSERT_TRUE(ast_storage_lookup(rand_string));
        }

        ast_storage_reset_state();
    }
}