/* ir_dump_bin.h - Generate binary files with weak IR.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

struct ir_unit;

void ir_dump_binary(struct ir_unit *unit, const char *filename);

struct ir_unit ir_read_binary(const char *filename);