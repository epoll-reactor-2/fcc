/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

#include <stdint.h>

enum arch {
    ARCH_RISC_V,
    ARCH_X86_64
};

void elf_init(const char *filename, enum arch arch);
void elf_exit();
void elf_put_code(uint8_t *code, uint64_t size);

#endif // WEAK_COMPILER_BACKEND_ELF_H