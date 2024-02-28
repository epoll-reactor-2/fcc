/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

enum arch {
    ARCH_RISC_V,
    ARCH_X86_64
};

void elf_gen(const char *filename, enum arch arch);

#endif // WEAK_COMPILER_BACKEND_ELF_H