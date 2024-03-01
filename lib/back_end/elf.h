/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

#include <stdint.h>
#include "util/vector.h"

enum arch {
    ARCH_RISC_V,
    ARCH_X86_64
};

struct elf_phdr {
    uint32_t type;
    uint32_t flags;
    uint64_t off;
    uint64_t vaddr;
    uint64_t paddr;
    uint64_t filesz;
    uint64_t memsz;
    uint64_t align;
};

struct elf_shdr {
    uint64_t name_ptr;
    uint64_t type;
    uint64_t flags;
    uint64_t addr;
    uint64_t off;
    uint64_t size;
    uint64_t link;
    uint64_t info;
    uint64_t addralign;
    uint64_t entsize;
};

struct elf_entry {
    const char               *filename;
    enum arch                 arch;
    vector_t(struct elf_phdr) phdr;
    vector_t(struct elf_shdr) shdr;
};

void elf_init(struct elf_entry *e);
void elf_exit();
void elf_put_code(uint8_t *code, uint64_t size);

#endif // WEAK_COMPILER_BACKEND_ELF_H