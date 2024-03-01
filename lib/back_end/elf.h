/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

#include <stdint.h>

/* All this code (as whole project) written for fun.
   Be a normal person. Use libelf. */

#define ARCH_RISC_V         0xF3
#define ARCH_X86_64         0x3E

#define EI_NIDENT             16

#define ET_NONE             0x00
#define ET_REL              0x01
#define ET_EXEC             0x02
#define ET_DYN              0x03

#define SHT_NULL               0
#define SHT_PROGBITS           1
#define SHT_SYMTAB             2
#define SHT_STRTAB             3
#define SHT_RELA               4
#define SHT_HASH               5
#define SHT_DYNAMIC            6
#define SHT_NOTE               7
#define SHT_NOBITS             8
#define SHT_REL                9
#define SHT_SHLIB             10
#define SHT_DYNSYM            11
#define SHT_INIT_ARRAY        14
#define SHT_FINI_ARRAY        15
#define SHT_PREINIT_ARRAY     16
#define SHT_GROUP             17
#define SHT_SYMTAB_SHNDX      18
#define  SHT_NUM              19
#define SHT_LOOS              0x60000000

#define SHF_WRITE             (1  <<  0)
#define SHF_ALLOC             (1  <<  1)
#define SHF_EXECINSTR         (1  <<  2)
#define SHF_MERGE             (1  <<  4)
#define SHF_STRINGS           (1  <<  5)
#define SHF_INFO_LINK         (1  <<  6)
#define SHF_LINK_ORDER        (1  <<  7)
#define SHF_OS_NONCONFORMING  (1  <<  8)
#define SHF_GROUP             (1  <<  9)
#define SHF_TLS               (1  << 10)
#define SHF_COMPRESSED        (1  << 11)
#define SHF_MASKOS            0x0ff00000
#define SHF_MASKPROC          0xf0000000
#define SHF_GNU_RETAIN        (1  << 21)
#define SHF_ORDERED           (1  << 30)
#define SHF_EXCLUDE           (1U << 31)

struct elf_fhdr {
    uint8_t ident[EI_NIDENT];
    uint16_t type;
    uint16_t machine;
    uint32_t version;
    uint64_t entry;
    uint64_t phoff;
    uint64_t shoff;
    uint32_t flags;
    uint16_t ehsize;
    uint16_t phentsize;
    uint16_t phnum;
    uint16_t shentsize;
    uint16_t shnum;
    uint16_t shstrndx;
};

struct elf_phdr {
    uint32_t type;
    uint32_t flags;
    uint64_t off;
    uint64_t vaddr;
    uint64_t paddr;
    uint32_t filesz;
    uint32_t memsz;
    uint32_t align;
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
    const char *filename;
    int         arch;
};

void elf_init(struct elf_entry *e);
void elf_exit();
void elf_put_code(uint8_t *code, uint64_t size);

#endif // WEAK_COMPILER_BACKEND_ELF_H