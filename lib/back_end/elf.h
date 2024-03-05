/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

#include <stdint.h>

/* All this code (as whole project) written for fun.
   Be a normal person. Use libelf.

   Notice: defined below structures matches alignment and
           field sizes in ELF header. User can copy whole
           structure into a file.
*/

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
    /* ELF magic header */
    uint8_t ident[EI_NIDENT];
    /* Object file type. */
    uint16_t type;
    /* ISA. */
    uint16_t machine;
    /* Another byte for ELF version... */
    uint32_t version;
    /* Address of program entry point.
       Virtual address to which the system first transfers control,
       thus starting the process. */
    uint64_t entry;
    /* Program header table start. It follows
        this header immediatly. */
    uint64_t phoff;
    /* Points to the start of the section header table. */
    uint64_t shoff;
    /* Some other flags. */
    uint32_t flags;
    /* Size of this header. Normally is 64 bytes. */
    uint16_t ehsize;
    /* Size of a program header table entry. */
    uint16_t phentsize;
    /* Number of entries in the program header table. */
    uint16_t phnum;
    /* Section header table size. */
    uint16_t shentsize;
    /* Number of entries in the section header table. */
    uint16_t shnum;
    /* Index of the section header table entry that contains the section names. */
    uint16_t shstrndx;
};

struct elf_phdr {
    /* Type of the segment. */
    uint32_t type;
    /* Flags (R, W or X) */
    uint32_t flags;
    /* Offset to a segment in file. */
    uint64_t off;
    /* Virtual address of the segment in memory. */
    uint64_t vaddr;
    /* Unused, I guess. */
    uint64_t paddr;
    /* Size in bytes of the segment in the file image. May be 0. */
    uint64_t filesz;
    /* Size in bytes of the segment in memory. May be 0. */
    uint64_t memsz;
    /* Unused now. */
    uint64_t align;
};

struct elf_shdr {
    /* An offset to a string in the .shstrtab section
       that represents the name of this section. */
    uint32_t name_ptr;
    /* Type of this header. */
    uint32_t type;
    /* Section attributes. */
    uint64_t flags;
    /* Virtual address of the section in memory, for sections that are loaded. */
    uint64_t addr;
    /* Offset of the section in the file image. */
    uint64_t off;
    /* Size in bytes of the section in the file image. May be 0. */
    uint64_t size;
    /* Contains the section index of an associated section. */
    uint32_t link;
    /* Contains extra information about the section. */
    uint32_t info;
    /* Contains the required alignment of the section. This field must be a power of two. */
    uint64_t addralign;
    /* Contains the size, in bytes, of each entry, for sections that
       contain fixed-size entries. Otherwise, this field contains zero. */
    uint64_t entsize;
};

struct elf_sym {
    /* An offset to a string in the .shstrtab section
       that represents the name of this section. */
    uint64_t name;
    /* The symbol's type and binding attributes. */
    uint8_t  info;
    /* A symbol's visibility. */
    uint8_t  other;
    /* Every symbol table entry is defined in relation to
       some section. This member holds the relevant section
       header table index. */
    uint64_t shndx;
    /* The value of the associated symbol. The value can be
       an absolute value or an address, depending on the
       context. */
    uint64_t value;
    /* Unused now. */
    uint64_t size;
};

struct elf_entry {
    const char *filename;
    int         arch;
};

void elf_init(struct elf_entry *e);
void elf_exit();
void elf_put_code(uint8_t *code, uint64_t size);

#endif // WEAK_COMPILER_BACKEND_ELF_H