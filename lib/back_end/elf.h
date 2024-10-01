/* elf.h - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_ELF_H
#define WEAK_COMPILER_BACKEND_ELF_H

#include <stdint.h>
#include "util/compiler.h"
#include "util/hashmap.h"
#include "util/vector.h"

/* All this code (as whole project) written for fun.
   Be a normal person. Use libelf.

   Notice: defined below structures matches alignment and
           field sizes in ELF header. User can copy whole
           structure into a file.
*/

#if defined CONFIG_USE_BACKEND_RISC_V
#define ELF_TARGET_ARCH     0xF3
#elif defined CONFIG_USE_BACKEND_X86_64
#define ELF_TARGET_ARCH     0x3E
#endif

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
#define SHT_NUM               19
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

/* Symbol bind. */
#define STB_LOCAL             0
#define STB_GLOBAL            1
#define STB_WEAK              2
#define STB_LOOS             10
#define STB_HIOS             12
#define STB_LOPROC           13
#define STB_HIPROC           15

/* Symbol type. */
#define STT_NOTYPE            0
#define STT_OBJECT            1
#define STT_FUNC              2
#define STT_SECTION           3
#define STT_FILE              4
#define STT_COMMON            5
#define STT_LOOS             10
#define STT_HIOS             12
#define STT_LOPROC           13
#define STT_SPARC_REGISTER   13
#define STT_HIPROC           15

/* Symbol visibility. */
#define STV_DEFAULT           0
#define STV_INTERNAL          1
#define STV_HIDDEN            2
#define STV_PROTECTED         3

#define PT_NULL               0
#define PT_LOAD               1
#define PT_DYNAMIC            2
#define PT_INTERP             3
#define PT_NOTE               4
#define PT_SHLIB              5
#define PT_PHDR               6
#define PT_TLS                7
#define PT_LOOS               0x60000000
#define PT_HIOS               0x6fffffff
#define PT_LOPROC             0x70000000
#define PT_HIPROC             0x7fffffff

#define PF_X                  0x1
#define PF_W                  0x2
#define PF_R                  0x4

struct packed elf_fhdr {
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

struct packed elf_phdr {
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

struct packed elf_shdr {
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

struct packed elf_sym {
    /* An offset to a string in the .shstrtab section
       that represents the name of this section. */
    uint32_t name;
    /* The symbol's type and binding attributes. */
    uint8_t  info;
    /* A symbol's visibility. */
    uint8_t  other;
    /* Every symbol table entry is defined in relation to
       some section. This member holds the relevant section
       header table index. */
    uint16_t shndx;
    /* The value of the associated symbol. The value can be
       an absolute value or an address, depending on the
       context. */
    uint64_t value;
    /* Unused now. */
    uint64_t size;
};

typedef vector_t(uint8_t) instr_vector_t;

struct elf_section {
    char           name[128];
    uint64_t       size;
    instr_vector_t instrs;
};

struct elf_symtab_entry {
    char           name[128];
    uint64_t       off;
};

typedef vector_t(struct elf_symtab_entry) symtab_vector_t;
typedef vector_t(struct elf_section) section_vector_t;

struct codegen_output {
    hashmap_t             fn_offsets;
    instr_vector_t        instrs;
    section_vector_t      sections;
    symtab_vector_t       symtab;
};

struct elf_entry {
    const char *filename;
    struct codegen_output
                output;
};

void elf_init_section(
    struct codegen_output *output,
    const char            *section,
    uint64_t               size
);

void elf_init_symtab(
    struct codegen_output *output,
    uint64_t               syms_cnt
);

instr_vector_t *elf_lookup_section(
    struct codegen_output *output,
    const char            *section
);

void elf_init(struct elf_entry *e);
void elf_exit(struct elf_entry *e);

#endif // WEAK_COMPILER_BACKEND_ELF_H