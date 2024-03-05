/* elf.c - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/elf.h"
#include "util/compiler.h"
#include "util/vector.h"
#include "util/unreachable.h"
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>

static char *map;
static int fd;

static int init_size      = 0x8000;
static int strtab_off     = 0x1000;
static int shstrtab_off   = 0x1500;
static int symtab_off     = 0x2000;
static int sh_off         = 0x4000;
static int text_off       = 0x6000;
static int entry_addr     = 0x401000;
/* How much bytes occupy one symtab entry. */
static int symtab_entsize = 24;

static int arch         = 0x00;
static int text_siz     = 0x00;
static int syms_cnt     = 0x00;
static int strtab_siz   = 0x00;

struct codegen_output *codegen_output;

#define emit(addr, byte_string) \
    { strcpy(&map[addr], byte_string); }

#define emit_bytes(addr, data) \
    { memcpy(&map[(addr)], (data), sizeof (*(data))); }

static char *emit_symbol(char *start, const char *section)
{
    uint64_t len = strlen(section);
    strcpy(start, section);
    start[len] = 0;
    strtab_siz += len + 1;
    return start + len + /* NULL byte. */1;
}

static void emit_phdr(uint64_t idx, struct elf_phdr *phdr)
{
    uint64_t phdr_siz = 0x38;
    uint64_t phdr_off = 0x40 + (phdr_siz * idx);

    emit_bytes(phdr_off, phdr);
}

static void emit_shdr(uint64_t idx, struct elf_shdr *shdr)
{
    uint64_t shdr_siz = 0x40;
    uint64_t shdr_off = sh_off + (shdr_siz * idx);

    emit_bytes(shdr_off, shdr);
}

static uint16_t emit_phdrs()
{
    uint16_t phnum = 0;

    struct elf_phdr phdr = {
        .type   = 0x01,
        .flags  = 6,
        .vaddr  = entry_addr,
        .paddr  = entry_addr,
        .memsz  = 0xFF,
        .filesz = 0xFF
    };
    emit_phdr(phnum++, &phdr);

    return phnum;
}

static uint16_t emit_shdrs()
{
    /* Number of symtab entries. */
    unused uint16_t symtab_total = 1;
    uint16_t shnum = 0;
    /* 1 is because first NULL byte for NULL section. */
    uint32_t strtab_start = 0x01;

    /* ELF requires sentinel section of type NULL. */
    /* TODO: This still named .text as points to the 0x00 offset
             in string section. */
    struct elf_shdr null_shdr = {
        0
    };
    emit_shdr(shnum++, &null_shdr);

    struct elf_shdr progbits_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_PROGBITS,
        .addr     = entry_addr,
        .off      = text_off,
        .size     = text_siz,
        .link     = 0x00
    };
    emit_shdr(shnum++, &progbits_shdr);
    strtab_start += strlen(".text") + 1;

    struct elf_shdr strtab_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_STRTAB,
        .addr     = strtab_off,
        .off      = strtab_off,
        .size     = strtab_siz + /* Some extra byte. Idk. */ 1,
        .link     = 0x00
    };
    emit_shdr(shnum++, &strtab_shdr);
    strtab_start += strlen(".strtab") + 1;

    struct elf_shdr shstrtab_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_STRTAB,
        .addr     = shstrtab_off,
        .off      = shstrtab_off,
        .size     = 0x100,
        .link     = 0x00
    };
    emit_shdr(shnum++, &shstrtab_shdr);
    strtab_start += strlen(".shstrtab") + 1;

    /* Unused in single binary. Useful for relocatable objects. */

    struct elf_shdr symtab_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_SYMTAB,
        .addr     = symtab_off,
        .off      = symtab_off,
        .size     = syms_cnt * symtab_entsize,
        .info     = syms_cnt,
        .entsize  = symtab_entsize,
        .link     = 0x02
    };
    emit_shdr(shnum++, &symtab_shdr);

    return shnum;
}

unused static char *emit_symtab_entry(char *s, uint64_t addr_from, const char *name)
{
    uint64_t __strtab_off   = 1 +
        strlen(".text")     + 1 +
        strlen(".strtab")   + 1 +
        strlen(".shstrtab") + 1 +
        strlen(".symtab")   + 1;

    static uint64_t str_it = 0;
    static uint64_t sym_it = 0;
    s = emit_symbol(s, name);

    /* TODO: Wrong elf_sym binary layout? */
    struct elf_sym sym = {
        .name  = __strtab_off + str_it,
        /* Probably unused. */
        .size  = 0x1,
        .value = addr_from,
        .shndx = 1,
        .info  = 4
    };
    emit_bytes(symtab_off + sym_it, &sym);
    /* TODO: Index to some section. */
    uint8_t byte = 0x01;
    /* TODO: Figure out why -18. */
    emit_bytes(symtab_off + sym_it + symtab_entsize - 18, &byte);

    str_it += strlen(name) + /* NULL */ 1;
    sym_it += symtab_entsize;

    ++syms_cnt;
    return s;
}

static void emit_elf()
{
    struct elf_fhdr fhdr = {
        .ident     = "\x7F\x45\x4C\x46\x02\x01\x01",
        .type      = ET_EXEC,
        .machine   = arch,
        .version   = 1,
        .entry     = entry_addr,
        .phoff     = 0x40,
        .shoff     = sh_off,
        .flags     = 0x00,
        .ehsize    = 0x40,
        .phentsize = 0x38,
        .phnum     = emit_phdrs(),
        .shentsize = 0x40,
        .shnum     = emit_shdrs(),
        .shstrndx  = 0x02
    };

    emit_bytes(0x00, &fhdr);
}

static void elf_put_code()
{
    void *start = map + text_off;
    memcpy(start,
        codegen_output->instrs.data,
        codegen_output->instrs.size
    );

    /* +1 is due to first NULL byte for NULL section. */
    char *s = &map[strtab_off + 1];
    s = emit_symbol(s, ".text");
    s = emit_symbol(s, ".strtab");
    s = emit_symbol(s, ".shstrtab");
    s = emit_symbol(s, ".symtab");

    /* For some reason, first emitted to .symtab entry is not
       displayed in ELF dump.

        Symbol table '.symtab' contains 6 entries:
        Num:    Value          Size Type    Bind   Vis      Ndx Name
            0: 000000000040100a     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_6 <<< NO LABEL!
            1: 0000000000401008     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_5
            2: 0000000000401006     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_4
            3: 0000000000401004     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_3
            4: 0000000000401002     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_2
            5: 0000000000401000     1 NOTYPE  LOCAL  DEFAULT    1 __example_sym_1

        No version information found in this file.

        __elf.o:     file format elf64-littleriscv


        Disassembly of section .text:

        0000000000401000 <__example_sym_1>:
        401000:	1141                	addi	sp,sp,-16

        0000000000401002 <__example_sym_2>:
        401002:	e422                	sd	s0,8(sp)

        0000000000401004 <__example_sym_3>:
        401004:	4781                	li	a5,0

        0000000000401006 <__example_sym_4>:
        401006:	853e                	mv	a0,a5

        0000000000401008 <__example_sym_5>:
        401008:	6422                	ld	s0,8(sp)
        40100a:	0141                	addi	sp,sp,16
        40100c:	8082                	ret
        40100e:	0000                	unimp
        401010:	0000                	unimp
            ...
*/
    hashmap_foreach(&codegen_output->fn_offsets, k, v) {
        const char *name = (const char *) k;
        uint64_t    off  = v;

        s = emit_symtab_entry(s, entry_addr + off, name);
    }

    text_siz = codegen_output->instrs.size;
}

/* https://github.com/jserv/amacc/blob/master/amacc.c
   
   NOTE: Headers are emitted in `elf_put_code` call,
         when size of each section is known, depending
         on how much code we put. */
void elf_init(struct elf_entry *e)
{
    fd = open(e->filename, O_CREAT | O_TRUNC | O_RDWR, 0666);

    if (ftruncate(fd, init_size) < 0)
        weak_fatal_errno("ftruncate()");

    map = (char *) mmap(NULL, init_size, PROT_WRITE | PROT_READ, MAP_SHARED, fd, 0);
    if ((void *) map == MAP_FAILED)
        weak_fatal_errno("mmap()");

    arch = e->arch;
    codegen_output = &e->output;

    elf_put_code();
    emit_elf();
}

void elf_exit()
{
    if (munmap(map, init_size) < 0)
        weak_fatal_errno("munmap()");

    if (close(fd) < 0)
        weak_fatal_errno("close()");
}

// void elf_put_code(uint8_t *code, uint64_t size)
// {
//     void *start = map + text_off;
//     memcpy(start, code, size);

//     text_siz = size;
//     emit_elf();
// }