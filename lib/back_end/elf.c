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

static int phdr_off       = 0x0040;
static int sh_size        = 0x0040;
static int phdr_size      = 0x0038;

static int init_size      = 0x8000;
static int strtab_off     = 0x1000;
static int shstrtab_off   = 0x1500;
static int symtab_off     = 0x2000;
static int sh_off         = 0x4000;
static int text_off       = 0x6000;
static int entry_addr     = 0x0100;
/* How much bytes occupy one symtab entry. */
static int symtab_entsize = 24;

static int arch         = 0x00;
static int text_size    = 0x00;
static int syms_cnt     = 0x00;
static int strtab_size  = 0x00;

struct codegen_output *codegen_output;

#define ELF64_ST_BIND(info)          ((info) >> 4)
#define ELF64_ST_TYPE(info)          ((info) & 0xf)
#define ELF64_ST_INFO(bind, type)    (((bind)<<4)+((type)&0xf))

#define emit(addr, byte_string) \
    { strcpy(&map[addr], byte_string); }

#define emit_bytes(addr, data) \
    { memcpy(&map[(addr)], (data), sizeof (*(data))); }

static char *emit_symbol(char *start, const char *section)
{
    uint64_t len = strlen(section);
    strcpy(start, section);
    start[len] = 0;
    strtab_size += len + 1;
    return start + len + /* NULL byte. */1;
}

static void emit_phdr(uint64_t idx, struct elf_phdr *phdr)
{
    uint64_t off = phdr_off + (phdr_size * idx);

    emit_bytes(off, phdr);
}

static void emit_shdr(uint64_t idx, struct elf_shdr *shdr)
{
    uint64_t shdr_off = sh_off + (sh_size * idx);

    emit_bytes(shdr_off, shdr);
}

static uint16_t emit_phdrs()
{
    uint16_t phnum = 0;

    struct elf_phdr phdr = {
        .type   = 0x01,
        .flags  = 7,
        .off    = 0,
        .vaddr  = entry_addr,
        .paddr  = entry_addr,
        .memsz  = text_size,
        .filesz = text_size,
        .align  = 0x1000
    };
    emit_phdr(phnum++, &phdr);

    return phnum;
}

static uint16_t emit_shdrs()
{
    uint16_t shnum = 0;
    /* 1 is because first NULL byte for NULL section. */
    uint32_t strtab_start = 0x01;

    /* ELF requires sentinel section of type NULL. */
    struct elf_shdr null_shdr = {
        0
    };
    emit_shdr(shnum++, &null_shdr);

    struct elf_shdr progbits_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_PROGBITS,
        .addr     = entry_addr,
        .off      = text_off,
        .size     = text_size,
        .flags    = SHF_ALLOC | SHF_EXECINSTR,
        .link     = 0x00
    };
    emit_shdr(shnum++, &progbits_shdr);
    strtab_start += strlen(".text") + 1;

    struct elf_shdr strtab_shdr = {
        .name_ptr = strtab_start,
        .type     = SHT_STRTAB,
        .addr     = strtab_off,
        .off      = strtab_off,
        .size     = strtab_size + /* NULL entry. */ 1,
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

/* If name is NULL, sentinel .symtab entry is emitted.
   Required by ELF. */
unused static char *emit_symtab_entry(
    uint64_t   *str_it,
    uint64_t   *sym_it,
    char       *s,
    uint64_t    addr_from,
    const char *name
) {
    uint64_t __strtab_off   = 1 +
        strlen(".text")     + 1 +
        strlen(".strtab")   + 1 +
        strlen(".shstrtab") + 1 +
        strlen(".symtab")   + 1;

    bool sentinel = name == NULL;

    if (!sentinel)
        s = emit_symbol(s, name);

    struct elf_sym sym = {
        .name  = sentinel ? 0 : __strtab_off + *str_it,
        /* Probably unused. */
        .size  = sentinel ? 0 : 0x0,
        .value = sentinel ? 0 : addr_from,
        .shndx = sentinel ? 0 : 1,
        .info  = sentinel ? 0 : 0
    };
    emit_bytes(symtab_off + *sym_it, &sym);

    /* This thing is wierd as fuck. I don't get `info`
       field at proper layout when I follow official ELF manual,
       so I've found `ndx` and `type` fields by cherry-pick method. */
    if (!sentinel) {
        /* TODO: Index to some section. */
        uint8_t byte = 0x01;
        /* TODO: Figure out why ndx is on -18. */
        emit_bytes(symtab_off + *sym_it + 6, &byte);
        byte = ELF64_ST_INFO(2, 2);
        /* TODO: Figure out why type is on -20. */
        emit_bytes(symtab_off + *sym_it + 4, &byte);

        *str_it += strlen(name) + /* NULL */ 1;
    }

    *sym_it += symtab_entsize;

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
        .phoff     = phdr_off,
        .shoff     = sh_off,
        .flags     = 0x00,
        .ehsize    = 0x40,
        .phentsize = phdr_size,
        .phnum     = emit_phdrs(),
        .shentsize = sh_size,
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

    uint64_t str_it = 0;
    uint64_t sym_it = 0;

    /* Sentinel NULL entry is necessary. */
    s = emit_symtab_entry(&str_it, &sym_it, s, entry_addr, NULL);
    hashmap_foreach(&codegen_output->fn_offsets, k, v) {
        const char *name = (const char *) k;
        uint64_t    off  = v;

        s = emit_symtab_entry(&str_it, &sym_it, s, entry_addr + off, name);
    }

    text_size = codegen_output->instrs.count;
}

static void elf_reset()
{
    syms_cnt = 0;
    text_size = 0;
    strtab_size = 0;
}

/* https://github.com/jserv/amacc/blob/master/amacc.c */
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

    elf_reset();
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