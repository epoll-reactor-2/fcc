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

static int init_size    = 0x8000;
static int sh_off       = 0x1060;
static int text_off     = 0x6000;
static int strtab_off   = 0x3000;
static int shstrtab_off = 0x3500;
static int symtab_off   = 0x4000;
static int entry_addr   = 0x401000;

#define emit(addr, byte_string) \
    { strcpy(&map[addr], byte_string); }

#define emit_bytes(addr, data) \
    { memcpy(&map[(addr)], (data), sizeof (*(data))); }

#define emit_byte(addr, i) \
    { map[(addr)] = i; }

#define emit_short(addr, i) \
    { uint16_t _ = (i); \
      char *bytes = (char *) &_; \
      map[(addr) + 0] = bytes[0]; \
      map[(addr) + 1] = bytes[1]; }

#define emit_int(addr, i) \
    { uint32_t _ = (i); \
      char *bytes = (char *) &_; \
      map[(addr) + 0] = bytes[0]; \
      map[(addr) + 1] = bytes[1]; \
      map[(addr) + 2] = bytes[2]; \
      map[(addr) + 3] = bytes[3]; }

#define emit_long(addr, i) \
    { uint64_t _ = (i); \
      char *bytes = (char *) &_; \
      map[(addr) + 0] = bytes[0]; \
      map[(addr) + 1] = bytes[1]; \
      map[(addr) + 2] = bytes[2]; \
      map[(addr) + 3] = bytes[3]; \
      map[(addr) + 4] = bytes[4]; \
      map[(addr) + 5] = bytes[5]; \
      map[(addr) + 6] = bytes[6]; \
      map[(addr) + 7] = bytes[7]; }

static char *emit_symbol(char *start, const char *section)
{
    uint64_t len = strlen(section);
    strcpy(start, section);
    start[len] = 0;
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
        .vaddr  = 0,
        .memsz  = 0,
        .filesz = 0
    };
    emit_phdr(phnum++, &phdr);

    return phnum;
}

static uint16_t emit_shdrs()
{
    /* Number of symtab entries. */
    unused uint16_t symtab_total = 1;
    uint16_t shnum = 0;

    struct elf_shdr progbits_shdr = {
        .name_ptr = 0x00,
        .type     = SHT_PROGBITS,
        .addr     = entry_addr,
        .off      = text_off,
        .size     = 0xFFF,
        .link     = 0x00
    };
    emit_shdr(shnum++, &progbits_shdr);

    struct elf_shdr strtab_shdr = {
        .name_ptr = strlen(".text") + 1,
        .type     = SHT_STRTAB,
        .addr     = 0x00,
        .off      = strtab_off,
        .size     = 0x100,
        .link     = 0x00
    };
    emit_shdr(shnum++, &strtab_shdr);

    struct elf_shdr shstrtab_shdr = {
        .name_ptr = strlen(".text")   + 1 +
                    strlen(".strtab") + 1,
        .type     = SHT_STRTAB,
        .addr     = 0x00,
        .off      = shstrtab_off,
        .size     = 0x100,
        .link     = 0x00
    };
    emit_shdr(shnum++, &shstrtab_shdr);

    /* Unused in single binary. Useful for relocatable objects. */
    /*
    struct elf_shdr symtab_shdr = {
        .name_ptr = strlen(".text")     + 1 +
                    strlen(".strtab")   + 1 +
                    strlen(".shstrtab") + 1,
        .type     = SHT_SYMTAB,
        .addr     = 0x00,
        .off      = symtab_off,
        .size     = symtab_total * sizeof (struct elf_sym),
        .info     = 0x01,
        .link     = 0x01
    };
    emit_shdr(shnum++, &symtab_shdr);
    */

    return shnum;
}

unused static void emit_symtab()
{
    struct elf_sym sym = {
        /* Name ptr should point to .strtab entry.

           TODO: Nice API for adding symbols. */
        .name = strlen(".text") + 1,
        .size = 10,
        /* TODO: size is written instead of value.
                 Wrong ABI? */
        .value = 0xFF
    };
    emit_bytes(symtab_off, &sym);
}

static void emit_elf(int arch)
{
    char *s = &map[strtab_off];
    s = emit_symbol(s, ".text");
    s = emit_symbol(s, ".strtab");
    s = emit_symbol(s, ".shstrtab");
    s = emit_symbol(s, ".symtab");

    /* Unused in single binary. Useful for relocatable objects. */
    /* emit_symtab(); */

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
        .shstrndx  = 0x01
    };

    emit_bytes(0x00, &fhdr);
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

    emit_elf(e->arch);
}

void elf_exit()
{
    if (munmap(map, init_size) < 0)
        weak_fatal_errno("munmap()");

    if (close(fd) < 0)
        weak_fatal_errno("close()");
}

void elf_put_code(uint8_t *code, uint64_t size)
{
    void *start = map + text_off;
    memcpy(start, code, size);
}