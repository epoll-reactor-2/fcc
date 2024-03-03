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

static int init_size  = 0x8000;
static int sh_off     = 0x1060;
static int text_off   = 0x6000;
static int strtab_off = 0x3000;
static int entry_addr = 0x401000;

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

static char *emit_section(char *start, const char *section)
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

/* https://github.com/jserv/amacc/blob/master/amacc.c */
void elf_init(struct elf_entry *e)
{
    fd = open(e->filename, O_CREAT | O_TRUNC | O_RDWR, 0666);

    if (ftruncate(fd, init_size) < 0)
        weak_fatal_errno("ftruncate()");

    map = (char *) mmap(NULL, init_size, PROT_WRITE | PROT_READ, MAP_SHARED, fd, 0);
    if ((void *) map == MAP_FAILED)
        weak_fatal_errno("mmap()");

    vector_t(struct elf_phdr) phdrs = {0};
    vector_t(struct elf_shdr) shdrs = {0};

    struct elf_phdr phdr = {
        .type   = 0x01,
        .flags  = 6,
        .vaddr  = 0,
        .memsz  = 0,
        .filesz = 0
    };
    vector_push_back(phdrs, phdr);

    struct elf_shdr progbits_shdr = {
        .name_ptr = 0x00,
        .type     = SHT_PROGBITS,
        .addr     = entry_addr,
        .off      = text_off,
        .size     = 0xFFF,
        .link     = 0x00
    };
    vector_push_back(shdrs, progbits_shdr);

    struct elf_shdr strtab_shdr = {
        .name_ptr = 0x06,
        .type     = SHT_STRTAB,
        .addr     = 0x00,
        .off      = strtab_off,
        .size     = 0x100,
        .link     = 0x00
    };
    vector_push_back(shdrs, strtab_shdr);

    char *s = &map[strtab_off];
    s = emit_section(s, ".text");
    s = emit_section(s, ".shstrtab");

    struct elf_fhdr fhdr = {
        .ident     = "\x7F\x45\x4C\x46\x02\x01\x01",
        .type      = ET_EXEC,
        .machine   = e->arch,
        .version   = 1,
        .entry     = entry_addr,
        .phoff     = 0x40,
        .shoff     = sh_off,
        .flags     = 0x00,
        .ehsize    = 0x40,
        .phentsize = 0x38,
        .phnum     = phdrs.count,
        .shentsize = 0x40,
        .shnum     = shdrs.count,
        .shstrndx  = 0x01
    };

    emit_bytes(0x00, &fhdr);

    vector_foreach(phdrs, i) {
        emit_phdr(i, &vector_at(phdrs, i));
    }

    vector_foreach(shdrs, i) {
        emit_shdr(i, &vector_at(shdrs, i));
    }

    vector_free(phdrs);
    vector_free(shdrs);

    /* Code should be placed from address 0x401000. */
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