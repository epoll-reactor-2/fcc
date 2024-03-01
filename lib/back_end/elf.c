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

static void emit_phdr(uint64_t idx, struct elf_phdr *phdr)
{
    /* Program header table size. Idk. 64. */
    emit_byte(0x36, 0x38);
    uint64_t phdr_siz = 0x38;
    uint64_t phdr_off = 0x40 + (phdr_siz * idx);

    /* Type of the segment. */
    emit_bytes(phdr_off + 0x00, &phdr->type);
    /* Flags (RW) */
    emit_bytes(phdr_off + 0x04, &phdr->flags);
    /* Virtual address of the segment in memory */
    emit_bytes(phdr_off + 0x10, &phdr->vaddr);
    emit_bytes(phdr_off + 0x20, &phdr->filesz);
    emit_bytes(phdr_off + 0x28, &phdr->memsz);
}

static void emit_shdr(uint64_t idx, struct elf_shdr *shdr)
{
    uint64_t shdr_siz = 0x40;
    uint64_t shdr_off = 0x1060 + (shdr_siz * idx);

    /* An offset to a string in the .shstrtab section that represents the name of this section. */
    emit(shdr_off + 0x00, "\x00\x70");
    /* Type of this header. */
    emit_bytes(shdr_off + 0x04, &shdr->type);
    /* Virtual address of the section in memory, for sections that are loaded. */
    emit_bytes(shdr_off + 0x10, &shdr->addr);
    /* Offset of the section in the file image. */
    emit_bytes(shdr_off + 0x18, &shdr->off);
    /* Size in bytes of the section in the file image. May be 0. */
    emit_bytes(shdr_off + 0x20, &shdr->size);
    /* Contains the section index of an associated section. */
    emit_bytes(shdr_off + 0x28, &shdr->link);
    /* Contains extra information about the section. */
    emit_bytes(shdr_off + 0x2C, &shdr->info);
    /* Contains the required alignment of the section. This field must be a power of two. */
    emit_bytes(shdr_off + 0x30, &shdr->addralign);
    /* Contains the size, in bytes, of each entry, for sections that
       contain fixed-size entries. Otherwise, this field contains zero. */
    emit_bytes(shdr_off + 0x38, &shdr->entsize);
}

/* https://github.com/jserv/amacc/blob/master/amacc.c */
void elf_init(struct elf_entry *e)
{
    fd = open(e->filename, O_CREAT | O_TRUNC | O_RDWR, 0666);

    if (ftruncate(fd, 0x401500) < 0)
        weak_fatal_errno("ftruncate()");

    map = (char *) mmap(NULL, 0x401500, PROT_WRITE | PROT_READ, MAP_SHARED, fd, 0);
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
    vector_push_back(phdrs, phdr);

    struct elf_shdr shdr = {
        .type   = SHT_PROGBITS,
        .addr   = 0x00,
        .link   = 0x00
    };
    vector_push_back(shdrs, shdr);

    struct elf_fhdr fhdr = {
        /* ELF header */
        .ident = "\x7F\x45\x4C\x46\x02\x01\x01",
        /* Object file type. */
        .type = ET_EXEC,
        /* ISA. */
        .machine = e->arch,
        /* Another byte for ELF version... */
        .version = 1,
        /* Address of program entry point.
           Virtual address to which the system first transfers control, thus starting the process. */
        .entry = 0x40100,
        /* Program header table start. It follows
           this header immediatly. */
        .phoff = 0x40,
        /* Points to the start of the section header table. */
        .shoff = 0x1060,
        /* Some other flags. */
        .flags = 0x00,
        /* Size of this header. Normally is 64 bytes. */
        .ehsize = 0x40,
        /* Size of a program header table entry. */
        .phentsize = 0x38,
        /* Number of entries in the program header table. */
        .phnum = phdrs.count,
        /* Section header table size. Idk. */
        .shentsize = 0x40,
        /* Number of entries in the section header table. */
        .shnum = shdrs.count,
        /* Index of the section header table entry that contains the section names. */
        .shstrndx = 0x00
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
    if (munmap(map, 0x401500) < 0)
        weak_fatal_errno("munmap()");

    if (close(fd) < 0)
        weak_fatal_errno("close()");
}

void elf_put_code(uint8_t *code, uint64_t size)
{
    void *start = map + 0x401000;
    memcpy(start, code, size);
}