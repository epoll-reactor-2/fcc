/* elf.c - ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/elf.h"
#include "util/compiler.h"
#include "util/unreachable.h"
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>

static char *map;

static void emit(uint64_t addr, const char *bytes)
{
    strcpy(&map[addr], bytes);
}

void elf_gen(const char *filename, unused enum arch arch)
{
    int fd = open(filename, O_CREAT | O_TRUNC | O_RDWR, 0666);

    if (ftruncate(fd, 0x401500) < 0)
        weak_fatal_errno("ftruncate()");

    map = (char *) mmap(NULL, 0x401500, PROT_WRITE | PROT_READ, MAP_SHARED, fd, 0);
    if ((void *) map == MAP_FAILED)
        weak_fatal_errno("mmap()");

    /* ELF header */
    emit(0x00, "\x7f");
    emit(0x01, "ELF");
    /* 0x1 for 32 bit, */
    /* 0x2 for 64 bit */
    emit(0x04, "\x02");
    /* 0x1 for little endian, */
    /* 0x2 for big endian */
    emit(0x05, "\x01");
    /* ELF version. Always 1. */
    emit(0x06, "\x01");
    /* System ABI. I set for System V. */
    emit(0x07, "\x00");
    /* ABI version. */
    emit(0x08, "\x00");
    /* Padding byte. Unused. */
    emit(0x09, "\x00");
    /* Object file type. 2 is executable. */
    emit(0x10, "\x02");
    /* ISA. */
    switch (arch) {
    case ARCH_X86_64:
        emit(0x12, "\x3E");
        break;
    case ARCH_RISC_V:
        emit(0x12, "\xF3");
        break;
    default:
        weak_unreachable("Fatal arch enum: %d", arch);
    }
    /* Another byte for ELF version... */
    emit(0x14, "\x01");
    /* Address of program entry point. */
    /* Little endian for some reason. */
    emit(0x18, "\x00\x10\x40");

    /* !!!
       All things below are hard-coded.
       !!! */

    /* Program header table start. It follows */
    /* This header immediatly. */
    emit(0x20, "\x40\x00");
    /* Start of section header table. */
    /* Hardcoded for now 4192 (0x1060). */
    emit(0x28, "\x60\x10");
    /* Some flags. Idk. */
    emit(0x30, "\x00");
    /* Size of the header. Normally is 64 bytes. */
    emit(0x34, "\x40");
    /* Program header table size. Idk. 64. */
    emit(0x36, "\x38");
    /* Number of entries in program header table. */
    emit(0x38, "\x04");
    /* Section header table size. Idk. */
    emit(0x3A, "\x40");
    /* Number of entries in section header table. */
    emit(0x3C, "\x05");
    /* Index of the section header table entry that contains the section names.  */
    emit(0x3E, "\x04");
    /* End of header. Actually size. */
    emit(0x40, "\x40");

    /* Code should be placed from address 0x401000. */

    if (munmap(map, 0x401500) < 0)
        weak_fatal_errno("munmap()");

    if (close(fd) < 0)
        weak_fatal_errno("close()");
}