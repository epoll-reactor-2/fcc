#include "back_end/back_end.h"
#include "back_end/elf.h"
#include "util/compiler.h"
#include <string.h>

static struct codegen_output *output_code;
static instr_vector_t        *text_section;
static uint64_t               text_seek;

uint64_t back_end_seek()
{
    return text_seek;
}

void back_end_seek_set(uint64_t seek)
{
    text_seek = seek;
}

void put(uint8_t *code, uint64_t size)
{
    uint64_t s = back_end_seek();

    for (uint64_t i = 0; i < size; ++i) {
        vector_emplace(*text_section, back_end_seek());
        vector_at(*text_section, s + i) = code[i];
        ++text_seek;
    }
}

static uint64_t calculate_strtab_size(symtab_vector_t *v)
{
    uint64_t len = 0;

    vector_foreach(*v, i) {
        struct elf_symtab_entry *e = &vector_at(*v, i);

        len += strlen(e->name) + 1;
    }

    return len;
}

void back_end_emit_sym(const char *name, uint64_t off)
{
    struct elf_symtab_entry entry = {0};
    strncpy(entry.name, name, sizeof (entry.name) - 1);
    entry.off = off;

    vector_push_back(output_code->symtab, entry);
}

void back_end_init(struct codegen_output *output)
{
    output_code = output;

    hashmap_init(&output_code->fn_offsets, 32);

    text_section = &output->instrs;
}

void back_end_emit(struct codegen_output *output, const char *path)
{
    uint64_t text_size   = output->instrs.count;
    uint64_t strtab_size = calculate_strtab_size(&output->symtab);

    struct {
        const char *name;
        uint64_t    size;
    } sections[] = {
        { ".text",     text_size   },
        { ".strtab",   strtab_size },
        { ".shstrtab", 40          }, /* Enough to place 4 sections (with symtab). */
    };

    for (uint64_t i = 0; i < __weak_array_size(sections); ++i)
        elf_init_section(output, sections[i].name, sections[i].size);

    elf_init_symtab(output, output->symtab.count);

    struct elf_entry elf = {
        .filename = path,
        .output   = *output
    };

    elf_init(&elf);
    elf_exit(&elf);

    output_code = NULL;
    text_section = NULL;
}