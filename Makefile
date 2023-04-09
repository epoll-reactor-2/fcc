DEBUG_BUILD = 1

CC          = gcc
LIB         = libweak_compiler.so
LDFLAGS     = -lfl -Wl,-R
CFLAGS      = -std=gnu11 -Wall -Wextra -fPIC -Ilib/include

ifeq ($(DEBUG_BUILD), 1)
CFLAGS     += -O0 -ggdb
else
CFLAGS     += -O3
endif

.PHONY: test clean all
all: build_dir test_files $(LIB) tests

build_dir:
	! [[ -d build ]] \
	    && mkdir -p build/test_inputs \
	    || echo "Build direcory already exists..."; \
	flex --outfile=build/lex.yy.c lex/grammar.lex

# TODO: make symlinks and not torture my SSD...
test_files: | build_dir
	cp -r tests/{front,middle}_end/input/* build/test_inputs

SRC = $(shell find lib -name '*.c') build/lex.yy.c

%.o: %.c
	$(CC) -c $(CFLAGS) $^ -o build/$(notdir $@)

OBJ = $(SRC:.c=.o)

$(LIB): $(OBJ) | build_dir
	$(CC) $(CFLAGS) $(addprefix build/,$(notdir $(^:.c=.o))) -shared -o build/$(LIB) $(LDFLAGS)

TEST_SRC = $(shell find tests -name '*.c')
TEST_OBJ = $(TEST_SRC:.c=.o)

$(TEST_OBJ): $(TEST_SRC) | $(LIB)
	$(CC) -Itests $(CFLAGS) $(@:.o=.c) build/lex.yy.o -o build/$(notdir $(@:.o=))_test -Lbuild -lweak_compiler $(LDFLAGS)

tests: $(TEST_OBJ)

test:
	@(cd build; LD_LIBRARY_PATH=. ./analysis_test)
	@(cd build; LD_LIBRARY_PATH=. ./ast_storage_test)
	@(cd build; LD_LIBRARY_PATH=. ./ast_dump_test)
	@(cd build; LD_LIBRARY_PATH=. ./data_type_test)
	@(cd build; LD_LIBRARY_PATH=. ./tok_test)
	@(cd build; LD_LIBRARY_PATH=. ./parse_test)
	@(cd build; LD_LIBRARY_PATH=. ./ir_dump_test)
	@(cd build; LD_LIBRARY_PATH=. ./ir_gen_test)

clean:
	@rm -rf build $(OBJECTS) *.o
	@echo "Done"