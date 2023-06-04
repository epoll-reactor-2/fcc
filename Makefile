DEBUG_BUILD := 1

CC          = gcc
LIB         = libweak_compiler.so
LDFLAGS     = -lfl -Wl,-R
CFLAGS      = -std=gnu99 -Wall -Wextra -Werror -fPIC -Ilib

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
	cp -r tests/{front,middle,back}_end/input/* build/test_inputs

SRC = $(shell find lib -name '*.c') build/lex.yy.c

%.o: %.c
	$(CC) -c $(CFLAGS) $^ -o build/$(notdir $@)

OBJ = $(SRC:.c=.o)

$(LIB): $(OBJ) | build_dir
	$(CC) $(CFLAGS) $(addprefix build/,$(notdir $(^:.c=.o))) -shared -o build/$(LIB) $(LDFLAGS)

TEST_SRC = $(shell find tests -name '*.c')
TEST_OBJ = $(TEST_SRC:.c=.o)

TEST_CFLAGS  = -Lbuild
TEST_LDFLAGS = -lweak_compiler

$(TEST_OBJ): $(TEST_SRC) | $(LIB)
	$(CC) -Itests $(CFLAGS) $(@:.o=.c) build/lex.yy.o -o build/$(notdir $(@:.o=))_test $(TEST_CFLAGS) $(TEST_LDFLAGS) $(LDFLAGS)

tests: $(TEST_OBJ)

test:
	$(foreach file,$(shell \
		find build -executable -name '*_test' -printf "./%f\n"),\
		 (cd build; LD_LIBRARY_PATH=. $(file));)

clean:
	@rm -rf build $(OBJECTS) *.o
	@echo "Done"