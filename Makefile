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

NR_CPUS     = $(shell nproc 2> /dev/null)

override MAKEFLAGS += -j $(NR_CPUS)

.PHONY: test clean all
all: build_dir test_files $(LIB) tests

\t        := $(info)	$(info)

ENDCOLOR  := $(shell tput sgr0 $(NULL_STDERR);              $(NULL_STDERR))
RED       := $(shell tput bold $(NULL_STDERR); tput setaf 1 $(NULL_STDERR))
GREEN     := $(shell tput bold $(NULL_STDERR); tput setaf 2 $(NULL_STDERR))
YELLOW    := $(shell tput bold $(NULL_STDERR); tput setaf 3 $(NULL_STDERR))
BLUE      := $(shell tput bold $(NULL_STDERR); tput setaf 6 $(NULL_STDERR))

CC_COLORED := "$(YELLOW)CC$(ENDCOLOR)"
LD_COLORED :=  "$(GREEN)LD$(ENDCOLOR)"

ifneq (,$(findstring UTF, $(LANG)))
$(info $(info) $(RED)                                                                                  $(ENDCOLOR) )
$(info $(info) $(RED)                                                                                  $(ENDCOLOR) )
$(info $(info) $(RED)                   ▄▀▀▄    ▄▀▀▄  ▄▀▀█▄▄▄▄  ▄▀▀█▄   ▄▀▀▄ █                         $(ENDCOLOR) )
$(info $(info) $(RED)                  █   █    ▐  █ ▐  ▄▀   ▐ ▐ ▄▀ ▀▄ █  █ ▄▀                         $(ENDCOLOR) )
$(info $(info) $(RED)                  ▐  █        █   █▄▄▄▄▄    █▄▄▄█ ▐  █▀▄                          $(ENDCOLOR) )
$(info $(info) $(RED)                    █   ▄    █    █    ▌   ▄▀   █   █   █                         $(ENDCOLOR) )
$(info $(info) $(RED)                     ▀▄▀ ▀▄ ▄▀   ▄▀▄▄▄▄   █   ▄▀  ▄▀   █                          $(ENDCOLOR) )
$(info $(info) $(RED)                           ▀     █    ▐   ▐   ▐   █    ▐                          $(ENDCOLOR) )
$(info $(info) $(RED)                                 ▐                ▐                               $(ENDCOLOR) )
$(info $(info) $(RED)                                 ▐                ▐                               $(ENDCOLOR) )
$(info $(info) $(RED)                                 ▐                ▐                               $(ENDCOLOR) )
$(info $(info) $(RED)     ▄▀▄▄▄▄   ▄▀▀▀▀▄   ▄▀▀▄ ▄▀▄  ▄▀▀▄▀▀▀▄  ▄▀▀█▀▄   ▄▀▀▀▀▄     ▄▀▀█▄▄▄▄  ▄▀▀▄▀▀▀▄ $(ENDCOLOR) )
$(info $(info) $(RED)    █ █    ▌ █      █ █  █ ▀  █ █   █   █ █   █  █ █    █     ▐  ▄▀   ▐ █   █   █ $(ENDCOLOR) )
$(info $(info) $(RED)    ▐ █      █      █ ▐  █    █ ▐  █▀▀▀▀  ▐   █  ▐ ▐    █       █▄▄▄▄▄  ▐  █▀▀█▀  $(ENDCOLOR) )
$(info $(info) $(RED)      █      ▀▄    ▄▀   █    █     █          █        █        █    ▌   ▄▀    █  $(ENDCOLOR) )
$(info $(info) $(RED)     ▄▀▄▄▄▄▀   ▀▀▀▀   ▄▀   ▄▀    ▄▀        ▄▀▀▀▀▀▄   ▄▀▄▄▄▄▄▄▀ ▄▀▄▄▄▄   █     █   $(ENDCOLOR) )
$(info $(info) $(RED)    █     ▐           █    █    █         █       █  █         █    ▐   ▐     ▐   $(ENDCOLOR) )
$(info $(info) $(RED)    ▐                 ▐    ▐    ▐         ▐       ▐  ▐         ▐                  $(ENDCOLOR) )
$(info $(info) $(RED)                                                                                  $(ENDCOLOR) )
$(info $(info) $(RED)                                                                                  $(ENDCOLOR) )
endif

build_dir:
	@! [[ -d build ]] \
	    && mkdir -p build/test_inputs; \
	flex --outfile=build/lex.yy.c lex/grammar.lex

test_files: | build_dir
	@cp -r tests/{front,middle,back}_end/input/* build/test_inputs

SRC = $(shell find lib -name '*.c') build/lex.yy.c

%.o: %.c
	@echo "[$(CC_COLORED)] $@"
	@$(CC) -c $(CFLAGS) $^ -o build/$(notdir $@)

OBJ = $(SRC:.c=.o)

$(LIB): $(OBJ) | build_dir
	@echo "[$(LD_COLORED)] $@"
	@$(CC) $(CFLAGS) $(addprefix build/,$(notdir $(^:.c=.o))) -shared -o build/$(LIB) $(LDFLAGS)

TEST_SRC = $(shell find tests -name '*.c')
TEST_OBJ = $(TEST_SRC:.c=.o)

TEST_CFLAGS  = -Lbuild
TEST_LDFLAGS = -lweak_compiler

$(TEST_OBJ): $(TEST_SRC) | $(LIB)
	@echo "[$(CC_COLORED)] $@"
	@$(CC) -Itests $(CFLAGS) $(@:.o=.c) \
	-o build/$(notdir $(@:.o=))_test \
	$(TEST_CFLAGS) $(TEST_LDFLAGS) $(LDFLAGS)

tests: $(TEST_OBJ)

test:
	@$(foreach file,$(shell \
		find build -executable -name '*_test' -printf "./%f\n"),\
		 (cd build; LD_LIBRARY_PATH=. $(file); \
		 ([[ $$? -eq 0 ]] && echo "OK") ||\
		 ([[ $$? -ne 0 ]] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$));)

clean:
	@rm -rf build $(OBJECTS) *.o
	@echo "Done"