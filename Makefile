NR_CPUS     = $(shell nproc 2> /dev/null)
override MAKEFLAGS += -j $(NR_CPUS)

REDIRECT_STDERR := 2> /dev/null

BOLD    := $(shell printf "\033[1m"  $(REDIRECT_STDERR))
RESET   := $(shell printf $(BOLD)"\033[0m"  $(REDIRECT_STDERR))
RED     := $(shell printf $(BOLD)"\033[31m" $(REDIRECT_STDERR))
GREEN   := $(shell printf $(BOLD)"\033[32m" $(REDIRECT_STDERR))
YELLOW  := $(shell printf $(BOLD)"\033[33m" $(REDIRECT_STDERR))

LOG         := 0
DEBUG_BUILD := 1
SANITIZE    := 0

CC          = gcc
LD          = ld
LIB         = libweak_compiler.so
LDFLAGS     = -lfl
CFLAGS      = -std=gnu99 -fPIC -Ilib

CFLAGS     += -Wall -Wextra -Wshadow -Wvla -Wpointer-arith -Wframe-larger-than=32768

ifeq ($(LOG), 1)
CFLAGS     += -D USE_LOG
endif # LOG

ifeq ($(DEBUG_BUILD), 1)
CFLAGS     += -O0 -ggdb


ifeq ($(SANITIZE), 1)
CFLAGS     +=                                                       \
              -fanalyzer                                            \
              -fsanitize=address -fno-omit-frame-pointer            \
              -fsanitize=undefined -fno-sanitize-recover=all        \
              -fsanitize-address-use-after-scope

ifeq ($(CC),clang)
CFLAGS     += -fsanitize=cfi -fvisibility=default -flto
endif # clang
endif # SANITIZE
else  # !DEBUG_BUILD
CFLAGS     += -march=native -mtune=generic -O3 -D NDEBUG
endif # !DEBUG_BUILD

\t         := $(info)	$(info)

CC_COLORED := "$(YELLOW)CC$(RESET)"
LD_COLORED :=  "$(GREEN)LD$(RESET)"

ifneq (,$(findstring UTF, $(LANG)))
$(info $(info) $(RED)                                                                                  $(RESET) )
$(info $(info) $(RED)                                                                                  $(RESET) )
$(info $(info) $(RED)                   ▄▀▀▄    ▄▀▀▄  ▄▀▀█▄▄▄▄  ▄▀▀█▄   ▄▀▀▄ █                         $(RESET) )
$(info $(info) $(RED)                  █   █    ▐  █ ▐  ▄▀   ▐ ▐ ▄▀ ▀▄ █  █ ▄▀                         $(RESET) )
$(info $(info) $(RED)                  ▐  █        █   █▄▄▄▄▄    █▄▄▄█ ▐  █▀▄                          $(RESET) )
$(info $(info) $(RED)                    █   ▄    █    █    ▌   ▄▀   █   █   █                         $(RESET) )
$(info $(info) $(RED)                     ▀▄▀ ▀▄ ▄▀   ▄▀▄▄▄▄   █   ▄▀  ▄▀   █                          $(RESET) )
$(info $(info) $(RED)                           ▀     █    ▐   ▐   ▐   █    ▐                          $(RESET) )
$(info $(info) $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(info) $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(info) $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(info) $(RED)     ▄▀▄▄▄▄   ▄▀▀▀▀▄   ▄▀▀▄ ▄▀▄  ▄▀▀▄▀▀▀▄  ▄▀▀█▀▄   ▄▀▀▀▀▄     ▄▀▀█▄▄▄▄  ▄▀▀▄▀▀▀▄ $(RESET) )
$(info $(info) $(RED)    █ █    ▌ █      █ █  █ ▀  █ █   █   █ █   █  █ █    █     ▐  ▄▀   ▐ █   █   █ $(RESET) )
$(info $(info) $(RED)    ▐ █      █      █ ▐  █    █ ▐  █▀▀▀▀  ▐   █  ▐ ▐    █       █▄▄▄▄▄  ▐  █▀▀█▀  $(RESET) )
$(info $(info) $(RED)      █      ▀▄    ▄▀   █    █     █          █        █        █    ▌   ▄▀    █  $(RESET) )
$(info $(info) $(RED)     ▄▀▄▄▄▄▀   ▀▀▀▀   ▄▀   ▄▀    ▄▀        ▄▀▀▀▀▀▄   ▄▀▄▄▄▄▄▄▀ ▄▀▄▄▄▄   █     █   $(RESET) )
$(info $(info) $(RED)    █     ▐           █    █    █         █       █  █         █    ▐   ▐     ▐   $(RESET) )
$(info $(info) $(RED)    ▐                 ▐    ▐    ▐         ▐       ▐  ▐         ▐                  $(RESET) )
$(info $(info) $(RED)                                                                                  $(RESET) )
$(info $(info) $(RED)                                                                                  $(RESET) )
endif

all: build_dir test_files $(LIB) tests

build_dir:
	@if ! [[ -d build ]]; then \
	    mkdir -p build/test_inputs; \
		flex --outfile=build/lex.yy.c lex/grammar.lex; \
	fi

test_files: | build_dir
	@cp -r tests/front_end/input/*  build/test_inputs; \
	 cp -r tests/middle_end/input/* build/test_inputs; \
	 cp -r tests/back_end/input/*   build/test_inputs

SRC  = $(shell find lib -name '*.c')
SRC += build/lex.yy.c

%.o: %.c
	@echo [$(CC_COLORED)] $@
	@$(CC) -c $(CFLAGS) $^ -o build/$(notdir $@)

OBJ = $(SRC:.c=.o)

$(LIB): $(OBJ) | build_dir
	@echo [$(LD_COLORED)] $@
	@$(LD) $(addprefix build/,$(notdir $^)) -shared -o build/$(LIB) -Lbuild $(LDFLAGS)

TEST_SRC = $(shell find tests -name '*.c')
TEST_OBJ = $(TEST_SRC:.c=.o)

LDFLAGS += -lweak_compiler

$(TEST_OBJ): $(TEST_SRC) | $(LIB)
	@echo [$(CC_COLORED)] $@
	@$(CC) -Itests -Lbuild $(CFLAGS) $(@:.o=.c) -o build/$(notdir $(@:.o=))_test $(LDFLAGS)

tests: $(TEST_OBJ)

.PHONY: test
test:
	@for file in $(shell find build -executable -name '*_test' -printf "./%f\n"); do \
		 (cd build; LD_LIBRARY_PATH=. $$file && \
		 ([[ $$? -eq 0 ]] && echo "OK") || \
		 ([[ $$? -ne 0 ]] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$);) \
	 done

.PHONY: clean
clean:
	@rm -rf build
	@echo "Done"

.PHONY: cppcheck
cppcheck:
ifeq ($(CHECK_ALL),1)
	@cppcheck -f -j$(NR_CPUS) --enable=all --language=c --std=c11 lib
else
	@cppcheck -f -j$(NR_CPUS) --enable=warning,performance,portability --language=c --std=c11 lib
endif
