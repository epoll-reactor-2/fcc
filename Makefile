NR_CPUS     = $(shell nproc 2> /dev/null)
override MAKEFLAGS += -j $(NR_CPUS)

REDIRECT_STDERR := 2> /dev/null

LOG         := 0
DEBUG_BUILD := 1
SANITIZE    := 0

CC          = gcc
LD          = ld
LIB         = libweak_compiler.so
LDFLAGS     = -lfl
CFLAGS      = -std=gnu99 -fPIC -Ilib \
              -Wall -Wextra -Wshadow -Wvla -Wpointer-arith

ifeq ($(LOG), 1)
CFLAGS     += -D USE_LOG
endif # LOG

ifeq ($(DEBUG_BUILD), 1)
CFLAGS     += -O0 -ggdb

ifeq ($(SANITIZE), 1)
CFLAGS     += -fanalyzer                                            \
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

RED    := $(shell echo -e "\033[031m")
RESET  := $(shell echo -e "\033[0m")

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

all: dir $(LIB) test_src

dir:
	@if ! [[ -d build ]]; then \
	    mkdir -p build/test_inputs; \
		flex --outfile=build/lex.yy.c lex/grammar.lex; \
	fi

test_src: | $(LIB)
	@ make -C tests

.PHONY: test
test:
	make -C tests test

SRC  = $(shell find lib -name '*.c')
SRC += build/lex.yy.c
OBJ  = $(SRC:.c=.o)

%.o: %.c
	@echo [CC] $(notdir $@)
	@$(CC) -c $(CFLAGS) $^ -o build/$(notdir $@)

$(LIB): $(OBJ) | dir
	@echo [$(LD_COLORED)] $@
	@$(LD) $(addprefix build/,$(notdir $^)) -shared -o build/$(LIB) -Lbuild $(LDFLAGS)

.PHONY: cppcheck
cppcheck:
ifeq ($(CHECK_ALL),1)
	@cppcheck -f -j$(NR_CPUS) --enable=all --language=c --std=c11 lib
else
	@cppcheck -f -j$(NR_CPUS) --enable=warning,performance,portability --language=c --std=c11 lib
endif