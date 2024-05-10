##################################
# Source files                   #
##################################
SRC = $(shell find front_end middle_end util -name '*.c')
LIB = libweak_compiler.so

ifeq ($(USE_BACKEND_EVAL), 1)
SRC += back_end/eval.c
endif # USE_BACKEND_EVAL

ifeq ($(USE_BACKEND_RISC_V), 1)
SRC += back_end/risc_v.c
endif # USE_BACKEND_EVAL

SRC += back_end/elf.c

OBJ = $(SRC:.c=.o)

##################################
# Compiler flags                 #
##################################
LDFLAGS      = -lfl
CFLAGS       = -std=gnu99 -fPIC -I. \
               -Wall -Wextra -Wunused -Wshadow -Wvla -Wpointer-arith

ifeq ($(USE_LOG), 1)
CFLAGS     += -D CONFIG_USE_LOG
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

ifeq ($(COV),1)
COV_CFLAGS  += -fprofile-arcs -ftest-coverage --coverage -fPIC
endif # cov

##################################
# Library targets                #
##################################
all: $(LIB)

$(info CC is $(CC))

../build/lex.yy.o: ../build/lex.yy.c
	@echo [CC] $(@F)
	@$(CC) -c $(CFLAGS) $^ -o ../build/$(@F)

%.o: %.c
	@echo [CC] $(@F)
	@$(CC) -c $(CFLAGS) $(COV_CFLAGS) $^ -o ../build/$(@F)

$(LIB): $(OBJ) ../build/lex.yy.o
	@echo [LD] $@
	@$(CC) $(addprefix ../build/,$(^F)) $(COV_CFLAGS) -shared -o ../build/$(LIB) -L../build $(LDFLAGS)