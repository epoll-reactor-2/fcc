##################################
# Source files                   #
##################################
SRC = $(shell find . -name '*.c') ../build/lex.yy.c
OBJ = $(SRC:.c=.o)
LIB = libweak_compiler.so

##################################
# Compiler flags                 #
##################################
LDFLAGS      = -lfl
CFLAGS       = -std=gnu99 -fPIC -I. \
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

##################################
# Library targets                #
##################################
all: $(LIB)

$(info CC is $(CC))

%.o: %.c
	@echo [CC] $(notdir $@)
	@$(CC) -c $(CFLAGS) $^ -o ../build/$(notdir $@)

$(LIB): $(OBJ)
	@echo [LD] $@
	@$(LD) $(addprefix ../build/,$(notdir $^)) -shared -o ../build/$(LIB) -L../build $(LDFLAGS)