##################################
# Source files                   #
##################################
SRC     = $(shell find front_end middle_end util -name '*.c')
LIB     = libweak_compiler.so
LEX_SRC = ../build/src/lex.yy.c
LEX_OBJ = $(LEX_SRC:.c=.o)

ifeq ($(USE_BACKEND_RISC_V), 1)
SRC += back_end/risc_v.c
endif

ifeq ($(USE_BACKEND_X86_64), 1)
endif

ifeq ($(USE_BACKEND_EVAL), 1)
SRC += back_end/eval.c
else
SRC += back_end/back_end.c
SRC += back_end/elf.c
SRC += back_end/emit.c
endif

OBJ = $(SRC:.c=.o)

##################################
# Compiler flags                 #
##################################
LDFLAGS             += -lfl
CFLAGS              += -fPIC -I.

ifeq ($(USE_LOG), 1)
CFLAGS              += -D CONFIG_USE_LOG
endif # LOG

ifeq ($(DEBUG_BUILD), 1)
CFLAGS              += -O0 -ggdb

ifeq ($(SANITIZE), 1)
SANITIZE_CFLAGS     += -fanalyzer

ifeq ($(CC),clang)
SANITIZE_CFLAGS     += -fsanitize=cfi -fvisibility=default -flto
endif # clang
SANITIZE_LDFLAGS    += -fsanitize=address -fno-omit-frame-pointer            \
                       -fsanitize=undefined -fno-sanitize-recover=all        \
                       -fsanitize-address-use-after-scope

endif # SANITIZE
else  # !DEBUG_BUILD
CFLAGS              += -march=native -mtune=generic -O3 -D NDEBUG
endif # !DEBUG_BUILD

ifeq ($(COV),1)
COV_CFLAGS          += -fprofile-arcs -ftest-coverage --coverage -fPIC
endif # cov

##################################
# Library targets                #
##################################
all: $(LIB)

$(info CC is $(CC))

# We don't care about potential sanitizer issues in flex output.
$(LEX_OBJ): $(LEX_SRC)
	@echo [CC] $(@F)
	@$(CC) -c $(CFLAGS) $^ -o ../build/obj/$(@F)

%.o: %.c
	@echo [CC] $(@F)
	@$(CC) -c $(CFLAGS) $(SANITIZE_CFLAGS) $(COV_CFLAGS) $^ -o ../build/obj/$(@F)

$(LIB): $(OBJ) $(LEX_OBJ)
	@echo [LD] $@
	$(CC) $(addprefix ../build/obj/,$(^F)) $(COV_CFLAGS) -shared -o ../build/lib/$(LIB) -L../build $(LDFLAGS) $(SANITIZE_LDFLAGS)