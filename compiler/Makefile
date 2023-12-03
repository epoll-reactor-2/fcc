##################################
# Compiler flags                 #
##################################
CFLAGS  = -I../tests -I../lib
LDFLAGS = -L../build -lweak_compiler -lfl
BIN     = weak_compiler
SRC     = compiler.c
OBJ     = $(SRC:.c=.o)

ifeq ($(USE_BACKEND_EVAL), 1)
CFLAGS += -D CONFIG_USE_BACKEND_EVAL
endif # USE_BACKEND_EVAL

ifeq ($(USE_BACKEND_X86_64), 1)
CFLAGS += -D CONFIG_USE_BACKEND_X86_64
endif # USE_BACKEND_X86_64

##################################
# Targets                        #
##################################
all: $(OBJ)

$(OBJ): $(SRC)
	@echo [CC] $(notdir $@)
	@$(CC) $(CFLAGS) $(@:.o=.c) -o ../build/$(notdir $(@:.o=)) $(LDFLAGS)