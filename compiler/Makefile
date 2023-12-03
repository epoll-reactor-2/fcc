##################################
# Compiler flags                 #
##################################
CFLAGS  = -I../tests -I../lib
LDFLAGS = -L../build -lweak_compiler -lfl
BIN     = weak_compiler
SRC     = compiler.c
OBJ     = $(SRC:.c=.o)

##################################
# Targets                        #
##################################
all: $(OBJ)

$(OBJ): $(SRC)
	@echo [CC] $(notdir $@)
	@$(CC) $(CFLAGS) $(@:.o=.c) -o ../build/$(notdir $(@:.o=)) $(LDFLAGS)