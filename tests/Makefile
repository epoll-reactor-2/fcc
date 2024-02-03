##################################
# Compiler flags                 #
##################################
CFLAGS  = -I../tests -I../lib -Werror
LDFLAGS = -L../build -lweak_compiler -lfl

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

FUZZER_SRC = fuzz/fuzz.c
FUZZER_OBJ = fuzz.o

all: files src $(FUZZER_OBJ)

##################################
# Test inputs                    #
##################################
files:
	@mkdir -p ../build/test_inputs; \
	 cp -r front_end/input/*  ../build/test_inputs; \
	 cp -r middle_end/input/* ../build/test_inputs; \
	 cp -r back_end/input/*   ../build/test_inputs

##################################
# Sources                        #
##################################
SRC = $(shell find front_end middle_end utils -name '*.c')

ifeq ($(USE_BACKEND_EVAL), 1)
SRC += back_end/eval.c
endif # USE_BACKEND_EVAL

ifeq ($(USE_BACKEND_X86_64), 1)
SRC += back_end/x86_64.c
endif # USE_BACKEND_EVAL

OBJ = $(SRC:.c=.o)

src: $(OBJ)

$(OBJ): $(SRC)
	@echo [CC] $(@F)
	@$(CC) $(CFLAGS) $(@:.o=.c) -o ../build/$(notdir $(@:.o=))_test $(LDFLAGS)

$(FUZZER_OBJ): $(FUZZER_SRC)
	@echo [CC] $(@F)
	@$(CC) $(CFLAGS) $^ -o ../build/fuzzer $(LDFLAGS)

##################################
# Phony targets                  #
##################################
.PHONY: test
test:
	@for file in $(shell find ../build -executable -name '*_test' -printf "./%f\n"); do \
		 (cd ../build; LD_LIBRARY_PATH=. $$file && \
		 ([ $$? -eq 0 ] && echo "OK") || \
		 ([ $$? -ne 0 ] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$);) \
	 done