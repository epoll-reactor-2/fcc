##################################
# Compiler flags                 #
##################################
CFLAGS  = -I../tests -I../lib
LDFLAGS = -L../build -lweak_compiler -lfl

all: files src

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
	@echo [CC] $(notdir $@)
	@$(CC) $(CFLAGS) $(@:.o=.c) -o ../build/$(notdir $(@:.o=))_test $(LDFLAGS)

##################################
# Phony targets                  #
##################################
.PHONY: test
test:
	@for file in $(shell find ../build -executable -name '*_test' -printf "./%f\n"); do \
		 (cd ../build; LD_LIBRARY_PATH=. $$file && \
		 ([[ $$? -eq 0 ]] && echo "OK") || \
		 ([[ $$? -ne 0 ]] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$);) \
	 done