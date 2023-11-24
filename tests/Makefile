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
SRC = $(shell find . -name '*.c')
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