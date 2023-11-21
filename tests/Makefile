SRC = $(shell find . -name '*.c')
OBJ = $(SRC:.c=.o)

override LDFLAGS += -lweak_compiler

all: files src run

files:
	@cp -r front_end/input/*  ../build/test_inputs; \
	 cp -r middle_end/input/* ../build/test_inputs; \
	 cp -r back_end/input/*   ../build/test_inputs

src: $(OBJ)

$(OBJ): $(SRC)
	@echo [$(CC_COLORED)] $@
	$(CC) -I../tests -I../lib -L../build $(CFLAGS) $(@:.o=.c) -o ../build/$(notdir $(@:.o=))_test $(LDFLAGS)

run:
	@for file in $(shell find ../build -executable -name '*_test' -printf "./%f\n"); do \
		 (cd ../build; LD_LIBRARY_PATH=. $$file && \
		 ([[ $$? -eq 0 ]] && echo "OK") || \
		 ([[ $$? -ne 0 ]] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$);) \
	 done