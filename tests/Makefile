##################################
# Compiler flags                 #
##################################
CFLAGS  += -I../tests -I../lib
LDFLAGS += -L../build/lib -lweak_compiler -lfl

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
	@mkdir -p ../build/inputs; \
	 cp -r back_end/input/*  ../build/inputs;
	 cp -r front_end/input/*  ../build/inputs;

##################################
# Sources                        #
##################################
SRC = $(shell find front_end utils -name '*.c')

ifeq ($(USE_BACKEND_EVAL), 1)
SRC += back_end/eval.c
else
SRC += back_end/back_end.c
SRC += back_end/emit.c
endif # USE_BACKEND_EVAL

ifeq ($(USE_BACKEND_RISC_V), 1)
SRC += back_end/risc_v_instr.c
endif # USE_BACKEND_RISC_V


OBJ = $(SRC:.c=.o)

src: $(OBJ)

$(OBJ): $(SRC)
	@echo [CC] $(@F)
	@$(CC) $(CFLAGS) $(@:.o=.c) -o ../build/bin/$(notdir $(@:.o=))_test $(LDFLAGS)

$(FUZZER_OBJ): $(FUZZER_SRC)
	@echo [CC] $(@F)
	@$(CC) $(CFLAGS) $^ -o ../build/bin/fuzzer $(LDFLAGS)

##################################
# Phony targets                  #
##################################
.PHONY: test
test:
	@for file in $(shell find ../build/bin -executable -name '*_test' -printf "./%f\n"); do \
		 (cd ../build; LD_LIBRARY_PATH=./lib ./bin/$$file && \
		 ([ $$? -eq 0 ] && echo "OK") || \
		 ([ $$? -ne 0 ] && echo "Test failed. Interrupt the rest."; kill -KILL $$$$);) \
	 done

.PHONY: valgrind
valgrind:
	@mkdir -p ../build/valgrind
	@for file in $(shell find ../build/bin -executable -name '*_test' -printf "%f\n"); do \
		 log="$$file.valgrind.log.txt"; \
		 ( \
		 	cd ../build; \
		 	export LD_LIBRARY_PATH=./lib; \
		 	valgrind --leak-check=full --tool=memcheck --log-fd=1 bin/$$file > valgrind/$$log; \
		 	([ $$? -eq 0 ] && echo $$file "processed") || \
		 	([ $$? -ne 0 ] && cat $$log; kill -KILL $$$$); \
 		); \
	 done

.PHONY: fuzz
fuzz:
	( \
		cd ../build; \
		export LD_LIBRARY_PATH=./lib; \
		while :; do ./bin/fuzzer; done \
	)