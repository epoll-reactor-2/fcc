##################################
# Common variables               #
##################################

# This is to use Bash-specific things like process substitution <().
SHELL                = /bin/bash
NR_CPUS              = $(shell nproc 2> /dev/null)
override MAKEFLAGS  += -j $(NR_CPUS)

REDIRECT_STDERR     := 2> /dev/null

CC                   = gcc
LD                   = ld
\t                  := $(info)	$(info)

DEBUG_BUILD          := 1
SANITIZE             := 0

USE_LOG              := 0
USE_BACKEND_EVAL     := 0
USE_BACKEND_RISC_V   := 1

# Export all defined now variables to Makefile's
# being child processes.
export

##################################
# Logo                           #
##################################
RED    := $(shell echo "\033[031m")
RESET  := $(shell echo "\033[0m")

ifneq (,$(findstring UTF, $(LANG)))
$(info $(RED)                                                                                  $(RESET) )
$(info $(RED)                                                                                  $(RESET) )
$(info $(RED)                   ▄▀▀▄    ▄▀▀▄  ▄▀▀█▄▄▄▄  ▄▀▀█▄   ▄▀▀▄ █                         $(RESET) )
$(info $(RED)                  █   █    ▐  █ ▐  ▄▀   ▐ ▐ ▄▀ ▀▄ █  █ ▄▀                         $(RESET) )
$(info $(RED)                  ▐  █        █   █▄▄▄▄▄    █▄▄▄█ ▐  █▀▄                          $(RESET) )
$(info $(RED)                    █   ▄    █    █    ▌   ▄▀   █   █   █                         $(RESET) )
$(info $(RED)                     ▀▄▀ ▀▄ ▄▀   ▄▀▄▄▄▄   █   ▄▀  ▄▀   █                          $(RESET) )
$(info $(RED)                           ▀     █    ▐   ▐   ▐   █    ▐                          $(RESET) )
$(info $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(RED)                                 ▐                ▐                               $(RESET) )
$(info $(RED)     ▄▀▄▄▄▄   ▄▀▀▀▀▄   ▄▀▀▄ ▄▀▄  ▄▀▀▄▀▀▀▄  ▄▀▀█▀▄   ▄▀▀▀▀▄     ▄▀▀█▄▄▄▄  ▄▀▀▄▀▀▀▄ $(RESET) )
$(info $(RED)    █ █    ▌ █      █ █  █ ▀  █ █   █   █ █   █  █ █    █     ▐  ▄▀   ▐ █   █   █ $(RESET) )
$(info $(RED)    ▐ █      █      █ ▐  █    █ ▐  █▀▀▀▀  ▐   █  ▐ ▐    █       █▄▄▄▄▄  ▐  █▀▀█▀  $(RESET) )
$(info $(RED)      █      ▀▄    ▄▀   █    █     █          █        █        █    ▌   ▄▀    █  $(RESET) )
$(info $(RED)     ▄▀▄▄▄▄▀   ▀▀▀▀   ▄▀   ▄▀    ▄▀        ▄▀▀▀▀▀▄   ▄▀▄▄▄▄▄▄▀ ▄▀▄▄▄▄   █     █   $(RESET) )
$(info $(RED)    █     ▐           █    █    █         █       █  █         █    ▐   ▐     ▐   $(RESET) )
$(info $(RED)    ▐                 ▐    ▐    ▐         ▐       ▐  ▐         ▐                  $(RESET) )
$(info $(RED)                                                                                  $(RESET) )
$(info $(RED)                                                                                  $(RESET) )
endif

##################################
# Make targets                   #
##################################
all: dir library test_suite driver

dir:
	@if ! [ -d build ]; then \
		mkdir build; \
		flex --outfile=build/lex.yy.c lex/grammar.lex; \
	fi

library:
	@make -C lib

test_suite: | library
	@make -C tests

driver: | library
	@make -C compiler

##################################
# Phony targets                  #
##################################
.PHONY: clean
clean:
	@rm -rf build;
	@echo "Done"

.PHONY: test
test:
	@make -C tests test

.PHONY: valgrind
valgrind:
	@make -C tests valgrind

CPPCHECK_SUPPRESSIONS = incorrectStringBooleanError\nallocaCalled

# Check out:
# https://github.com/danmar/cppcheck/blob/main/addons/
.PHONY: static_analysis
static_analysis:
	cppcheck -f -j$(NR_CPUS) --enable=warning,performance,portability \
	--suppressions-list=<(echo -e '${CPPCHECK_SUPPRESSIONS}') \
	--language=c --std=c11 lib \
	-Ilib

# Usage:
# $ make COV=1
# $ make cov
.PHONY: cov
cov:
	lcov --zerocounters --directory $$PWD
	lcov --capture --initial --directory $$PWD --output-file coverage_output
	make test
	lcov --no-checksum --directory $$PWD --capture --output-file coverage_output
	genhtml --branch-coverage --highlight --legend --output-directory build/coverage coverage_output

.PHONY: cyclomatic_complexity
cyclomatic_complexity:
	pmccabe -v -c `find lib -name '*.c'` | sort -k1,1n --numeric-sort
