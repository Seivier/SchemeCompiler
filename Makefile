# Picked from https://stackoverflow.com/questions/714100/os-detecting-makefile
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	BIN_FORMAT = elf64
	TARGET = x86_64-linux
endif
ifeq ($(UNAME_S),Darwin) # for mac
	BIN_FORMAT = macho64
	TARGET = x86_64-apple-darwin14
	LDFLAGS = -ld_classic
endif
export CFLAGS ?= -target $(TARGET) -g $(LDFLAGS)

F =  # nothing by default
src = test


.PHONY: test

init:
	dune build @check

test:
	dune exec execs/run_test.exe -- test '$(F)'

ctest:
	dune exec execs/run_test.exe -- test '$(F)' -c

compile: 
	dune exec execs/run_compile.exe ./examples/$(src).src

compile-run: $(subst .src,.run,./examples/$(src).src)
	HEAP_SIZE=8 USE_GC=1 STACK_SIZE=0x800000 ./$<

interp: 
	dune exec execs/run_interp.exe $(src)

%.run: %.o rt/sys.c
	clang -o $@ $(CFLAGS) rt/sys.c $<

%.o: %.s
	nasm -g -f $(BIN_FORMAT) -o $@ $<

%.s: %.src 
	dune exec execs/run_compile.exe $< > $@

%.exe:
	dune build execs/$@

clean: clean-tests
	rm -Rf _build
	rm -rf examples/*.{o,s,run,dSYM/} 

# clean-tests:
# 	find bbctests/ -type f -regex '.*\.\(o\|s\|run\|result\)' -delete

clean-tests:
	find bbctests/ -type f -regex '.*\.\(o\|s\|run\|result\)' -delete

