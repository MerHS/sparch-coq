# Makefile originally taken from coq-club

SRC_DIR := src
CFLAGS := -Wall -O2
SRC := $(wildcard $(SRC_DIR)/*.c)
OBJ := $(SRC:$(SRC_DIR)/%.c=$(SRC_DIR)/%.o)

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f *.o src/*.o

$(SRC_DIR)/%.o: $(SRC_DIR)/%.h $(SRC_DIR)/$.c
	gcc $(CFLAGS) -c $< -o $@

main.o: src/sparch.h main.c
	gcc $(CFLAGS) -c main.c -o main.o

main: $(OBJ) main.o
	gcc $(CFLAGS) src/sparch.o main.o -o sparch

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony
