# Makefile originally taken from coq-club

SRC_DIR := src
CFLAGS := -Wall -g
SRC := $(wildcard $(SRC_DIR)/*.c)
OBJ := $(SRC:$(SRC_DIR)/%.c=$(SRC_DIR)/%.o)

COQMFFLAGS := -Q . SpArch
ALLVFILES := src/sparch.v src/verif_sparch.v

all: main Makefile.coq $(ALLVFILES)
	$(MAKE) -f Makefile.coq
	+make -f Makefile.coq all

clean: 
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf
	rm -f *.o src/*.o

$(SRC_DIR)/%.o: $(SRC_DIR)/%.h $(SRC_DIR)/$.c
	gcc $(CFLAGS) -c $< -o $@

src/sparch.v: src/sparch.h src/sparch.c
	./compcert/clightgen -normalize -short-idents src/sparch.c

main.o: src/sparch.h main.c
	gcc $(CFLAGS) -c main.c -o main.o

main: $(OBJ) main.o
	gcc $(CFLAGS) src/sparch.o main.o -o sparch

#Makefile.coq: _CoqProject Makefile
#	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: all clean
