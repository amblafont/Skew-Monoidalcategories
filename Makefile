OBJS = Complements.vo IModules.vo StructuralStrengths.vo  InitialAlgebraicMonoid.vo Summary.vo
CC = coqc
FLAGS = -noinit -indices-matter -type-in-type -w none

all: $(OBJS)

%.vo: %.v
	coqc $(FLAGS) $<

clean:
	rm *.vo



