OBJS = SkewMonoidalCategories.vo  Complements.vo SkewMonoids.vo IModules.vo StructuralActions.vo StructuralStrengths.vo  AssumeLemma48.vo
CC = coqc
FLAGS = -noinit -indices-matter -type-in-type -w none

all: $(OBJS)

%.vo: %.v
	coqc $(FLAGS) $<

clean:
	rm *.vo



