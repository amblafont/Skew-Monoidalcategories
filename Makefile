OBJS = SkewMonoidalCategories.vo IModules.vo StructuralActions.vo
CC = coqc
FLAGS = -noinit -indices-matter -type-in-type -w none

all: $(OBJS)

%.vo: %.v
	coqc $(FLAGS) $<

