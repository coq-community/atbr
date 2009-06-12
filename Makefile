##########################################################################
#  This is part of ATBR, it is distributed under the terms of the        #
#           GNU Lesser General Public License version 3                  #
#                (see file LICENSE for more details)                     #
#                                                                        #
#          Copyright 2009: Thomas Braibant, Damien Pous.                 #
#                                                                        #
##########################################################################

COQC = coqc 
COQDOC = coqdoc 
COQFLAGS = -R . ATBR
COQDOCFLAGS = --html --utf8 -d doc/

-include Makefile.local

COQFILES = \
	ListOrderedType.v \
	Utils_WF.v 	\
	Force.v \
	Common.v \
	Classes.v \
	Quote.v \
	Graph.v \
	SemiLattice.v \
	Monoid.v \
	SemiRing.v \
	KleeneAlgebra.v \
	Converse.v \
	Functors.v \
	MxGraph.v \
	MxSemiLattice.v \
	MxSemiRing.v \
	MxKleeneAlgebra.v \
	MxFunctors.v \
	BoolAlg.v \
	FreeKleeneAlg.v \
	Isomorphism.v   \
	DKA_Sets.v 	\
	DKA_Algo.v 	\
	DKA_Convert.v 	\
	DKA_Annexe.v 	\
	DKA_Thompson.v 	\
	DKA_Determinisation.v \
	DKA_SimpleMinimisation.v    \
	DKA_Minimisation.v 	\
	DecideKleeneAlgebra.v \
	Commutation.v \
	RelAlg.v \
	PropAlg.v \
	Structures.v \
	Matrices.v 


VOFILES = $(COQFILES:.v=.vo)
DEPFILES = $(addprefix ., $(COQFILES:.v=.v.d))

all: $(VOFILES)

doc: doc/Examples.html 

doc/Examples.html: Examples.v
	@mkdir -p doc
	$(COQDOC) $(COQDOCFLAGS) --no-index -s Examples.v 

clean:
	rm -f *.vo .*.v.d *.glob .depend *.html

tests: Tests.vo Examples.vo

CoLoR/%.vo: $(wildcard CoLoR/*.v)
	make -C CoLoR 

%.vo: %.v
	$(COQC) $(COQFLAGS) $< 

.%.v.d: %.v
	@coqdep -I . -R CoLoR CoLoR $< > $@

-include $(DEPFILES)

