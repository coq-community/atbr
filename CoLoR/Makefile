##########################################################################
#  This is part of ATBR, it is distributed under the terms of the        #
#           GNU Lesser General Public License version 3                  #
#             (see file LICENSE.txt for more details)                    #
#                                                                        #
#  Copyright 2009: Thomas Braibant, Damien Pous.                         #
#                                                                        #
##########################################################################

COQC = coqc 
COQDOC = coqdoc 

-include ../Makefile.local

COQFLAGS = -R . ATBR.CoLoR
COQFILES = $(wildcard *.v)

VOFILES = $(COQFILES:.v=.vo)
DOCFILES = $(COQFILES:.v=.html)
DEPFILES = $(addprefix ., $(COQFILES:.v=.v.d))

all: $(VOFILES)

doc: $(DOCFILES)

clean:
	rm -f *.vo .*.v.d *.glob .depend *.html

tests: Tests.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $< 

%.html: %.v
	$(COQDOC) -g $< 

.%.v.d: %.v
	@coqdep -I . $< > $@

-include $(DEPFILES)


