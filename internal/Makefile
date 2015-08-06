V = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

QECHO_0 := @true
QECHO_1 := @echo
QECHO = $(QECHO_$(V))

containing = $(foreach v,$2,$(if $(findstring $1,$v),$v))
not-containing = $(foreach v,$2,$(if $(findstring $1,$v),,$v))

FAST_TARGETS := clean archclean printenv clean-old update-_CoqProject Makefile.coq agda

.PHONY: agda all coq FORCE

all: agda coq

%.agdai: %.agda
	agda -i . --html $<

agda: lob.agdai mini-lob.agdai mini-quine.agdai

Makefile.coq: Makefile _CoqProject
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif/g' | tr '~' '\n' | sed s'/^clean:/clean-old:/g' | sed s'/^Makefile: /Makefile-old: /g' > $@

-include Makefile.coq

# Recursively find the transitively closed dependencies of the set $1
# of *.vo files, using an accumulating parameter $2 of dependencies
# previously found.  We extract the dependencies from the
# corresponding *.v.d files using sed(1), filter out previously found
# dependencies, sort to remove duplicates, then make a recursive call
# with the deduplicated newly found dependencies.  When $1 becomes
# empty, the result is $2.
read_deps = $(if $(wildcard $1),$(filter %.vo,$(shell sed -n 's/^[^:]*: // p' $1 | sed s',\./,,g')))
vo_closure = $(if $1,$(call vo_closure,$(sort $(filter-out $1 $2,$(call read_deps,$(1:.vo=.v.d)))),$1 $2),$2)

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

update-_CoqProject:
	(echo '-R . Lob'; echo '-arg -no-native-compiler'; find . -name "*.v" | sed 's,^\./,,g' | $(SORT_COQPROJECT)) > _CoqProject

$(filter-out $(VOFILES),$(call vo_closure,$(VOFILES))): FORCE
	@ echo
	@ echo 'error: $@ is missing from _CoqProject.'
	@ echo 'error: Please run `make update-_CoqProject`.'
	$(QECHO) '_CoqProject contents: $(VOFILES)'
	$(QECHO) 'All files : $(call vo_closure,$(VOFILES))'
	@ false

coq: $(VOFILES)

clean::
	$(VECHO) "RM *.CMO *.CMI *.CMA"
	$(Q)rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	$(VECHO) "RM *.CMX *.CMXS *.CMXA *.O *.A"
	$(Q)rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	$(VECHO) "RM *.ML.D *.MLI.D *.ML4.D *.MLLIB.D"
	$(Q)rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	$(VECHO) "RM *.VO *.VI *.G *.V.D *.V.BEAUTIFIED *.V.OLD"
	$(Q)rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	$(VECHO) "RM *.PS *.PDF *.GLOB *.TEX *.G.TEX"
	$(Q)rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	$(VECHO) "RM *.AGDAI"
	$(Q)rm -f *.agdai
	- rm -rf html mlihtml
	rm -f Makefile.coq .depend
