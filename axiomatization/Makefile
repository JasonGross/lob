.PHONY: all

FAST_TARGETS := clean archclean printenv clean-old Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif/g' | tr '~' '\n' | sed s'/^clean:/clean-old:/g' | sed s'/^Makefile: /Makefile-old: /g' > $@

-include Makefile.coq
