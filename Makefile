.PHONY: agda all

all: agda coq coq-axiomatization

agda:
	cd internal && $(MAKE) agda

coq:
	cd internal && $(MAKE) coq

coq-axiomatization:
	cd axiomatization && $(MAKE)

clean::
	cd internal && $(MAKE) clean
	cd axiomatization && $(MAKE) clean
