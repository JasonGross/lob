.PHONY: agda all

all: agda coq coq-axiomatization

agda:
	cd internal && make agda

coq:
	cd internal && make coq

coq-axiomatization:
	cd axiomatization && make
