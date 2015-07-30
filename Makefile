.PHONY: agda all

all: agda

agda:
	cd internal && make agda
