EASYCRYPT ?= easycrypt

.PHONY: all check
all: check

check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1 NTRUPlus768KeygenShapeProof.ec
