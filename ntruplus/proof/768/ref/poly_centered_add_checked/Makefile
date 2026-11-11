EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1
OCAMLRUNPARAM ?= o=20
export OCAMLRUNPARAM

.PHONY: all check
all: check
check:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) NTRUPlus768PolyCenteredAddCorrectness.ec
