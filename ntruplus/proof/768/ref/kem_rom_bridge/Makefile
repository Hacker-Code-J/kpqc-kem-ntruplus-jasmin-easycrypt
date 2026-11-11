EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1
PROOFS := NTRUPlus768KEMPayloadSpec.ec NTRUPlus768KEMPayloadAlgebra.ec NTRUPlus768ROMPayloadHash.ec NTRUPlus768ROMKeygen.ec NTRUPlus768ROMEncap.ec NTRUPlus768ROMDecap.ec NTRUPlus768ROMCorrectness.ec
.PHONY: all check
all: check
check:
	@set -e; for proof in $(PROOFS); do OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EASYCRYPT_FLAGS) "$$proof"; done
