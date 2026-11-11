EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1
PROOFS := NTRUPlus768ROMSeedObserver.ec NTRUPlus768ROMSeedCollision.ec NTRUPlus768ROMKeygenObserver.ec
.PHONY: all check
all: check
check:
	@set -e; for proof in $(PROOFS); do OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EASYCRYPT_FLAGS) "$$proof"; done
