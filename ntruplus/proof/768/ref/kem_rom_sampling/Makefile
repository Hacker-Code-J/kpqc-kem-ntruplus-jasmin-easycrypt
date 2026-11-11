EASYCRYPT ?= easycrypt
export OCAMLRUNPARAM = o=20
.PHONY: all check
all: check
check:
	$(EASYCRYPT) compile -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1 NTRUPlus768ROMSOTPMaskLaw.ec
	$(EASYCRYPT) compile -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1 NTRUPlus768ROMSOTPSampling.ec
