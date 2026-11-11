EASYCRYPT ?= /home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt
EC_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1

.PHONY: all check
all: check
check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecCanonical.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecTerminal.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecTransform.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecSerialization.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecLinearModel.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecLinearProcedures.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecLinearAlgebra.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecLinearProof.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecNativeComparison.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecNativeProcedures.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecNativeProof.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RRecACWC2Bridge.ec
