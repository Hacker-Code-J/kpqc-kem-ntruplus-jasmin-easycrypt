EASYCRYPT ?= /home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt
EC_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1

.PHONY: all check
all: check
check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768KeygenTerminalUnit.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768KeygenGlobalUnit.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenModel.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenAcceptance.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenKeyProjection.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenDistribution.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenProcedures.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768GenROMBridge.ec
