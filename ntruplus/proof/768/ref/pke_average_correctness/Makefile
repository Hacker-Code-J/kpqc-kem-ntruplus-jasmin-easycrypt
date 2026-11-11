EASYCRYPT ?= /home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt
EC_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1

.PHONY: all check
all: check
check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEModel.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEProcedures.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEAlgebra.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKECallProof.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEKeyDistribution.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEAverageModel.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEAverageCorrectness.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768PKEAverageROM.ec
