EASYCRYPT ?= /home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt
EC_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1

.PHONY: all check
all: check
check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCAQueryCodec.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCAOraclePorts.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCAStatusAdapter.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCADecapOracle.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCAProbability.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RawXOFSampling.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RawXOFStreams.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RawXOF.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCASetup.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCAGame.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768RawXOFLaws.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768CCARawStateFrame.ec
