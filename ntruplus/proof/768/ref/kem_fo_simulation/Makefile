EASYCRYPT ?= /home/hacker-code-j/.opam/cryptotools-2026.09/bin/easycrypt
EC_FLAGS ?= -no-eco -pragmas Proofs:check -p Z3 -timeout 60 -max-provers 1

.PHONY: all check
all: check
check:
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimAverage.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimCandidate.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimFreshHash.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimModel.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSequentialDistance.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimHybrid.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimLookup.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSampling.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimAnswer.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimKnownAlgebra.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimOracles.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPrefix.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPublicError.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSpreadHash.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimAnswerErasure.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimGErasure.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimKnown.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPorts.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPublicBound.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimChallengeAnswer.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimGames.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPortContracts.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPublicCapRemoval.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPublicGames.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPublicInstances.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimRealBridge.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSelected.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSetupBridge.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimKnownCoupling.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimLookupGameBridge.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPhaseState.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimRealGameBridge.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSelectedCoupling.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSelectedInvariant.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimKnownBridge.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimSelectedBound.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimPhaseBound.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimKernelBound.ec
	OCAMLRUNPARAM=o=20 $(EASYCRYPT) compile $(EC_FLAGS) NTRUPlus768SimFinal.ec
