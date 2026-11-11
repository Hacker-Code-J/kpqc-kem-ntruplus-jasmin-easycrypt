EASYCRYPT ?= easycrypt

.PHONY: all prime algebra bridge baseinv-word clean

all: prime algebra bridge baseinv-word

prime:
	$(EASYCRYPT) compile NTRUPlus768FqInvPrime.ec

algebra:
	$(EASYCRYPT) compile NTRUPlus768FqInvAlgebra.ec

bridge:
	$(EASYCRYPT) compile NTRUPlus768FqInvBaseInvBridge.ec

baseinv-word:
	$(EASYCRYPT) compile NTRUPlus768BaseInvWordAlgebra.ec

clean:
	rm -f *.eco

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

prime algebra bridge baseinv-word: check-model-compatibility
