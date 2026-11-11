EASYCRYPT ?= easycrypt

.PHONY: all algebra bridge clean

all: algebra bridge

algebra:
	$(EASYCRYPT) compile NTRUPlus768BaseInvAlgebra.ec

bridge:
	$(EASYCRYPT) compile NTRUPlus768PolyBaseInvBridge.ec

clean:
	rm -f *.eco

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

algebra bridge: check-model-compatibility
