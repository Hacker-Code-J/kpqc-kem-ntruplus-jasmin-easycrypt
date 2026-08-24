EASYCRYPT ?= easycrypt

.PHONY: all algebra bridge clean

all: algebra bridge

algebra:
	$(EASYCRYPT) compile NTRUPlus768BaseInvAlgebra.ec

bridge:
	$(EASYCRYPT) compile NTRUPlus768PolyBaseInvBridge.ec

clean:
	rm -f *.eco
