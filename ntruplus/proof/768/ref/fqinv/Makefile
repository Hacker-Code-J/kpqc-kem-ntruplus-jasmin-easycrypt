EASYCRYPT ?= easycrypt

.PHONY: all prime algebra bridge clean

all: prime algebra bridge

prime:
	$(EASYCRYPT) compile NTRUPlus768FqInvPrime.ec

algebra:
	$(EASYCRYPT) compile NTRUPlus768FqInvAlgebra.ec

bridge:
	$(EASYCRYPT) compile NTRUPlus768FqInvBaseInvBridge.ec

clean:
	rm -f *.eco
