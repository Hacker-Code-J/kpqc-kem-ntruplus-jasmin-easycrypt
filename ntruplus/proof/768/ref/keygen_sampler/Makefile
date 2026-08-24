EASYCRYPT ?= easycrypt

.PHONY: all algebra bridge clean

all: algebra bridge

algebra:
	$(EASYCRYPT) compile NTRUPlus768KeygenSamplerAlgebra.ec

bridge:
	$(EASYCRYPT) compile NTRUPlus768KeygenSamplerBridge.ec

clean:
	rm -f *.eco
