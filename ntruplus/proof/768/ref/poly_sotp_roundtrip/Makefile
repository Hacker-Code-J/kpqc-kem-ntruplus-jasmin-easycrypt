# -*- Makefile -*-

EASYCRYPT ?= easycrypt
ENCODE_PROOF := NTRUPlus768PolySOTPEncodeAlgebra.ec
ROUNDTRIP_PROOF := NTRUPlus768PolySOTPRoundTrip.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1

.PHONY: all check encode roundtrip

all: check

check: encode roundtrip

encode:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(ENCODE_PROOF)

roundtrip:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(ROUNDTRIP_PROOF)
