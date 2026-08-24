# -*- Makefile -*-

EASYCRYPT ?= easycrypt
TERMINAL_PROOF := NTRUPlus768DecapTerminalProof.ec
BRIDGE_PROOF := NTRUPlus768DecapTerminalBridge.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1
EASYCRYPT_INCLUDES ?= -I . -I ../decap_fail -I ../decap_mask

.PHONY: all check terminal-proof bridge-proof

all: check

check: terminal-proof bridge-proof

terminal-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(EASYCRYPT_INCLUDES) $(TERMINAL_PROOF)

bridge-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(EASYCRYPT_INCLUDES) $(BRIDGE_PROOF)
