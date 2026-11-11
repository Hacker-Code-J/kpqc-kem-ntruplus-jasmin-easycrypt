PYTHON ?= python3

.PHONY: all check gates
all: check

check:
	$(PYTHON) verify_encap_guard.py

gates:
	$(PYTHON) test_gates.py
