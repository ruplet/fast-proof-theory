.PHONY: build build-lib build-exe check extract

MYPA_FILE ?= demo/smoke_linear_gentzen.mypa
THEOREM ?= smoke
OUT ?= demo/$(THEOREM)_extracted.lean
CHECK_ARG := $(word 2,$(MAKECMDGOALS))

build: build-lib build-exe

build-lib:
	lake build FastProofTheory

build-exe:
	lake build fast-proof-theory

check:
	node proofAssistant/cli.js verify $(if $(CHECK_ARG),$(CHECK_ARG),$(MYPA_FILE))

extract:
	node proofAssistant/cli.js extract $(MYPA_FILE) $(THEOREM) -o $(OUT)

# Allow: make check path/to/file.mypa
%:
	@:
