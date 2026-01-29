.PHONY: help list-tests questa questa-waves vcs xcelium regress-questa fsdbreport clean

SIM_DIR := uvm_back2back/sim

TEST ?= axi4_b2b_test
SEED ?= 1
UVM_VERBOSITY ?= UVM_LOW
PLUSARGS ?=

USE_IGNRC ?= 0
IGNRC ?= /tools/scripts/ignrc

FSDB ?=
BT ?=
ET ?=

ifneq ($(USE_IGNRC),0)
RUN_PREFIX := $(IGNRC)
else
RUN_PREFIX :=
endif

COMMON_PLUSARGS := +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY) +ntb_random_seed=$(SEED) $(PLUSARGS)

help:
	@echo "KVIPS AXI4 examples (UVM back2back)"
	@echo ""
	@echo "Targets:"
	@echo "  make list-tests"
	@echo "  make questa         TEST=<name> SEED=<n> UVM_VERBOSITY=<lvl> PLUSARGS='<...>' [USE_IGNRC=1]"
	@echo "  make questa-waves   (Questa FSDB) same vars as 'questa' [USE_IGNRC=1]"
	@echo "  make vcs            TEST=<name> SEED=<n> ... [USE_IGNRC=1]"
	@echo "  make xcelium        TEST=<name> SEED=<n> ... [USE_IGNRC=1]"
	@echo "  make regress-questa PLUSARGS='<...>'"
	@echo "  make fsdbreport     FSDB=<path> [BT=<time>] [ET=<time>]"
	@echo "  make clean"
	@echo ""
	@echo "Notes:"
	@echo "  - USE_IGNRC=1 prepends '$(IGNRC)' (required on some clusters)."
	@echo "  - The sim scripts auto-load tool modules when available."

list-tests:
	@cat $(SIM_DIR)/tests_questa.list

questa:
	@$(RUN_PREFIX) $(SIM_DIR)/run_questa.sh $(COMMON_PLUSARGS)

questa-waves:
	@$(RUN_PREFIX) $(SIM_DIR)/run_questa_fsdb.sh $(COMMON_PLUSARGS)

vcs:
	@$(RUN_PREFIX) $(SIM_DIR)/run_vcs.sh $(COMMON_PLUSARGS)

xcelium:
	@$(RUN_PREFIX) $(SIM_DIR)/run_xcelium.sh $(COMMON_PLUSARGS)

regress-questa:
	@$(SIM_DIR)/regress_questa_ignrc.sh $(PLUSARGS)

fsdbreport:
	@if [ -z "$(FSDB)" ]; then echo "ERROR: FSDB=<path> required"; exit 2; fi
	@$(RUN_PREFIX) $(SIM_DIR)/run_fsdbreport_ignrc.sh "$(FSDB)" $(if $(BT),--bt "$(BT)",) $(if $(ET),--et "$(ET)",)

clean:
	@rm -rf $(SIM_DIR)/out
