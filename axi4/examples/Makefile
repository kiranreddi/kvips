.PHONY: help list-tests questa questa-waves vcs xcelium verilator regress-questa regress-vcs regress-xcelium regress-verilator fsdbreport clean

SIM_DIR := uvm_back2back/sim
SIM_DIR_ABS := $(abspath $(SIM_DIR))

TEST ?= axi4_b2b_test
SEED ?= 1
UVM_VERBOSITY ?= UVM_LOW
PLUSARGS ?=

USE_LSF ?= 0
# LSF Settings (Optional)
LSF_BSUB ?= bsub -Ip -app gnrc -q interactive

FSDB ?=
BT ?=
ET ?=

ifneq ($(USE_LSF),0)
RUN_PREFIX := $(LSF_BSUB)
else
RUN_PREFIX :=
endif

COMMON_PLUSARGS := +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY) +ntb_random_seed=$(SEED) $(PLUSARGS)

help:
	@echo "KVIPS AXI4 examples (UVM back2back)"
	@echo ""
	@echo "Targets:"
	@echo "  make list-tests"
	@echo "  make questa         TEST=<name> SEED=<n> UVM_VERBOSITY=<lvl> PLUSARGS='<...>' [USE_LSF=1]"
	@echo "  make questa-waves   (Questa FSDB) same vars as 'questa' [USE_LSF=1]"
	@echo "  make vcs            TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make xcelium        TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make regress-questa PLUSARGS='<...>'"
	@echo "  make regress-vcs    PLUSARGS='<...>'"
	@echo "  make regress-xcelium PLUSARGS='<...>'"
	@echo "  make verilator      TEST=<name> UVM_VERBOSITY=<lvl> PLUSARGS='<...>'"
	@echo "  make regress-verilator PLUSARGS='<...>'"
	@echo "  make fsdbreport     FSDB=<path> [BT=<time>] [ET=<time>]"
	@echo "  make clean"
	@echo ""
	@echo "Notes:"
	@echo "  - USE_LSF=1 prepends '$(LSF_BSUB)' (edit LSF_BSUB to match your site)."
	@echo "  - The sim scripts auto-load tool modules when available."

list-tests:
	@cat $(SIM_DIR)/tests_questa.list

questa:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_questa.sh $(COMMON_PLUSARGS)

questa-waves:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_questa_fsdb.sh $(COMMON_PLUSARGS)

vcs:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_vcs.sh $(COMMON_PLUSARGS)

xcelium:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_xcelium.sh $(COMMON_PLUSARGS)

verilator:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_verilator.sh $(COMMON_PLUSARGS)

regress-questa:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_questa_lsf.sh $(PLUSARGS)

regress-vcs:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_vcs_lsf.sh $(PLUSARGS)

regress-xcelium:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_xcelium_lsf.sh $(PLUSARGS)

regress-verilator:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_verilator.sh $(PLUSARGS)

fsdbreport:
	@if [ -z "$(FSDB)" ]; then echo "ERROR: FSDB=<path> required"; exit 2; fi
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_fsdbreport_lsf.sh "$(FSDB)" $(if $(BT),--bt "$(BT)",) $(if $(ET),--et "$(ET)",)

clean:
	@rm -rf $(SIM_DIR)/out
