.PHONY: help list-tests questa vcs xcelium verilator regress-verilator clean

SIM_DIR := uvm_back2back/sim
SIM_DIR_ABS := $(abspath $(SIM_DIR))

TEST ?= ahb_smoke_test
SEED ?= 1
UVM_VERBOSITY ?= UVM_LOW
PLUSARGS ?=

USE_LSF ?= 0
LSF_BSUB ?= bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive

ifneq ($(USE_LSF),0)
RUN_PREFIX := $(LSF_BSUB)
else
RUN_PREFIX :=
endif

COMMON_PLUSARGS := +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY) +ntb_random_seed=$(SEED) $(PLUSARGS)

help:
	@echo "KVIPS AHB examples (UVM back2back)"
	@echo ""
	@echo "Targets:"
	@echo "  make list-tests"
	@echo "  make questa         TEST=<name> SEED=<n> UVM_VERBOSITY=<lvl> PLUSARGS='<...>' [USE_LSF=1]"
	@echo "  make vcs            TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make xcelium        TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make verilator      TEST=<name> SEED=<n> ..."
	@echo "  make regress-verilator PLUSARGS='<...>'"
	@echo "  make clean"

list-tests:
	@cat $(SIM_DIR)/tests_questa.list

questa:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_questa.sh $(COMMON_PLUSARGS)

vcs:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_vcs.sh $(COMMON_PLUSARGS)

xcelium:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_xcelium.sh $(COMMON_PLUSARGS)

verilator:
	@$(SIM_DIR_ABS)/run_verilator.sh $(COMMON_PLUSARGS)

regress-verilator:
	@$(SIM_DIR_ABS)/regress_verilator.sh $(PLUSARGS)

clean:
	@rm -rf $(SIM_DIR)/out

