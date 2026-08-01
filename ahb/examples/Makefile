.PHONY: help list-tests list-dut-tests questa vcs xcelium regress-questa regress-vcs regress-xcelium verilator regress-verilator verilator-dut regress-verilator-dut rtl-questa rtl-vcs rtl-xcelium regress-rtl-questa regress-rtl-vcs regress-rtl-xcelium clean

SIM_DIR := uvm_back2back/sim
SIM_DIR_ABS := $(abspath $(SIM_DIR))
RTL_SIM_DIR := uvm_dut/sim
RTL_SIM_DIR_ABS := $(abspath $(RTL_SIM_DIR))

TEST ?= ahb_smoke_test
RTL_TEST ?= $(if $(filter ahb_smoke_test,$(TEST)),ahb_dut_smoke_test,$(TEST))
SEED ?= 1
UVM_VERBOSITY ?= UVM_LOW
PLUSARGS ?=

USE_LSF ?= 0
# LSF Settings (Optional)
LSF_BSUB ?= bsub -Ip -app gnrc -q interactive

ifneq ($(USE_LSF),0)
RUN_PREFIX := $(LSF_BSUB)
else
RUN_PREFIX :=
endif

COMMON_PLUSARGS := +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY) +ntb_random_seed=$(SEED) $(PLUSARGS)
RTL_COMMON_PLUSARGS := +UVM_TESTNAME=$(RTL_TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY) +ntb_random_seed=$(SEED) $(PLUSARGS)

help:
	@echo "KVIPS AHB examples (UVM back2back and RTL-DUT)"
	@echo ""
	@echo "Targets:"
	@echo "  make list-tests"
	@echo "  make list-dut-tests"
	@echo "  make questa         TEST=<name> SEED=<n> UVM_VERBOSITY=<lvl> PLUSARGS='<...>' [USE_LSF=1]"
	@echo "  make vcs            TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make xcelium        TEST=<name> SEED=<n> ... [USE_LSF=1]"
	@echo "  make regress-questa [USE_LSF=1]"
	@echo "  make regress-vcs [USE_LSF=1]"
	@echo "  make regress-xcelium [USE_LSF=1]"
	@echo "  make verilator      TEST=<name> SEED=<n> ..."
	@echo "  make regress-verilator PLUSARGS='<...>'"
	@echo "  make verilator-dut RTL_TEST=<name> SEED=<n> ..."
	@echo "  make regress-verilator-dut PLUSARGS='<...>'"
	@echo "  make rtl-questa RTL_TEST=<name> ... [USE_LSF=1]"
	@echo "  make rtl-vcs RTL_TEST=<name> ... [USE_LSF=1]"
	@echo "  make rtl-xcelium RTL_TEST=<name> ... [USE_LSF=1]"
	@echo "  make regress-rtl-questa [USE_LSF=1]"
	@echo "  make regress-rtl-vcs [USE_LSF=1]"
	@echo "  make regress-rtl-xcelium [USE_LSF=1]"
	@echo "  make clean"

list-tests:
	@cat $(SIM_DIR)/tests_questa.list

list-dut-tests:
	@cat $(RTL_SIM_DIR)/tests_questa.list

questa:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_questa.sh $(COMMON_PLUSARGS)

vcs:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_vcs.sh $(COMMON_PLUSARGS)

xcelium:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/run_xcelium.sh $(COMMON_PLUSARGS)

regress-questa:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_questa.sh $(PLUSARGS)

regress-vcs:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_vcs.sh $(PLUSARGS)

regress-xcelium:
	@$(RUN_PREFIX) $(SIM_DIR_ABS)/regress_xcelium.sh $(PLUSARGS)

verilator:
	@$(SIM_DIR_ABS)/run_verilator.sh $(COMMON_PLUSARGS)

regress-verilator:
	@$(SIM_DIR_ABS)/regress_verilator.sh $(PLUSARGS)

verilator-dut:
	@$(RTL_SIM_DIR_ABS)/run_verilator.sh $(RTL_COMMON_PLUSARGS)

regress-verilator-dut:
	@$(RTL_SIM_DIR_ABS)/regress_verilator.sh $(PLUSARGS)

rtl-questa:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/run_questa.sh $(RTL_COMMON_PLUSARGS)

rtl-vcs:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/run_vcs.sh $(RTL_COMMON_PLUSARGS)

rtl-xcelium:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/run_xcelium.sh $(RTL_COMMON_PLUSARGS)

regress-rtl-questa:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/regress_commercial.sh questa $(PLUSARGS)

regress-rtl-vcs:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/regress_commercial.sh vcs $(PLUSARGS)

regress-rtl-xcelium:
	@$(RUN_PREFIX) $(RTL_SIM_DIR_ABS)/regress_commercial.sh xcelium $(PLUSARGS)

clean:
	@rm -rf $(SIM_DIR)/out $(RTL_SIM_DIR)/out
