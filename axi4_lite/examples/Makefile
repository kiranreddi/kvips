.PHONY: help questa vcs xcelium clean

SIM_DIR := $(abspath loopback/sim)
USE_LSF ?= 0
LSF_BSUB ?= bsub -Ip -app gnrc -q interactive
RUN_PREFIX := $(if $(filter-out 0,$(USE_LSF)),$(LSF_BSUB),)

help:
	@echo "KVIPS AXI4-Lite standalone loopback"
	@echo "  make questa  [USE_LSF=1]"
	@echo "  make vcs     [USE_LSF=1]"
	@echo "  make xcelium [USE_LSF=1]"

questa:
	@$(RUN_PREFIX) $(SIM_DIR)/run_questa.sh

vcs:
	@$(RUN_PREFIX) $(SIM_DIR)/run_vcs.sh

xcelium:
	@$(RUN_PREFIX) $(SIM_DIR)/run_xcelium.sh

clean:
	@rm -rf $(SIM_DIR)/out
