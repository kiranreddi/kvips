.PHONY: help lint test-smoke test-verilator docs-build clean-all

help:
	@echo "KVIPS top-level targets"
	@echo "  make lint            Run portable Verilator lint (AXI4/APB/AHB)"
	@echo "  make test-smoke      Run one Verilator smoke test per protocol"
	@echo "  make test-verilator  Run all back2back Verilator regressions"
	@echo "  make docs-build      bundle install && jekyll build"
	@echo "  make clean-all       Remove sim outputs and downloaded UVM trees"
	@echo ""
	@echo "Published docs live under pages/docs/ (see docs/README.md)."

lint:
	@chmod +x scripts/lint-verilator.sh
	@./scripts/lint-verilator.sh

test-smoke:
	@$(MAKE) -C axi4/examples verilator TEST=axi4_b2b_test
	@$(MAKE) -C apb/examples verilator TEST=apb_b2b_smoke_test
	@$(MAKE) -C ahb/examples verilator TEST=ahb_smoke_test

test-verilator:
	@$(MAKE) -C axi4/examples regress-verilator
	@$(MAKE) -C apb/examples regress-verilator
	@$(MAKE) -C ahb/examples regress-verilator

docs-build:
	bundle install
	bundle exec jekyll build

clean-all:
	@find . -path '*/sim/out' -type d -prune -exec rm -rf {} + 2>/dev/null || true
	@rm -rf third_party/uvm_verilator _site .jekyll-cache .jekyll-metadata
