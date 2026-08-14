ROCQ ?= rocq
ROCQ_PROJECT := _RocqProject
ROCQ_MAKEFILE := Makefile.rocq
ROCQ_SOURCES := $(shell find rocq -type f -name '*.v' | LC_ALL=C sort)
ROCQ_MODULES := $(shell find rocq -type f -name '*.v' | LC_ALL=C sort | \
	sed -e 's|^rocq/||' -e 's|\.v$$||' -e 's|/|.|g' -e 's|^|PathDependent.|')

.PHONY: all lean rocq rocq-audit rocq-clean clean

all: lean rocq

lean:
	lake build

rocq: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE) all

$(ROCQ_MAKEFILE): $(ROCQ_PROJECT) $(ROCQ_SOURCES)
	$(ROCQ) makefile -f $(ROCQ_PROJECT) $(ROCQ_SOURCES) -o $(ROCQ_MAKEFILE)

rocq-audit: rocq
	@if rg -n '\b(Axiom|Conjecture|Admitted|admit|Abort|Parameter|FunctionalExtensionality|PropExtensionality|ProofIrrelevance|JMeq_eq|ClassicalChoice)\b' rocq -g '*.v'; then \
		echo 'Forbidden unchecked assumption or extensionality import found.' >&2; \
		exit 1; \
	fi
	$(ROCQ) check -silent -Q rocq PathDependent $(ROCQ_MODULES)
	@if test -f rocq/Assumptions.v; then \
		assumption_log=$$(mktemp); \
		trap 'rm -f "$$assumption_log"' EXIT; \
		$(ROCQ) repl -batch -q -Q rocq PathDependent \
			-l rocq/Assumptions.v 2>&1 | tee "$$assumption_log"; \
		if rg -n '^Axioms:' "$$assumption_log"; then \
			echo 'A published theorem depends on an axiom.' >&2; \
			exit 1; \
		fi; \
	fi

rocq-clean:
	@if test -f $(ROCQ_MAKEFILE); then $(MAKE) -f $(ROCQ_MAKEFILE) clean; fi
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf

clean: rocq-clean
	lake clean
