# fricas-symbolic: build and test against an installed FriCAS (1.4.0 or later).
#
#   make check        compile each package and run its unit tests
#   make check-gsexpr / make check-symterm   one package only
#   make tutorial     run docs/tutorial/tutorial.input; the log is build/tutorial/run.log
#   make tutorial-md  regenerate docs/tutorial/tutorial.md from its template and transcripts
#   make tutorial-md-check   fail if tutorial.md is out of date (needs no FriCAS)
#   make lint         check the math in the markdown documents, and tutorial-md-check
#   make clean
#
# FRICAS names the FriCAS command (default: fricas on the PATH). Each check
# runs in its own directory under build/, compiles the .spad file there, reads
# the test file in the same session (so no )lib is needed) and then judges the
# run by the statistics() summary: every "File summary" must report
# "unexpected failures: 0" and "unexpected passes: 0".

FRICAS ?= fricas
BUILD  := build
TOP    := $(CURDIR)

.PHONY: check check-gsexpr check-symterm tutorial tutorial-md tutorial-md-check lint clean

check: check-gsexpr check-symterm

# $(1) = name, $(2) = spad files (compiled in order), $(3) = test file
define fricas_check
	rm -rf $(BUILD)/$(1) && mkdir -p $(BUILD)/$(1)
	( for f in $(2); do printf ')compile %s\n' $(TOP)/$$f; done; \
	  printf ')read %s\n)quit\n' $(TOP)/$(3) ) > $(BUILD)/$(1)/run.input
	cd $(BUILD)/$(1) && $(FRICAS) -nosman < run.input > run.log 2>&1 || true
	python3 tools/check_summary.py $(BUILD)/$(1)/run.log
endef

check-gsexpr:
	$(call fricas_check,gsexpr,src/algebra/gsexpr.spad,src/input/gsexpr.input)

check-symterm:
	$(call fricas_check,symterm,src/algebra/gsexpr.spad src/algebra/symterm.spad,src/input/symterm.input)


# The tutorial is a walk-through, not a test: it is judged by reading the log.
# Five library errors are intended (docs/tutorial/tutorial.md, use cases 7 and 9).
tutorial:
	rm -rf $(BUILD)/tutorial && mkdir -p $(BUILD)/tutorial
	( printf ')compile %s\n' $(TOP)/src/algebra/gsexpr.spad; \
	  printf ')compile %s\n' $(TOP)/src/algebra/symterm.spad; \
	  printf ')read %s\n)quit\n' $(TOP)/docs/tutorial/tutorial.input ) > $(BUILD)/tutorial/run.input
	cd $(BUILD)/tutorial && $(FRICAS) -nosman < run.input > run.log 2>&1 || true
	@echo "log: $(BUILD)/tutorial/run.log"
	@echo "library errors in the log (5 are intended): $$(grep -c 'Error detected within library code' $(BUILD)/tutorial/run.log)"

tutorial-md:
	python3 tools/tutorial/build_tutorial.py

tutorial-md-check:
	python3 tools/tutorial/build_tutorial.py --check

lint: tutorial-md-check
	python3 tools/check_md_math.py docs/ references/ README.md ORIENTATION.md \
	  CONTRIBUTING.md GLOSSARY.md AGENTS.md AI-USE.md

clean:
	rm -rf $(BUILD)
