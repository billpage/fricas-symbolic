# fricas-symbolic: build and test against an installed FriCAS (1.4.0 or later).
#
#   make check        compile each package and run its unit tests
#   make check-gsexpr / make check-symterm   one package only
#   make lint         check the math in the markdown documents
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

.PHONY: check check-gsexpr check-symterm lint clean

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


lint:
	python3 tools/check_md_math.py docs/ references/ README.md ORIENTATION.md \
	  CONTRIBUTING.md GLOSSARY.md AGENTS.md AI-USE.md

clean:
	rm -rf $(BUILD)
