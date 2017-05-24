.SECONDEXPANSION:
.SUFFIXES:

include mk/bits.mk

lower = $(shell $(PERL) -e 'print lcfirst("$(1)")')
map = $(foreach x,$(2),$(call $(1),$(x)))
TOPLEVELL := $(call map,lower,$(TOPLEVEL))

-include $(addprefix src/,$(addsuffix /build.mk,$(TOPLEVELL)))

%/.dir:
	mkdir -p $(dir $@)
	@touch $@

.PRECIOUS: %/.dir

distclean:: clean

dist_clean: distclean
dist_clean_%: distclean-%
dist-clean: distclean
dist-clean-%: distclean-%

.PHONY: clean clean-% distclean dist_clean dist_clean_% dist-clean dist-clean-%
.PHONY: depend native native-% bytecode bytecode-%
