# this file is included from each src/foo/build.mk file, which should define
#  DIR = src/foo
#  PACK = Foo
#  DEP = Packages That It Depends On
#  FILES = files.ml relative/to.ml src.ml directory.ml

# Note that inside commands and during secondary expansion, the values may be
# different. The trick is to remember $(PACK) for use inside a rule, as follows:
#
# foo: PACK := $(PACK)
# foo: ...
#    ... $(DIR_$(PACK)) ... $(DEP_$(PACK)) ... etc.

# define some useful variables
PACKL  := $(call lower,$(PACK))
SRC    := $(DIR)/src
BUILD  := $(DIR)/build
DEPDIR := $(BUILD)/.dep

LIB_$(PACK)   := $(DIR)/$(PACKL).cmxa
LIBO_$(PACK)  := $(DIR)/$(PACKL).cma
DIR_$(PACK)   := $(DIR)
SRC_$(PACK)   := $(SRC)
DEP_$(PACK)   := $(DEP)
BUILD_$(PACK) := $(BUILD)
FILES_$(PACK) := $(FILES)
PACKL_$(PACK) := $(PACKL)
SRCDIRS_$(PACK) := $(addprefix -I $(DIR)/,$(shell $(PERL) -e ' \
  $$a{$$_} = 1 for qw(build/ $(dir $(FILES:%=build/%))); \
  @a=keys(%a); \
  print "@a"; \
')) $(addprefix -I src/,$(call map,lower,$(DEP)))

# take care of dependencies
# skip dependency generation if we're only cleaning
ifeq "$(filter clean clean-% distclean distclean-% dist_clean dist_clean_% dist-clean dist-clean-% help,$(MAKECMDGOALS))" ""
include mk/subdir-depend.mk
endif

# compile (generated) source file to native (byte) code - 4 rules
$(BUILD)/%.cmx: PACK := $(PACK)
$(BUILD)/%.cmx: $(SRC)/%.ml | $$(dir $$@).dir
	$(OCAMLOPT) -c -for-pack $(PACK)x $(SRCDIRS_$(PACK)) -o $@ $<

$(BUILD)/%.cmx: PACK := $(PACK)
$(BUILD)/%.cmx: $(BUILD)/%.ml
	$(OCAMLOPT) -c -for-pack $(PACK)x $(SRCDIRS_$(PACK)) -o $@ $<

$(BUILD)/%.cmo: PACK := $(PACK)
$(BUILD)/%.cmo: $(SRC)/%.ml | $$(dir $$@).dir
	$(OCAMLC) -c $(SRCDIRS_$(PACK)) -o $@ $<

$(BUILD)/%.cmo: PACK := $(PACK)
$(BUILD)/%.cmo: $(BUILD)/%.ml
	$(OCAMLC) -c $(SRCDIRS_$(PACK)) -o $@ $<

# generate pack (foox.cmx/o)
$(BUILD)/$(PACKL)x.cmx: PACK := $(PACK)
$(BUILD)/$(PACKL)x.cmx: $(OBJS_$(PACK))
	$(OCAMLOPT) $(SRCDIRS_$(PACK)) -pack -o $@ $^

$(BUILD)/$(PACKL)x.cmo: PACK := $(PACK)
$(BUILD)/$(PACKL)x.cmo: $(OBJS_$(PACK):.cmx=.cmo)
	$(OCAMLC) $(SRCDIRS_$(PACK)) -pack -o $@ $^

# compile native (byte) interface module (foo.cmx/cmo)
# note that these rules take care of compiling the .mli file as well
$(BUILD)/$(PACKL).cmx: PACK := $(PACK)
$(BUILD)/$(PACKL).cmx: $(SRC)/$(PACKL).ml $(SRC)/$(PACKL).mli $(BUILD)/$(PACKL)x.cmx
	$(OCAMLOPT) $(SRCDIRS_$(PACK)) -c -o $(@:.cmx=.cmi) $(<:.ml=.mli)
	$(OCAMLOPT) $(SRCDIRS_$(PACK)) -c -o $@ $<

$(BUILD)/$(PACKL).cmo: PACK := $(PACK)
$(BUILD)/$(PACKL).cmo: $(SRC)/$(PACKL).ml $(SRC)/$(PACKL).mli $(BUILD)/$(PACKL)x.cmo
	$(OCAMLC) $(SRCDIRS_$(PACK)) -c -o $(@:.cmx=.cmi) $(<:.ml=.mli)
	$(OCAMLC) $(SRCDIRS_$(PACK)) -c -o $@ $<

# generate native (byte) pack for linking (foo.cmxa/cma)
$(DIR)/$(PACKL).cmxa: PACK := $(PACK)
$(DIR)/$(PACKL).cmxa: $(BUILD)/$(PACKL)x.cmx $(BUILD)/$(PACKL).cmx
	$(OCAMLOPT) -a -o $@ $^
	cp $(BUILD_$(PACK))/$(PACKL_$(PACK)).cmi $(DIR_$(PACK))

$(DIR)/$(PACKL).cma: PACK := $(PACK)
$(DIR)/$(PACKL).cma: $(BUILD)/$(PACKL)x.cmo $(BUILD)/$(PACKL).cmo
	$(OCAMLC) -a -o $@ $^
	cp $(BUILD_$(PACK))/$(PACKL_$(PACK)).cmi $(DIR_$(PACK))

# aliases
native-$(PACK): $(LIB_$(PACK))
native-$(PACKL): $(LIB_$(PACK))
bytecode-$(PACK): $(LIBO_$(PACK))
bytecode-$(PACKL): $(LIBO_$(PACK))
distclean-$(PACK):: PACK := $(PACK)
distclean-$(PACK):: clean-$(PACK)
distclean-$(PACKL): distclean-$(PACK)

# housekeeping
clean-$(PACK):: PACK := $(PACK)
clean-$(PACK)::
	rm -rf $(BUILD_$(PACK)) $(addprefix $(LIB_$(PACK):.cmxa=),.cmxa .cma .cmi .a)
clean-$(PACKL): clean-$(PACK)

clean:: clean-$(PACK)
depend:: depend-$(PACK)
distclean:: distclean-$(PACK)
native:: native-$(PACK)
bytecode:: bytecode-$(PACK)
