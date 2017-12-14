DIR   := src/tool
PACK  := Tool
DEP   := Util Parsec Ctrs Smt Rewriting Io Termination Confluence Inductive
GENERATED :=
FILES := \
  main.ml
  $(GENERATED)
# packs to include in executable, in dependency order
PACKS_$(PACK) := Util Parsec Ctrs Smt Rewriting Io Termination Confluence Inductive Tool
EXECUTABLE_$(PACK) := ctrl

# For normal use it should not be necessary to touch anything below.

include mk/subdir.mk

# take care of generated files
$(BUILD)/%.ml: $(SRC)/%.mly | $$(dir $$@).dir
	$(OCAMLYACC) -b $(@:.ml=) $<
	rm $(@:.ml=.mli)

$(BUILD)/%.ml: $(SRC)/%.mll | $$(dir $$@).dir
	$(OCAMLLEX) -o $@ $<

.PRECIOUS: $(GENERATED:%=$(BUILD)/%)


LIBS_$(PACK) = $(foreach x,$(PACKS_$(PACK)),$(LIB_$(x)))
LIBSO_$(PACK) = $(foreach x,$(PACKS_$(PACK)),$(LIBO_$(x)))

# using secondary expansion (the $$) is important: some LIB_Foo variables may
# not be defined yet the first time we get here
$(EXECUTABLE_$(PACK)):: PACK := $(PACK)
$(EXECUTABLE_$(PACK)):: $(DIR)/main.cmx $$(LIBS_$(PACK))
	$(OCAMLOPT) $(LINK) -o $@ $(LIBS_$(PACK)) $<

$(EXECUTABLE_$(PACK)).bytecode:: PACK := $(PACK)
$(EXECUTABLE_$(PACK)).bytecode:: $(DIR)/main.cmo $$(LIBSO_$(PACK))
	$(OCAMLC) $(LINK:.cmxa=.cma) -o $@ $(LIBSO_$(PACK)) $<

$(DIR)/main.cmx:: PACK := $(PACK)
$(DIR)/main.cmx:: $(DIR)/main.ml $(LIB_$(PACK))
	$(OCAMLOPT) -c -I $(DIR_$(PACK)) -o $@ $<

$(DIR)/main.cmo:: PACK := $(PACK)
$(DIR)/main.cmo:: $(DIR)/main.ml $(LIBO_$(PACK))
	$(OCAMLC) -c -I $(DIR_$(PACK)) -o $@ $<

# extra housekeeping
clean-$(PACK)::
	rm -f $(foreach x,$(addprefix $(DIR_$(PACK))/,main),$(addprefix $x,.cmx .cmo .cmi .o))

distclean-$(PACK)::
	rm -rf $(EXECUTABLE_$(PACK)) $(EXECUTABLE_$(PACK)).bytecode
