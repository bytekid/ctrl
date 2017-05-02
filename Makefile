include mk/toplevel-util.mk

SHELL     := bash
OCAML     := $(call check-opt,ocaml)
OCAMLOPT  := $(call check-opt,ocamlopt) -g
OCAMLC    := $(call check-opt,ocamlc)
OCAMLTOP  := $(call check-opt,ocamlmktop)
OCAMLDEP  := $(call check-opt,ocamldep)
OCAMLYACC := $(call check-opt,ocamlyacc)
OCAMLLEX  := $(call check-opt,ocamllex)
OCAMLDOC  := $(call check-opt,ocamldoc)
PERL      := perl
STATIC    :=

# other programs:
# echo, cp, chmod, rm, mkdir

include mk/bits.mk

# list of packages to consider
TOPLEVEL  := Parsec Ctrs Util Smt Rewriting Io Confluence Termination Inductive Tool

# flags for linking
STDLIBS   := nums str unix
LINK      := $(if $(STATIC),-ccopt -static,) -cc g++ $(STDLIBS:=.cmxa)

# default target. (see src/ttt2/build.mk)
all: ctrl

.SUFFIXES:

include mk/toplevel.mk

# helpers for building file names
make-xcmi = $(BUILD_$(1))/$(call lower,$(1))x.cmi
make-mli = $(SRC_$(1))/$(call lower,$(1)).mli
make-inc = -I $(DIR_$(1))

# make an ocaml toplevel interpreter that includes the Tool packages
top: top.build/top $(DIR)/build.mk
	cp $(LIBS_Tool:.cmxa=.cmi) $(call map,make-xcmi,$(PACKS_Tool)) top.build
	@( echo '#! /bin/bash' ; \
	   echo 'exec $(shell pwd)/top.build/top -I $(shell pwd)/top.build "$$@"' ) > top
	chmod +x top

top.build/top: $$(subst .cmxa,.cma,$$(LIBS_Tool)) $(EXTRA_Tool) | top.build/.dir
	$(OCAMLTOP) $(LINK:.cmxa=.cma) $(subst .cmx,.cmo,$(LINK_Logic:.cmxa=.cma)) -o $@ $(LIBS_Tool:.cmxa=.cma) $(LINK_Tool)

# build documentation
doc: $(LIBS_Tool) README.txt | doc/.dir
	$(OCAMLDOC) -html -d doc -text README.txt $(call map,make-mli,$(PACKS_Tool)) $(call map,make-inc,$(PACKS_Tool))

README.txt: README
	cp $< $@

.INTERMEDIATE: README.txt

# extra housekeeping
distclean::
	rm -rf top top.build doc build $(add_suffix .tar.gz,$(TOOLS))

clean::
	rm -f README.txt

help:
	@cat README

.PHONY: doc help

