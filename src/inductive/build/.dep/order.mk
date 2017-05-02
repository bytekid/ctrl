all: src/inductive/build/completenesschecker.cmx src/inductive/build/proverbase.cmx src/inductive/build/manualprover.cmx src/inductive/build/theoremprover.cmx ;
include completenesschecker.ml proverbase.ml manualprover.ml theoremprover.ml
src/inductive/%.cmx: ; @echo $@
%: ;
