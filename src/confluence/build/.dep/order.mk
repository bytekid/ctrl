all: src/confluence/build/confluencechecker.cmx ;
include confluencechecker.ml
src/confluence/%.cmx: ; @echo $@
%: ;
