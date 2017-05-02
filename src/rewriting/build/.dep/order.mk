all: src/rewriting/build/constrainedrewriter.cmx src/rewriting/build/rewriter.cmx ;
include constrainedrewriter.ml rewriter.ml
src/rewriting/%.cmx: ; @echo $@
%: ;
