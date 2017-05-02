all: src/termination/build/chainer.cmx src/termination/build/dpgraph.cmx src/termination/build/dpframework.cmx src/termination/build/dpproblem.cmx src/termination/build/subtermcriterion.cmx src/termination/build/terminator.cmx src/termination/build/valuecriterion.cmx ;
include chainer.ml dpgraph.ml dpframework.ml dpproblem.ml subtermcriterion.ml terminator.ml valuecriterion.ml
src/termination/%.cmx: ; @echo $@
%: ;
