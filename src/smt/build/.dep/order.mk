all: src/smt/build/externalsolver.cmx src/smt/build/internalsolver.cmx src/smt/build/internalthinker.cmx src/smt/build/manualsolver.cmx src/smt/build/smtquantifiers.cmx src/smt/build/smtresults.cmx src/smt/build/solver.cmx ;
include externalsolver.ml internalsolver.ml internalthinker.ml manualsolver.ml smtquantifiers.ml smtresults.ml solver.ml
src/smt/%.cmx: ; @echo $@
%: ;
