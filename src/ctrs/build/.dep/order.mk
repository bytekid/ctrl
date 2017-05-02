all: src/ctrs/build/alphabet.cmx src/ctrs/build/context.cmx src/ctrs/build/csmapping.cmx src/ctrs/build/elogic.cmx src/ctrs/build/environment.cmx src/ctrs/build/function.cmx src/ctrs/build/position.cmx src/ctrs/build/prelude.cmx src/ctrs/build/rule.cmx src/ctrs/build/sort.cmx src/ctrs/build/sortdeclaration.cmx src/ctrs/build/specialdeclaration.cmx src/ctrs/build/substitution.cmx src/ctrs/build/term.cmx src/ctrs/build/trs.cmx src/ctrs/build/typechecker.cmx src/ctrs/build/variable.cmx ;
include alphabet.ml context.ml csmapping.ml elogic.ml environment.ml function.ml position.ml prelude.ml rule.ml sort.ml sortdeclaration.ml specialdeclaration.ml substitution.ml term.ml trs.ml typechecker.ml variable.ml
src/ctrs/%.cmx: ; @echo $@
%: ;
