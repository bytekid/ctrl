DIR   := src/ctrs
PACK  := Ctrs
DEP   := Util Parsec
FILES := \
  alphabet.ml \
  context.ml \
  csmapping.ml \
  elogic.ml \
  environment.ml \
  function.ml \
  position.ml \
  prelude.ml \
  rule.ml \
  sort.ml \
  sortdeclaration.ml \
  specialdeclaration.ml \
  substitution.ml \
  term.ml \
  trs.ml \
  typechecker.ml \
  variable.ml

include mk/subdir.mk
