DIR   := src/smt
PACK  := Smt
DEP   := Util Ctrs Parsec
FILES := \
  externalsolver.ml \
  internalsolver.ml \
  internalthinker.ml \
  manualsolver.ml \
  smtquantifiers.ml \
  smtresults.ml \
  solver.ml

include mk/subdir.mk
