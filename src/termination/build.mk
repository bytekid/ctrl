DIR   := src/termination
PACK  := Termination
DEP   := Util Ctrs Smt Rewriting Io
FILES := \
  chainer.ml \
  dpgraph.ml \
  dpframework.ml \
  dpproblem.ml \
  subtermcriterion.ml \
  terminator.ml \
  valuecriterion.ml

include mk/subdir.mk
