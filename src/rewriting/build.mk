DIR   := src/rewriting
PACK  := Rewriting
DEP   := Util Ctrs Smt
FILES := \
  constrainedrewriter.ml \
  rewriter.ml

include mk/subdir.mk
