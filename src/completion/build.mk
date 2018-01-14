DIR   := src/completion
PACK  := Completion
DEP   := Util Ctrs Smt Rewriting Io Confluence Termination
FILES := \
  kB.ml \
  ordered.ml

include mk/subdir.mk
