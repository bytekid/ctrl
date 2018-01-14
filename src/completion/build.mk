DIR   := src/completion
PACK  := Completion
DEP   := Util Ctrs Smt Rewriting Io Confluence Termination
FILES := \
  kB.ml

include mk/subdir.mk
