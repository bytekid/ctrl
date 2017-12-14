DIR   := src/confluence
PACK  := Confluence
DEP   := Util Ctrs Smt Rewriting Termination
FILES := \
  confluencechecker.ml

include mk/subdir.mk

