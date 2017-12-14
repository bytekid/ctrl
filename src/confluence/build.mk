DIR   := src/confluence
PACK  := Confluence
DEP   := Util Io Ctrs Smt Rewriting Termination
FILES := \
  confluencechecker.ml

include mk/subdir.mk

