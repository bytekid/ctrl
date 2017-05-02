DIR   := src/inductive
PACK  := Inductive
DEP   := Util Ctrs Smt Rewriting Io Confluence Termination
FILES := \
  completenesschecker.ml \
  proverbase.ml \
  manualprover.ml \
  theoremprover.ml

include mk/subdir.mk
