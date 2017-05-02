DIR   := src/io
PACK  := Io
DEP   := Util Parsec Ctrs Smt Rewriting
FILES := \
  cleaner.ml \
  reader.ml \
  printer.ml

include mk/subdir.mk

