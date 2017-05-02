all: src/io/build/cleaner.cmx src/io/build/reader.cmx src/io/build/printer.cmx ;
include cleaner.ml reader.ml printer.ml
src/io/%.cmx: ; @echo $@
%: ;
