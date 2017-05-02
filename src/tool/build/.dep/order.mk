all: src/tool/build/main.cmx ;
include main.ml
src/tool/%.cmx: ; @echo $@
%: ;
