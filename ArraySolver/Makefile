goal : arrsolver
	
arrsolver : solver.ml
	ocamlopt -o arrsolver -ccopt -static unix.cmxa solver.ml

run : arrsolver
	./arrsolver intarray.smt

.PHONY : clean
clean :
	rm solver.cmi solver.cmx solver.o

