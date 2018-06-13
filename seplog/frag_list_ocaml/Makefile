include ../../vars.mk

#CC=ocamlopt
PROG=bigtoe

main: parser
	$(CC) -o $(PROG) extracted.cmx convert.cmx pprinter.cmx lexer.cmx grammar.cmx main.cmx

parser: extracted.ml pprinter.ml convert.ml grammar.mly lexer.mll  
	$(CC) -c extracted.ml
	$(CC) -c convert.ml
	$(CC) -c pprinter.ml
	ocamlyacc grammar.mly
	ocamllex lexer.mll
	$(CC) -c grammar.mli
	$(CC) -c lexer.ml
	$(CC) -c grammar.ml
	$(CC) -c main.ml 

extracted.ml:
	cat README > extracted.ml
	$(COQ) -opt $(FLAG) -I ../ -batch -l extraction >> extracted.ml

clean:
	rm -f *.cmo *.cmi *.cmx *.o lexer.ml grammar.ml grammar.mli $(PROG)
