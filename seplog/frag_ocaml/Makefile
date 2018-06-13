CC=ocamlc
PROG=bigtoe

main: main.ml parser
	$(CC) -o $(PROG) extracted.cmo pprinter.cmo convert.cmo lexer.cmo grammar.cmo main.ml

parser: extracted.ml pprinter.ml convert.ml grammar.mly lexer.mll  
	$(CC) -c extracted.ml
	$(CC) -c pprinter.ml
	$(CC) -c convert.ml
	ocamlyacc grammar.mly
	ocamllex lexer.mll
	$(CC) -c grammar.mli
	$(CC) -c lexer.ml
	$(CC) -c grammar.ml

extracted.ml:
	cat README > extracted.ml
	coqc -opt -I ../  extraction.v >> extracted.ml
	rm extraction.vo

clean:
	rm -f *.cmo *.cmi *.cmx *.o lexer.ml grammar.ml grammar.mli $(PROG)
