%.asm: %.imp std.imp impc.byte
	./impc.byte $<

mars: tests/$(TEST).asm
	java -jar ../Mars4_5.jar tests/$(TEST).asm pa $(PARAM)

clean:
	rm -f tests/*.mimp tests/*.aimp tests/*.eimp tests/*.asm

impc.byte: aimp.ml aimp2eimp.ml eimp.ml eimp2mips.ml graph.ml \
           imp.ml imp2mimp.ml impc.ml implexer.mll impparser.mly \
		   mimp.ml mimp2aimp.ml mips.ml ops.ml register_allocation.ml
	ocamlbuild impc.byte