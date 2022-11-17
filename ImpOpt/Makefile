TEST = test

impc:
	ocamlbuild impc.byte

%.asm: %.imp
	./impc.byte $<

mars: tests/$(TEST).asm
	java -jar ../Mars4_5.jar tests/$(TEST).asm pa $(PARAM)

clean:
	rm -f tests/*.mimp tests/*.aimp tests/*.eimp tests/*.asm