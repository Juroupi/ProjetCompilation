.PRECIOUS: %.imp

mars: tests/$(TEST).asm
	java -jar Mars4_5.jar tests/$(TEST).asm pa $(PARAM)

%.asm: %.imp ImpOpt/impc.byte
	./ImpOpt/impc.byte $<

%.imp: %.fun Fun/func.byte
	./Fun/func.byte $<

clean:
	rm -f tests/*.imp tests/*.mimp tests/*.aimp tests/*.eimp tests/*.asm