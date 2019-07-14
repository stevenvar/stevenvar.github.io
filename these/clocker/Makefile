
Checker.vo : Checker.v
	coqc $<

Check.vo : Check.v Checker.vo
	coqc $<

coq : Checker.vo

ml : Check.vo

clean:
	$(RM) -r *.vo *.html *.glob *.mli *.ml *.cmi *.cmo *.css
