# Hand-written (not coq_makefile-generated) build for the coq2py Gallina
# sources. Kept deliberately simple: this project's dependency graph is
# small and linear, and a hand-rolled Makefile avoids fighting
# coq_makefile's generated output against the local BSD/GNU make split
# (coqc itself needs GNU make's conditionals; invoke as `gmake` here if
# your default `make` is BSD make).

COQC = coqc -Q . ""

VFILES = Lang.v PyLang.v Translate.v Json.v PyRename.v PyPrint.v RealIR.v RealJson.v RealBridge.v
VOFILES = $(VFILES:.v=.vo)

.PHONY: all extract clean

all: $(VOFILES)

Lang.vo: Lang.v
	$(COQC) Lang.v

PyLang.vo: PyLang.v Lang.vo
	$(COQC) PyLang.v

RealIR.vo: RealIR.v Lang.vo
	$(COQC) RealIR.v

RealJson.vo: RealJson.v RealIR.vo Json.vo
	$(COQC) RealJson.v

Translate.vo: Translate.v Lang.vo PyLang.vo
	$(COQC) Translate.v

Json.vo: Json.v Lang.vo
	$(COQC) Json.v

PyRename.vo: PyRename.v PyLang.vo Json.vo
	$(COQC) PyRename.v

PyPrint.vo: PyPrint.v PyLang.vo Json.vo PyRename.vo
	$(COQC) PyPrint.v

RealBridge.vo: RealBridge.v
	$(COQC) RealBridge.v

extract: all Extract.v
	$(COQC) Extract.v

clean:
	rm -f *.vo *.vos *.vok *.glob
	rm -f coq2py_core.ml coq2py_core.mli
