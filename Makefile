COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." FormalMath -native-compiler

SOURCE := $(shell find "." -type f -name '*.v')
VO_FILE := $(shell find "." -type f -name '*.vo')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
VOAUX_FILE := $(shell find "." -type f -name '*.vo.aux')
AUX_FILE := $(shell find "." -type f -name '*.aux')

$(SOURCE:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

.PHONY: dep
.depend dep:
	@echo 'COQDEP ... > .depend'
	@$(COQDEP) $(COQ_FLAG) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)

.PHONY: clean
clean:
	@rm $(VO_FILE) $(GLOB_FILE) $(VOAUX_FILE) $(AUX_FILE) .depend

.DEFAULT_GOAL := all

include .depend
