COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." FormalMath -native-compiler yes -bytecode-compiler yes

SOURCE := $(shell find "." -type f -name '*.v')
VO_FILE := $(shell find "." -type f -name '*.vo')
VOS_FILE := $(shell find "." -type f -name '*.vos')
VOK_FILE := $(shell find "." -type f -name '*.vok')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
VOAUX_FILE := $(shell find "." -type f -name '*.vo.aux')
AUX_FILE := $(shell find "." -type f -name '*.aux')
NATIVE_DIR := $(shell find "." -type d -name '.coq-native')

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
	@rm $(VO_FILE) $(VOS_FILE) $(VOK_FILE) $(GLOB_FILE) $(VOAUX_FILE) $(AUX_FILE)
	@rm .depend
	@rm -fr $(NATIVE_DIR)

.DEFAULT_GOAL := all

include .depend
