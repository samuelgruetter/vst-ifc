
default_target: examples

# the file ./CONFIGURE should contain a line of the form
# VSTDIR=path/to/the/VST/directory
-include CONFIGURE

REQUIRED_VST_VERSION := $(shell cat VST_VERSION)
ACTUAL_VST_VERSION := $(shell cd $(VSTDIR) && git rev-parse HEAD)

ifneq ($(REQUIRED_VST_VERSION), $(ACTUAL_VST_VERSION))
  $(error VST commit hash does not match: expected $(REQUIRED_VST_VERSION) but got $(ACTUAL_VST_VERSION))
endif

COMPCERT ?= $(VSTDIR)/compcert

EXTFLAGS = -R $(COMPCERT) compcert

VSTSUBDIRS=msl sepcomp veric floyd

DIRS = lib ifc examples

COQFLAGS=$(foreach d, $(VSTSUBDIRS), -Q $(VSTDIR)/$(d) $(d)) $(foreach d, $(DIRS), -Q $(d) $(d)) $(EXTFLAGS)
DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v 

.loadpath: Makefile
	echo $(COQFLAGS) > .loadpath

.depend depend:
	$(COQDEP) >.depend `find $(DIRS) -name "*.v"`

examples: $(patsubst %.v,%.vo,$(wildcard examples/*.v))

clean:
	rm -f .loadpath .depend; find $(DIRS) -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete

include .depend

