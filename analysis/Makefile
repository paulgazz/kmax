PAPERDIR = ~/tuningpost/research/conferences/icse

ELEMENTS = \
	table_cfiles_data.tex \
	table_units.tex \
	table_comparison.tex \
	table_buildsystem.tex

.PHONY: all FORCE

all: $(patsubst %, $(PAPERDIR)/%, $(ELEMENTS))

$(PAPERDIR)/table_units.tex: table_comparison.py FORCE
	python $(PYARGS) $< units > $@

$(PAPERDIR)/%.tex $(PAPERDIR)/%.pdf: %.py FORCE
	python $(PYARGS) $< > $@
