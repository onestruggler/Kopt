# Makefile for converting SVG figures to PDF for LaTeX inclusion
# Usage:
#   make          - convert all SVGs to PDFs
#   make clean    - remove generated PDFs
#   make watch    - continuously watch for changes (requires inotifywait)

INKSCAPE := inkscape
SVG_DIR  := .
SVG_FILES := $(wildcard $(SVG_DIR)/*.svg)
PDF_FILES := $(SVG_FILES:.svg=.pdf)

.PHONY: all clean watch

all: $(PDF_FILES)

%.pdf: %.svg
	$(INKSCAPE) -D $< -o $@

clean:
	rm -f $(PDF_FILES)

watch:
	@echo "Watching for SVG changes..."
	@while inotifywait -e modify -e create $(SVG_DIR)/*.svg 2>/dev/null; do \
		$(MAKE) all; \
	done
