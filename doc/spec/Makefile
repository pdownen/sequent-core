OTT_FILES = Syntax.ott Lint.ott OpSem.ott
OTT_TEX   = Ott.tex
OTT_OPTS  = -tex_show_meta false
TARGET    = spec
TARGET_RAW= $(TARGET)-raw

$(TARGET).pdf: $(TARGET).tex $(OTT_TEX)
	latex -output-format=pdf $<
	latex -output-format=pdf $<

$(TARGET_RAW).pdf: $(TARGET_RAW).tex
	latex -output-format=pdf $<
	latex -output-format=pdf $<

$(TARGET).tex: $(TARGET).mng $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)

$(TARGET_RAW).tex: $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $(OTT_FILES)

$(OTT_TEX): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^

.PHONY: clean
clean:
	rm -f $(TARGET).pdf $(TARGET).tex $(OTT_TEX) *.aux *.fdb_latexmk *.log
