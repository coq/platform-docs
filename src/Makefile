# Source: https://github.com/jscoq/coqdoc-template

.PHONY: all clean serve

COQDOC_AUTO=coqdoc.css

# Select all the .v files in the current directory
FILES=$(wildcard *.v)
FILES_HTML=$(addsuffix .html,$(basename $(FILES)))

all: $(FILES_HTML)

%.html: %.v %.glob jscoqdoc
	./jscoqdoc $<

%.glob: %.v
	coqc $<

clean:
	rm -f *.vo *.vok .*.aux *.glob *.vos $(FILES_HTML) $(COQDOC_AUTO)

node_modules: package.json package-lock.json
	npm i

serve: node_modules
	./node_modules/.bin/http-server .
