#!/bin/bash

.PHONY: idris2 idris2-clean idris2-clobber clean all default clobber git-clean-interactive git-clean-force

default: all

idris2:
	idris2 --build dao.ipkg

idris2-clean:
	idris2 --clean dao.ipkg

idris2-clobber:
	rm -rf build

clean:: idris2-clean

clobber:: idris2-clobber

git-clean-interactive::
	git clean -idx

git-clean-force::
	git clean -fdxf

all:: idris2
