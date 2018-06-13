ARCHIVE Formal verification of low-level programs using Separation Logic
========================================================================

## Contents

The purpose of this repository is to serve as an archive for the code
corresponding to the following papers:
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#affeldt2014jfr (SEPLOGC)
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#affeldt2013isse (BEGCD)
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#affeldt2012scp (BBS)
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#marti2008compsoft (SEPLOG)
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#affeldt2006asian (cryptoasm)
- https://staff.aist.go.jp/reynald.affeldt/bib/bib_en.html#marti2006icfem (SEPLOG)

## Requirements

Coq version 8.8.0, mathcomp version 1.7.0

## Install

coq_makefile -o Makefile -f _CoqProject

#### Install X only, where X \in {SEPLOG,BBS,BEGCD,SEPLOGC}

coq_makefile -o Makefile -f XMake; make

#### Doc

make -f MakeDoc
(once everything has been compiled)
