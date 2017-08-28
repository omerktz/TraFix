#!/bin/bash
set -x
rm *.tags
rm *.out
rm model*
rm vocabs*
rm *.diff
rm *.words
for f in $( ls *.corpus.c ); do cp $f ${f:0:-9}.words; done