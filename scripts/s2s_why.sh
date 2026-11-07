#!/bin/bash
# print the unported original names named by type-mismatch errors in the last build log, and their defining file
L=${S4LOG:-/tmp/s4build.log}
grep -A1 "in the application" $L | grep -v "^--\|in the application" | sed 's/^ *@\?//;s/ .*//' | sort -u | while read n; do
  b=${n##*.}; echo "$n -> $(grep -lE "^(theorem|def|lemma|abbrev) $b\b" Tools/*.lean | grep -v S2sAdm | tr '\n' ' ')"; done
