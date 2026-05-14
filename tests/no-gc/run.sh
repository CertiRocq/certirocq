#!/usr/bin/env sh

set -eu

TOTAL=0
PASSED=0

for f in no_gc_bool no_gc_list no_gc_closure
do
    TOTAL=$((TOTAL + 1))
    echo "Running ${f}..."
    "./${f}"
    PASSED=$((PASSED + 1))
    echo "PASS ${f}"
done

echo "PASS ${PASSED}/${TOTAL} --no-gc tests"
