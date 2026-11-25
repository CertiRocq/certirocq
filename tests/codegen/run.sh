#!/usr/bin/env sh

set -eu

FILES=$(cat TESTS)
TMPDIR=$(mktemp -d "${TMPDIR:-/tmp}/certirocq-codegen.XXXXXX")
trap 'rm -rf "$TMPDIR"' EXIT HUP INT TERM
TOTAL=0
PASSED=0

for f in $FILES
do
    TOTAL=$((TOTAL + 1))
    expected="./expected_outputs/${f%%_*}.txt"
    actual="${TMPDIR}/${f}.txt"

    if [ ! -x "${f}" ]; then
        echo "FAIL ${f}: executable not found" >&2
        exit 1
    fi

    echo "Running ${f}..."
    "./${f}" > "${actual}"

    if cmp -s "${actual}" "${expected}"; then
        PASSED=$((PASSED + 1))
        echo "PASS ${f}"
    else
        echo "FAIL ${f}: output differed from ${expected}" >&2
        echo "Expected output:" >&2
        cat "${expected}" >&2
        echo "Actual output:" >&2
        cat "${actual}" >&2
        exit 1
    fi
done

echo "PASS ${PASSED}/${TOTAL} codegen tests"
