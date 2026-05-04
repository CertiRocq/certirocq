#!/usr/bin/env sh

set -eu

FILES=$(cat TESTS)
TMPDIR=$(mktemp -d "${TMPDIR:-/tmp}/certirocq-closures.XXXXXX")
trap 'rm -rf "$TMPDIR"' EXIT HUP INT TERM
PREVIEW_BYTES=2000
TOTAL=0
PASSED=0

for f in $FILES
do
    TOTAL=$((TOTAL + 1))
    if [ -x "${f}" ]; then
        echo "Running ${f}..."
        "./${f}" > "${TMPDIR}/${f}.txt"
        if cmp -s "${TMPDIR}/${f}.txt" "./expected_outputs/${f}.txt"; then
            PASSED=$((PASSED + 1))
            echo "PASS ${f}"
        else
            echo "FAIL ${f}: output differed from ./expected_outputs/${f}.txt" >&2
            EXPECTED_BYTES=$(wc -c < "./expected_outputs/${f}.txt" | tr -d ' ')
            ACTUAL_BYTES=$(wc -c < "${TMPDIR}/${f}.txt" | tr -d ' ')
            EXPECTED_PREVIEW_BYTES=${EXPECTED_BYTES}
            ACTUAL_PREVIEW_BYTES=${ACTUAL_BYTES}
            if [ "${EXPECTED_PREVIEW_BYTES}" -gt "${PREVIEW_BYTES}" ]; then
                EXPECTED_PREVIEW_BYTES=${PREVIEW_BYTES}
            fi
            if [ "${ACTUAL_PREVIEW_BYTES}" -gt "${PREVIEW_BYTES}" ]; then
                ACTUAL_PREVIEW_BYTES=${PREVIEW_BYTES}
            fi
            if [ "${EXPECTED_BYTES}" -gt "${PREVIEW_BYTES}" ]; then
                echo "Expected output (${EXPECTED_PREVIEW_BYTES}/${EXPECTED_BYTES} bytes, truncated):" >&2
            else
                echo "Expected output (${EXPECTED_PREVIEW_BYTES}/${EXPECTED_BYTES} bytes):" >&2
            fi
            head -c "${EXPECTED_PREVIEW_BYTES}" "./expected_outputs/${f}.txt" >&2
            printf '\n' >&2
            if [ "${ACTUAL_BYTES}" -gt "${PREVIEW_BYTES}" ]; then
                echo "Actual output (${ACTUAL_PREVIEW_BYTES}/${ACTUAL_BYTES} bytes, truncated):" >&2
            else
                echo "Actual output (${ACTUAL_PREVIEW_BYTES}/${ACTUAL_BYTES} bytes):" >&2
            fi
            head -c "${ACTUAL_PREVIEW_BYTES}" "${TMPDIR}/${f}.txt" >&2
            printf '\n' >&2
            exit 1
        fi
    else
        echo "FAIL ${f}: executable not found" >&2
        exit 1
    fi
done

echo "PASS ${PASSED}/${TOTAL} closure tests"
