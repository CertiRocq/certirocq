#!/usr/bin/env sh

set -eu

FILES=$(cat TESTS)
CPS_FILES=$(cat CPS_TESTS)
TMPDIR=$(mktemp -d "${TMPDIR:-/tmp}/certirocq-programs.XXXXXX")
trap 'rm -rf "$TMPDIR"' EXIT HUP INT TERM
PREVIEW_BYTES=2000
TOTAL=0
PASSED=0

# The C compiler (clang, or else gcc, unless CCOMPILER is set: not CC, which build
# environments set to their default compiler) and the directory of the C
# runtime, which the dune rule sets
CCOMPILER=${CCOMPILER:-$(command -v clang || command -v gcc)}
RUNTIME=${RUNTIME:?RUNTIME must be the directory of the C runtime}

run_variant() {
    f=$1
    variant=$2
    exe="${f}_${variant}"
    expected="./expected_outputs/${f}.txt"
    actual="${TMPDIR}/${exe}.txt"

    TOTAL=$((TOTAL + 1))

    echo "Compiling ${exe}..."
    if ! ${CCOMPILER} -o "${exe}" -w -Wno-everything -O2 -fomit-frame-pointer -I"${RUNTIME}" \
         "${f}_main.c" "glue_${f}.c" "${RUNTIME}/gc_stack.c" "CertiRocq.Tests.tests.${exe}.c"; then
        echo "FAIL ${exe}: compilation failed" >&2
        exit 1
    fi

    echo "Running ${exe}..."
    "./${exe}" 1 > "${actual}"

    if cmp -s "${actual}" "${expected}"; then
        PASSED=$((PASSED + 1))
        echo "PASS ${exe}"
    else
        echo "FAIL ${exe}: output differed from ${expected}" >&2

        EXPECTED_BYTES=$(wc -c < "${expected}" | tr -d ' ')
        ACTUAL_BYTES=$(wc -c < "${actual}" | tr -d ' ')
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
        head -c "${EXPECTED_PREVIEW_BYTES}" "${expected}" >&2
        printf '\n' >&2

        if [ "${ACTUAL_BYTES}" -gt "${PREVIEW_BYTES}" ]; then
            echo "Actual output (${ACTUAL_PREVIEW_BYTES}/${ACTUAL_BYTES} bytes, truncated):" >&2
        else
            echo "Actual output (${ACTUAL_PREVIEW_BYTES}/${ACTUAL_BYTES} bytes):" >&2
        fi
        head -c "${ACTUAL_PREVIEW_BYTES}" "${actual}" >&2
        printf '\n' >&2
        exit 1
    fi
}

for f in $FILES
do
    run_variant "${f}" default
    run_variant "${f}" O0
done

for f in $CPS_FILES
do
    run_variant "${f}" cps
done

echo "PASS ${PASSED}/${TOTAL} program variants"
