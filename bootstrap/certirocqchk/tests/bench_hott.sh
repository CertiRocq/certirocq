#!/usr/bin/env bash
# Compare the running time of the bootstrapped MetaRocq checker (certirocqchk) on MetaRocq's
# hott_example.v with rocqchk and with MetaRocq's checker extracted to OCaml (MetaRocq SafeCheck),
# and print the results as a Markdown table.
#
# [Time] has a resolution of 1 ms, and most checks take a few milliseconds: each constant is
# checked REPEATS times in a row, in its own session, in a file run by a single [Time Load], and
# the time of a check is the time of the block divided by REPEATS. Each checker runs RUNS times
# (default 5), in separate processes, after one warm-up run that is not counted; the table
# gives the median and the range (min-max) of the timings.
#
# With BENCH_ANNOTATIONS=github, the results are also printed as a GitHub Actions notice (and a
# failure as a warning), which shows up as an annotation of the CI run and of the pull request.
#
# Usage: [RUNS=n] [BENCH_ANNOTATIONS=github] tests/bench_hott.sh <rocq c options to find the
#   certirocqchk plugin>
# Run by make bench-hott in bootstrap/certirocqchk, after building the plugin (make plugin).

set -eo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C   # Decimal points in the timings
TESTS="-Q tests CertiRocq.CertiRocqCheck.tests"
RUNS=${RUNS:-5}
ulimit -Ss 65500 2>/dev/null || true

# The constants checked (those of MetaRocq's safechecker_test.v), and the number of times each
# one is checked in a row, for blocks of at least ~0.1 s with MetaRocq SafeCheck
CONSTANTS=("issect'" ap_pp isequiv_adjointify IsEquiv)
REPEATS=(50 50 5 200)

OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
printf '%s\n' "${CONSTANTS[@]}" > "$OUT/constants"
printf '%s\n' "${REPEATS[@]}" > "$OUT/repeats"

# gen <name> <loader> <check command>: for each constant i, the session $OUT/<name>_i.v, which
# loads <loader> and hott_example.v, then times a block of REPEATS[i] <check command> <constant>.
# Each constant gets its own session: in a session, the checks get slower after other constants
# were checked.
gen() {
  for i in "${!CONSTANTS[@]}"; do
    for ((k = 0; k < REPEATS[i]; k++)); do echo "$3${CONSTANTS[i]}."; done > "$OUT/$1_block$i.v"
    {
      echo "$2"
      echo "From CertiRocq.CertiRocqCheck.tests Require Import hott_example."
      echo "Time Load \"$OUT/$1_block$i.v\"."
    } > "$OUT/$1_$i.v"
  done
}
gen safecheck "From MetaRocq.SafeCheckerPlugin Require Import Loader." "MetaRocq SafeCheck @"
gen certirocqchk "From CertiRocq.CertiRocqCheck Require Import Loader." "CertiRocqCheck "

# annotate <notice|warning> <title> <message lines...>: a GitHub Actions annotation, if requested
annotate() {
  [ "${BENCH_ANNOTATIONS:-}" = github ] || return 0
  local kind=$1 title=$2; shift 2
  local msg; msg=$(printf '%s\n' "$@" | sed 's/%/%25/g' | awk 'NR > 1 { printf "%%0A" } { printf "%s", $0 }')
  title=$(printf '%s' "$title" | sed 's/%/%25/g; s/:/%3A/g; s/,/%2C/g')
  echo "::$kind title=$title::$msg"
}

# run <name> <command...>: run the command, its output in $OUT/<name>.log and its real time
# (in seconds) in $OUT/<name>.time; on failure, show the errors and stop.
run() {
  local name=$1; shift
  local TIMEFORMAT=%R
  if ! { time "$@" > "$OUT/$name.log" 2>&1 ; } 2> "$OUT/$name.time"; then
    echo "$name failed:" >&2
    awk '/Error|Anomaly/ { n = 5 } n > 0 { print; n-- }' "$OUT/$name.log" >&2
    annotate warning "certirocqchk benchmark failed" "$name failed:" \
      "$(awk '/Error|Anomaly/ { n = 5 } n > 0 { print; n-- }' "$OUT/$name.log")"
    exit 1
  fi
}

# check_count <file> <n>: <file> has <n> lines
check_count() {
  if [ "$(wc -l < "$1")" -ne "$2" ]; then
    echo "Unexpected number of timings in $1:" >&2; cat "$1" >&2; exit 1
  fi
}

# block_times <run>: the time of one check of each constant (seconds), from the [Time] of its block
block_times() {
  sed -n 's/^Finished transaction in \([0-9.]*\) secs.*/\1/p' "$OUT/$1.log" > "$OUT/$1.blocks"
  check_count "$OUT/$1.blocks" "${#CONSTANTS[@]}"
  paste "$OUT/$1.blocks" "$OUT/repeats" | awk '{ printf "%.6f\n", $1 / $2 }' > "$OUT/$1.times"
}

# checker_times <run>: the mean time spent in the compiled checker itself (without quoting) for
# each constant, from the times reported by its C wrapper for each check
checker_times() {
  sed -n 's/^Time taken \([0-9.]*\) seconds.*/\1/p' "$OUT/$1.log" > "$OUT/$1.checks"
  check_count "$OUT/$1.checks" "$(awk '{ s += $1 } END { print s }' "$OUT/repeats")"
  awk 'NR == FNR { r[NR] = $1; next }
       { s += $1; if (++k == r[i + 1]) { printf "%.6f\n", s / k; i++; s = 0; k = 0 } }' \
    "$OUT/repeats" "$OUT/$1.checks" > "$OUT/$1.ctimes"
}

run example rocq c $TESTS tests/hott_example.v

for i in $(seq 0 "$RUNS"); do
  printf '\rRun %d/%d' "$i" "$RUNS" >&2
  run rocqchk.$i rocqchk -silent $TESTS -norec CertiRocq.CertiRocqCheck.tests.hott_example
  for j in "${!CONSTANTS[@]}"; do
    run safecheck.$i.$j rocq c $TESTS "$OUT/safecheck_$j.v"
    run certirocqchk.$i.$j rocq c "$@" $TESTS "$OUT/certirocqchk_$j.v"
  done
  cat $(for j in "${!CONSTANTS[@]}"; do echo "$OUT/safecheck.$i.$j.log"; done) > "$OUT/safecheck.$i.log"
  cat $(for j in "${!CONSTANTS[@]}"; do echo "$OUT/certirocqchk.$i.$j.log"; done) > "$OUT/certirocqchk.$i.log"
  block_times safecheck.$i
  block_times certirocqchk.$i
  checker_times certirocqchk.$i
done
printf '\r%*s\r' 20 '' >&2

# stats <files...>: for each line (constant), the median, min and max of the timings of the
# given runs (one file per run), in milliseconds
stats() {
  paste "$@" | awk '{ n = NF; for (i = 1; i <= n; i++) v[i] = $i * 1000;
    for (i = 2; i <= n; i++) { x = v[i]; for (j = i - 1; j >= 1 && v[j] > x; j--) v[j+1] = v[j]; v[j+1] = x }
    med = (n % 2) ? v[(n+1)/2] : (v[n/2] + v[n/2+1]) / 2;
    printf "%.4f %.4f %.4f\n", med, v[1], v[n] }'
}
runs() { for i in $(seq 1 "$RUNS"); do echo "$OUT/$1.$i.$2"; done; }  # The warm-up run 0 is left out

stats $(runs certirocqchk times) > "$OUT/certirocqchk.stats"
stats $(runs certirocqchk ctimes) > "$OUT/ccheck.stats"
stats $(runs safecheck times) > "$OUT/safecheck.stats"
stats $(runs rocqchk time) > "$OUT/rocqchk.stats"

echo "Time of one check, in milliseconds: median (min-max) of $RUNS runs, each checking each"
echo "constant the given number of times in a row, in its own session."
echo
echo "| Constant | Checks per run | certirocqchk | certirocqchk (checker only) | MetaRocq SafeCheck (OCaml) | certirocqchk / SafeCheck |"
echo "|---|---:|---:|---:|---:|---:|"
paste "$OUT/constants" "$OUT/repeats" "$OUT/certirocqchk.stats" "$OUT/ccheck.stats" "$OUT/safecheck.stats" > "$OUT/all.stats"
awk -F'[\t ]' 'function ms(x) { return sprintf(x < 10 ? "%.3f" : "%.1f", x) }
    { ratio = ($9 > 0) ? sprintf("%.1fx", $3 / $9) : "-";
      printf "| `%s` | %d | %s (%s-%s) | %s (%s-%s) | %s (%s-%s) | %s |\n", $1, $2,
        ms($3), ms($4), ms($5), ms($6), ms($7), ms($8), ms($9), ms($10), ms($11), ratio }' "$OUT/all.stats"
echo
read -r med min max < "$OUT/rocqchk.stats"
ROCQCHK=$(printf 'rocqchk on the whole file (%s declarations, dependencies admitted, process included): %.0f ms (%.0f-%.0f)' \
  "$(grep -cE '^(Definition|Inductive|Lemma|Record|Class|Fixpoint|Theorem)' tests/hott_example.v)" \
  "$med" "$min" "$max")
echo "$ROCQCHK"

# The annotation is plain text: one line per constant, with the medians
annotate notice "certirocqchk benchmark (hott_example.v)" \
  "Time of one check, median of $RUNS runs:" \
  "$(awk -F'[\t ]' 'function ms(x) { return sprintf(x < 10 ? "%.3f" : "%.1f", x) }
    { ratio = ($9 > 0) ? sprintf("%.1fx", $3 / $9) : "-";
      printf "%s: certirocqchk %s ms (checker only %s ms), SafeCheck %s ms, certirocqchk / SafeCheck %s\n", $1, ms($3), ms($6), ms($9), ratio }' "$OUT/all.stats")" \
  "$ROCQCHK"
