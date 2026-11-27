#!/usr/bin/env bash
# Compare the running time of the bootstrapped MetaRocq checker (certirocqchk) on MetaRocq's
# hott_example.v with rocqchk and with MetaRocq's checker extracted to OCaml (MetaRocq SafeCheck),
# and print the results as a Markdown table.
#
# Each checker runs RUNS times (default 10), in separate processes, after one warm-up run that
# is not counted; the table gives the median and the range (min-max) of the timings.
#
# Usage: [RUNS=n] tests/bench_hott.sh <rocq c options to find the certirocqchk plugin>
# Run by make bench-hott in bootstrap/certirocqchk, after building the plugin (make plugin).

set -eo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C   # Decimal points in the timings
TESTS="-Q tests CertiRocq.CertiRocqCheck.Tests"
RUNS=${RUNS:-10}
ulimit -Ss 65500 2>/dev/null || true

# The constants checked by hott_safecheck.v and hott_certirocqchk.v, in order
CONSTANTS=("issect'" ap_pp isequiv_adjointify IsEquiv)

OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# run <name> <command...>: run the command, its output in $OUT/<name>.log and its real time
# (in seconds) in $OUT/<name>.time; on failure, show the errors and stop.
run() {
  local name=$1; shift
  local TIMEFORMAT=%R
  if ! { time "$@" > "$OUT/$name.log" 2>&1 ; } 2> "$OUT/$name.time"; then
    echo "$name failed:" >&2
    awk '/Error|Anomaly/ { n = 5 } n > 0 { print; n-- }' "$OUT/$name.log" >&2
    exit 1
  fi
}

# times <name> <regexp>: the timings captured by <regexp> in $OUT/<name>.log, one per constant
times() {
  sed -n "s/$2/\1/p" "$OUT/$1.log" > "$OUT/$1.times"
  if [ "$(wc -l < "$OUT/$1.times")" -ne "${#CONSTANTS[@]}" ]; then
    echo "Unexpected number of timings in $1:" >&2; cat "$OUT/$1.times" >&2; exit 1
  fi
}
TIME='^Finished transaction in \([0-9.]*\) secs.*'
# Time spent in the compiled checker itself, without quoting, as reported by its C wrapper
CTIME='^Time taken \([0-9.]*\) seconds.*'

run example rocq c $TESTS tests/hott_example.v

for i in $(seq 0 "$RUNS"); do
  printf '\rRun %d/%d' "$i" "$RUNS" >&2
  run rocqchk.$i rocqchk -silent $TESTS -norec CertiRocq.CertiRocqCheck.Tests.hott_example
  run safecheck.$i rocq c $TESTS tests/hott_safecheck.v
  run certirocqchk.$i rocq c "$@" $TESTS tests/hott_certirocqchk.v
  times safecheck.$i "$TIME"
  times certirocqchk.$i "$TIME"
  cp "$OUT/certirocqchk.$i.log" "$OUT/ccheck.$i.log"; times ccheck.$i "$CTIME"
done
printf '\r%*s\r' 20 '' >&2

# stats <files...>: for each line (constant), the timings of the given runs (one file per run)
# as "median min max"
stats() {
  paste "$@" | awk '{ n = NF; for (i = 1; i <= n; i++) v[i] = $i;
    for (i = 2; i <= n; i++) { x = v[i]; for (j = i - 1; j >= 1 && v[j] > x; j--) v[j+1] = v[j]; v[j+1] = x }
    med = (n % 2) ? v[(n+1)/2] : (v[n/2] + v[n/2+1]) / 2;
    printf "%.4f %.4f %.4f\n", med, v[1], v[n] }'
}
runs() { for i in $(seq 1 "$RUNS"); do echo "$OUT/$1.$i.$2"; done; }  # The warm-up run 0 is left out

printf '%s\n' "${CONSTANTS[@]}" > "$OUT/constants"
stats $(runs certirocqchk times) > "$OUT/certirocqchk.stats"
stats $(runs ccheck times) > "$OUT/ccheck.stats"
stats $(runs safecheck times) > "$OUT/safecheck.stats"
stats $(runs rocqchk time) > "$OUT/rocqchk.stats"

echo "Median (min-max) of $RUNS runs, in seconds. [Time] has a resolution of 1 ms, so the ratios"
echo "are only significant for the constants that take several milliseconds to check."
echo
echo "| Constant | certirocqchk | certirocqchk (checker only) | MetaRocq SafeCheck (OCaml) | certirocqchk / SafeCheck |"
echo "|---|---:|---:|---:|---:|"
paste "$OUT/constants" "$OUT/certirocqchk.stats" "$OUT/ccheck.stats" "$OUT/safecheck.stats" |
  awk -F'[\t ]' '{ ratio = ($8 > 0) ? sprintf("%.1fx", $2 / $8) : "-";
    printf "| `%s` | %.3f (%.3f-%.3f) | %.3f (%.3f-%.3f) | %.3f (%.3f-%.3f) | %s |\n",
      $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, ratio }'
echo
read -r med min max < "$OUT/rocqchk.stats"
printf 'rocqchk on the whole file (%s declarations, dependencies admitted, process included): %.3f s (%.3f-%.3f)\n' \
  "$(grep -cE '^(Definition|Inductive|Lemma|Record|Class|Fixpoint|Theorem)' tests/hott_example.v)" \
  "$med" "$min" "$max"
