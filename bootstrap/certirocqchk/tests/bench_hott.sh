#!/usr/bin/env bash
# Compare the running time of the bootstrapped MetaRocq checker (certirocqchk) on MetaRocq's
# hott_example.v with rocqchk and with MetaRocq's checker extracted to OCaml (MetaRocq SafeCheck),
# and print the results as a Markdown table.
#
# Usage: tests/bench_hott.sh <rocq c options to find the certirocqchk plugin>
# Run by make bench-hott in bootstrap/certirocqchk, after building the plugin (make plugin).

set -eo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C   # Decimal points in the timings
TESTS="-Q tests CertiRocq.CertiRocqCheck.Tests"
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

# The [Time] timings (seconds) of a log, one per line
times_of() { sed -n 's/^Finished transaction in \([0-9.]*\) secs.*/\1/p' "$OUT/$1.log"; }

run example rocq c $TESTS tests/hott_example.v
run rocqchk rocqchk -silent $TESTS -norec CertiRocq.CertiRocqCheck.Tests.hott_example
run safecheck rocq c $TESTS tests/hott_safecheck.v
run certirocqchk rocq c "$@" $TESTS tests/hott_certirocqchk.v

times_of safecheck > "$OUT/safecheck.times"
times_of certirocqchk > "$OUT/certirocqchk.times"
# Time spent in the compiled checker itself, without quoting, as reported by its C wrapper
sed -n 's/^Time taken \([0-9.]*\) seconds.*/\1/p' "$OUT/certirocqchk.log" > "$OUT/certirocqchk.ctimes"
printf '%s\n' "${CONSTANTS[@]}" > "$OUT/constants"

for f in safecheck.times certirocqchk.times certirocqchk.ctimes; do
  if [ "$(wc -l < "$OUT/$f")" -ne "${#CONSTANTS[@]}" ]; then
    echo "Unexpected number of timings in $f:" >&2; cat "$OUT/$f" >&2; exit 1
  fi
done

echo "| Constant | certirocqchk | certirocqchk (checker only) | MetaRocq SafeCheck (OCaml) | certirocqchk / SafeCheck |"
echo "|---|---:|---:|---:|---:|"
paste "$OUT/constants" "$OUT/certirocqchk.times" "$OUT/certirocqchk.ctimes" "$OUT/safecheck.times" |
  awk -F'\t' '{ ratio = ($4 > 0) ? sprintf("%.1fx", $2 / $4) : "-";
                printf "| `%s` | %.3f s | %.3f s | %.3f s | %s |\n", $1, $2, $3, $4, ratio }'
echo
printf 'rocqchk on the whole file (%s declarations, dependencies admitted, process included): %.3f s\n' \
  "$(grep -cE '^(Definition|Inductive|Lemma|Record|Class|Fixpoint|Theorem)' tests/hott_example.v)" \
  "$(cat "$OUT/rocqchk.time")"
