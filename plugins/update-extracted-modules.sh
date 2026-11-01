#!/bin/sh
# Updates the lists of extracted modules in plugins/*/dune, which dune needs to know in
# advance, when the extracted code changes (e.g. with a new dependency of the compiler).
# The extractions are run again with the CertiRocq theory as built by dune, so run
# `dune build theories` first.
set -e

root=$(cd "$(dirname "$0")/.." && pwd)
theories=$root/_build/default/theories

for plugin in plugin cplugin; do
  tmp=$(mktemp -d)
  cp "$root/plugins/$plugin/extraction.v" "$tmp/"
  (cd "$tmp" &&
    rocq c -Q "$theories" CertiRocq -w -extraction-default-directory extraction.v > /dev/null)
  python3 -I - "$root/plugins/$plugin/dune" "$tmp" <<'EOF'
import os, re, sys
dune, tmp = sys.argv[1:]
modules = sorted((f[:-3] for f in os.listdir(tmp) if f.endswith(".ml")), key=str.lower)
lines, line = [], ""
for m in modules:
    if line and len(line) + len(m) > 70:
        lines.append(line)
        line = ""
    line = f"{line} {m}" if line else m
lines.append(line)
block = " (extracted_modules\n" + "\n".join("  " + l for l in lines) + ")"
s = open(dune).read()
s, n = re.subn(r" \(extracted_modules[^)]*\)", lambda _: block, s)
assert n == 1, dune
open(dune, "w").write(s)
print(f"{dune}: {len(modules)} extracted modules")
EOF
  rm -rf "$tmp"
done
