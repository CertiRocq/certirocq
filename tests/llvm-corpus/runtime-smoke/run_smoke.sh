#!/usr/bin/env bash
# Builds and runs the standalone smoke test of runtime/gc_stack_checked.c
# (plain, and with ASan+UBSan), including the negative scenarios that must
# be rejected by the checker.  Exit status 0 iff all expectations hold.
set -u
here=$(cd "$(dirname "$0")" && pwd)
rt=$(cd "$here/../../../runtime" && pwd)
out=${OUT:-$(mktemp -d)}; mkdir -p "$out"
CC=${CC:-clang}
fail=0
build() { # name extra-flags...
  local name=$1; shift
  $CC -std=gnu11 -g -O1 -Wall -I"$rt" "$@" -o "$out/$name" \
      "$here/smoke_gc_contract.c" "$rt/gc_stack_checked.c" -lpthread || exit 1
}
expect() { # binary scenario want(ok|violation) [env...]
  local bin=$1 sc=$2 want=$3; shift 3
  local log="$out/$(basename "$bin").$sc.log"
  # inner bash (no exec) so that its "Aborted" job message goes to /dev/null
  bash -c 'ulimit -c 0; log=$1; shift; "$@" >"$log" 2>&1' _ "$log" \
       env "$@" "$out/$bin" "$sc" 2>/dev/null; local st=$?
  local got=ok
  grep -q "certirocq-contract: VIOLATION" "$log" && got=violation
  [ $st -ne 0 ] && [ $got = ok ] && got="crash($st)"
  if [ "$got" = "$want" ]; then echo "PASS  $bin $sc $* -> $want"; else
    echo "FAIL  $bin $sc $* -> got $got, want $want"; fail=1; fi
  sed 's/^/      /' "$log" | grep -v "^      *$" | grep -v "^      *#[0-9]" | head -4
}
build smoke
build smoke_san -fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer
build smoke_selftest -DCERTIROCQ_CHECK_SELFTEST
for b in smoke smoke_san; do
  expect $b ok ok CERTIROCQ_CHECK_MIN_GC=1
  for sc in tag251 misaligned free-nursery bad-chain nalloc-huge old-write limit-write; do
    expect $b $sc violation ASAN_OPTIONS=handle_abort=0
  done
done
expect smoke_selftest selftest ok
for m in stack frame unboxed deep; do
  expect smoke_selftest selftest violation CERTIROCQ_CHECK_SELFTEST=$m
done
exit $fail
