(** The bootstrapped MetaRocq checker on MetaRocq's [hott_example.v].
    [bench_hott.sh] compares its running time with [rocqchk] and with
    [MetaRocq SafeCheck] (the same checker, extracted to OCaml, [hott_safecheck.v]). *)

From CertiRocq.CertiRocqCheck Require Import Loader.
From CertiRocq.CertiRocqCheck.tests Require Import hott_example.

(* The same constants as MetaRocq's test-suite/safechecker_test.v *)
Time CertiRocqCheck issect'.
Time CertiRocqCheck ap_pp.
Time CertiRocqCheck isequiv_adjointify.
Time CertiRocqCheck IsEquiv.
