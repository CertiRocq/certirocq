(** MetaRocq's checker extracted to OCaml on [hott_example.v], to compare with
    [hott_certirocqchk.v]. *)

From MetaRocq.SafeCheckerPlugin Require Import Loader.
From CertiRocq.CertiRocqCheck.Tests Require Import hott_example.

Time MetaRocq SafeCheck @issect'.
Time MetaRocq SafeCheck @ap_pp.
Time MetaRocq SafeCheck @isequiv_adjointify.
Time MetaRocq SafeCheck @IsEquiv.
