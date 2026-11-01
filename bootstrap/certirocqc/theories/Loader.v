From MetaRocq Require Import ExtractableLoader.
From CertiRocq.VanillaPlugin Require Export CertiRocqVanilla. (* We reuse the ML certirocq plugin to parse options and print Clight code *)
(* Use Export to export the primitives registrations *)

Declare ML Module "rocq-certirocqc.plugin".
