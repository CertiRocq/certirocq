From MetaRocq Require Import ExtractableLoader.
From CertiRocq Require Export CertiRocqVanilla. (* We reuse the ML certirocq plugin to parse options and print Clight code *)
(* Using Export to get the primitives registrations the *)
Declare ML Module "rocq-certirocq-bootstrapped-erasure.plugin".
