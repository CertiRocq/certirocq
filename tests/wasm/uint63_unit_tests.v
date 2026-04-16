Set Warnings "-primitive-turned-into-axiom".
From CertiRocq.Plugin Require Import CertiRocq.

From Stdlib Require Import List Uint63 ZArith.

Import ListNotations.

Open Scope uint63.

(* Sanity checks + unit tests taken from https://github.com/coq/coq/tree/master/test-suite/primitive/uint63 *)

Definition add1 := 2 + 3. (* = 5 *)
CertiRocq Compile Wasm add1.

Definition add2 := 9223372036854775807 + 1. (* = 0 *)
CertiRocq Compile Wasm add2.

Definition addc1 := 2 +c 3 (* = C0 5 *).
CertiRocq Compile Wasm addc1.

Definition addc2 := 9223372036854775807 +c 2. (* = C1 1 *)
CertiRocq Compile Wasm addc2.

Definition addcarryc1 := addcarryc 2 3. (* = C0 6 *)
CertiRocq Compile Wasm addcarryc1.

Definition addcarryc2 := addcarryc 9223372036854775807 2. (* = C1 2 *)
CertiRocq Compile Wasm addcarryc2.

Definition sub1 := 3 - 2. (* = 1 *)
CertiRocq Compile Wasm sub1.

Definition sub2 := 0 - 1. (* = 9223372036854775807 *)
CertiRocq Compile Wasm sub2.

Definition subc1 := 3 -c 2. (* = C0 1 *)
CertiRocq Compile Wasm subc1.

Definition subc2 := 0 -c 1. (* = C1 9223372036854775807 *)
CertiRocq Compile Wasm subc2.

Definition subcarryc1 := subcarryc 3 1. (* = C0 1 *)
CertiRocq Compile Wasm subcarryc1.

Definition subcarryc2 := subcarryc 0 1. (* = C1 9223372036854775806 *)
CertiRocq Compile Wasm subcarryc2.

Definition mul1 := 2 * 3. (* = 6 *)
CertiRocq Compile Wasm mul1.

Definition mul2 := 9223372036854775807 * 2. (* = 9223372036854775806 *)
CertiRocq Compile Wasm mul2.

Definition mulc1 := mulc 2 3. (* = WW 0 6. *)
CertiRocq Compile Wasm mulc1.

Definition mulc2 := mulc 9223372036854775807 2. (* = WW 1 9223372036854775806 *)
CertiRocq Compile Wasm mulc2.

Definition mulc3 := mulc 0 0. (* = W0. *)
CertiRocq Compile Wasm mulc3.

Definition mulc4 := mulc 12188099900 12188099900. (* (16, 975826582703597072) *)
CertiRocq Compile Wasm mulc4.

Definition mulc5 := mulc 8500964271916320249 8500964271916320249. (* (7835138088720211561, 6616587037742705713) *)
CertiRocq Compile Wasm mulc5.

Definition div1 := 6 / 3. (* = 2 *)
CertiRocq Compile Wasm div1.

Definition div2 := 3 / 2. (* = 1 *)
CertiRocq Compile Wasm div2.

Definition div3 := 42 / 0. (* = 0 *)
CertiRocq Compile Wasm div3.

Definition mod1 := 6 mod 3. (* = 0 *)
CertiRocq Compile Wasm mod1.

Definition mod2 := 5 mod 3. (* = 2 *)
CertiRocq Compile Wasm mod2.

Definition mod3 := 42 mod 0. (* = 0 *)
CertiRocq Compile Wasm mod3.

Definition land1 := 0 land 0. (* = 0 *)
CertiRocq Compile Wasm land1.

Definition land2 := 9223372036854775807 land 0. (* = 0 *)
CertiRocq Compile Wasm land2.

Definition land3 := 0 land 9223372036854775807. (* = 0 *)
CertiRocq Compile Wasm land3.

Definition land4 := 9223372036854775807 land 9223372036854775807. (* = 9223372036854775807 *)
CertiRocq Compile Wasm land4.

Definition lor1 := 0 lor 0. (* = 0 *)
CertiRocq Compile Wasm lor1.

Definition lor2 := 9223372036854775807 lor 0. (* = 9223372036854775807 *)
CertiRocq Compile Wasm lor2.

Definition lor3 := 0 lor 9223372036854775807. (* = 9223372036854775807 *)
CertiRocq Compile Wasm lor3.

Definition lor4 := 9223372036854775807 lor 9223372036854775807. (* = 9223372036854775807 *)
CertiRocq Compile Wasm lor4.

Definition lxor1 := 0 lxor 0. (* = 0 *)
CertiRocq Compile Wasm lxor1.

Definition lxor2 := 9223372036854775807 lxor 0. (* = 9223372036854775807 *)
CertiRocq Compile Wasm lxor2.

Definition lxor3 :=  0 lxor 9223372036854775807. (* = 9223372036854775807 *)
CertiRocq Compile Wasm lxor3.

Definition lxor4 := 9223372036854775807 lxor 9223372036854775807. (* = 0 *)
CertiRocq Compile Wasm lxor4.

Definition lsl1 := 3 << 61. (* = 6917529027641081856 *)
CertiRocq Compile Wasm lsl1.

Definition lsl2 := 2 << 62. (* = 0 *)
CertiRocq Compile Wasm lsl2.

Definition lsl3 := 9223372036854775807 << 64. (* = 0 *)
CertiRocq Compile Wasm lsl3.

Definition lsr1 := 6917529027641081856 >> 61. (* = 3 *)
CertiRocq Compile Wasm lsr1.

Definition lsr2 := 2305843009213693952 >> 62. (* = 0 *)
CertiRocq Compile Wasm lsr2.

Definition lsr3 := 9223372036854775807 >> 64. (* = 0 *)
CertiRocq Compile Wasm lsr3.

Definition compare1 := 1 ?= 1. (* = Eq *)
CertiRocq Compile Wasm compare1.

Definition compare2 := 1 ?= 2. (* = Lt *)
CertiRocq Compile Wasm compare2.

Definition compare3 := 9223372036854775807 ?= 0. (* = Gt *)
CertiRocq Compile Wasm compare3.

Definition eqb1 := 1 =? 1. (* = true *)
CertiRocq Compile Wasm eqb1.

Definition eqb2 := 9223372036854775807 =? 0. (* = false *)
CertiRocq Compile Wasm eqb2.

Definition ltb1 := 1 <? 1. (* = false *)
CertiRocq Compile Wasm ltb1.

Definition ltb2 := 1 <? 2. (* = true *)
CertiRocq Compile Wasm ltb2.

Definition ltb3 := 9223372036854775807 <? 0. (* = false *)
CertiRocq Compile Wasm ltb3.

Definition leb1 := 1 <=? 1. (* = true *)
CertiRocq Compile Wasm leb1.

Definition leb2 := 1 <=? 2. (* = true *)
CertiRocq Compile Wasm leb2.

Definition leb3 := 9223372036854775807 <=? 0. (* = false *)
CertiRocq Compile Wasm leb3.

Definition head0_1 := head0 3. (* = 61 *)
CertiRocq Compile Wasm head0_1.

Definition head0_2 := head0 4611686018427387904. (* = 0 *)
CertiRocq Compile Wasm head0_2.

Definition head0_3 := head0 0. (* = 63 *)
CertiRocq Compile Wasm head0_3.

Definition tail0_1 := tail0 2305843009213693952. (* = 61 *)
CertiRocq Compile Wasm tail0_1.

Definition tail0_2 := tail0 1. (* = 0 *)
CertiRocq Compile Wasm tail0_2.

Definition tail0_3 := tail0 0. (* = 63 *)
CertiRocq Compile Wasm tail0_3.

Definition diveucl1 := diveucl 6 3. (* = (2,0) *)
CertiRocq Compile Wasm diveucl1.

Definition diveucl2 := diveucl 5 3. (* = (1,2) *)
CertiRocq Compile Wasm diveucl2.

Definition diveucl3 := diveucl 42 0. (* = (0, 42) *)
CertiRocq Compile Wasm diveucl3.

Definition diveucl_21_1 := diveucl_21 1 1 2. (* = (4611686018427387904,1) *)
CertiRocq Compile Wasm diveucl_21_1.

Definition diveucl_21_2 := diveucl_21 3 1 2. (* = (0, 0) *)
CertiRocq Compile Wasm diveucl_21_2.

Definition diveucl_21_3 := diveucl_21 1 1 0. (* = (0,0) *)
CertiRocq Compile Wasm diveucl_21_3.

Definition diveucl_21_4 := diveucl_21 9223372036854775807 0 1. (* = (0,0) *)
CertiRocq Compile Wasm diveucl_21_4.

Definition diveucl_21_5 := diveucl_21 9305446873517 1793572051078448654 4930380657631323783. (* = (17407905077428, 3068214991893055266) *)
CertiRocq Compile Wasm diveucl_21_5.

Definition addmuldiv1 := addmuldiv 32 3 5629499534213120. (* = 12887523328 *)
CertiRocq Compile Wasm addmuldiv1.

Definition addmuldiv2 := addmuldiv 63 1 0. (* = 0 *)
CertiRocq Compile Wasm addmuldiv2.

Definition addmuldiv3 := addmuldiv 63 1 9223372036854775807. (* = 9223372036854775807 *)
CertiRocq Compile Wasm addmuldiv3.

Definition unsigned1 := 1/(0-1). (* = 0 *)
CertiRocq Compile Wasm unsigned1.

Definition unsigned2 := 3 mod (0-1). (* = 3 *)
CertiRocq Compile Wasm unsigned2.
