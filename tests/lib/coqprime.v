(* coq prime benchmark *)
From Coqprime Require Import PocklingtonRefl.
From MetaRocq.Utils Require Import bytestring MRString.

Local Open Scope positive_scope.
Open Scope bs.

Definition cert1 :=
         (Pock_certif 2453592460649055756812450508556009475577084379843351664172069410531995758325371349410079350684102193 5 ((535891737757285083698263, 1)::(22187633823577, 1)::(2,4)::nil) 263365669118842309261237752510635123964) ::
        (Pock_certif 535891737757285083698263 3 ((29771763208738060205459, 1)::(2,1)::nil) 1) ::
         (Pock_certif 29771763208738060205459 2 ((2141, 1)::(1867, 1)::(7, 1)::(2,1)::nil) 17474375) ::
         (Pock_certif 22187633823577 7 ((13, 2)::(3, 3)::(2,3)::nil) 22167) ::
         (Proof_certif 2141 prime2141) ::
         (Proof_certif 1867 prime1867) ::
         (Proof_certif 13 prime13) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_cert1 := test_Certif cert1.
(* Eval compute in "Checking primality of 2453592460649055756812450508556009475577084379843351664172069410531995758325371349410079350684102193 (100 digits)". *)
(* Time Eval vm_compute in check_cert1. *)


Definition cert2 :=
         (Pock_certif 5351956038121333109794470473803140209428240474621443000490827925245658234802043104136048237347232839 7 ((7931077303135578295706501, 1)::(807509, 1)::(23071, 1)::(2,1)::nil) 83825513627931379579640353334701292) ::
        (Pock_certif 7931077303135578295706501 2 ((94477, 1)::(19, 1)::(5, 2)::(2,2)::nil) 53011245) ::
         (Pock_certif 807509 2 ((53, 1)::(2,2)::nil) 416) ::
         (Pock_certif 94477 2 ((7873, 1)::(2,2)::nil) 1) ::
         (Proof_certif 23071 prime23071) ::
         (Proof_certif 7873 prime7873) ::
         (Proof_certif 53 prime53) ::
         (Proof_certif 19 prime19) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_cert2 := test_Certif cert2.
(* Eval compute in "Checking primality of 5351956038121333109794470473803140209428240474621443000490827925245658234802043104136048237347232839 (100 digits)". *)
(* Time Eval vm_compute in check_cert2. *)


Definition cert3 :=
         (Pock_certif 5156668690509008564394179574550331202149987474724297759354684344612323405888046576355302595612624991 3 ((1064619103664925607325345484869851719496771558974058884015408678407183477, 1)::(2,1)::nil) 1) ::
        (Pock_certif 1064619103664925607325345484869851719496771558974058884015408678407183477 2 ((3912194362405668030913307804243, 1)::(2,2)::nil) 26551391883318726506260350984158) ::
         (Pock_certif 3912194362405668030913307804243 2 ((369180882757, 1)::(2,1)::nil) 949924248164) ::
         (Pock_certif 369180882757 6 ((3, 7)::(2,2)::nil) 1388) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_cert3 := test_Certif cert3.
(* Eval compute in "Checking primality of 5156668690509008564394179574550331202149987474724297759354684344612323405888046576355302595612624991 (100 digits)". *)
(* Time Eval vm_compute in check_cert3. *)
(* Extraction "ocaml_prime3" check_cert3. *)


Definition cert4 :=
         (Pock_certif 4563975913455889091356468710155013974880832493315598107353834542502587892695693300925853265435622357 2 ((616868944230556873267, 1)::(35974457, 1)::(15383, 1)::(2,2)::nil) 2510617228410479161890451128591679) ::
        (Pock_certif 616868944230556873267 2 ((66797, 1)::(1069, 1)::(2,1)::nil) 242273896) ::
         (Pock_certif 35974457 3 ((569, 1)::(2,3)::nil) 1) ::
         (Pock_certif 66797 2 ((16699, 1)::(2,2)::nil) 1) ::
         (Proof_certif 16699 prime16699) ::
         (Proof_certif 15383 prime15383) ::
         (Proof_certif 1069 prime1069) ::
         (Proof_certif 569 prime569) ::
         (Proof_certif 2 prime2) ::
          nil.


Definition check_cert4 := test_Certif cert4.
(* Eval compute in "Checking primality of 4563975913455889091356468710155013974880832493315598107353834542502587892695693300925853265435622357 (100 digits)". *)
(* Time Eval vm_compute in check_cert4. *)
