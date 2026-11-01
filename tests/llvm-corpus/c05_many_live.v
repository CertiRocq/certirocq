(* Many live variables across a call: [many] binds 40 boxed values and then
   calls [churn], which allocates ~200K words (several collections); all 40
   values are used after the call, so the emitted [Eletapp] registers a
   40-slot root array, and every collection inside [churn] must forward all
   of them.  [many] is called 234 times.
   Targets: roots_ok with a large root frame, slots_from, room.
   Expected (Rocq): (D0, D5)
   EXPECTED: (C0 0 5) *)
From Stdlib Require Import List.
Inductive d7 := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition s7 (d : d7) : d7 :=
  match d with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D0 end.
Definition add7 (x y : d7) : d7 :=
  match x with
  | D0 => y | D1 => s7 y | D2 => s7 (s7 y) | D3 => s7 (s7 (s7 y))
  | D4 => s7 (s7 (s7 (s7 y))) | D5 => s7 (s7 (s7 (s7 (s7 y))))
  | D6 => s7 (s7 (s7 (s7 (s7 (s7 y))))) end.

(* [hide 0 v] is [v], but through a recursive function, which the
   optimizer does not inline: without it, case-of-known-constructor would
   fold every [match v_i with ...] below and the v_i would never be
   allocated. *)
Fixpoint hide {A} (n : nat) (a : A) : A := match n with O => a | S m => hide m a end.

Inductive tree := Leaf | Node (l : tree) (x : d7) (r : tree).
Fixpoint mk (n : nat) (x : d7) : tree :=
  match n with O => Leaf | S m => Node (mk m (s7 x)) x (mk m x) end.
Fixpoint tsum (t : tree) (acc : d7) : d7 :=
  match t with Leaf => acc | Node l x r => tsum r (add7 x (tsum l acc)) end.
(* 2^15 - 1 nodes * 4 words = ~131K words: two nursery overflows per call *)
Definition churn (x : d7) : d7 := tsum (mk 15 x) D0.

Definition many (x : d7) : d7 :=
  let v1 := hide 0 (Some x) in let v2 := hide 0 ((x, s7 x)) in let v3 := hide 0 (Some (s7 x)) in
  let v4 := hide 0 ((v1, v2)) in let v5 := hide 0 (Some v3) in let v6 := hide 0 ((x, x)) in
  let v7 := hide 0 (Some (s7 (s7 x))) in let v8 := hide 0 ((v3, v7)) in let v9 := hide 0 (Some v4) in
  let v10 := hide 0 ((v5, v6)) in let v11 := hide 0 (Some v8) in let v12 := hide 0 ((v9, v10)) in
  let v13 := hide 0 (Some v11) in let v14 := hide 0 ((v12, v13)) in let v15 := hide 0 (Some v14) in
  let v16 := hide 0 ((v15, x)) in let v17 := hide 0 (Some v16) in let v18 := hide 0 ((v17, v1)) in
  let v19 := hide 0 (Some v18) in let v20 := hide 0 ((v19, v2)) in let v21 := hide 0 (Some v20) in
  let v22 := hide 0 ((v21, v3)) in let v23 := hide 0 (Some v22) in let v24 := hide 0 ((v23, v4)) in
  let v25 := hide 0 (Some v24) in let v26 := hide 0 ((v25, v5)) in let v27 := hide 0 (Some v26) in
  let v28 := hide 0 ((v27, v6)) in let v29 := hide 0 (Some v28) in let v30 := hide 0 ((v29, v7)) in
  let v31 := hide 0 (Some v30) in let v32 := hide 0 ((v31, v8)) in let v33 := hide 0 (Some v32) in
  let v34 := hide 0 ((v33, v9)) in let v35 := hide 0 (Some v34) in let v36 := hide 0 ((v35, v10)) in
  let v37 := hide 0 (Some v36) in let v38 := hide 0 ((v37, v11)) in let v39 := hide 0 (Some v38) in
  let v40 := hide 0 ((v39, v12)) in
  let r := churn x in
  (* use every v_i after the call *)
  let g1 := match v1 with Some a => a | None => D0 end in
  let g2 := snd v2 in
  let g3 := match v3 with Some a => a | None => D0 end in
  let g4 := snd (snd v4) in
  let g5 := match v5 with Some (Some a) => a | _ => D0 end in
  let g6 := fst v6 in
  let g7 := match v7 with Some a => a | None => D0 end in
  let g8 := match snd v8 with Some a => a | None => D0 end in
  let g9 := match v9 with Some (_, (_, a)) => a | None => D0 end in
  let g10 := snd (snd v10) in
  let g11 := match v11 with Some (_, Some a) => a | _ => D0 end in
  let g12 := snd (snd (snd v12)) in
  let g13 := match v13 with Some (Some (Some a, _)) => a | _ => D0 end in
  let g14 := match snd v14 with Some (Some (_, Some a)) => a | _ => D0 end in
  let g15 := match v15 with Some (_, Some _) => s7 x | _ => D0 end in
  let g16 := snd v16 in
  let g17 := match v17 with Some (_, a) => a | None => D0 end in
  let g18 := match snd v18 with Some a => a | None => D0 end in
  let g19 := match v19 with Some (_, Some a) => a | _ => D0 end in
  let g20 := snd (snd v20) in
  let g21 := match v21 with Some (_, (_, a)) => s7 a | _ => D0 end in
  let g22 := match snd v22 with Some a => a | None => D0 end in
  let g23 := match v23 with Some (_, Some a) => s7 (s7 a) | _ => D0 end in
  let g24 := match snd v24 with (_, (_, a)) => a end in
  let g25 := match v25 with Some (_, _) => D5 | None => D0 end in
  let g26 := match snd v26 with Some (Some a) => a | _ => D0 end in
  let g27 := match v27 with Some _ => D6 | None => D0 end in
  let g28 := fst (snd v28) in
  let g29 := match v29 with Some (_, (a, _)) => a | None => D0 end in
  let g30 := match snd v30 with Some a => s7 a | None => D0 end in
  let g31 := match v31 with Some (_, Some a) => a | _ => D0 end in
  let g32 := match snd v32 with (_, Some a) => a | _ => D0 end in
  let g33 := match v33 with Some (_, (_, Some a)) => a | _ => D0 end in
  let g34 := match snd v34 with Some ((Some a), _) => a | _ => D0 end in
  let g35 := match v35 with Some (_, Some (Some a, _)) => a | _ => D0 end in
  let g36 := match snd v36 with (_, (a, _)) => a end in
  let g37 := match v37 with Some _ => D2 | None => D0 end in
  let g38 := match snd v38 with Some (_, Some a) => a | _ => D0 end in
  let g39 := match v39 with Some _ => D1 | None => D0 end in
  let g40 := match snd v40 with (Some (_, (_, a)), _) => a | _ => D0 end in
  fold_right add7 r
    (g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12
     :: g13 :: g14 :: g15 :: g16 :: g17 :: g18 :: g19 :: g20 :: g21 :: g22 :: g23
     :: g24 :: g25 :: g26 :: g27 :: g28 :: g29 :: g30 :: g31 :: g32 :: g33 :: g34
     :: g35 :: g36 :: g37 :: g38 :: g39 :: g40 :: nil)%list.

Fixpoint loop (n : nat) (x : d7) : d7 :=
  match n with O => x | S m => loop m (many x) end.

Definition prog : d7 * d7 := (loop 200 D1, loop 34 D3).

Example prog_expected : prog = (D0, D5) := ltac:(vm_compute; reflexivity).
