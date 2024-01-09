Require Import ZArith.
Require Import Common.
From CertiCoq Require Import
     LambdaANF.cps LambdaANF.cps_util LambdaANF.state LambdaANF.eval LambdaANF.shrink_cps LambdaANF.LambdaBoxLocal_to_LambdaANF
     LambdaANF.inline LambdaANF.uncurry_proto LambdaANF.closure_conversion
     LambdaANF.closure_conversion LambdaANF.hoisting LambdaANF.dead_param_elim LambdaANF.lambda_lifting.
From CertiCoq Require Import LambdaBoxLocal.toplevel.
(* From CertiCoq.Codegen Require Import LambdaANF_to_Clight. *)

Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import Monads.

Import MonadNotation.

Definition prim_env := M.t (kername * string (* C definition *) * bool (* tinfo *) * nat (* arity *)). 

Definition LambdaANFenv : Type := eval.prims * prim_env * ctor_env * ctor_tag * ind_tag * name_env * fun_env * eval.env.

Definition LambdaANFterm : Type := cps.exp.
Definition LambdaANFval : Type := cps.val.
Definition LambdaANF_FullTerm : Type := LambdaANFenv * LambdaANFterm.

Section IDENT.
  
  Context (next_var : positive).

  Instance LambdaANF_Lang : Lang LambdaANF_FullTerm :=
    { Value := LambdaANFval;
      TermWf := fun p =>
                  let '(_, e) := p in
                  identifiers.closed_exp e /\
                  identifiers.unique_bindings e ;
      BigStep := fun p v =>
                   let '(pr, prims, cenv, ctag, itag, nenv, fenv, rho, e) := p in
                   exists c, bstep_cost pr cenv rho e v c
    }.


  (* starting tags for L5_to_LambdaANF, anything under default is reserved for special
   constructors/types *)
  Definition default_ctor_tag := 99%positive.
  Definition default_ind_tag := 99%positive.
  (* assigned for the constructor and the type of closures *)
  Definition clo_tag := 15%positive.
  Definition clo_ind_tag := 16%positive.
  (* tags for functions and continuations *)
  Definition fun_fun_tag := 3%positive.
  Definition kon_fun_tag := 2%positive.


  Definition make_prim_env (prims : list (kername * string * bool * nat * positive)) : prim_env :=    
    List.fold_left (fun map '(k, s, b, ar, p) => M.set p (k, s, b, ar) map) prims (M.empty _).  
  
  Definition compile_LambdaANF_CPS (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaBoxLocalTerm LambdaANF_FullTerm :=
    fun src => 
      debug_msg "Translating from LambdaBoxLocal to LambdaANF (CPS)" ;;
      LiftErrorCertiCoqTrans "LambdaANF CPS"
                             (fun (p : toplevel.LambdaBoxLocalTerm) =>
                                let prim_env := make_prim_env prims in
                                match convert_top prim_env fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag next_var p with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src. 

  Definition compile_LambdaANF_ANF (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaBoxLocalTerm LambdaANF_FullTerm :=
    fun src => 
      debug_msg "Translating from LambdaBoxLocal to LambdaANF (ANF)" ;;
      LiftErrorCertiCoqTrans "LambdaANF ANF"
                             (fun (p : toplevel.LambdaBoxLocalTerm) =>
                                let prim_env := make_prim_env prims in
                                match convert_top_anf prim_env fun_fun_tag default_ctor_tag default_ind_tag next_var p with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src.

  (** * Definition of LambdaANF backend pipelines *)

  (* Add all names to name env *)
  Definition update_var (names : cps_util.name_env) (x : var)
    : cps_util.name_env :=
    match M.get x names with
    | Some (nNamed _) => names
    | Some nAnon => M.set x (nNamed "x") names
    | None => M.set x (nNamed "x") names
    end.

  Definition update_vars names xs :=
    List.fold_left update_var xs names.

  (** Adds missing names to name environment for the C translation *)
  Fixpoint add_binders_exp (names : cps_util.name_env) (e : exp)
    : name_env :=
    match e with
    | Econstr x _ _ e
    | Eprim_val x _ e
    | Eprim x _ _ e
    | Eletapp x _ _ _ e          
    | Eproj x _ _ _ e => add_binders_exp (update_var names x) e
    | Ecase _ pats =>
      List.fold_left (fun names p => add_binders_exp names (snd p)) pats names
    | Eapp _ _ _
    | Ehalt _ => names
    | Efun B e => add_binders_exp (add_binders_fundefs names B) e
    end
  with add_binders_fundefs (names : cps_util.name_env) (B : fundefs) : cps_util.name_env :=
         match B with
         | Fcons f _ xs e1 B1 =>
           add_binders_fundefs (add_binders_exp (update_vars (update_var names f) xs) e1) B1
         | Fnil => names
         end.

  Definition log_prog (e : exp) (c_data : comp_data) : comp_data :=
    match c_data with
    | mkCompData nv nc ni nf cenv fenv nenv imap log =>
      let msg := cps_show.show_exp nenv cenv false e in
      mkCompData nv nc ni nf cenv fenv nenv imap ("term" :: msg :: log)      
    end.


  Record anf_options :=
    { time            : bool;    (* Keep ANF per phase timing *)
      cps             : bool;    (* CPS *)
      do_lambda_lift  : bool;    (* Do lambda lifting *)
      args            : nat;     (* Arg threshold for lambda lifting *)
      no_push         : nat;     (* *)
      inl_wrappers    : bool;    (* If true, all known calls to lambda lifted functions are inlined *)
      inl_known       : bool;    (* If true, lambda lifting inlines known calls inside wrappers *)
      inl_before      : bool;    (* Perform shrink/inline loop before closure conversion *)
      inl_after       : bool;    (* Perform shrink/inline loop after closure conversion *)
      dpe             : bool;    (* Turn it off for the top-level theorm because it does not have a proof yet *)
    }.


  Definition anf_state (A : Type) := comp_data -> error A * comp_data.

  
  Definition anf_trans : Type := exp -> anf_state exp.


  Global Instance MonadState : Monad anf_state :=
    { ret A x := (fun c_data  => (Ret x, c_data));
      bind A B m f :=
        (fun c_data =>
           let (a_err, c_data') := m c_data in
           match a_err with
           | Ret a => f a c_data'
           | Err s => (Err s, c_data')
           end)
    }.
  

  Definition id_trans : anf_trans := fun e c => (Ret e, c).
  
  Section Pipeline.

    Context (anf_opts : anf_options).

    Definition time_anf {A B} (name : string) (f : A -> anf_state B) : A -> anf_state B :=
      fun x s => if time anf_opts then timePhase name (f x) s else f x s. 
    
    (* Optimizing λANF pipeline *)

    Definition anf_pipeline (e : exp) : anf_state exp :=
      e <- time_anf "Shrink" shrink_err e;;
      e <- time_anf "Uncurry" (uncurry_top (cps anf_opts)) e ;;
      e <- time_anf "Inline uncurry wrappers" (inline_uncurry next_var 10 100) e ;;
      e <- (if inl_before anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if (do_lambda_lift anf_opts) then
              time_anf "Lambda lift" (lambda_lift (args anf_opts) (no_push anf_opts) (inl_wrappers anf_opts)) e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- time_anf "Closure conversion and hoisting" (closure_conversion_hoist clo_tag clo_ind_tag) e ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_after anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if dpe anf_opts then
              time_anf "Dead param elim" dead_param_elim.DPE e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_known anf_opts then
              time_anf "Inline known functions inside wrappers" (inline_lifted next_var 10 1000) e
            else id_trans e) ;;
      ret e. 


    Definition run_anf_pipeline (t : LambdaANF_FullTerm) : error LambdaANF_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := (M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1)%positive in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv (M.empty nat) nil
      in
      let (res, c_data') := anf_pipeline e0 c_data in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling LambdaANF program: " ++ s)%bs, "")
      | compM.Ret e =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, _, log) := c_data' in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end%positive.
    
  End Pipeline.


  (* ANF/Lambda-lifting Configurations for measuring performance. Passed through the anf_conf flag.

0: (DEFAULT)
   - LL: agressive inlining of wrappers at known call cites (always the known function is called)
   - do not inline  wrappers
   - fvs live across 0 calls
1: Like 0, but conservative inlining
2: Like 0, but inline known calls inside wrappers
3: Like 0, but like across 0 call
4: Like 0, but like across 2 calls
5: Like 0, but like across 10 calls
6: Like 0, but do not perform inline/shrink loop before CC
7: Like 0, but do not perform inline/shrink loop after CC
8: Like 0, but do not perform inline/shrink at all
9: Like 0, but non-selective lambda lifting
   *)

  Open Scope nat.
  
  Definition make_anf_options (opts : Options) : anf_options :=
    let '(inl_wrappers, inl_known, no_push, inl_before, inl_after) :=
        let default := (true, false, 1, true, true) in 
        match anf_conf opts with
        | 0 => default
        | 1 => (false, false, 1, true, true)
        | 2 => (true, true, 1, true, true)
        | 3 => (true, false, 0, true, true)
        | 4 => (true, false, 2, true, true)
        | 5 => (true, false, 10, true, true)
        | 6 => (true, false, 1, false, true)
        | 7 => (true, false, 1, true, false)
        | 8 => (true, false, 1, false, false)
        | 9 => (true, false, 1000, true, true)
        | _ => default
        end
    in
    {| time := Pipeline_utils.time opts;
       cps  := negb (Pipeline_utils.direct opts);
       do_lambda_lift := (1 <=? o_level opts);
       args := if anf_conf opts =? 9 then 1000 else Pipeline_utils.c_args opts;
       no_push := no_push; 
       inl_wrappers := inl_wrappers;
       inl_known    := inl_known;
       inl_before   := inl_before;
       inl_after    := inl_after;
       dpe          := true;
    |}.


  Definition compile_LambdaANF : CertiCoqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src => 
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiCoqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.


  Definition compile_LambdaANF_debug : CertiCoqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiCoqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.

End IDENT.
