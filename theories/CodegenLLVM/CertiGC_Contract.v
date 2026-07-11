(** * CertiGC_Contract — the [garbage_collect] specification we ADOPT from CertiGC.

    CertiGC (CertiGraph/CertiGC, Wang–Cao–Mohan–Hobor et al.) is a VST-verified
    generational copying collector for CertiRocq — the very [gc_stack.c] our VIR
    backend links and calls.  Rather than leave [garbage_collect] as an opaque
    axiom, we adopt CertiGC's *proven* contract as a foreign-function interface
    assumption (the standard "verified component across an FFI boundary" story:
    CertiGC proves it in VST over CompCert's C memory; we consume it, stated over
    Vellvm's memory, at the call boundary).

    The contract has two halves.  The PRECONDITION is exactly what the
    shadow-stack root-registration pass (see [Flatten]/[LambdaANF_to_LLVM] GC
    safepoints) must establish: every live value is reachable as a root through
    the [tinfo->fp] frame chain, and [tinfo->nalloc = n].  The POSTCONDITION is
    what CertiGC guarantees: the collector may RELOCATE objects (it copies), but
    (i) it frees at least [n] words, (ii) it updates the roots to the relocated
    addresses, and — the fact our [Econstr_case] needs — (iii) it PRESERVES the
    value-representation of every root, up to that relocation.

    We state it parametrically over the proof's memory ([Mem]), address ([Addr]),
    root-set, the [words_free]/[roots_registered] predicates, and the
    value-representation relation [ReprVal].  Instantiating [Mem := memory_stack],
    [ReprVal := repr_val_LambdaANF_LLVM], etc. yields the concrete assumption that
    discharges the GC half of the current [refinement_runs] axiom. *)

From Stdlib Require Import List. Import ListNotations.

Section CertiGC_Contract.

  Variable Mem  : Type.                 (* Vellvm [memory_stack] *)
  Variable Addr : Type.                 (* Vellvm [addr] *)
  Variable Val  : Type.                 (* source value: [cps.val] *)

  (* the shadow-stack roots live in [m], enumerated through [tinfo->fp] *)
  Variable roots_registered : Mem -> Addr (* tinfo *) -> list Addr -> Prop.
  (* [tinfo->nalloc = n] *)
  Variable nalloc_set       : Mem -> Addr -> nat -> Prop.
  (* the collector ran and returned, taking [m] to [m'] *)
  Variable gc_runs          : Mem -> Addr -> Mem -> Prop.
  (* at least [n] words are free after collection *)
  Variable words_free       : Mem -> Addr -> nat -> Prop.
  (* value representation of a source value at an address in a memory *)
  Variable ReprVal          : Mem -> Val -> Addr -> Prop.

  (** The precondition the mutator (our generated code + shadow stack) must
      establish before calling [garbage_collect]. *)
  Definition gc_pre (m : Mem) (tinfo : Addr) (roots : list Addr) (n : nat) : Prop :=
    roots_registered m tinfo roots /\ nalloc_set m tinfo n.

  (** CertiGC's proven contract, adopted as an FFI assumption.  [reloc] is the
      relocation CertiGC's copying phase computes; it is the identity on
      already-tenured objects and moves nursery survivors. *)
  Definition CertiGC_spec : Prop :=
    forall (m : Mem) (tinfo : Addr) (roots : list Addr) (n : nat),
      gc_pre m tinfo roots n ->
      exists (m' : Mem) (reloc : Addr -> Addr),
        gc_runs m tinfo m'
        /\ words_free m' tinfo n
        /\ (* roots are updated to their relocated addresses *)
           (forall r, In r roots -> roots_registered m' tinfo (map reloc roots))
        /\ (* THE fact [Econstr_case] consumes: value-representation of every
              live root is preserved, up to relocation *)
           (forall (v : Val) (r : Addr),
              In r roots -> ReprVal m v r -> ReprVal m' v (reloc r)).

End CertiGC_Contract.

(** To DISCHARGE the GC half of the current [refinement_runs] axiom, instantiate
    the section variables with the Vellvm/proof concretes
    ([Mem := memory_stack], [Addr := addr], [Val := cps.val],
    [ReprVal := fun m v a => repr_val_LambdaANF_LLVM … v m (DVALUE_Addr a)], …)
    and assume [CertiGC_spec …] — an assumption BACKED BY CertiGC's VST proof,
    not an unjustified axiom.  The remaining gap to a fully axiom-free result is
    the cross-memory-model bridge (CompCert-C memory ↔ Vellvm memory), which is
    orthogonal and flagged as future work. *)
