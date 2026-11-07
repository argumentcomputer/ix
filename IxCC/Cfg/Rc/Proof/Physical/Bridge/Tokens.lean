import IxCC.Own.Plain.Proof.State
import IxCC.Own.Plain.Proof.Drops
import IxCC.Cfg.Rc.Proof.State
import IxCC.Cfg.Rc.Proof.Physical.Placement

/-! Concrete idle source/Cfg token boundary. No execution effect, desired
simulation, or liveness of every stale environment entry is assumed. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Suspended callers identify their actual Cfg frames and exactly which
lexical variables still own tokens. Remaining stale bindings own nothing.
The physical frame correspondence is recorded, not a native cursor theorem. -/
structure SavedCaller (addresses : AddressMap) where
  frame : Cfg.Frame
  destination : Fir.Var
  live : List Fir.Var
  roots : List RVal
  exactRoots : Own.Plain.EnvRoots frame.env live roots
  target : Lir.Frame
  bound : Nat
  registers : Cfg.Rc.Native.EnvWordsBelow addresses bound frame.env target.env

def savedRoots {addresses : AddressMap} (saved : List (SavedCaller addresses)) : List RVal :=
  saved.flatMap (·.roots)

def savedStack {addresses : AddressMap} (saved : List (SavedCaller addresses)) :
    List (Cfg.Frame × Fir.Var) := saved.map fun s => (s.frame, s.destination)

/-- This is the token/denotation projection of H1's full State. Join views
remain in the original H1 state; no unsupported reconstruction after dropping
a captured variable is claimed by this smaller boundary. -/
structure Tokens (H : Heap) (external : Nat → Nat) (held : List RVal)
    (live : List Fir.Var) (ρf : Fir.Env) (ρo : Own.Env) (roots : List RVal) : Prop where
  den : Own.Plain.EnvDen H live ρf ρo
  exactRoots : Own.Plain.EnvRoots ρo live roots
  balance : Balance H (holdRoots external held) roots
  distinct : live.Nodup

def Tokens.ofState {functions : Own.Plain.Signatures} {H : Heap} {external : Nat → Nat}
    {held roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (state : Own.Plain.State functions H (holdRoots external held) live ρf ρo roots joins Jf Jo) :
    Tokens H external held live ρf ρo roots :=
  ⟨state.env, state.roots, state.counts, state.distinct⟩

/-- Concrete syntax cursor, exact source-owned roots and real register words.
This is a local boundary relation, not a premise claiming whole-run reachability.
It must ultimately be constructed by the checked execution induction. -/
structure Boundary (F : Fir.Program) (P : Cfg.Rc.Program) (addresses : AddressMap)
    (saved : List (SavedCaller addresses)) (H : Heap) (external : Nat → Nat)
    (live : List Fir.Var) (ρf : Fir.Env) (ρo : Own.Env) (roots : List RVal)
    (fr : Cfg.Frame) (target : Lir.Frame) (bound : Nat)
    (joins : List Own.Plain.JEntry) (code : Own.Plain.Code) : Prop where
  tokens : Tokens H external (savedRoots saved) live ρf ρo roots
  cursor : Cfg.Rc.At F P fr ρo joins code
  registers : Cfg.Rc.Native.EnvWordsBelow addresses bound ρo target.env
  liveBound : ∀ x ∈ live, x < bound

/-- The consumed value is obtained from actual variable evaluation. Aliases
in the remaining live roots or suspended callers retain their multiplicity. -/
theorem Tokens.decrement {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots) :
    ∃ value remaining H', ρo.get? x = some value ∧ roots = value :: remaining ∧
      Own.Plain.evalAction ρo H (.dec x) = .ok H' ∧
      Tokens H' external held live ρf ρo remaining ∧
      (∀ root ∈ remaining, H.value? root = H'.value? root) ∧
      (∀ root ∈ held, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, lookup, exactRoots, equal⟩ := Own.Plain.envRoots_cons before.exactRoots
  have balance : Balance H (holdRoots external held) (value :: remaining) := equal ▸ before.balance
  obtain ⟨H', action, afterBalance, retained, externalValues⟩ :=
    Own.Plain.evalAction_dec_owned lookup balance
  have den : Own.Plain.EnvDen H live ρf ρo := fun y hy => before.den y (by simp [hy])
  refine ⟨value, remaining, H', lookup, equal, action,
    ⟨den.transport exactRoots retained, exactRoots, afterBalance, before.distinct.tail⟩,
    retained, ?_⟩
  intro root member
  exact externalValues root (held_external member)

end IxCC.Cfg.Rc.Proof.Physical.Bridge
