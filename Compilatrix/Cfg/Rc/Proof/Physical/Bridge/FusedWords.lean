import Compilatrix.Cfg.Rc.Proof.Physical.PublicationRegisters
import Compilatrix.Rt.Proof.Env

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native

/-- Dynamic-address register relation for the actual consumed function.
`D` names only omitted comparison results; lexical ownership is independent
of omission. All populated source names retain the real register bound. -/
structure FusedWords (addresses : AddressMap) (D : Nat → Prop) (bound : Nat)
    (source : Own.Env) (target : Lir.Env) : Prop where
  dom : ∀ {x value}, source.get? x = some value → x < bound
  word : ∀ {x value}, source.get? x = some value → ¬ D x →
    ∃ actual, valueWord addresses value = some actual ∧ target[x]? = some actual

namespace FusedWords
variable {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
  {source : Own.Env} {target : Lir.Env}

theorem empty : FusedWords addresses D bound .leaf target := by
  constructor
  · intro x value lookup
    cases lookup
  · intro x value lookup
    cases lookup

theorem of_full (related : EnvWordsBelow addresses bound source target)
    (dom : ∀ {x value}, source.get? x = some value → x < bound) :
    FusedWords addresses D bound source target :=
  ⟨dom, fun lookup _ => related _ _ (dom lookup) lookup⟩

/-- Full register coverage is recovered only when no populated source name
is omitted. The global fused cursor must retain the weaker relation. -/
theorem full (related : FusedWords addresses D bound source target)
    (present : ∀ {x value}, source.get? x = some value → ¬ D x) :
    EnvWordsBelow addresses bound source target :=
  fun _ _ _ lookup => related.word lookup (present lookup)

theorem marker (related : FusedWords addresses D bound source target)
    {dummy : Nat} (reserved : bound ≤ dummy) (value : Lir.Word) :
    FusedWords addresses D bound source (target.insert dummy value) := by
  refine ⟨related.dom, ?_⟩
  intro x v lookup live
  obtain ⟨actual, represented, register⟩ := related.word lookup live
  refine ⟨actual, represented, ?_⟩
  rw [Lir.env_insert_ne _ _ (by have := related.dom lookup; omega)]
  exact register

theorem bind (related : FusedWords addresses D bound source target)
    {x : Nat} {value : Own.RVal} {actual : Lir.Word} (real : x < bound)
    (represented : valueWord addresses value = some actual) :
    FusedWords addresses D bound (source.insert x value) (target.insert x actual) := by
  constructor
  · intro y v lookup
    rw [Src.NatMap.get?_insert] at lookup
    split at lookup
    · omega
    · exact related.dom lookup
  · intro y v lookup live
    by_cases equal : y = x
    · subst y
      rw [Src.NatMap.get?_insert_self] at lookup
      cases lookup
      exact ⟨actual, represented, Lir.env_insert_self ..⟩
    · rw [Src.NatMap.get?_insert_ne _ _ equal] at lookup
      obtain ⟨word, hw, hr⟩ := related.word lookup live
      refine ⟨word, hw, ?_⟩
      rw [Lir.env_insert_ne _ _ (Ne.symm equal)]
      exact hr

/-- Fusing a comparison changes the source map with zero target steps.
The omitted result is never claimed to occupy a physical register. -/
theorem bind_omitted (related : FusedWords addresses D bound source target)
    {x : Nat} (real : x < bound) (omitted : D x) (value : Own.RVal) :
    FusedWords addresses D bound (source.insert x value) target := by
  constructor
  · intro y v lookup
    rw [Src.NatMap.get?_insert] at lookup
    split at lookup
    · omega
    · exact related.dom lookup
  · intro y v lookup live
    by_cases equal : y = x
    · subst y
      exact False.elim (live omitted)
    · rw [Src.NatMap.get?_insert_ne _ _ equal] at lookup
      exact related.word lookup live

theorem placeFresh (related : FusedWords addresses D bound source target)
    {fresh : Nat} (bounded : Own.Plain.EnvBounded fresh source) (address : Lir.Word) :
    FusedWords (Compilatrix.Cfg.Rc.Native.placeFresh addresses fresh address) D bound source target := by
  refine ⟨related.dom, ?_⟩
  intro x value lookup live
  obtain ⟨actual, represented, register⟩ := related.word lookup live
  refine ⟨actual, ?_, register⟩
  rw [placeFresh_old (bounded x value lookup)]
  exact represented

theorem publish (related : FusedWords addresses D bound source target)
    {fresh x : Nat} (real : x < bound)
    (bounded : Own.Plain.EnvBounded fresh source) (address : Lir.Word) :
    FusedWords (Compilatrix.Cfg.Rc.Native.placeFresh addresses fresh address) D bound
      (source.insert x (.loc fresh)) (target.insert x address) :=
  (related.placeFresh bounded address).bind real (placeFresh_new addresses fresh address)

theorem agree (related : FusedWords addresses D bound source target)
    {target' : Lir.Env}
    (agreement : ∀ {x value}, source.get? x = some value → ¬ D x → target'[x]? = target[x]?) :
    FusedWords addresses D bound source target' := by
  refine ⟨related.dom, ?_⟩
  intro x value lookup live
  obtain ⟨actual, represented, register⟩ := related.word lookup live
  exact ⟨actual, represented, (agreement lookup live).trans register⟩
end FusedWords










end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
