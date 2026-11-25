import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Environment
import IxCC.Cfg.Rc.Raw

/-!
# Raw 64-bit registers in the physical relation

A register the lowering's tables name raw (`Rt.Lower.Tables.rawVar fn`) holds the untagged word
`n` of a `Nat` literal `n < 2^64` (`RawVal`), not the tagged word `valueWord` gives. The tagged
relation (`FusedWords`) omits it, with the fused comparisons (`Omit`); `RawWords` states what
it holds. A function the flow check lets hold a raw register has no heap-cell instruction
(`Cfg.Rc.Raw.rawOk`), so in a function with one, `RawWords` is vacuous (`RawWords.of_noRaw`)
and `Omit` is the fused comparisons alone (`FusedWords.toFused`, `FusedWords.ofFused`).
-/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt.Rc.Procs
open IxCC.Rt.Lower (Tables)
open IxCC.Rt.Proof (Fused ListRel)

/-- Registers the tagged relation omits: the fused comparisons and the raw registers. -/
def Omit (T : Tables) (fn : Nat) (fd : Cfg.Fun) (y : Nat) : Prop :=
  Fused T fd y ∨ T.rawVar fn y = true

/-- The raw word of a value: a `Nat` literal below `2^64`, untagged. -/
def RawVal : Own.RVal → Lir.Word → Prop
  | .lit (.nat n), w => n < 2 ^ 64 ∧ w = UInt64.ofNat n
  | _, _ => False

theorem RawVal.lit {v : Own.RVal} {w : Lir.Word} (h : RawVal v w) :
    ∃ n, v = .lit (.nat n) ∧ n < 2 ^ 64 ∧ w = UInt64.ofNat n := by
  match v, h with
  | .lit (.nat n), ⟨lt, eq⟩ => exact ⟨n, rfl, lt, eq⟩

theorem RawVal.toNat {n : Nat} {w : Lir.Word} (h : RawVal (.lit (.nat n)) w) : w.toNat = n := by
  obtain ⟨lt, rfl⟩ := h
  exact Rt.Proof.toNat_ofNat_lt lt

/-- **What the raw registers hold.** -/
structure RawWords (R : Nat → Bool) (source : Own.Env) (target : Lir.Env) : Prop where
  word : ∀ {x v}, source.get? x = some v → R x = true → ∃ w, target[x]? = some w ∧ RawVal v w

namespace RawWords

variable {R : Nat → Bool} {source : Own.Env} {target : Lir.Env}

theorem empty : RawWords R .leaf target :=
  ⟨fun lookup _ => by cases lookup⟩

/-- No register is raw. -/
theorem of_noRaw (h : ∀ y, R y = false) : RawWords R source target :=
  ⟨fun _ raw => by rw [h] at raw; cases raw⟩

/-- Raw registers keep their words where the target keeps its registers. -/
theorem agree (related : RawWords R source target) {target' : Lir.Env}
    (same : ∀ {x v}, source.get? x = some v → R x = true → target'[x]? = target[x]?) :
    RawWords R source target' :=
  ⟨fun lookup raw => by
    obtain ⟨w, hw, hv⟩ := related.word lookup raw
    exact ⟨w, (same lookup raw).trans hw, hv⟩⟩

theorem restrict (related : RawWords R source target) {env : Own.Env} (sub : EnvSub env source) :
    RawWords R env target :=
  ⟨fun lookup raw => related.word (sub _ _ lookup) raw⟩

/-- A binding of a register that is not raw, with every other register below the bound kept. -/
theorem insert_tagged (related : RawWords R source target) {bound : Nat}
    (dom : ∀ {y v}, source.get? y = some v → y < bound) {x : Nat} (notRaw : R x = false)
    (v : Own.RVal) {target' : Lir.Env} (same : ∀ y, y < bound → y ≠ x → target'[y]? = target[y]?) :
    RawWords R (source.insert x v) target' := by
  refine ⟨fun {y w} lookup raw => ?_⟩
  rw [Src.NatMap.get?_insert] at lookup
  split at lookup
  · rename_i e; subst e; rw [notRaw] at raw; cases raw
  · rename_i ne
    obtain ⟨u, hu, hv⟩ := related.word lookup raw
    exact ⟨u, (same y (dom lookup) ne).trans hu, hv⟩

/-- A binding of a raw register to its raw word, every other register below the bound kept. -/
theorem insert_raw (related : RawWords R source target) {bound : Nat}
    (dom : ∀ {y v}, source.get? y = some v → y < bound) {x : Nat} {v : Own.RVal} {w : Lir.Word}
    (rawVal : RawVal v w) {target' : Lir.Env} (bound' : target'[x]? = some w)
    (same : ∀ y, y < bound → y ≠ x → target'[y]? = target[y]?) :
    RawWords R (source.insert x v) target' := by
  refine ⟨fun {y u} lookup raw => ?_⟩
  rw [Src.NatMap.get?_insert] at lookup
  split at lookup
  · rename_i e; subst e; cases lookup; exact ⟨w, bound', rawVal⟩
  · rename_i ne
    obtain ⟨u', hu, hv⟩ := related.word lookup raw
    exact ⟨u', (same y (dom lookup) ne).trans hu, hv⟩

/-- A register at or above the bound changes nothing. -/
theorem temp (related : RawWords R source target) {bound : Nat}
    (dom : ∀ {y v}, source.get? y = some v → y < bound) {t : Nat} (ht : bound ≤ t) (u : Lir.Word) :
    RawWords R source (target.insert t u) :=
  related.agree fun lookup _ => Lir.env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (dom lookup) ht))

/-- A source binding of a register the target does not see (an omitted comparison), when it
is not raw. -/
theorem insert_dead (related : RawWords R source target) {x : Nat} (notRaw : R x = false)
    (v : Own.RVal) : RawWords R (source.insert x v) target := by
  refine ⟨fun {y w} lookup raw => ?_⟩
  rw [Src.NatMap.get?_insert] at lookup
  split at lookup
  · rename_i e; subst e; rw [notRaw] at raw; cases raw
  · exact related.word lookup raw

end RawWords

/-! ## The tagged relation over omitted registers -/

theorem omit_of_fused {T : Tables} {fn : Nat} {fd : Cfg.Fun} {y : Nat} (h : Fused T fd y) :
    Omit T fn fd y := .inl h

theorem FusedWords.ofFused {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Fused T fd) bound source target) :
    FusedWords addresses (Omit T fn fd) bound source target :=
  ⟨related.dom, fun lookup live => related.word lookup (fun h => live (.inl h))⟩

theorem FusedWords.toFused {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Omit T fn fd) bound source target)
    (noRaw : ∀ y, T.rawVar fn y = false) :
    FusedWords addresses (Fused T fd) bound source target :=
  ⟨related.dom, fun lookup live => related.word lookup (fun h => h.elim live (by rw [noRaw]; simp))⟩


end IxCC.Cfg.Rc.Proof.Physical.Bridge
