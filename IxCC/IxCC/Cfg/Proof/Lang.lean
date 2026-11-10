import IxCC.Cfg.Proof.Correct
import IxCC.Own.Proof.Lang
import IxCC.Sem.Entry

/-! # Cfg as a language, and `Cfg.lower` as a pass

Cfg programs run under the immortal policy from an export on `Nat` inputs,
from the empty heap, applied as Anf applies a root (`Sem.entryRun`), with
Own's observation of a value in its heap. `Cfg.run` is clock monotone for
every program (its step bound grows with the clock, `ClockMono.runClocked`),
so this is a `Sem.Lang`, and through `Lang.instTLang` a traced one
(decision D-1).

`lower_refines`: an Own program with the properties `Cfg.lower_correct`
needs (`Good`) is refined by its lowering on every input. -/

set_option autoImplicit false

namespace IxCC.Cfg

open IxCC.Sem (Result ClockMono Obs Lang Sim)
open IxCC.Own (RVal Heap)
open IxCC.Cfg.Proof

/-- `Cfg.run` is clock monotone, for every program. -/
theorem run_clockMono (pol : Own.AllocPol) (P : Program) (f : Fir.FunId) (args : List RVal) (H : Heap) :
    ClockMono fun k => run pol P k f args H :=
  Sem.ClockMono.runClocked (step pol P) (fun hk => by unfold fuelFor; exact Nat.mul_le_mul_right _ (by omega))
    (.call f args [] H)

/-- A run of export `i.1` on the `Nat` inputs `i.2` under the immortal
policy from the empty heap, applied as Anf applies a root. -/
def cfgRun (C : Program) (i : Nat × List Nat) (k : Nat) : Result (RVal × Heap) :=
  match C.exports[i.1]? with
  | some f =>
    match C.fun? f with
    | some fd =>
      Sem.entryRun fd.params.length (.erased, {}) (fun ns k => run .immortal C k f (Own.litArgs ns) {}) i.2 k
    | none => .stuck
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := RVal × Heap
  run := cfgRun
  mono C i := by
    unfold cfgRun
    split
    · split
      · exact Sem.entryRun_mono (fun ns => run_clockMono .immortal C _ _ _) _
      · exact ClockMono.const _
    · exact ClockMono.const _
  obs := Own.obsV

theorem lang_run (C : Program) (i : Nat × List Nat) : Lang.run C i = cfgRun C i := rfl

/-- A lowered function's parameters are block 0's, the Own function's. -/
theorem function_params (f : Fir.FunId) {fd : Own.Fun} (h : fd.sig.params.length = fd.params.length) :
    (Lower.function f fd).params = fd.params := by
  obtain ⟨t, hb⟩ := block_zero f fd
  simp only [Fun.params]
  have : (Lower.function f fd).blocks.head? = some
      { params := fd.params.zip fd.sig.params, body := spine fd.body, term := t } := by
    rw [List.head?_eq_getElem?]; exact hb
  rw [this]
  exact zip_fst h

/-- **`Cfg.lower` refines** every `Good` Own program, on every input. -/
theorem lower_refines {q : Own.Program} (G : Good q) : Sem.Refines q (lower q) := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨id, ?_⟩
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Own.ownRun q (r, ns)) (cfgRun (lower q) (r, ns))
  unfold Own.ownRun cfgRun
  have hex : (lower q).exports = q.exports := rfl
  simp only [hex]
  cases hr : q.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only
    rw [lower_fun?]
    cases hf : q.fun? f with
    | none =>
      simp only [Option.map_none]
      split <;> exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      simp only [G.dense hf, ↓reduceIte, Option.map_some, function_params f (G.sigLen hf)]
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact (lower_correct G f _ _).mono fun _ _ h => by rw [h]; rfl
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := Lang.ObsEq (S := Own.Program) (T := Program)) rfl
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := Lang.ObsEq (S := Own.Program) (T := Program)) rfl (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (R := Eq) (g := fun _ _ => .stuck) (lower_correct G f _ _) fun _ _ _ => rfl

/-- `Cfg.lower` as a pass. -/
def lowerPass : Sem.Transform Own.Program Program where
  name := "Cfg.lower"
  pre := Good
  run q _ := .ok (lower q)
  post _ := True
  correct q _ C hq h := by
    cases h
    exact ⟨trivial, lower_refines hq⟩

/-- `lower_refines` in the traced shape (decision D-1). -/
theorem lower_refines_traced {q : Own.Program} (G : Good q) : Sem.TRefines q (lower q) :=
  Sem.Refines.ofPure (lower_refines G)

end IxCC.Cfg
