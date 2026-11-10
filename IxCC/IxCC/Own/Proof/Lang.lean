import IxCC.Own.Proof.Refines
import IxCC.Fir.Proof.Lang

/-! # Own as a language, and the immortal embedding as a pass

Own programs run under the immortal policy from an export on `Nat` inputs,
from the empty heap, applied as Anf applies a root (`Sem.entryRun`); a
value is observed through the Fir value it denotes in its heap (`obsV`).
Through `Lang.instTLang` it is also a traced language (decision D-1).

`immortal_refines_lang`: a Fir program whose `Bool` pins have no fields is
refined by its immortal embedding on every input (`Own.immortal_refines`
for the exact arity). `immortalPass` packages it as a pass, `immortalTPass`
as a traced one. -/

set_option autoImplicit false

namespace IxCC.Own

open IxCC.Sem (Result ClockMono Obs Lang Sim Forall2)
open IxCC.Own.Proof

/-- `Nat` inputs as Own values. -/
def litArgs (ns : List Nat) : List RVal := ns.map fun n => .lit (.nat n)

/-- The observation of an Own value in its heap: the Fir value it denotes,
observed as Anf observes it. -/
def obsV (p : RVal × Heap) : Option Obs := (p.2.value? p.1).bind Fir.obsV

/-- A run of export `i.1` on the `Nat` inputs `i.2` under the immortal
policy from the empty heap, applied as Anf applies a root. -/
def ownRun (q : Program) (i : Nat × List Nat) (k : Nat) : Result (RVal × Heap) :=
  match q.exports[i.1]? with
  | some f =>
    match q.fun? f with
    | some fd => Sem.entryRun fd.params.length (.erased, {}) (fun ns k => run .immortal q k f (litArgs ns) {}) i.2 k
    | none => .stuck
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := RVal × Heap
  run := ownRun
  mono q i := by
    unfold ownRun
    split
    · split
      · exact Sem.entryRun_mono (fun ns => run_mono .immortal q _ _ _) _
      · exact ClockMono.const _
    · exact ClockMono.const _
  obs := obsV

theorem lang_run (q : Program) (i : Nat × List Nat) : Lang.run q i = ownRun q i := rfl

theorem obsV_den {H : Heap} {v : RVal} {w : Fir.Val} (h : Den H v w) : obsV (v, H) = Fir.obsV w := by
  simp only [obsV, show H.value? v = some w from h, Option.bind_some]

theorem obsV_erased (H : Heap) : obsV (.erased, H) = none := by
  rw [obsV_den (den_erased H)]; rfl

theorem dens_lits (H : Heap) (ns : List Nat) : Forall2 (Den H) (litArgs ns) (Fir.litArgs ns) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih => exact .cons (den_lit H _) ih

theorem immortalOk_empty : ({} : Heap).immortalOk = true := rfl

/-- **The immortal embedding refines**: on every input. -/
theorem immortal_refines_lang {F : Fir.Program} (hb : BoolsOk F) : Sem.Refines F (immortal F) := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨id, ?_⟩
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Fir.firRun F (r, ns)) (ownRun (immortal F) (r, ns))
  unfold Fir.firRun ownRun
  have hex : (immortal F).exports = F.exports := rfl
  simp only [hex]
  cases hr : F.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only
    rw [immortal_fun?]
    cases hf : F.fun? f with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      simp only [Option.map_some, immFun, List.length_map]
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact (immortal_refines hb f immortalOk_empty (dens_lits {} ns)).mono fun w p hw => by
          show Fir.obsV w = obsV p
          rw [obsV_den hw.1]
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := Lang.ObsEq (S := Fir.Program) (T := Program))
              (show Fir.obsV .erased = obsV (.erased, {}) by rw [obsV_erased]; rfl)
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := Lang.ObsEq (S := Fir.Program) (T := Program))
              (show Fir.obsV .erased = obsV (.erased, {}) by rw [obsV_erased]; rfl) (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          have hd : Forall2 (Den {}) (litArgs (ns.take fd.params.length)) (Fir.litArgs (ns.take fd.params.length)) :=
            dens_lits {} _
          exact Sim.bindStuck (R := ImmRes {}) (g := fun _ _ => .stuck)
            (immortal_refines hb f immortalOk_empty hd) fun _ _ _ => rfl

/-- The immortal embedding as a pass: it needs the `Bool` pins
without fields and the names the Own → Cfg lowering needs (both of which
`Fir.lower`'s output has, `Cfg.Proof.immortal_good`), and keeps the names. -/
def immortalPass (P : Fir.Program → Prop) (hP : ∀ F, P F → BoolsOk F) (Q : Program → Prop)
    (hQ : ∀ F, P F → Q (immortal F)) : Sem.Transform Fir.Program Program where
  name := "Own.immortal"
  pre := P
  run F _ := .ok (immortal F)
  post := Q
  correct F _ q hF h := by
    cases h
    exact ⟨hQ F hF, immortal_refines_lang (hP F hF)⟩

/-- `immortal_refines_lang` in the traced shape (decision D-1). -/
theorem immortal_refines_traced_lang {F : Fir.Program} (hb : BoolsOk F) : Sem.TRefines F (immortal F) :=
  Sem.Refines.ofPure (immortal_refines_lang hb)

end IxCC.Own
