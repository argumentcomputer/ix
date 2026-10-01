import Compilatrix.Anf.Proof.Pass.Basic
import Compilatrix.Anf.Inline
import Compilatrix.Anf.Proof.Lang

/-! # P3 inlining is correct

An inline round walks each listed caller's body under the configuration
that inlines its listed callees, all against the program at the start of the
round; the other globals are kept. Every round is therefore a walk pass
(`WalkProg`) whose valid configurations read the round's input program, so
the output refines the input for **every** oracle (`round_refines`, M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Inline.Proof

open Compilatrix.Anf.PassProof
open Walk (Cfg)

/-- The round's configurations: the input program, no redirection. -/
def V (P : Program) : Cfg → List Val → List Val → Prop := fun C _ _ => C.prog = P ∧ C.redirect = none

/-- A global after the round (itself if not a listed caller, or if its walk
fails). -/
def after (P : Program) (r : Round) (g : GlobalId) (gd : GDef) : GDef :=
  match r.lookup g with
  | some cs@(_ :: _) =>
    match (Walk.global { prog := P, inline := cs } gd).run {} with
    | .ok (gd', _) => gd'
    | .error _ => gd
  | _ => gd

variable {P : Program} {r : Round}

theorem after_walked (g : GlobalId) (gd : GDef) : WalkProof.Walked (V P) gd (after P r g gd) := by
  unfold after
  split
  · split
    · next gd' f h => exact WalkProof.walked_global h ⟨rfl, rfl⟩
    · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩

/-- What a successful round computes. -/
theorem round_global {Q : Program} {f : Walk.Fires} (h : round P r = .ok (Q, f)) :
    Q.roots = P.roots ∧ Q.known = P.known ∧ Q.size = P.size ∧
      ∀ g, Q.global? g = if g < P.size then (P.global? g).map (after P r g) else none := by
  unfold round at h
  obtain ⟨rs, hrs, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  refine ⟨rfl, rfl, rfl, fun g => ?_⟩
  obtain ⟨hlen, hall⟩ := Lam.ModesOk.mapM_ok hrs
  have hrs' : (rs.map fun (x : GlobalId × GDef × Walk.Fires) => (x.1, x.2.1)) =
      P.globalList.map fun q => (q.1, after P r q.1 q.2) := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
    cases hj : P.globalList[j]? with
    | none =>
      have : rs[j]? = none := by rw [List.getElem?_eq_none_iff] at hj ⊢; omega
      simp [this]
    | some q =>
      obtain ⟨y, hy, hf⟩ := hall j q hj
      rw [hy, Option.map_some, Option.map_some]
      obtain ⟨g', gd⟩ := q
      simp only at hf ⊢
      have hafter : after P r g' gd = y.2.1 ∧ y.1 = g' := by
        unfold after
        split at hf
        · next hd tl hcs =>
          obtain ⟨⟨gd', f'⟩, hw, hret⟩ := Lam.ModesOk.bind_ok hf
          cases hret
          simp [hcs, Lam.ModesOk.mapError_ok hw]
        · next hcs =>
          cases hf
          split
          · next hd tl hcs' => exact (hcs _ _ hcs').elim
          · exact ⟨rfl, rfl⟩
      rw [hafter.1, hafter.2]
  show (Src.NatMap.ofList (rs.map fun (x : GlobalId × GDef × Walk.Fires) => (x.1, x.2.1))).get? g = _
  rw [hrs']
  exact get?_ofList_globalList P (after P r) g

/-- **P3 is correct**: every round the oracle asks for refines its input,
and keeps its ids `0 … size - 1`. -/
theorem round_refines (h0 : P.WF) {Q : Program} {f : Walk.Fires} (h : round P r = .ok (Q, f)) :
    Q.WF ∧ Sem.Refines P Q := by
  obtain ⟨hroots, hknown, hsize, hQ⟩ := round_global h
  refine ⟨wf_of_mapped hsize hQ h0, WalkProof.WalkProg.refines (Valid := V P)
    { roots := hroots, known := hknown
      globals := fun g gd hg => ⟨after P r g gd, by rw [hQ, if_pos (h0.1 g gd hg), hg]; rfl, after_walked g gd⟩
      suffix := fun _ _ _ _ _ hV _ _ => hV
      cknown := fun C _ _ hV => by rw [hV.1]
      cglob := fun C _ _ hV g => by rw [hV.1]
      cbody := fun C _ _ hV g _ => by rw [hV.1]
      inl := fun C _ _ _ hV => ⟨hV.1, rfl⟩
      noRed := fun C _ _ hV => hV.2 }⟩


/-- P3 as a pass: the certificate is the round (the oracle's choice); the
ids are `0 … size - 1` before and after. -/
def inlinePass : Sem.Transform Program Program where
  name := "P3 inline"
  Cert := Round
  pre P := P.WF
  run P r := (round P r).map (·.1)
  post Q := Q.WF
  correct P r Q h0 h := by
    cases hr : round P r with
    | error e => rw [hr] at h; cases h
    | ok x =>
      rw [hr] at h
      cases h
      exact round_refines h0 hr

/-! ## The traced shape (decision D-1) -/

theorem round_refines_traced (h0 : P.WF) {Q : Program} {f : Walk.Fires}
    (h : round P r = .ok (Q, f)) : Sem.TRefines P Q :=
  Sem.Refines.ofPure (round_refines h0 h).2

/-- P3 as a traced pass. -/
def inlineTPass : Sem.TTransform Program Program := inlinePass.lift

end Compilatrix.Anf.Inline.Proof
