import Compilatrix.Anf.Proof.Walk.Level
import Compilatrix.Lam.Proof.ModesOk

/-! # The rewriting walk: programs of walked globals

A pass whose output keeps each global's parameters and either keeps its
body or replaces it by the walk of its body over its parameters
(`Walk.global`), under configurations that read the program as the source
does and redirect nothing, refines its input (`WalkProg.refines`): calls and
global values simulate at each bound by the walk's simulation (or the
fundamental lemma) one clock down (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf

namespace Program

theorem mem_globalList {P : Program} {g : GlobalId} {gd : GDef} :
    (g, gd) ∈ P.globalList ↔ g < P.size ∧ P.global? g = some gd := by
  unfold globalList
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨g', hg', gd', hgd, rfl, rfl⟩
    exact ⟨hg', hgd⟩
  · rintro ⟨hg, hgd⟩
    exact ⟨g, hg, gd, hgd, rfl, rfl⟩

theorem globalList_pairwise (P : Program) : P.globalList.Pairwise fun p p' => p.1 < p'.1 := by
  unfold globalList
  refine List.Pairwise.filterMap _ (fun a a' h b hb b' hb' => ?_) List.pairwise_lt_range
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨_, _, rfl⟩ := hb
  obtain ⟨_, _, rfl⟩ := hb'
  exact h

theorem globalList_keys_nodup (P : Program) : (P.globalList.map (·.1)).Nodup :=
  (List.pairwise_map.2 (globalList_pairwise P)).imp Nat.ne_of_lt

end Program

namespace WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg}

theorem factsOk_leaf (ρ' : List Val) : FactsOk Q Valid (.leaf : Src.NatMap Fact) ρ' :=
  fun l f h => by simp [Src.NatMap.get?] at h

variable (Valid) in
/-- A global of the target: the source global, or its body walked over its
parameters. -/
def Walked (gd gd' : GDef) : Prop :=
  gd'.ps = gd.ps ∧ (gd'.body = gd.body ∨ ∃ C fuel s s', Valid C [] [] ∧
    (Walk.walk C fuel { σ := Walk.entsOf (paramOpds 0 gd.ps.length) }
      { d := gd.ps.length, dj := 0, facts := .leaf } gd.body .ret).run s = .ok (gd'.body, s'))

theorem walked_global {C : Cfg} {gd gd' : GDef} {s s' : Fires}
    (h : (Walk.global C gd).run s = .ok (gd', s')) (hV : Valid C [] []) : Walked Valid gd gd' := by
  unfold Walk.global at h
  obtain ⟨body, s1, h1, h2⟩ := Walk.run_bind_ok h
  obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2
  exact ⟨rfl, .inr ⟨C, Walk.fuel, s, s1, hV, h1⟩⟩

variable (P Q Valid Xc) in
/-- A pass whose globals are walks of the source's (`Walked`), under
configurations that read the program as the source does and redirect
nothing. -/
structure WalkProg : Prop where
  roots : Q.roots = P.roots
  known : Q.known = P.known
  globals : ∀ g gd, P.global? g = some gd → ∃ gd', Q.global? g = some gd' ∧ Walked Valid gd gd'
  suffix : ∀ C ρ ρ' ρ₂ ρ'₂, Valid C ρ ρ' → ρ <:+ ρ₂ → ρ' <:+ ρ'₂ → Valid C ρ₂ ρ'₂
  cknown : ∀ C ρ ρ', Valid C ρ ρ' → C.prog.known = P.known
  cglob : ∀ C ρ ρ', Valid C ρ ρ' → ∀ g,
    (C.prog.global? g).map (·.ps.length) = (P.global? g).map (·.ps.length)
  cbody : ∀ C ρ ρ', Valid C ρ ρ' → ∀ g, C.inline.contains g = true → C.prog.global? g = P.global? g
  inl : ∀ C ρ ρ' ρ₂, Valid C ρ ρ' → Valid { C with inline := [], redirect := none } ρ₂ ρ'
  noRed : ∀ C ρ ρ', Valid C ρ ρ' → C.redirect = none

/-- A global's body against its target version, entered with related
arguments, at a bound below the walk's simulation and the fundamental
lemma. -/
theorem walked_body (H : WalkProg P Q Valid) {m : Nat} (hW : ∀ fuel, WalkAt P Q Valid Xc m fuel)
    (hF : Rel.FundAt P Q (WV Q Valid Xc) m) {gd gd' : GDef} (hwk : Walked Valid gd gd') {vs ws : List Val}
    (hvs : WVs Q Valid Xc vs ws) (hl : vs.length = gd.ps.length) :
    SimUpTo (WV Q Valid Xc) m (fun k => eval P k vs.reverse [] gd.body) (fun k => eval Q k ws.reverse [] gd'.body) := by
  obtain ⟨-, hb | ⟨C, fuel, s, s', hV, hrun⟩⟩ := hwk
  · rw [hb]; exact hF (pw_of hvs).reverse .nil gd.body
  · have hwl : ws.length = gd.ps.length := by rw [hvs.length, hl]
    have hp := paramOpds_val [] ws
    rw [hwl] at hp
    have henv := WEnv.pushOpds hp hvs.reverse (WEnv.nil (Q := Q) (Valid := Valid) (Xc := Xc) (C := C) (ρ' := ws.reverse ++ []))
    simp only [List.append_nil, paramOpds_length, List.length_nil] at henv hp
    have hk : KontW Q Valid Xc m .ret (fun v _ => .ok v) ws.reverse [] := ⟨_, rfl, fun x w hxw => SimUpTo.ok hxw⟩
    refine ((hW fuel).walk hrun vs.reverse [] ws.reverse [] _ [] _
      (H.suffix C [] [] _ _ hV List.nil_suffix List.nil_suffix) henv .nil (by simp [hwl]) rfl (factsOk_leaf _)
      ⟨fun i hi => by simp [List.getElem?_replicate] at hi, fun j hj => by simp at hj⟩ hk).congr
      (fun k => (Sem.Result.bind_pure _).symm) (fun _ => rfl)

theorem WalkProg.hyp (H : WalkProg P Q Valid) : Hyp P Q Valid noXc where
  known := H.known
  arity g gd hg := by
    obtain ⟨gd', hg', hps, -⟩ := H.globals g gd hg
    exact ⟨gd', hg', by rw [hps]⟩
  suffix := H.suffix
  cknown := H.cknown
  cglob := H.cglob
  cbody := H.cbody
  inl := H.inl
  call n hlow g vs ws hvs := by
    cases hP : P.global? g with
    | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
    | some gd =>
      obtain ⟨gd', hQ, hwk⟩ := H.globals g gd hP
      have hvl := hvs.length
      by_cases hl : vs.length = gd.ps.length
      · have hl' : ws.length = gd'.ps.length := by rw [hwk.1, hvl, hl]
        refine (SimUpTo.later fun m hm => walked_body H (hlow m (by omega)).1 (hlow m (by omega)).2.1 hwk
          (of_pw hvs) hl).congr (fun k => ?_) (fun k => ?_)
        · simp only [Result.ofOption, Result.bind_ok, callVal, hl, if_true]
        · rw [hQ]; simp only [Result.ofOption, Result.bind_ok, callVal, hl', if_true]
      · have hl' : ¬ ws.length = gd'.ps.length := by rw [hwk.1, hvl]; exact hl
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        simp only [Result.ofOption, Result.bind_ok, callVal, hl, if_false]
  glob n hlow g := by
    cases hP : P.global? g with
    | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
    | some gd =>
      obtain ⟨gd', hQ, hwk⟩ := H.globals g gd hP
      rw [hQ]
      simp only [Result.ofOption, Result.bind_ok]
      unfold globVal
      rw [hwk.1]
      cases hps : gd.ps with
      | nil =>
        refine SimUpTo.later fun m hm => ?_
        have := walked_body H (hlow m (by omega)).1 (hlow m (by omega)).2.1 hwk (.nil) (by simp [hps])
        exact this
      | cons p ps =>
        refine SimUpTo.ok ?_
        obtain ⟨-, hb | ⟨C, fuel, s, s', hV, hrun⟩⟩ := hwk
        · rw [hb]; exact .idc .nil .nil
        · rw [hps] at hrun
          exact .walkc (σP := Walk.entsOf (paramOpds 0 (p :: ps).length)) (σ0 := []) (live := [])
            (got := []) (got' := []) (oOf := fun _ => .box) (wOf := fun _ => .box) hV
            (by simpa using hrun) .nil (factsOk_leaf _)
            ⟨fun i hi => by simp [List.getElem?_replicate] at hi, fun j hj => by simp at hj⟩
            (by simp [Walk.entsOf, paramOpds_length]) (Nat.le_refl _) (by simp) (by simp) (by simp)
            (fun p hp => by omega) (fun p v hp => by omega)
            (fun q _ hq => by
              simp only [Walk.entsOf, List.getElem?_map, paramOpds_get _ _ hq, Option.map_some]
              simp)
            (fun _ _ _ _ _ hv => by simp at hv)
  red n _ C ρ ρ' r hV hr := by rw [H.noRed C ρ ρ' hV] at hr; cases hr
  xenter _ _ _ _ _ _ _ _ _ _ _ _ _ hx := hx.elim

/-- **A walk pass refines its input.** -/
theorem WalkProg.refines (H : WalkProg P Q Valid) : Sem.Refines P Q :=
  WalkProof.refines H.hyp H.roots

end WalkProof

end Compilatrix.Anf
