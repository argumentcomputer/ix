import Compilatrix.Lam.Erase.Proof.Build
import Compilatrix.Lam.Erase.Val
import Compilatrix.Lam.Readback
import Compilatrix.Src.Readback
import Compilatrix.Sem.Transform

/-! # Erasure is correct

`erase_correct`: a successful erasure of a program with well-formed
declarations (`ProgWF`) simulates each root at every clock (`Sem.Sim` with
the identity clock map: a Src result is matched by a related Lam result, a
trap by a trap, a Src timeout at clock `k` by a Lam timeout at `k`; a stuck
Src run imposes nothing). On first-order values the relation is erasure
itself (`readback_erase`: the Lam result is `eraseVal` of the Src result),
and first-order observations agree (`vr_obs`). With runs from a root on
`Nat` arguments as the languages' semantics, erasure refines the checked
Src program (`erase_refines`, through `Refines.of_sim`) (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels)
open Compilatrix.Sem (Result ClockMono SimUpTo Sim Obs Lang)

/-- **Erasure is correct**: every root of a successfully erased program with
well-formed declarations simulates, at every clock, from related
arguments. -/
theorem erase_correct {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) (wf : ProgWF (Input.ofProgram p ch)) :
    ∃ G : Key.GKey → GlobalId → Prop, Forall2 (fun c g => ∀ (xs : List Src.Value) (xs' : List Val),
        Forall2 (VR (Input.ofProgram p ch) G) xs xs' →
          Sim (VR (Input.ofProgram p ch) G) id (fun k => Src.run p k c xs)
            (fun k => Lam.run L k g xs'))
      (p.roots.map (·.2)) L.roots := by
  obtain ⟨G, hprog, hknown, hsucc, hroots⟩ := erase_spec h
  let S : Setting := ⟨p, ch, L, G, hprog, hknown, hsucc⟩
  exact ⟨G, Forall2.imp (fun c g hr xs xs' hx => Setting.run_correct (S := S) wf hr hx) hroots⟩

/-! ## First-order values -/

section Values

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

theorem eraseNth_of_getElem? : ∀ {j : Nat} {fs : List Src.Value} {a : Src.Value},
    fs[j]? = some a → eraseNth I j fs = eraseVal I a
  | 0, _ :: _, _, h => by simp at h; subst h; rfl
  | j + 1, _ :: fs, a, h => by
    simp only [List.getElem?_cons_succ] at h
    exact eraseNth_of_getElem? (fs := fs) h
  | _, [], _, h => by simp at h

theorem eraseVal_con (c : CId) (ls : Levels) (ps : List Src.Slot) (fs : List Src.Value) :
    eraseVal I (.con c ls ps fs) =
      match I.decl? c with
      | some (.quot .ctor ..) => eraseNth I 0 fs
      | some (.ctor _ _ ind _ _ _ _) =>
        match I.unbox? ind (Profile.normalize (Src.profileOf ls) (I.lvls c)) with
        | some j => eraseNth I j fs
        | none => (eraseKept I c (Profile.normalize (Src.profileOf ls) (I.lvls c)) 0 fs).map
            (.con (I.ctorKey c))
      | _ => none := by
  rw [eraseVal]; rfl

mutual

/-- On first-order values the related Lam value is the erasure. -/
theorem vr_eraseVal : ∀ {v : Src.Value} {v' : Val}, VR I G v v' → ∀ {w : Val},
    eraseVal I v = some w → w = v'
  | _, _, .lit, _, h => by rw [eraseVal] at h; cases h; rfl
  | _, _, .str, _, h => by rw [eraseVal] at h; cases h; rfl
  | _, _, .irr, _, h => by rw [eraseVal] at h; cases h; rfl
  | _, _, .quot hd ha, w, h => by
    rw [eraseVal_con, hd] at h
    exact vr_eraseVal ha (by simpa [eraseNth] using h)
  | _, _, .unboxed hd _ hu hj ha _, w, h => by
    rw [eraseVal_con, hd] at h
    dsimp only at h
    rw [Input.unbox?_prof, hu] at h
    dsimp only at h
    rw [eraseNth_of_getElem? hj] at h
    exact vr_eraseVal ha h
  | _, _, .con (c := c) hd _ hu hk, w, h => by
    rw [eraseVal_con, hd] at h
    dsimp only at h
    rw [Input.unbox?_prof, hu] at h
    dsimp only at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨fs'', hfs, rfl⟩ := h
    rw [keptR_eraseKept hk hfs]
  | _, _, .clo .., _, h => by rw [eraseVal] at h; cases h
  | _, _, .pap .., _, h => by rw [eraseVal] at h; cases h

theorem keptR_eraseKept : ∀ {c : CId} {i : Nat} {fs : List Src.Value} {fs' : List Val},
    KeptR I G c i fs fs' → ∀ {q : Profile} {ws : List Val}, eraseKept I c q i fs = some ws →
      ws = fs'
  | _, _, _, _, .nil, _, _, h => by rw [eraseKept] at h; cases h; rfl
  | c, i, _, _, .kept hk hv hr, q, ws, h => by
    rw [eraseKept] at h
    have hk' : I.kept c q i = true := by rw [Input.kept_prof]; exact hk
    cases hrest : eraseKept I c q (i + 1) _ with
    | none => rw [hrest] at h; cases h
    | some rest =>
      rw [hrest] at h
      simp only [Option.bind_some, hk', ↓reduceIte] at h
      cases hf : eraseVal I _ with
      | none => rw [hf] at h; cases h
      | some w =>
        rw [hf] at h
        simp at h
        subst h
        rw [vr_eraseVal hv hf, keptR_eraseKept hr hrest]
  | c, i, _, _, .drop hk _ hr, q, ws, h => by
    rw [eraseKept] at h
    have hk' : I.kept c q i = false := by rw [Input.kept_prof]; exact hk
    cases hrest : eraseKept I c q (i + 1) _ with
    | none => rw [hrest] at h; cases h
    | some rest =>
      rw [hrest] at h
      simp [hk'] at h
      subst h
      exact keptR_eraseKept hr hrest

end

end Values

/-- **Readback on first-order results**: when a Src value has an erasure,
the related Lam value is it (so every readback of the Lam result is the
readback of the erased Src result). -/
theorem readback_erase {I : Input} {G : Key.GKey → GlobalId → Prop} {v : Src.Value} {v' : Val}
    (h : VR I G v v') {w : Val} (he : eraseVal I v = some w) (L : Program) :
    Lam.readback L v' = Lam.readback L w := by
  rw [vr_eraseVal h he]

/-- A `Nat` result reads back the same on both sides. -/
theorem readback_erase_nat {I : Input} {G : Key.GKey → GlobalId → Prop} {n : Nat} {v' : Val}
    (h : VR I G (.lit n) v') (L : Program) (p : Src.Program)
    (keep : CId → Levels → Nat → Bool) :
    Lam.readback L v' = Src.readback p keep (.lit n) := by
  cases h
  rw [Lam.readback, Src.readback]

/-! ## Observations and refinement -/

mutual

/-- A program-independent observation of a Lam value: literals, and
constructor trees tagged by the source constructor. -/
def obsV : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .con (.src c) fs => (obsList fs).map (.ctor c)
  | _ => none

def obsList : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match obsV v, obsList vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

section Obs

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

mutual

/-- Related values observe the same, the Src one through erasure. -/
theorem vr_obs : ∀ {v : Src.Value} {v' : Val}, VR I G v v' → (eraseVal I v).bind obsV = obsV v'
  | _, _, .lit => by rw [eraseVal]; rfl
  | _, _, .str => by rw [eraseVal]; rfl
  | _, _, .irr => by rw [eraseVal]; rfl
  | _, _, .quot hd ha => by
    rw [eraseVal_con, hd]
    exact vr_obs ha
  | _, _, .unboxed hd _ hu hj ha _ => by
    rw [eraseVal_con, hd]
    dsimp only
    rw [Input.unbox?_prof, hu]
    dsimp only
    rw [eraseNth_of_getElem? hj]
    exact vr_obs ha
  | _, _, .con (c := c) (ls := ls) hd _ hu hk => by
    rw [eraseVal_con, hd]
    dsimp only
    rw [Input.unbox?_prof, hu]
    dsimp only
    have := keptR_obs hk (q := Profile.normalize (Src.profileOf ls) (I.lvls c))
    cases he : eraseKept I c (Profile.normalize (Src.profileOf ls) (I.lvls c)) 0 _ with
    | none =>
      rw [he] at this
      simp only [Option.map_none, Option.bind_none, Input.ctorKey, obsV]
      rw [← this]
      rfl
    | some ws =>
      rw [he] at this
      simp only [Option.map_some, Option.bind_some, Input.ctorKey, obsV]
      rw [← this]
      rfl
  | _, _, .clo .. => by rw [eraseVal]; rfl
  | _, _, .pap .. => by rw [eraseVal]; rfl

theorem keptR_obs : ∀ {c : CId} {i : Nat} {fs : List Src.Value} {fs' : List Val},
    KeptR I G c i fs fs' → ∀ {q : Profile}, (eraseKept I c q i fs).bind obsList = obsList fs'
  | _, _, _, _, .nil, _ => by rw [eraseKept]; rfl
  | c, i, _, _, .kept hk hv hr, q => by
    rw [eraseKept]
    have hk' : I.kept c q i = true := by rw [Input.kept_prof]; exact hk
    have ih := keptR_obs hr (q := q)
    have hvo := vr_obs hv
    rw [obsList]
    cases hrest : eraseKept I c q (i + 1) _ with
    | none =>
      rw [hrest] at ih
      simp only [Option.bind_none] at ih ⊢
      rw [← ih]
      cases obsV _ <;> rfl
    | some rest =>
      rw [hrest] at ih
      simp only [Option.bind_some, hk', ↓reduceIte]
      cases hf : eraseVal I _ with
      | none =>
        rw [hf] at hvo
        simp only [Option.bind_none] at hvo
        rw [← hvo]
        simp
      | some w =>
        rw [hf] at hvo
        simp only [Option.bind_some] at hvo ih
        rw [← hvo, ← ih]
        simp [obsList]
  | c, i, _, _, .drop hk _ hr, q => by
    rw [eraseKept]
    have hk' : I.kept c q i = false := by rw [Input.kept_prof]; exact hk
    have ih := keptR_obs hr (q := q)
    cases hrest : eraseKept I c q (i + 1) _ with
    | none => rw [hrest] at ih; simp only [Option.bind_none] at ih ⊢; exact ih
    | some rest =>
      rw [hrest] at ih
      simp only [Option.bind_some, hk', Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      exact ih

end

end Obs

/-- A Src program with its checked annotation: what erasure reads. -/
structure CheckedProgram where
  p : Src.Program
  ch : Src.Relevance.Checked

/-- A run's input: a root by its index, and `Nat` arguments. -/
abbrev RunInput := Nat × List Nat

/-- SrcEval from a root, the value paired with the erasure input. -/
def srcRun (s : CheckedProgram) (i : RunInput) (k : Nat) : Result (Input × Src.Value) :=
  match s.p.roots[i.1]? with
  | some (_, c) =>
    (Src.run s.p k c (i.2.map .lit)).map fun v => (Input.ofProgram s.p s.ch, v)
  | none => .stuck

/-- Lam from a root. -/
def lamRun (L : Program) (i : RunInput) (k : Nat) : Result Val :=
  match L.roots[i.1]? with
  | some g => Lam.run L k g (i.2.map fun n => .lit (.nat n))
  | none => .stuck

theorem ClockMono.map' {α β : Type} {c : Nat → Result α} (h : ClockMono c) (f : α → β) :
    ClockMono fun k => (c k).map f :=
  h.bind fun _ => ClockMono.const _

instance : Lang RunInput CheckedProgram where
  Val := Input × Src.Value
  run := srcRun
  mono s i := by
    unfold srcRun
    split
    · exact ClockMono.map' (Src.run_mono s.p _ _) _
    · exact ClockMono.const _
  obs x := (eraseVal x.1 x.2).bind obsV

instance : Lang RunInput Program where
  Val := Val
  run := lamRun
  mono L i := by
    unfold lamRun
    split
    · exact Lam.run_mono L _ _
    · exact ClockMono.const _
  obs := obsV

theorem Sim.map_left {α β γ : Type} {R : α → β → Prop} {R' : γ → β → Prop} (f : α → γ)
    (hR : ∀ a b, R a b → R' (f a) b) {c₁ : Nat → Result α} {c₂ : Nat → Result β}
    (h : Sim R id c₁ c₂) : Sim R' id (fun k => (c₁ k).map f) c₂ where
  forward k hk := by
    have hk' : c₁ k ≠ .timeout := fun e => hk (by simp [e, Result.map, Result.bind])
    obtain ⟨k', hr⟩ := h.forward k hk'
    refine ⟨k', ?_⟩
    show Sem.Result.Refines R' ((c₁ k).map f) (c₂ k')
    revert hr hk'
    generalize c₁ k = r
    generalize c₂ k' = r'
    intro hk' hr
    cases hr with
    | ok hv => exact .ok (hR _ _ hv)
    | timeout => exact absurd rfl hk'
    | trap => exact .trap
    | stuck => exact .stuck
    | resource failure => exact .resource failure
  timeout k hk := by
    apply h.timeout k
    cases e : c₁ (id k) <;> simp_all [Result.map, Result.bind]

theorem Sim.stuck {α β : Type} {R : α → β → Prop} (c₂ : Nat → Result β) :
    Sim R id (fun _ => (.stuck : Result α)) c₂ where
  forward _ _ := ⟨0, .stuck⟩
  timeout _ h := nomatch h

/-- **Erasure refines the checked program**: on every root and `Nat`
arguments, the erased program's behaviour refines SrcEval's up to equal
first-order observations. -/
theorem erase_refines {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) (wf : ProgWF (Input.ofProgram p ch)) :
    Sem.Refines (⟨p, ch⟩ : CheckedProgram) L := by
  obtain ⟨G, hroots⟩ := erase_correct h wf
  refine Sem.Refines.of_sim (R := fun x w => x.1 = Input.ofProgram p ch ∧
    VR (Input.ofProgram p ch) G x.2 w) (fun x w ⟨e, hv⟩ => ?_) fun i => ⟨id, ?_⟩
  · show (eraseVal x.1 x.2).bind obsV = obsV w
    rw [e]
    exact vr_obs hv
  · show Sim _ id (srcRun ⟨p, ch⟩ i) (lamRun L i)
    have hlen := hroots.length
    simp only [List.length_map] at hlen
    unfold srcRun lamRun
    dsimp only
    cases hr : p.roots[i.1]? with
    | none =>
      have : L.roots[i.1]? = none := by
        rw [List.getElem?_eq_none_iff] at hr ⊢
        omega
      rw [this]
      exact Sim.stuck _
    | some ac =>
      obtain ⟨a, c⟩ := ac
      have hc : (p.roots.map (·.2))[i.1]? = some c := by simp [hr]
      obtain ⟨g, hg, hsim⟩ := hroots.get hc
      rw [hg]
      dsimp only
      have hx : Forall2 (VR (Input.ofProgram p ch) G) (i.2.map Src.Value.lit)
          (i.2.map fun n => Val.lit (.nat n)) := by
        induction i.2 with
        | nil => exact .nil
        | cons n ns ih => exact .cons .lit ih
      exact Sim.map_left _ (fun v w hv => ⟨rfl, hv⟩) (hsim _ _ hx)

end Compilatrix.Lam.Erase.Proof
