import IxCC.Anf.Proof.Pass.Basic
import IxCC.Anf.Shrink
import IxCC.Anf.Proof.Lang

/-! # P2 shrink is correct

`Shrink.run` performs, per global, the certified number of rounds, each a
walk of the global's body under the shrink configuration of the *input*
program. Its output is reached from the input through stages: stage `i + 1`
applies one more round to the globals with more than `i` certified rounds
(`roundOn`); each stage's globals are walks of the previous stage's, under
a configuration that reads the program as every stage does (constructors,
arities), so each stage refines the previous (`WalkProg.refines`), and the
last stage has the output's globals. Hence every certificate the re-run
accepts gives a program that refines the input (`run_refines`). -/

set_option autoImplicit false

namespace IxCC.Anf.Shrink.Proof

open IxCC.Anf.PassProof
open Walk (Cfg)

variable (P0 : Program) (p : Params)

/-- Only the rounds' configuration is valid. -/
def V : Cfg → List Val → List Val → List (Val × Val) → Prop := fun C _ _ _ => C = cfg P0 p

/-- A global after a round, or itself if the round fails. -/
def roundOr (gd : GDef) : GDef :=
  match round P0 p gd with
  | .ok (gd', _) => gd'
  | .error _ => gd

/-- One round on the selected globals. -/
def roundOn (sel : GlobalId → Bool) (P : Program) : Program :=
  { P with
    globals := Src.NatMap.ofList (P.globalList.map fun q => (q.1, if sel q.1 then roundOr P0 p q.2 else q.2)) }

/-- What a round reads of a program agrees with the input. -/
structure Agree (P : Program) : Prop where
  known : P.known = P0.known
  roots : P.roots = P0.roots
  size : P.size = P0.size
  arity : ∀ g, (P.global? g).map (·.ps.length) = (P0.global? g).map (·.ps.length)
  below : P.GlobalsBelow
  disp : ∀ g gd, P0.global? g = some gd →
    (∃ ar m alts dflt, gd.key = .dispatch ar ∧ gd.body = .case (.var m) alts dflt ∧ m > 0 ∧ m + 1 = gd.ps.length) →
    P.global? g = some gd

/-- `j` rounds (or the global itself once a round fails). -/
def iter (gd : GDef) : Nat → GDef
  | 0 => gd
  | j + 1 => roundOr P0 p (iter gd j)

/-- The stages from the input to the output. -/
def stage (cert : Cert) : Nat → Program
  | 0 => P0
  | i + 1 => roundOn P0 p (fun g => decide (i < cert.getD g 0)) (stage cert i)

variable {P0 p}

theorem roundOr_walked (gd : GDef) : WalkProof.Walked (V P0 p) gd (roundOr P0 p gd) := by
  unfold roundOr round
  cases hd : Walk.isDispatchDef gd with
  | true =>
    simp only [↓reduceIte, pure, Except.pure]
    exact ⟨rfl, .inl rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · next gd' f h => exact WalkProof.walked_global h rfl
    · exact ⟨rfl, .inl rfl⟩

theorem roundOr_disp {gd : GDef} (hd : Walk.isDispatchDef gd = true) : roundOr P0 p gd = gd := by
  simp [roundOr, round, hd, pure, Except.pure]

theorem roundOr_ps (gd : GDef) : (roundOr P0 p gd).ps = gd.ps := (roundOr_walked gd).1

theorem roundOn_global (sel : GlobalId → Bool) (P : Program) (g : GlobalId) :
    (roundOn P0 p sel P).global? g =
      if g < P.size then (P.global? g).map (fun gd => if sel g then roundOr P0 p gd else gd) else none :=
  get?_ofList_globalList P (fun g gd => if sel g then roundOr P0 p gd else gd) g

theorem roundOn_walkProg {sel : GlobalId → Bool} {P : Program} (h : Agree P0 P) :
    WalkProof.WalkProg P (roundOn P0 p sel P) (V P0 p) where
  roots := rfl
  known := rfl
  globals g gd hg := by
    refine ⟨if sel g then roundOr P0 p gd else gd, ?_, ?_⟩
    · rw [roundOn_global, if_pos (h.below g gd hg), hg]; rfl
    · split
      · exact roundOr_walked gd
      · exact ⟨rfl, .inl rfl⟩
  suffix _ _ _ _ _ _ hV _ _ := hV
  cknown C _ _ _ hV := by subst hV; exact h.known.symm
  cglob C _ _ _ hV g := by subst hV; exact (h.arity g).symm
  cbody C _ _ _ hV g hin := by subst hV; simp [cfg] at hin
  cdisp C _ _ _ hV _ g gd hgd hdk := by
    subst hV
    simp only [Walk.isDispatchDef, Bool.and_eq_true] at hdk
    obtain ⟨hkey, hbody⟩ := hdk
    have har : ∃ ar, gd.key = .dispatch ar := by
      cases hk : gd.key with
      | dispatch ar => exact ⟨ar, rfl⟩
      | const _ _ | byName _ _ | recStar _ _ | wrapper _ _
      | spec _ _ | worker _ _ | lam _ _ | entry _ _ => simp [Walk.isDispatchKey, hk] at hkey
    obtain ⟨ar, hkey'⟩ := har
    cases hb : gd.body with
    | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => simp [hb] at hbody
    | case x alts dflt =>
      cases x with
      | lit _ | box => simp [hb] at hbody
      | var m =>
        simp only [hb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbody
        exact h.disp g gd hgd ⟨ar, m, alts, dflt, hkey', hb, hbody.1, hbody.2⟩
  inl C _ _ _ _ hV := by subst hV; rfl
  noRed C _ _ _ hV := by subst hV; rfl

theorem roundOn_agree {sel : GlobalId → Bool} {P : Program} (h : Agree P0 P) :
    Agree P0 (roundOn P0 p sel P) where
  known := h.known
  roots := h.roots
  size := h.size
  arity g := by
    rw [roundOn_global, ← h.arity g]
    split
    · cases P.global? g with
      | none => rfl
      | some gd => simp only [Option.map_some]; split <;> simp [roundOr_ps]
    · next hlt =>
      cases hg : P.global? g with
      | none => rfl
      | some gd => exact absurd (h.below g gd hg) hlt
  below g gd hg := by
    rw [roundOn_global] at hg
    split at hg
    · next hlt => exact hlt
    · cases hg
  disp g gd hgd har := by
    have hP := h.disp g gd hgd har
    have hdk : Walk.isDispatchDef gd = true := by
      obtain ⟨ar, m, alts, dflt, hkey, hbody, hm0, hm1⟩ := har
      simp [Walk.isDispatchDef, Walk.isDispatchKey, hkey, hbody, hm0, hm1]
    rw [roundOn_global, if_pos (h.below g gd hP), hP]
    simp [roundOr_disp hdk]

theorem agree_self (h0 : P0.GlobalsBelow) : Agree P0 P0 :=
  ⟨rfl, rfl, rfl, fun _ => rfl, h0, fun _ _ h _ => h⟩

theorem stage_agree (h0 : P0.GlobalsBelow) {cert : Cert} : ∀ i, Agree P0 (stage P0 p cert i)
  | 0 => agree_self h0
  | i + 1 => roundOn_agree (stage_agree h0 i)

theorem stage_refines (h0 : P0.GlobalsBelow) {cert : Cert} : ∀ i, Sem.Refines P0 (stage P0 p cert i)
  | 0 => Sem.Refines.refl _
  | i + 1 => (stage_refines h0 i).trans (roundOn_walkProg (stage_agree h0 i)).refines

theorem stage_global (h0 : P0.GlobalsBelow) {cert : Cert} : ∀ i g, (stage P0 p cert i).global? g =
    if g < P0.size then (P0.global? g).map (fun gd => iter P0 p gd (min i (cert.getD g 0))) else none
  | 0, g => by
    simp only [stage, Nat.zero_min, iter]
    split
    · cases P0.global? g <;> rfl
    · next hlt =>
      cases hg : P0.global? g with
      | none => rfl
      | some gd => exact absurd (h0 g gd hg) hlt
  | i + 1, g => by
    rw [stage, roundOn_global, stage_global h0 i g, (stage_agree h0 i).size]
    split
    · next hlt =>
      cases P0.global? g with
      | none => rfl
      | some gd =>
        simp only [Option.map_some, Option.some.injEq]
        by_cases hi : i < cert.getD g 0
        · rw [if_pos (by simpa using hi), show min (i + 1) (cert.getD g 0) = min i (cert.getD g 0) + 1 by omega]
          rfl
        · rw [if_neg (by simpa using hi), show min (i + 1) (cert.getD g 0) = min i (cert.getD g 0) by omega]
    · rfl

theorem iter_succ' (gd : GDef) : ∀ j, iter P0 p gd (j + 1) = iter P0 p (roundOr P0 p gd) j
  | 0 => rfl
  | j + 1 => by rw [iter, iter_succ' gd j]; rfl

theorem rounds_iter : ∀ (n : Nat) (gd gd' : GDef) (work work' : Nat),
    rounds P0 p gd work n = .ok (gd', work') → iter P0 p gd n = gd'
  | 0, gd, gd', work, work', h => by
    simp only [rounds, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | n + 1, gd, gd', work, work', h => by
    simp only [rounds] at h
    obtain ⟨⟨gd1, f⟩, h1, h2⟩ := Lam.ModesOk.bind_ok h
    have hr : roundOr P0 p gd = gd1 := by unfold roundOr; rw [h1]
    rw [iter_succ', hr]
    try dsimp only at h2
    split at h2
    · exact rounds_iter n gd1 gd' _ _ h2
    · cases h2

/-- The globals `runGlobals` makes are the input's after their certified
rounds. -/
theorem runGlobals_eq {cert : Cert} : ∀ (xs : List (GlobalId × GDef)) (nodes work : Nat)
    (gs : List (GlobalId × GDef)), runGlobals P0 p cert xs nodes work = .ok gs →
    gs = xs.map fun q => (q.1, iter P0 p q.2 (cert.getD q.1 0))
  | [], _, _, gs, h => by
    simp only [runGlobals, Except.ok.injEq] at h
    subst h
    rfl
  | (g, gd) :: rest, nodes, work, gs, h => by
    simp only [runGlobals] at h
    cases hr : rounds P0 p gd work (cert.getD g 0) with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨gd', work'⟩ := r
      rw [hr] at h
      simp only at h
      split at h
      · cases h
      · cases hrest : runGlobals P0 p cert rest (nodes + gd'.body.nodesUpTo maxProgramNodes) work' with
        | error e => rw [hrest] at h; cases h
        | ok gs' =>
          rw [hrest] at h
          simp only [Except.ok.injEq] at h
          subst h
          rw [List.map_cons, rounds_iter _ _ _ _ _ hr, runGlobals_eq rest _ _ gs' hrest]

theorem getD_le_foldr : ∀ (cert : Cert) (g : GlobalId), cert.getD g 0 ≤ cert.foldr max 0
  | [], g => by simp
  | c :: cs, 0 => by simp only [List.getD_cons_zero, List.foldr_cons]; exact Nat.le_max_left _ _
  | c :: cs, g + 1 => by
    simp only [List.getD_cons_succ, List.foldr_cons]
    exact Nat.le_trans (getD_le_foldr cs g) (Nat.le_max_right _ _)

/-- What a successful re-run computes: each global after its certified
rounds. -/
theorem run_global {cert : Cert} {Q : Program} (h : run p cert P0 = .ok Q) :
    Q.roots = P0.roots ∧ Q.known = P0.known ∧ Q.size = P0.size ∧ ∀ g, Q.global? g =
      if g < P0.size then (P0.global? g).map (fun gd => iter P0 p gd (cert.getD g 0)) else none := by
  unfold run at h
  obtain ⟨gs, hgs, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  refine ⟨rfl, rfl, rfl, fun g => ?_⟩
  have hgs' := runGlobals_eq _ _ _ _ hgs
  show (Src.NatMap.ofList gs).get? g = _
  rw [hgs']
  exact get?_ofList_globalList P0 (fun g gd => iter P0 p gd (cert.getD g 0)) g

/-- A successful re-run keeps the constructor table. -/
theorem run_ctors {cert : Cert} {Q : Program} (h : run p cert P0 = .ok Q) : Q.ctors = P0.ctors := by
  unfold run at h
  obtain ⟨gs, -, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  rfl

/-- **P2 is correct**: for every certificate the re-run accepts, the
output refines the input, and keeps its ids `0 … size - 1`. -/
theorem run_refines (h0 : P0.WF) {cert : Cert} {Q : Program} (h : run p cert P0 = .ok Q) :
    Q.WF ∧ Sem.Refines P0 Q := by
  obtain ⟨hroots, hknown, hsize, hQ⟩ := run_global h
  refine ⟨wf_of_mapped hsize hQ h0, (stage_refines h0.1 (cert.foldr max 0)).trans
    (refines_of_globals (P := stage P0 p cert (cert.foldr max 0)) (by rw [hroots, (stage_agree h0.1 _).roots])
      (by rw [hknown, (stage_agree h0.1 _).known]) fun g => ?_)⟩
  rw [hQ, stage_global h0.1, Nat.min_eq_right (getD_le_foldr cert g)]


/-- P2 as a pass: the certificate is the rounds per global; the ids are
`0 … size - 1` before and after. -/
def shrinkPass (p : Params) : Sem.Transform Program Program where
  name := "P2 shrink"
  Cert := Cert
  pre P := P.WF
  run P c := run p c P
  post Q := Q.WF
  correct _ _ _ h0 h := run_refines h0 h

/-! ## The traced shape (decision D-1) -/

theorem run_refines_traced (h0 : P0.WF) {cert : Cert} {Q : Program} (h : run p cert P0 = .ok Q) :
    Sem.TRefines P0 Q :=
  Sem.Refines.ofPure (run_refines h0 h).2

/-- P2 as a traced pass. -/
def shrinkTPass (p : Params) : Sem.TTransform Program Program := (shrinkPass p).lift

end IxCC.Anf.Shrink.Proof
