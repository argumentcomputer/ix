module

public import ConLeche.Semantics.Tower.SumLeaf
import ConLeche.Semantics.Tower.TowerRec
public import ConLeche.Semantics.Tower.TowerWire

@[expose] public section

/-!
# The index equation, spelled (task #175 indexed)

An indexed family's carrier at an index tuple `ı⃗` is the tagged union
of the constructor towers **restricted** to the constructors' index
equations `e⃗_k f⃗ = ı⃗`.  The restriction is one extra proof-field per
constructor: the chain `Fs_k ++ [idxEqAV eqs_k]`, where `idxEqAV eqs`
spells the conjunction of the equations `eqs = [(e₀, ı₀), …]` as the
truth value

    ¬ (e₀ = ı₀ → e₁ = ı₁ → … → False)

with bit-`0` Π nodes and `eqE` equations (whose reading is the
equality's truth value, `eqv`).  Nothing here depends on how the
equations are spelled: `idxEqAV_interp` reads it to `truthVal (EqAll ρ
eqs)` (every left side interprets as its right side), `idxEqAV_wellDenoted`
grades it from the sides' gradings, and `idxEqAV_mem_univ` bounds it in
every universe (a truth value).  The chain-level facts
(`FieldsOkB_append_idxEq`, `spineFit_append_idxEq`) are what the fibre
construction consumes: a fitting spine of the restricted chain is a
fitting spine of the fields followed by the point, with the equations
holding at the fields.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The spelling -/

/-- `e₀ = ı₀ → e₁ = ı₁ → … → False`, each later equation lifted under
the earlier binders (the equations are scoped at the chain's head). -/
def eqChainAV : List (AnnotTerm × AnnotTerm) → AnnotTerm
  | [] => .const .empty [0]
  | (a, b) :: r => .pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0)

/-- **The index equation**: the truth value of every equation holding. -/
def idxEqAV (eqs : List (AnnotTerm × AnnotTerm)) : AnnotTerm := negAV (eqChainAV eqs)

/-- Every equation holds at `ρ`. -/
def EqAll (ρ : Nat → V) (eqs : List (AnnotTerm × AnnotTerm)) : Prop :=
  ∀ e ∈ eqs, interp V ρ e.1 = interp V ρ e.2

theorem EqAll_nil (ρ : Nat → V) : EqAll (V := V) ρ [] := fun _ h => nomatch h

theorem EqAll_cons {ρ : Nat → V} {a b : AnnotTerm} {r : List (AnnotTerm × AnnotTerm)} :
    EqAll ρ ((a, b) :: r) ↔ interp V ρ a = interp V ρ b ∧ EqAll ρ r := by
  constructor
  · intro h
    exact ⟨h (a, b) List.mem_cons_self, fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨h1, h2⟩ e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact h1
    · exact h2 e he'

/-! ## The reading -/

/-- The chain is inhabited exactly when some equation fails. -/
theorem eqChainAV_inhab :
    ∀ (eqs : List (AnnotTerm × AnnotTerm)) (ρ : Nat → V),
      (∃ y, y ∈ˢ interp V ρ (eqChainAV eqs)) ↔ ¬ EqAll ρ eqs
  | [], ρ => by
    refine ⟨fun ⟨y, hy⟩ => absurd hy (not_mem_empty y), fun h => absurd (EqAll_nil ρ) h⟩
  | (a, b) :: r, ρ => by
    show (∃ y, y ∈ˢ piR 0 (eqv (interp V ρ a) (interp V ρ b))
      fun x => interp V (cons x ρ) ((eqChainAV r).liftN 1 0)) ↔ _
    have heqv : eqv (interp V ρ a) (interp V ρ b)
        = truthVal (interp V ρ a = interp V ρ b) := by unfold eqv; rfl
    rw [heqv, piR_zero, exists_mem_truthVal, EqAll_cons]
    have hlift : ∀ x : V, interp V (cons x ρ) ((eqChainAV r).liftN 1 0)
        = interp V ρ (eqChainAV r) := fun x => by
      rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
    constructor
    · intro h ⟨hab, hall⟩
      have := h pt (pt_mem_truthVal hab)
      rw [hlift] at this
      exact (eqChainAV_inhab r ρ).mp this hall
    · intro h x hx
      rw [hlift]
      refine (eqChainAV_inhab r ρ).mpr fun hall => h ⟨of_mem_truthVal hx, hall⟩

/-- **The index equation reads to the truth value of every equation
holding.** -/
theorem idxEqAV_interp (eqs : List (AnnotTerm × AnnotTerm)) (ρ : Nat → V) :
    interp V ρ (idxEqAV eqs) = truthVal (EqAll ρ eqs) := by
  unfold idxEqAV
  rw [interp_negAV]
  refine truthVal_congr ?_
  rw [eqChainAV_inhab]
  exact ⟨fun h => Classical.byContradiction h, fun h h' => h' h⟩

/-- A truth value sits in every universe. -/
theorem truthVal_mem_univ (p : Prop) (w : Nat) : (truthVal p : V) ∈ˢ univ w :=
  univ_mono (Nat.zero_le w) _ (univ_zero (V := V) ▸ truthVal_mem_univZero p)

theorem idxEqAV_mem_univ (eqs : List (AnnotTerm × AnnotTerm)) (ρ : Nat → V) (w : Nat) :
    interp V ρ (idxEqAV eqs) ∈ˢ (univ w : V) := by
  rw [idxEqAV_interp]; exact truthVal_mem_univ _ w

/-- The point inhabits the index equation exactly when every equation
holds. -/
theorem pt_mem_idxEqAV {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V} :
    (pt : V) ∈ˢ interp V ρ (idxEqAV eqs) ↔ EqAll ρ eqs := by
  rw [idxEqAV_interp, mem_truthVal]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem mem_idxEqAV {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ interp V ρ (idxEqAV eqs)) : x = pt ∧ EqAll ρ eqs := by
  rw [idxEqAV_interp, mem_truthVal] at hx
  exact ⟨hx.2, hx.1⟩

/-! ## The grading -/

/-- The equations' sides graded at `ρ`. -/
def EqsOk (ρ : Nat → V) (eqs : List (AnnotTerm × AnnotTerm)) : Prop :=
  ∀ e ∈ eqs, WellDenoted V ρ e.1 ∧ WellDenoted V ρ e.2

theorem eqChainAV_wellDenoted :
    ∀ {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V}, EqsOk ρ eqs →
      WellDenoted V ρ (eqChainAV eqs)
  | [], _, _ => trivial
  | (a, b) :: r, ρ, hok => by
    show WellDenoted V ρ (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0))
    rw [WellDenoted_pi, WellDenoted_eqE]
    refine ⟨hok (a, b) List.mem_cons_self, fun x _ => ?_⟩
    rw [WellDenoted_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
    exact eqChainAV_wellDenoted fun e he => hok e (List.mem_cons_of_mem _ he)

/-- **The index equation is graded** from its sides' gradings. -/
theorem idxEqAV_wellDenoted {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V} (hok : EqsOk ρ eqs) :
    WellDenoted V ρ (idxEqAV eqs) := by
  unfold idxEqAV negAV
  rw [WellDenoted_pi]
  exact ⟨eqChainAV_wellDenoted hok, fun _ _ => trivial⟩

/-! ## The restricted chain -/

/-- The restricted chain `Fs ++ [idxEqAV eqs]` is graded when the
fields are and the equations' sides are graded at every fitting field
frame. -/
theorem FieldsOkB_append_idxEq {w : Nat} {eqs : List (AnnotTerm × AnnotTerm)} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → EqsOk (consList bs ρ) eqs) →
      FieldsOkB w ρ (Fs ++ [idxEqAV eqs])
  | [], ρ, _, hE => by
    refine ⟨idxEqAV_wellDenoted (by simpa [consList] using hE [] trivial),
      fun _ => idxEqAV_mem_univ eqs ρ w, fun _ _ => trivial⟩
  | F :: Fs, ρ, hok, hE => by
    refine ⟨hok.1, hok.2.1, fun a ha => ?_⟩
    refine FieldsOkB_append_idxEq (hok.2.2 a ha) fun bs hsp => ?_
    have := hE (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A fit of an appended chain splits (the `SpineFit` twin of the
Model tier's `spineFit_append_inv`, restated here below it). -/
theorem spineFit_append_split :
    ∀ {Ds₁ Ds₂ : List AnnotTerm} {ρ : Nat → V} {as : List V},
      SpineFit ρ (Ds₁ ++ Ds₂) as →
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂
  | [], _, ρ, as, h => ⟨[], as, rfl, trivial, h⟩
  | _ :: _, _, _, [], h => h.elim
  | D :: Ds₁, Ds₂, ρ, a :: as, h => by
    obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_split (Ds₁ := Ds₁) h.2
    exact ⟨a :: as₁, as₂, rfl, ⟨h.1, h1⟩, by rw [consList_cons]; exact h2⟩

/-- A spine fits the restricted chain exactly when it is a fitting
field spine followed by the point, with every equation holding at the
fields. -/
theorem spineFit_append_idxEq {Fs : List AnnotTerm} {eqs : List (AnnotTerm × AnnotTerm)}
    {ρ : Nat → V} {as : List V} :
    SpineFit ρ (Fs ++ [idxEqAV eqs]) as ↔
      ∃ bs, as = bs ++ [pt] ∧ SpineFit ρ Fs bs ∧ EqAll (consList bs ρ) eqs := by
  constructor
  · intro h
    obtain ⟨bs, cs, rfl, hsp, hE⟩ := spineFit_append_split h
    match cs, hE with
    | [], hE => exact hE.elim
    | [c], hE =>
      obtain ⟨rfl, hall⟩ := mem_idxEqAV hE.1
      exact ⟨bs, rfl, hsp, hall⟩
    | _ :: _ :: _, hE => exact hE.2.elim
  · rintro ⟨bs, rfl, hsp, hall⟩
    exact hsp.append ⟨pt_mem_idxEqAV.mpr hall, trivial⟩

/-- The projections of a member of the restricted tower: the field
projections fit, the last projection is the point, and the equations
hold at the field projections (graph regime). -/
theorem restricted_member_elim {w : Nat} (hw : w ≠ 0) {Fs : List AnnotTerm}
    {eqs : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V} {y : V}
    (hy : y ∈ˢ towerSet w (teleOfFields ρ (Fs ++ [idxEqAV eqs]))) :
    SpineFit ρ Fs (projList Fs.length y) ∧ projS Fs.length y = pt ∧
      EqAll (consList (projList Fs.length y) ρ) eqs ∧
      y = mkTower (projList Fs.length y ++ [pt]) := by
  obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw hy
  rw [List.length_append, List.length_singleton] at hfit heta
  obtain ⟨bs, hbs, hspF, hall⟩ := spineFit_append_idxEq.mp hfit
  rw [projList_snoc] at hbs heta
  have hlen : (projList Fs.length y).length = bs.length := by
    rw [projList_length, hspF.length_eq]
  have h1 : projList Fs.length y = bs := List.append_inj_left hbs hlen
  have h2 : projS Fs.length y = pt := by
    have := List.append_inj_right hbs hlen
    simpa using this
  subst h1
  exact ⟨hspF, h2, hall, heta.trans (by rw [h2])⟩

/-- The squash-regime witness of a member of the restricted tower: a
fitting field spine at which the equations hold. -/
theorem restricted_member_zero {Fs : List AnnotTerm} {eqs : List (AnnotTerm × AnnotTerm)}
    {ρ : Nat → V} {y : V} (hy : y ∈ˢ towerSet 0 (teleOfFields ρ (Fs ++ [idxEqAV eqs]))) :
    y = pt ∧ ∃ bs, SpineFit ρ Fs bs ∧ EqAll (consList bs ρ) eqs := by
  obtain ⟨rfl, as, hfit⟩ := towerSet_zero_elim _ hy
  obtain ⟨bs, -, hspF, hall⟩ := spineFit_append_idxEq.mp (fitsS_teleOfFields.mp hfit)
  exact ⟨rfl, bs, hspF, hall⟩

/-- The restricted tower's intro: a fitting field spine at which the
equations hold puts the point-terminated tuple in the tower (graph
regime) and the point in the squash. -/
theorem restricted_member_intro {w : Nat} {Fs : List AnnotTerm} {eqs : List (AnnotTerm × AnnotTerm)}
    {ρ : Nat → V} {bs : List V} (hsp : SpineFit ρ Fs bs) (hall : EqAll (consList bs ρ) eqs) :
    (if w = 0 then (pt : V) else mkTower (bs ++ [pt]))
      ∈ˢ towerSet w (teleOfFields ρ (Fs ++ [idxEqAV eqs])) := by
  have hsp' : SpineFit ρ (Fs ++ [idxEqAV eqs]) (bs ++ [pt]) :=
    spineFit_append_idxEq.mpr ⟨bs, rfl, hsp, hall⟩
  split
  · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp'
  · next hnz => exact mkTower_mem_teleOfFields hnz hsp'

/-! ## Bounds -/

theorem eqChainAV_below {k : Nat} :
    ∀ {eqs : List (AnnotTerm × AnnotTerm)},
      (∀ e ∈ eqs, Term.bvarsBelow k e.1.erase ∧ Term.bvarsBelow k e.2.erase) →
      Term.bvarsBelow k (eqChainAV eqs).erase
  | [], _ => trivial
  | (a, b) :: r, h => by
    refine ⟨⟨(h (a, b) List.mem_cons_self).1, (h (a, b) List.mem_cons_self).2⟩, ?_⟩
    rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN 1 _ k 0
      (eqChainAV_below fun e he => h e (List.mem_cons_of_mem _ he))

theorem idxEqAV_below {k : Nat} {eqs : List (AnnotTerm × AnnotTerm)}
    (h : ∀ e ∈ eqs, Term.bvarsBelow k e.1.erase ∧ Term.bvarsBelow k e.2.erase) :
    Term.bvarsBelow k (idxEqAV eqs).erase :=
  ⟨eqChainAV_below h, trivial⟩

/-- The restricted chain is bounded when the fields are and the
equations are bounded at the field frame. -/
theorem FieldsBelow_append_idxEq {eqs : List (AnnotTerm × AnnotTerm)} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs →
      (∀ e ∈ eqs, Term.bvarsBelow (k + Fs.length) e.1.erase ∧
        Term.bvarsBelow (k + Fs.length) e.2.erase) →
      FieldsBelow k (Fs ++ [idxEqAV eqs])
  | [], k, _, h => ⟨idxEqAV_below (by simpa using h), trivial⟩
  | F :: Fs, k, hb, h => by
    refine ⟨hb.1, FieldsBelow_append_idxEq hb.2 ?_⟩
    intro e he
    have := h e he
    rwa [List.length_cons, show k + (Fs.length + 1) = k + 1 + Fs.length from by omega] at this

/-! ## Lifting a chain into a deeper frame -/

/-- A field chain lifted by `n` at cutoff `k` (domain `i` at cutoff
`k + i`, as `liftDoms` does for binder data). -/
def liftFields (n : Nat) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | k, F :: Fs => F.liftN n k :: liftFields n (k + 1) Fs

@[simp] theorem liftFields_nil (n k : Nat) : liftFields n k [] = [] := rfl
@[simp] theorem liftFields_cons (n k : Nat) (F : AnnotTerm) (Fs : List AnnotTerm) :
    liftFields n k (F :: Fs) = F.liftN n k :: liftFields n (k + 1) Fs := rfl

theorem liftFields_length (n : Nat) :
    ∀ (Fs : List AnnotTerm) (k : Nat), (liftFields n k Fs).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, k => by simp [liftFields_length n Fs (k + 1)]

theorem liftFields_append (n : Nat) :
    ∀ (Fs Gs : List AnnotTerm) (k : Nat),
      liftFields n k (Fs ++ Gs) = liftFields n k Fs ++ liftFields n (k + Fs.length) Gs
  | [], _, _ => by simp
  | F :: Fs, Gs, k => by
    simp only [List.cons_append, liftFields_cons, liftFields_append n Fs Gs (k + 1),
      List.length_cons]
    rw [show k + 1 + Fs.length = k + (Fs.length + 1) from by omega]

/-- A spine fits the lifted chain at `σ` exactly when it fits the
chain at the shifted frame. -/
theorem spineFit_liftFields (n : Nat) :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V} {as : List V},
      SpineFit σ (liftFields n k Fs) as ↔ SpineFit (shiftE n k σ) Fs as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | F :: Fs, k, σ, a :: as => by
    simp only [liftFields_cons, SpineFit, interp_liftN]
    rw [cons_shiftE]
    exact and_congr Iff.rfl (spineFit_liftFields n)

/-- The lifted chain's grading is the chain's at the shifted frame. -/
theorem FieldsOkB_liftFields {w n : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat} {σ : Nat → V},
      FieldsOkB w σ (liftFields n k Fs) ↔ FieldsOkB w (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsOkB, WellDenoted_liftN, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun a => imp_congr Iff.rfl ?_))
    rw [cons_shiftE]
    exact FieldsOkB_liftFields

theorem FieldsBelow_liftFields {n : Nat} :
    ∀ {Fs : List AnnotTerm} {k K : Nat}, k ≤ K → FieldsBelow K Fs →
      FieldsBelow (K + n) (liftFields n k Fs)
  | [], _, _, _, _ => trivial
  | F :: Fs, k, K, hk, hb => by
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN n _ K k hb.1
    · have := FieldsBelow_liftFields (n := n) (Fs := Fs) (k := k + 1) (K := K + 1)
        (by omega) hb.2
      rwa [show K + 1 + n = K + n + 1 from by omega] at this

/-! ## The restricted chains of an indexed family

A constructor's field chain `Fs` is scoped at the parameter frame, its
index expressions `Es` at the constructor frame (parameters, then the
`nF` fields).  At a frame `d` binders below the parameters whose LAST
`nIdx` binders are the index variables — `(p⃗, ı⃗)` for the former's
leaf, `(p⃗, motive, minors, ı⃗)` for the recursor's — the restricted
chain is the lifted field chain followed by the index equation
`e⃗ = ı⃗` (each `e_l` lifted under the `d` binders past the fields, the
index variable `ı_l` at `nF + nIdx - 1 - l`). -/

/-- The equations `e_l = ı_l` at a frame `d` below the parameters,
under `nF` fields. -/
def idxEqsAt (d nIdx nF : Nat) (Es : List AnnotTerm) : List (AnnotTerm × AnnotTerm) :=
  (List.range nIdx).map fun l => ((Es.getD l default).liftN d nF, .bvar (nF + nIdx - 1 - l))

/-- Constructor's restricted chain at a frame `d` below the parameters. -/
def rChain (d nIdx : Nat) (Fs : List AnnotTerm) (Es : List AnnotTerm) : List AnnotTerm :=
  liftFields d 0 Fs ++ [idxEqAV (idxEqsAt d nIdx Fs.length Es)]

/-- The restricted chains of all constructors. -/
def rChains (d nIdx : Nat) (Fss : List (List AnnotTerm)) (Ess : List (List AnnotTerm)) :
    List (List AnnotTerm) :=
  List.zipWith (rChain d nIdx) Fss Ess

theorem rChains_length (d nIdx : Nat) (Fss Ess : List (List AnnotTerm)) :
    (rChains d nIdx Fss Ess).length = Nat.min Fss.length Ess.length := by
  simp [rChains]

theorem rChains_getElem? (d nIdx : Nat) (Fss Ess : List (List AnnotTerm)) (j : Nat) :
    (rChains d nIdx Fss Ess)[j]? = match Fss[j]?, Ess[j]? with
      | some Fs, some Es => some (rChain d nIdx Fs Es)
      | _, _ => none := by
  simp only [rChains, List.getElem?_zipWith]
  cases Fss[j]? <;> cases Ess[j]? <;> rfl

theorem rChain_length (d nIdx : Nat) (Fs Es : List AnnotTerm) :
    (rChain d nIdx Fs Es).length = Fs.length + 1 := by
  simp [rChain, liftFields_length]

/-- The frame's index tuple: the last `nIdx` binders' values, the first
index first. -/
def frameIdx (nIdx : Nat) (σ : Nat → V) : List V :=
  (List.range nIdx).map fun l => σ (nIdx - 1 - l)

/-- A constructor's index tuple at a field spine, read at the
parameter frame. -/
noncomputable def idxValsAt (ρp : Nat → V) (Es : List AnnotTerm) (bs : List V) : List V :=
  Es.map (interp V (consList bs ρp))

omit [SetTheory V] in
theorem shiftE_consList_len' (n : Nat) :
    ∀ (as : List V) (k : Nat) (σ : Nat → V),
      shiftE n (as.length + k) (consList as σ) = consList as (shiftE n k σ)
  | [], k, σ => by simp [consList]
  | a :: as, k, σ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show as.length + 1 + k = as.length + (k + 1) from by omega,
      shiftE_consList_len' n as (k + 1) (cons a σ), cons_shiftE]

omit [SetTheory V] in
theorem shiftE_consList_len (n : Nat) (as : List V) (σ : Nat → V) :
    shiftE n as.length (consList as σ) = consList as (shiftE n 0 σ) := by
  have := shiftE_consList_len' n as 0 σ
  rwa [Nat.add_zero] at this

theorem getD_mem_of_lt {l : Nat} {Es : List AnnotTerm} (hl : l < Es.length) :
    Es.getD l default ∈ Es := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.getElem_mem hl

theorem getD_eq_default_of_le {l : Nat} {Es : List AnnotTerm} (hl : Es.length ≤ l) :
    Es.getD l default = default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none]

/-- **The index equation at a fitting spine**: every `e_l = ı_l` holds
exactly when the constructor's index tuple at the fields is the
frame's index tuple. -/
theorem EqAll_idxEqsAt {d nIdx nF : Nat} {Es : List AnnotTerm} (hEs : Es.length = nIdx)
    {σ : Nat → V} {bs : List V} (hbs : bs.length = nF) :
    EqAll (consList bs σ) (idxEqsAt d nIdx nF Es) ↔
      idxValsAt (shiftE d 0 σ) Es bs = frameIdx nIdx σ := by
  have hvar : ∀ l, l < nIdx →
      interp V (consList bs σ) (.bvar (nF + nIdx - 1 - l)) = σ (nIdx - 1 - l) := by
    intro l hl
    rw [interp_bvar, show nF + nIdx - 1 - l = (nIdx - 1 - l) + bs.length from by omega,
      consList_apply_add]
  have hlift : ∀ E : AnnotTerm, interp V (consList bs σ) (E.liftN d nF)
      = interp V (consList bs (shiftE d 0 σ)) E := by
    intro E
    rw [interp_liftN, ← hbs, shiftE_consList_len]
  -- the pointwise form of the equation
  have hpt : EqAll (consList bs σ) (idxEqsAt d nIdx nF Es) ↔
      ∀ l, l < nIdx → interp V (consList bs (shiftE d 0 σ)) (Es.getD l default)
        = σ (nIdx - 1 - l) := by
    unfold EqAll idxEqsAt
    constructor
    · intro h l hl
      have := h ((Es.getD l default).liftN d nF, .bvar (nF + nIdx - 1 - l))
        (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
      simp only at this
      rwa [hlift, hvar l hl] at this
    · intro h e he
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      simp only
      rw [hlift, hvar l (List.mem_range.mp hl)]
      exact h l (List.mem_range.mp hl)
  rw [hpt]
  unfold idxValsAt frameIdx
  constructor
  · intro h
    apply List.ext_getElem
    · simp [hEs]
    · intro l h1 h2
      have hl : l < nIdx := by simpa using h2
      simp only [List.getElem_map, List.getElem_range]
      have := h l hl
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        at this
  · intro h l hl
    have := congrArg (fun xs : List V => xs[l]?) h
    simp only [List.getElem?_map, List.getElem?_range hl, Option.map_some] at this
    rw [List.getElem?_eq_getElem (by omega), Option.map_some, Option.some.injEq] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact this

/-- The restricted chain's grading: from the field chain's grading at
the parameter frame and the index expressions' gradings at every
fitting field frame (the index variables are bare variables). -/
theorem FieldsOkB_rChain {w d nIdx : Nat} {Fs Es : List AnnotTerm} {σ : Nat → V}
    (hEs : Es.length = nIdx) (hok : FieldsOkB w (shiftE d 0 σ) Fs)
    (hE : ∀ bs : List V, SpineFit (shiftE d 0 σ) Fs bs →
      ∀ E ∈ Es, WellDenoted V (consList bs (shiftE d 0 σ)) E) :
    FieldsOkB w σ (rChain d nIdx Fs Es) := by
  unfold rChain
  refine FieldsOkB_append_idxEq (FieldsOkB_liftFields.mpr hok) fun bs hsp e he => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  refine ⟨?_, trivial⟩
  simp only
  have hsp' := (spineFit_liftFields d).mp hsp
  rw [WellDenoted_liftN, ← hsp'.length_eq, shiftE_consList_len]
  exact hE bs hsp' _ (getD_mem_of_lt (by rw [hEs]; exact List.mem_range.mp hl))

/-- The restricted chain is bounded at a frame `K` when the fields are
bounded at the parameter frame `K - d` and the index expressions at
the constructor frame. -/
theorem FieldsBelow_rChain {d nIdx : Nat} (hd : nIdx ≤ d) {Fs Es : List AnnotTerm} {K : Nat}
    (hEs : Es.length = nIdx) (hF : FieldsBelow K Fs)
    (hE : ∀ E ∈ Es, Term.bvarsBelow (K + Fs.length) E.erase) :
    FieldsBelow (K + d) (rChain d nIdx Fs Es) := by
  unfold rChain
  refine FieldsBelow_append_idxEq (FieldsBelow_liftFields (Nat.zero_le _) hF) ?_
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  rw [liftFields_length]
  refine ⟨?_, ?_⟩
  · simp only
    rw [AnnotTerm.erase_liftN]
    have : Term.bvarsBelow (K + Fs.length) (Es.getD l default).erase :=
      hE _ (getD_mem_of_lt (by rw [hEs]; exact List.mem_range.mp hl))
    have h2 := VExprAux.bvarsBelow_liftN d _ (K + Fs.length) Fs.length this
    rwa [show K + Fs.length + d = K + d + Fs.length from by omega] at h2
  · simp only [AnnotTerm.erase_bvar]
    show Fs.length + nIdx - 1 - l < K + d + Fs.length
    have := List.mem_range.mp hl
    omega

end ConLeche.Semantics
