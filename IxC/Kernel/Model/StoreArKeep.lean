module

public import IxC.Kernel.Model.LevelRen
public import IxC.Kernel.Model.ThmLevels
public import IxC.Kernel.Model.JudgeRules
public import IxC.Kernel.Verify.Shift

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Arity-correct stored terms, in the form a fold carries

`StoreAr` (`Model/LevelRenKit.lean`) says that the stored terms apply every stored constant at its
own number of level parameters. Read at one environment it is not monotone: a stored term may
name a constant the environment does not hold, which a later step may store at another arity.
`StoreArR` is the form a fold carries: every stored term is arity-correct **and resolves**
(`ArRes`), so a step that keeps the old lookups keeps it, and a comparison of `Nat` stored as a
definition finds both `Bool` values stored with no level parameter (`BoolLvPinned`, which the
comparison's install checks, `natOpGuard`). `StoreArR.toStoreAr` gives `StoreAr`.

* `StoreArR.step`: a step that keeps the old lookups and stores arity-correct constants keeps it;
  `storeArR_cons` at one fresh constant.
* `infer_full_arOk`: a full-grade inference establishes its subject's arity from its own
  derivation (`Infer.const` checks the count), given its annotations'.
* `storeArR_declRunJ_value`: a declaration step that stores one definition, theorem or axiom
  keeps it (every other kind of step is excluded by its shape).
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel (Env Key Expr ConstantInfo ConstantVal RecRule Declaration StoreAr ProjTable
  IndCaps BasisKind)
open Ix.Kernel.LevelRen
open Ix.Kernel.Rules (Infer Red DefEq Certs DefEqList EtaProjCerts Grade)

/-! ## The clause -/

/-- **Arity-correct and resolving.** -/
structure ArRes (env : Env md) (e : Expr md) : Prop where
  ar : Expr.arOk env e = true
  res : e.constsResolve env = true

/-- **Each stored term of a constant is arity-correct and resolves**: its type, a definition's
or a theorem's value, a recursor's rule right-hand sides and nested pins, a projection table's
bodies. -/
structure ConstArR (env : Env md) (c : ConstantInfo md) : Prop where
  type : ArRes env c.toConstantVal.type
  defn : ∀ cv v h, c = .defnInfo cv v h → ArRes env v
  thm : ∀ cv v, c = .thmInfo cv v → ArRes env v
  rhs : ∀ cv mI rP (rules : List (RecRule md)), c = .recInfo cv mI rP rules → ∀ rl ∈ rules,
    ArRes env rl.rhs ∧ ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, ArRes env p
  proj : ∀ tbl, c = .projInfo tbl → ∀ (i : Nat) (b : Expr md), tbl.bodies[i]? = some b →
    ArRes env b

/-- **Both `Bool` values are stored with no level parameter.** -/
structure BoolLvPinned (env : Env md) : Prop where
  tru : ∃ ci, env.find? Ix.Kernel.boolTrueName = some ci ∧ ci.toConstantVal.levelParams = []
  fls : ∃ ci, env.find? Ix.Kernel.boolFalseName = some ci ∧ ci.toConstantVal.levelParams = []

/-- **The stored terms are arity-correct and resolve**, and a stored comparison of `Nat` finds
both `Bool` values pinned: the form of `StoreAr` a fold carries. -/
structure StoreArR (env : Env md) : Prop where
  const : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → ConstArR env ci
  bool : ∀ {c : Key md}, Ix.Kernel.natOpStored env c = true →
    (c = Ix.Kernel.natBeqName ∨ c = Ix.Kernel.natBleName) → BoolLvPinned env

/-! ## Monotonicity -/

section Mono

variable {env env₂ : Env md}

/-- **A resolving arity-correct term stays arity-correct** where the old lookups are kept. -/
theorem arOk_mono
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → env₂.find? n = some ci) :
    ∀ {e : Expr md}, e.constsResolve env = true → Expr.arOk env e = true →
      Expr.arOk env₂ e = true := by
  intro e
  induction e with
  | bvar _ => intro _ _; rfl
  | sort _ => intro _ _; rfl
  | lit _ => intro _ _; rfl
  | const c us =>
    intro hr ha
    simp only [Expr.constsResolve, Option.isSome_iff_exists] at hr
    obtain ⟨ci, hci⟩ := hr
    have h2 := hf hci
    simp only [Expr.arOk, hci, h2] at ha ⊢
    exact ha
  | fvar i ty ih =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk] at hr ha ⊢
    exact ih hr ha
  | app f a ihf iha =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨ihf hr.1 ha.1, iha hr.2 ha.2⟩
  | lam ty b m iht ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨iht hr.1 ha.1, ihb hr.2 ha.2⟩
  | forallE ty b m iht ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨iht hr.1 ha.1, ihb hr.2 ha.2⟩
  | letE ty v b l iht ihv ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨⟨iht hr.1.1 ha.1.1, ihv hr.1.2 ha.1.2⟩, ihb hr.2 ha.2⟩
  | proj s i e ih =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ih hr.2 ha

theorem ArRes.mono
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → env₂.find? n = some ci)
    {e : Expr md} (h : ArRes env e) : ArRes env₂ e :=
  ⟨arOk_mono hf h.res h.ar, Ix.Kernel.Expr.constsResolve_of_find (fun n hn => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hf hci]
    rfl) h.res⟩

theorem ConstArR.mono
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → env₂.find? n = some ci)
    {c : ConstantInfo md} (h : ConstArR env c) : ConstArR env₂ c where
  type := h.type.mono hf
  defn := fun cv v hh he => (h.defn cv v hh he).mono hf
  thm := fun cv v he => (h.thm cv v he).mono hf
  rhs := fun cv mI rP rules he rl hrl =>
    ⟨(h.rhs cv mI rP rules he rl hrl).1.mono hf,
      fun lvls pins hfire p hp => ((h.rhs cv mI rP rules he rl hrl).2 lvls pins hfire p hp).mono hf⟩
  proj := fun tbl he i b hb => (h.proj tbl he i b hb).mono hf

theorem BoolLvPinned.mono
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → env₂.find? n = some ci)
    (h : BoolLvPinned env) : BoolLvPinned env₂ where
  tru := by
    obtain ⟨ci, h1, h2⟩ := h.tru
    exact ⟨ci, hf h1, h2⟩
  fls := by
    obtain ⟨ci, h1, h2⟩ := h.fls
    exact ⟨ci, hf h1, h2⟩

end Mono

/-! ## `StoreAr` from the carried form -/

/-- A default-padded read of arity-correct bodies is arity-correct. -/
theorem arOk_getD_bodies {env : Env md} (a : Array (Expr md)) (i : Nat)
    (ha : ∀ (j : Nat) (b : Expr md), a[j]? = some b → ArRes env b) :
    Expr.arOk env (a.getD i default) = true := by
  by_cases hi : i < a.size
  · have h1 : a.getD i default = a[i] := by simp [Array.getD, hi]
    rw [h1]
    exact (ha i _ (by simp [hi])).ar
  · have h1 : a.getD i default = default := by simp [Array.getD, hi]
    rw [h1]
    rfl

/-- **`StoreArR` gives `StoreAr`.** -/
theorem StoreArR.toStoreAr {env : Env md} (h : StoreArR env) : StoreAr env where
  type := fun hf => (h.const hf).type.ar
  defn := fun hf => ((h.const hf).defn _ _ _ rfl).ar
  thm := fun hf => ((h.const hf).thm _ _ rfl).ar
  rhs := fun hf rl hrl =>
    ⟨((h.const hf).rhs _ _ _ _ rfl rl hrl).1.ar,
      fun lvls pins hfire p hp => (((h.const hf).rhs _ _ _ _ rfl rl hrl).2 lvls pins hfire p hp).ar⟩
  proj := fun {sn i entry} hent => by
    obtain ⟨tbl, hf, -, rfl⟩ := Ix.Kernel.Env.findProj?_some hent
    exact arOk_getD_bodies tbl.bodies i ((h.const hf).proj tbl rfl)
  bool := fun {c} hst hcb {n ci} hn hf => by
    have hb := h.bool hst hcb
    rcases hn with rfl | rfl
    · obtain ⟨ci', h1, h2⟩ := hb.tru
      rw [hf] at h1
      obtain rfl := Option.some.inj h1
      exact h2
    · obtain ⟨ci', h1, h2⟩ := hb.fls
      rw [hf] at h1
      obtain rfl := Option.some.inj h1
      exact h2

/-- The empty environment. -/
theorem StoreArR.empty : StoreArR (md := md) Env.empty where
  const := fun h => by simp [Env.find?, Env.empty] at h
  bool := by
    intro c hst
    simp [Ix.Kernel.natOpStored, Env.find?, Env.empty] at hst

/-! ## A step -/

/-- **A step keeps `StoreArR`** when it keeps the old lookups, every constant it stores is
arity-correct at the new environment, and a comparison of `Nat` it stores finds the `Bool`
values pinned. -/
theorem StoreArR.step {env env₂ : Env md} (h : StoreArR env)
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci → env₂.find? n = some ci)
    (hnew : ∀ {n : Key md} {ci : ConstantInfo md}, env₂.find? n = some ci → env.find? n = none →
      ConstArR env₂ ci)
    (hbool : ∀ {c : Key md}, Ix.Kernel.natOpStored env₂ c = true → env.find? c = none →
      (c = Ix.Kernel.natBeqName ∨ c = Ix.Kernel.natBleName) → BoolLvPinned env₂) :
    StoreArR env₂ where
  const := fun {n ci} hf₂ => by
    cases hold : env.find? n with
    | none => exact hnew hf₂ hold
    | some c =>
      have h2 := hf hold
      rw [hf₂] at h2
      obtain rfl := Option.some.inj h2
      exact (h.const hold).mono hf
  bool := fun {c} hst hcb => by
    cases hold : env.find? c with
    | none => exact hbool hst hold hcb
    | some ci =>
      have hst' : Ix.Kernel.natOpStored env c = true := by
        have h2 := hf hold
        unfold Ix.Kernel.natOpStored at hst ⊢
        rw [h2] at hst
        rw [hold]
        exact hst
      exact (h.bool hst' hcb).mono hf

/-- A cons of a fresh head keeps the old lookups. -/
theorem find?_cons_fresh_ext {env : Env md} {c : ConstantInfo md}
    (hfresh : env.find? c.name = none) :
    ∀ {n : Key md} {x : ConstantInfo md}, env.find? n = some x →
      Env.find? ⟨c :: env.consts⟩ n = some x :=
  fun hx => Ix.Kernel.Env.find?_cons_of_fresh hfresh hx

/-- A lookup in a cons that the old environment misses finds the head. -/
theorem find?_cons_new {env : Env md} {c x : ConstantInfo md} {n : Key md}
    (hf : Env.find? ⟨c :: env.consts⟩ n = some x) (hn : env.find? n = none) :
    x = c ∧ c.name = n := by
  rw [Ix.Kernel.Env.find?_cons] at hf
  by_cases h : c.name = n
  · rw [if_pos h] at hf
    exact ⟨(Option.some.inj hf).symm, h⟩
  · rw [if_neg h, hn] at hf
    exact nomatch hf

/-- A comparison stored by a cons that the old environment misses is the head, a definition. -/
theorem natOpStored_cons_new {env : Env md} {ci : ConstantInfo md} {c : Key md}
    (hst : Ix.Kernel.natOpStored ⟨ci :: env.consts⟩ c = true) (hn : env.find? c = none) :
    ci.name = c ∧ ∃ cv v h, ci = .defnInfo cv v h := by
  unfold Ix.Kernel.natOpStored at hst
  rw [Ix.Kernel.Env.find?_cons] at hst
  by_cases hc : ci.name = c
  · rw [if_pos hc] at hst
    refine ⟨hc, ?_⟩
    cases ci with
    | defnInfo cv v h => exact ⟨cv, v, h, rfl⟩
    | _ => simp at hst
  · rw [if_neg hc, hn] at hst
    simp at hst

/-- **One fresh constant keeps `StoreArR`**, given its terms' arity at the new environment and,
at a comparison of `Nat` stored as a definition, the `Bool` values pinned. -/
theorem storeArR_cons {env : Env md} {ci : ConstantInfo md} (h : StoreArR env)
    (hfresh : env.find? ci.name = none) (hc : ConstArR ⟨ci :: env.consts⟩ ci)
    (hb : (∃ cv v hh, ci = .defnInfo cv v hh) →
      (ci.name = Ix.Kernel.natBeqName ∨ ci.name = Ix.Kernel.natBleName) →
      BoolLvPinned ⟨ci :: env.consts⟩) :
    StoreArR ⟨ci :: env.consts⟩ := by
  refine h.step (fun hx => Ix.Kernel.Env.find?_cons_of_fresh hfresh hx) (fun hx hn => ?_)
    (fun hst hn hcb => ?_)
  · obtain ⟨rfl, -⟩ := find?_cons_new hx hn
    exact hc
  · obtain ⟨hname, hdef⟩ := natOpStored_cons_new hst hn
    refine hb hdef ?_
    rw [hname]
    exact hcb

/-! ## A full-grade inference establishes its subject's arity -/

mutual

theorem red_arOk_aux {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → True
  | _, _, _, _ => trivial

theorem defEq_arOk_aux {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

/-- **A full-grade inference's subject is arity-correct**, given its annotations'. -/
theorem infer_full_arOk {env : Env md} :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      (∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true) → Expr.arOk env e = true
  | _, _, _, _, .sort, _, _ => rfl
  | _, _, _, _, .fvar (idx := idx) (ty := ty) _, _, hl => hl (idx, ty) (by simp [Expr.fvarLeaves])
  | _, _, _, _, .const hf _ hus, _, _ =>
    arOk_const_of (fun ci' hf' => by rw [hf] at hf'; cases hf'; exact hus)
  | _, _, _, _, .natLit _, _, _ => rfl
  | _, _, _, _, .strLit _, _, _ => rfl
  | _, _, _, _, .forallE (ty := ty) (body := body) hs _ hbs _ _, hg, hl => by
    have hl' := Ix.Kernel.Rules.leaves_forallE hl
    have hty := infer_full_arOk hs hg hl'.1
    have hb := infer_full_arOk hbs hg (Ix.Kernel.Rules.leaves_open _ hty hl'.1 hl'.2)
    exact Ix.Kernel.Rules.arOk_bind.mpr ⟨hty, arOk_of_instantiate1 body 0 hb⟩
  | _, _, _, _, .lam (ty := ty) (body := body) hs _ hbt _ _ _ _, hg, hl => by
    have hl' := Ix.Kernel.Rules.leaves_lam hl
    have hty := infer_full_arOk (hs hg) rfl hl'.1
    have hb := infer_full_arOk hbt hg (Ix.Kernel.Rules.leaves_open _ hty hl'.1 hl'.2)
    exact Ix.Kernel.Rules.arOk_lam.mpr ⟨hty, arOk_of_instantiate1 body 0 hb⟩
  | _, _, _, _, .app htf _ hta _, hg, hl => by
    have hl' := Ix.Kernel.Rules.leaves_app hl
    exact arOk_app.mpr ⟨infer_full_arOk htf hg hl'.1, infer_full_arOk hta hg hl'.2⟩
  | _, _, _, _, .appSkip .., hg, _ => nomatch hg
  | _, _, _, _, .proj htpe .., hg, hl => by
    have h := infer_full_arOk htpe hg (Ix.Kernel.Rules.leaves_proj hl)
    exact h

theorem certs_arOk_aux {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem defEqList_arOk_aux {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem etaProjCerts_arOk_aux {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us : List Ix.Kernel.Level} {targs : List (Expr md)} {b : Expr md}
      {lps : List Ix.Kernel.LevelParam} {is : List Nat},
      EtaProjCerts env d T us targs b lps is → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- **An annotated closed term inferred at the full grade is arity-correct.** -/
theorem arOk_of_annot_infer {env : Env md} {e e' t : Expr md} (hfv : e.hasFvar = false)
    (hann : rulesJ.annot env 0 e e') (hinf : rulesJ.infer env 0 e' t) :
    Expr.arOk env e' = true := by
  have hnf' : e'.hasFvar = false :=
    Ix.Kernel.Expr.not_hasFvar_of_fvarsBelow_zero
      ((annot_wscoped hann (Ix.Kernel.Expr.WScoped.of_not_hasFvar hfv)).fvarsBelow)
  refine infer_full_arOk hinf rfl (fun l hl => ?_)
  rw [Ix.Kernel.Rules.fvarLeaves_nil_of_hasFvar hnf'] at hl
  exact nomatch hl

/-- The checked type of a declaration front is arity-correct and resolves. -/
theorem arRes_of_cvRun {env : Env md} {cv : ConstantVal md} {type' : Expr md}
    (h : ConstantValRunJ rulesJ env cv type') : ArRes env type' := by
  obtain ⟨-, -, -, -, -, hfv, hann, -, hres, stype, u, hinf, -⟩ := h
  exact ⟨arOk_of_annot_infer hfv hann hinf, hres⟩

/-- The checked value of a declaration front is arity-correct and resolves. -/
theorem arRes_of_valueFront {env : Env md} {cv : ConstantVal md} {value type' value' : Expr md}
    (h : ValueFrontRunJ rulesJ env cv value type' value') : ArRes env value' := by
  obtain ⟨-, hfv, hann, -, hres, vtype, hinf, -⟩ := h
  exact ⟨arOk_of_annot_infer hfv hann hinf, hres⟩

/-- A checked constant is arity-correct and resolves. -/
theorem arRes_of_cvCheck {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ rulesJ env cv cv') : ArRes env cv'.type := by
  obtain ⟨type', hrun, rfl⟩ := h
  exact arRes_of_cvRun hrun

/-! ## The value constants -/

theorem ConstArR.of_thm {env : Env md} {cv : ConstantVal md} {v : Expr md}
    (ht : ArRes env cv.type) (hv : ArRes env v) : ConstArR env (.thmInfo cv v) where
  type := ht
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => by cases he; exact hv
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => nomatch he

theorem ConstArR.of_defn {env : Env md} {cv : ConstantVal md} {v : Expr md}
    {hint : Ix.Kernel.ReducibilityHint}
    (ht : ArRes env cv.type) (hv : ArRes env v) : ConstArR env (.defnInfo cv v hint) where
  type := ht
  defn := fun _ _ _ he => by cases he; exact hv
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => nomatch he

theorem ConstArR.of_axiom {env : Env md} {cv : ConstantVal md}
    (ht : ArRes env cv.type) : ConstArR env (.axiomInfo cv) where
  type := ht
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => nomatch he

theorem ConstArR.of_ind {env : Env md} {cv : ConstantVal md} {caps : IndCaps md}
    (ht : ArRes env cv.type) : ConstArR env (.indInfo cv caps) where
  type := ht
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => nomatch he

theorem ConstArR.of_ctor {env : Env md} {cv : ConstantVal md} {nP nF : Nat}
    (ht : ArRes env cv.type) : ConstArR env (.ctorInfo cv nP nF) where
  type := ht
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => nomatch he

/-- **The `Bool` values a comparison's install pins.** -/
theorem boolLvPinned_of_natOpGuard {env : Env md} {c : Key md}
    (h : Ix.Kernel.natOpGuard env c = true)
    (hc : c = Ix.Kernel.natBeqName ∨ c = Ix.Kernel.natBleName) : BoolLvPinned env := by
  unfold Ix.Kernel.natOpGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hb⟩ := h
  split at hb
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨hT, hF⟩ := hb
    constructor
    · revert hT
      cases hfT : env.find? Ix.Kernel.boolTrueName with
      | none => intro hT; simp at hT
      | some ci => intro hT; exact ⟨ci, rfl, by simpa using hT⟩
    · revert hF
      cases hfF : env.find? Ix.Kernel.boolFalseName with
      | none => intro hF; simp at hF
      | some ci => intro hF; exact ⟨ci, rfl, by simpa using hF⟩
  · rename_i hne
    exfalso
    apply hne
    rcases hc with rfl | rfl <;> simp

/-- The comparisons are among the certified operations. -/
theorem natOpNames_contains_cmp {c : Key md}
    (hc : c = Ix.Kernel.natBeqName ∨ c = Ix.Kernel.natBleName) :
    (Ix.Kernel.natOpNames (md := md)).contains c = true := by
  rcases hc with rfl | rfl <;> simp [Ix.Kernel.natOpNames]

/-! ## Excluding the other kinds of step at one fresh value constant -/

/-- A definition, a theorem or an axiom. -/
def IsValueCI (ci : ConstantInfo md) : Prop :=
  (∃ cv v h, ci = .defnInfo cv v h) ∨ (∃ cv v, ci = .thmInfo cv v) ∨ ∃ cv, ci = .axiomInfo cv

theorem notValue_ind (cv : ConstantVal md) (caps : IndCaps md) :
    ¬ IsValueCI (.indInfo cv caps) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h

theorem notValue_ctor (cv : ConstantVal md) (a b : Nat) : ¬ IsValueCI (.ctorInfo cv a b) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h

theorem notValue_rec (cv : ConstantVal md) (a b : Nat) (rs : List (RecRule md)) :
    ¬ IsValueCI (.recInfo cv a b rs) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h

theorem notValue_proj (t : ProjTable md) : ¬ IsValueCI (.projInfo t) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩) <;> cases h

/-- Every basis block stores at least two constants. -/
theorem basis_two (kind : BasisKind) : 1 < (kind.declsA (md := md)).length := by
  cases kind <;> (cases md <;> decide +kernel)

/-- A basis block does not store exactly one constant. -/
theorem not_one_basis {env env₂ : Env md} {kind : BasisKind} {ci : ConstantInfo md}
    (hb : DeclBasisRun env kind env₂) (henv : env₂ = ⟨ci :: env.consts⟩) : False := by
  obtain ⟨-, hinst⟩ := hb
  obtain ⟨hE, -⟩ := basisInstallRun_eq hinst
  rw [henv] at hE
  have hl := congrArg (fun e : Env md => e.consts.length) hE
  simp only [List.length_cons, List.length_append, List.length_reverse] at hl
  have := basis_two (md := md) kind
  omega

/-- An environment is not its own extension by one constant. -/
theorem not_self_cons {env : Env md} {ci : ConstantInfo md} (h : env = ⟨ci :: env.consts⟩) :
    False := by
  have hl := congrArg (fun e : Env md => e.consts.length) h
  simp only [List.length_cons] at hl
  omega

/-- **An inductive route does not store exactly one fresh value constant.** -/
theorem not_value_routes {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} {ci : ConstantInfo md}
    (hI : IndRoutesJ J env block nP env₂) (henv : env₂ = ⟨ci :: env.consts⟩)
    (hfresh : env.find? ci.name = none) (hval : IsValueCI ci) : False := by
  have hself : env₂.find? ci.name = some ci := by
    rw [henv]
    exact Ix.Kernel.Env.find?_cons_self ci env
  have hnew : ∀ {Q : ConstantInfo md → Prop}, NewSat env env₂ Q → Q ci := fun hQ => by
    rcases hQ _ _ hself with h | h
    · rw [hfresh] at h
      exact nomatch h
    · exact h
  rcases hI with ⟨_, -, hN⟩ | hM | ⟨_, -, hN⟩ | hT
  · exact hnew (Q := fun x => ¬ IsValueCI x)
      (native_newSat notValue_ind notValue_ctor notValue_rec notValue_proj hN) hval
  · exact hnew (Q := fun x => ¬ IsValueCI x)
      (modeled_newSat (fun cv => notValue_ind cv {}) notValue_ctor notValue_rec hM) hval
  · exact hnew (Q := fun x => ¬ IsValueCI x)
      (nativeNoRec_newSat notValue_ind notValue_ctor notValue_proj hN) hval
  · obtain ⟨ws, f, hne, -, hE, -⟩ := hT
    rw [henv] at hE
    have hc := congrArg Env.consts hE
    cases ws with
    | nil => exact hne rfl
    | cons w ws' =>
      simp only [twinRecs, List.map_cons, List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact notValue_rec _ _ _ _ hval

/-- `⟨a :: env.consts⟩ = ⟨b :: env.consts⟩` names the same head. -/
theorem cons_env_inj {env : Env md} {a b : ConstantInfo md}
    (h : (⟨a :: env.consts⟩ : Env md) = ⟨b :: env.consts⟩) : a = b := by
  injection h with h'
  injection h' with h1 h2

/-! ## The value step -/

/-- **A declaration step that stores one fresh definition, theorem or axiom keeps `StoreArR`.**
The stored type and value were inferred at the full grade (`infer_full_arOk`) and resolve (the
front's checks); a comparison of `Nat` finds the `Bool` values pinned (`natOpGuard`). -/
theorem storeArR_declRunJ_value {env env₂ : Env md} {ci : ConstantInfo md}
    {d : Declaration md} (h : StoreArR env) (hfresh : env.find? ci.name = none)
    (hval : IsValueCI ci) (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂)
    (henv : env₂ = ⟨ci :: env.consts⟩) : StoreArR env₂ := by
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, hvf, rfl⟩ := hrun
    obtain rfl := cons_env_inj henv
    exact storeArR_cons h hfresh
      (ConstArR.of_thm ((arRes_of_cvRun hcv).mono (find?_cons_fresh_ext hfresh)) ((arRes_of_valueFront hvf).mono (find?_cons_fresh_ext hfresh)))
      (fun ⟨_, _, _, he⟩ => nomatch he)
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvf, rfl, hnat, -⟩ := hrun
    obtain rfl := cons_env_inj henv
    exact storeArR_cons h hfresh
      (ConstArR.of_defn ((arRes_of_cvRun hcv).mono (find?_cons_fresh_ext hfresh)) ((arRes_of_valueFront hvf).mono (find?_cons_fresh_ext hfresh)))
      (fun _ hcb => boolLvPinned_of_natOpGuard (hnat (natOpNames_contains_cmp hcb)).1 hcb)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    obtain rfl := cons_env_inj henv
    exact storeArR_cons h hfresh (ConstArR.of_axiom ((arRes_of_cvRun hcv).mono (find?_cons_fresh_ext hfresh)))
      (fun ⟨_, _, _, he⟩ => nomatch he)
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact (not_self_cons henv).elim
    · obtain rfl := cons_env_inj henv
      exact storeArR_cons h hfresh (ConstArR.of_axiom ((arRes_of_cvRun hcv).mono (find?_cons_fresh_ext hfresh)))
        (fun ⟨_, _, _, he⟩ => nomatch he)
    · exact (not_self_cons henv).elim
  | basisDecl kind => exact (not_one_basis hrun henv).elim
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact (not_one_basis hrun henv).elim
    · exact (not_value_routes hrun henv hfresh hval).elim
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact (not_one_basis hrun henv).elim
    · subst hrun
      exact (not_self_cons henv).elim

end Ix.Kernel.Model
