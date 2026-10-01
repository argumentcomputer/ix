module

import ConLeche.Verify.Subst
public import ConLeche.Verify.Leaves
public import ConLeche.Verify.InstLevels

public section

/-!
# Syntactic kit for `Expr.instSpine`

`Expr.instSpine` (kernel) instantiates a telescope-context expression
at an argument spine; it is definitionally the verification's
`instSeq`.  The nested-auxiliary iota path fabricates
`instSpine args pin` comparands at fire time, so the scoping /
shift-invariance / resolution walks need the usual preservation
lemmas, plus the `instSeq` bridge for the model layer.
-/

namespace ConLeche

open Expr

/-- `Expr.instSpine` is the verification's `instSeq`. -/
theorem Expr.instSpine_eq_instSeq :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      Expr.instSpine args t e = instSeq args t e
  | [], _, _ => rfl
  | _ :: as, t, _e => Expr.instSpine_eq_instSeq as (t - 1) _

/-- `shiftFrom` commutes with `instSpine` (arguments shifted
pointwise). -/
theorem shiftFrom_instSpine {p : Nat} :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      shiftFrom p (Expr.instSpine args t e) =
        Expr.instSpine (args.map (shiftFrom p)) t (shiftFrom p e)
  | [], _, _ => rfl
  | a :: as, t, e => by
    show shiftFrom p (Expr.instSpine as (t - 1) (e.instantiate1 a t)) = _
    rw [shiftFrom_instSpine as (t - 1) _, shiftFrom_instantiate1_gen]
    rfl

/-- `instSpine` keeps terms well-scoped: a closed (fvar-free) base
instantiated at well-scoped arguments is well-scoped. -/
theorem instSpine_WScoped {d : Nat} :
    ∀ {args : List Expr} (t : Nat) {e : Expr}, WScoped d e →
      (∀ a ∈ args, WScoped d a) →
      WScoped d (Expr.instSpine args t e)
  | [], _, _, he, _ => he
  | a :: _as, t, _e, he, hargs =>
    instSpine_WScoped (t - 1)
      (WScoped.instantiate1_gen (hargs a List.mem_cons_self) t he)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- A full-telescope `instSpine` at bvar-closed arguments closes the
base: a term bounded by `args.length` binders instantiated at the
whole spine is bvar-closed. -/
theorem instSpine_closed :
    ∀ {args : List Expr} {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded args.length = true →
      (Expr.instSpine args (args.length - 1) e).looseBVarsBounded 0
        = true
  | [], e, _, he => he
  | a :: as, e, hargs, he => by
    show (Expr.instSpine as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))).looseBVarsBounded 0
      = true
    have hlen : (a :: as).length - 1 = as.length := by
      simp only [List.length_cons, Nat.add_sub_cancel]
    rw [hlen]
    have h1 : (e.instantiate1 a as.length).looseBVarsBounded as.length
        = true :=
      looseBVarsBounded_instantiate1_gen (k := as.length)
        (hargs a List.mem_cons_self)
        (by simpa [List.length_cons] using he)
    exact instSpine_closed
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) h1

/-- The fvar leaves of an `instSpine` come from the base or the
arguments. -/
theorem fvarLeaves_instSpine :
    ∀ {args : List Expr} (t : Nat) {e : Expr} {l},
      l ∈ (Expr.instSpine args t e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ a ∈ args, l ∈ a.fvarLeaves
  | [], _, _, _, hl => Or.inl hl
  | a :: as, t, e, l, hl => by
    rcases fvarLeaves_instSpine (t - 1) hl with hl' | ⟨a', ha', hla'⟩
    · rcases fvarLeaves_instantiate1 e t hl' with hl'' | hl''
      · exact Or.inl hl''
      · exact Or.inr ⟨a, List.mem_cons_self, hl''⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hla'⟩

/-- Resolution survives substitution by an arbitrary resolving term
(the fvar-annotation-specific `constsResolve_instantiate1`
generalized). -/
theorem Expr.constsResolve_instantiate1_gen {env : Env} {v : Expr}
    (hv : v.constsResolve env = true) :
    ∀ {e : Expr} (k : Nat), e.constsResolve env = true →
      (e.instantiate1 v k).constsResolve env = true := by
  intro e
  induction e <;> intro k h <;>
    simp_all [Expr.instantiate1, Expr.constsResolve]
  case bvar i =>
    split
    · exact hv
    · split <;> simp [Expr.constsResolve]

/-- Resolution survives `instSpine` (base and arguments resolving). -/
theorem instSpine_constsResolve {env : Env} :
    ∀ {args : List Expr} (t : Nat) {e : Expr},
      e.constsResolve env = true →
      (∀ a ∈ args, a.constsResolve env = true) →
      (Expr.instSpine args t e).constsResolve env = true
  | [], _, _, he, _ => he
  | a :: _as, t, _e, he, hargs =>
    instSpine_constsResolve (t - 1)
      (Expr.constsResolve_instantiate1_gen
        (hargs a List.mem_cons_self) t he)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-! ## The firing comparands under shifts -/

/-- The level comparand of a rule does not depend on the argument
spine. -/
theorem recFireComparands_fst_congr (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args args' : List Expr)
    (mI : Nat) :
    (recFireComparands rl lps us cvjLps args mI).1 =
      (recFireComparands rl lps us cvjLps args' mI).1 := by
  cases hf : rl.fire <;> simp [recFireComparands, hf]

/-- The parameter comparand commutes with `shiftFrom` on the argument
spine (the stored instantiations of a nested rule are fvar-free). -/
theorem recFireComparands_snd_shift {p : Nat} (rl : RecRule)
    (lps : List Name) (us : List Level) (cvjLps : List Name)
    (args : List Expr) (mI : Nat)
    (hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ pin ∈ pins, pin.hasFvar = false) :
    (recFireComparands rl lps us cvjLps
        (args.map (shiftFrom p)) mI).2 =
      ((recFireComparands rl lps us cvjLps args mI).2).map
        (shiftFrom p) := by
  cases hf : rl.fire with
  | nested lvls pins =>
    simp only [recFireComparands, hf, List.map_map]
    refine List.map_congr_left ?_
    intro pin hpin
    show Expr.instSpine ((args.map (shiftFrom p)).take mI) (mI - 1)
        (pin.instantiateLevelParams lps us) =
      shiftFrom p (Expr.instSpine (args.take mI) (mI - 1)
        (pin.instantiateLevelParams lps us))
    rw [shiftFrom_instSpine, List.map_take,
      shiftFrom_eq_self_of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact hpins lvls pins hf pin hpin)]
  | inert =>
    simp only [recFireComparands, hf, List.map_take]
  | plain =>
    simp only [recFireComparands, hf, List.map_take]

/-- The parameter comparand's entries are well-scoped at the ambient
depth (arguments well-scoped; a nested rule's stored instantiations
fvar-free). -/
theorem recFireComparands_snd_WScoped {d : Nat} (rl : RecRule)
    (lps : List Name) (us : List Level) (cvjLps : List Name)
    (args : List Expr) (mI : Nat)
    (hargs : ∀ a ∈ args, WScoped d a)
    (hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ pin ∈ pins, pin.hasFvar = false) :
    ∀ x ∈ (recFireComparands rl lps us cvjLps args mI).2,
      WScoped d x := by
  cases hf : rl.fire with
  | nested lvls pins =>
    intro x hx
    simp only [recFireComparands, hf, List.mem_map] at hx
    obtain ⟨pin, hpin, rfl⟩ := hx
    exact instSpine_WScoped _
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact hpins lvls pins hf pin hpin))
      (fun a ha => hargs a (List.mem_of_mem_take ha))
  | inert =>
    intro x hx
    simp only [recFireComparands, hf] at hx
    exact hargs x (List.mem_of_mem_take hx)
  | plain =>
    intro x hx
    simp only [recFireComparands, hf] at hx
    exact hargs x (List.mem_of_mem_take hx)

/-- A telescope that strips syntactically admits any instantiation
walk of matching length.  A statement about `Expr` alone, and what the
install layer needs: the projection bottom constructs its
constructor/recursor `instPisAt` runs from the checker's `stripPis`
pins rather than from a stored run. -/
theorem instPisAt_isSome_of_stripPis :
    ∀ (args : List Expr) {e : Expr},
      (e.stripPis args.length).isSome = true →
      (Expr.instPisAt args e).isSome = true
  | [], e, _ => by simp [Expr.instPisAt]
  | a :: as, e, h => by
    match e, h with
    | .forallE dom body m, h =>
      simp only [List.length_cons, Expr.stripPis, Option.isSome_map] at h
      have h' : ((body.instantiate1 a).stripPis as.length).isSome = true :=
        Expr.stripPis_instantiate1_isSome as.length 0 h
      have := instPisAt_isSome_of_stripPis as h'
      simp only [Expr.instPisAt, Option.isSome_map]
      exact this

/-! ## The rule-shape residue

The four `V`-free facts about `recRulePlain` and `recFireComparands`
that task #148's T1 relocation pass did not cover; both verified lanes'
recursor-group installs read them, so they sit here rather than in
either lane (relocated verbatim from
`ConLeche/TTVerify/DeclIndRecs.lean`, task #148 T5 stage 3). -/

/-- A canonical rule's constructor parameters are among the recursor's
prefix. -/
theorem recRulePlain_leT {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) :
    cnP ≤ rP := by
  rw [Expr.recRulePlain, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1

/-- A canonical rule's prefix fits under the major's position. -/
theorem recRulePlain_le_mIT {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) :
    rP ≤ mI := by
  rw [Expr.recRulePlain, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

/-- The fire comparand levels of a plain rule. -/
theorem recFireComparands_plain {rl : RecRule} {lps : List Name}
    {us : List Level} {cvjLps : List Name} {args : List Expr} {rP : Nat}
    (h : RecRule.fire rl = .plain) :
    (recFireComparands rl lps us cvjLps args rP).1 =
      cvjLps.map fun p => Level.subst lps us (.param p) := by
  unfold recFireComparands
  rw [h]

/-- The fire comparand levels of a nested rule. -/
theorem recFireComparands_nested {rl : RecRule} {lps : List Name}
    {us : List Level} {cvjLps : List Name} {args : List Expr} {rP : Nat}
    {lvls : List Level} {pins : List Expr}
    (h : RecRule.fire rl = .nested lvls pins) :
    (recFireComparands rl lps us cvjLps args rP).1 =
      lvls.map (Level.subst lps us) := by
  unfold recFireComparands
  rw [h]

/-! ## Two scoping facts the cached call-discipline needs

Rehomed here at task #221 with the deletion of `Verify/Disc.lean` (the
*memoized* knot's call discipline, whose knot induction had already
gone): these two were the only
declarations of that module the cached discipline
(`Verify/Cached/DiscC*.lean`) still read. -/

/-- A list of well-scoped expressions has a well-scoped `getD`. -/
theorem wscoped_getD {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x (List.mem_cons_self ..)
    | succ n =>
      simpa [List.getD] using
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- A level-instantiated `fvar`-free expression (e.g. a stored type or
rule right-hand side) is well-scoped at any depth. -/
theorem wscoped_instLevels_of_not_hasFvar {e : Expr}
    (h : e.hasFvar = false) (ps : List Name) (us : List Level) {d : Nat} :
    WScoped d (e.instantiateLevelParams ps us) :=
  WScoped.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact h)

end ConLeche
