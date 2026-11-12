module

public import IxC.Kernel.Model.StoreFold
public import IxC.Kernel.Semantics.DeclExt
public import IxC.Kernel.Semantics.Inductives.DeclNativeExtJ
/- `Ix.Kernel.PropWhen` seals its representation; the pinned recursors' rule heads are decided
by evaluating terms that carry it, so `import all` gives that view HERE only. -/
import all IxC.Kernel.PropWhen

@[expose] public section

/-!
# A block installed without its recursor is never eliminated through a recursor

The native route without a recursor record (`DeclNativeNoRecRunJ`) installs a family `T`, its
constructors and, at a structure-like block, its projection table, and no recursor. This file
proves that no rule that reads a recursor can then fire on `T`:

* `NoRuleFamily env T`: no rule of any stored recursor is at a constructor whose type ends in
  `T`. The install leaves it holding (`noRuleFamily_noRec`, which also says the route stores no
  recursor at any key, the stub's `Key.aux T .recursor` among them);
* at such an environment, the major premise of an `ι` step is never a constructor of `T`
  (`iota_ctor_family_ne`), and the family of the K, structure-η and `And` rescues, each of which
  fires the single rule of a stored recursor, is never `T` (`rescue_family_ne`);
* every later declaration keeps it (`noRuleFamily_declsRunJ`): the value kinds and the native
  routes without a recursor install no recursor; a basis block's recursors are at constructors of
  reserved families, which `T` is not; the native route's recursor is at the constructors of the
  block's own former, which is fresh while `T` is stored, so `T`'s own recursor can never arrive
  later (`nativeRoute_former_ne`). The modeled route installs rules at the constructors its
  declared recursors name; that they avoid `T` is the lemma's explicit hypothesis on the run's
  modeled blocks (`NewRulesAvoid`), which the reading supplies.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (Env Key Expr Level ConstantInfo ConstantVal RecRule Declaration BasisKind IndCaps
  InductiveShape NativeParts RecFieldKind)

/-! ## Expressions -/

theorem constsResolve_piResult {env : Env md} :
    ∀ {e : Expr md}, e.constsResolve env = true → e.piResult.constsResolve env = true := by
  intro e
  induction e with
  | forallE ty b m _ ihb =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ihb h.2
  | _ => intro h; exact h

theorem constsResolve_getAppFn {env : Env md} :
    ∀ {e : Expr md}, e.constsResolve env = true → e.getAppFn.constsResolve env = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ihf h.1
  | _ => intro h; exact h

theorem piResult_of_stripPis : ∀ (k : Nat) {e body : Expr md}
    {bs : List (Expr md × Ix.Kernel.BinderMeta)},
    e.stripPis k = some (bs, body) → e.piResult = body.piResult := by
  intro k
  induction k with
  | zero =>
    intro e body bs h
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | succ k ih =>
    intro e body bs h
    cases e with
    | forallE ty b m =>
      cases hb : Ix.Kernel.Expr.stripPis k b with
      | none => simp [Ix.Kernel.Expr.stripPis, hb] at h
      | some q =>
        obtain ⟨bs', e'⟩ := q
        simp [Ix.Kernel.Expr.stripPis, hb] at h
        obtain ⟨-, rfl⟩ := h
        show b.piResult = _
        exact ih hb
    | _ => simp [Ix.Kernel.Expr.stripPis] at h

/-- An application spine whose head is not a `∀` is its own telescope body. -/
theorem piResult_mkAppN : ∀ (args : List (Expr md)) (f : Expr md),
    (∀ ty b m, f ≠ .forallE ty b m) → (Expr.mkAppN f args).piResult = Expr.mkAppN f args
  | [], f, hf => by
    cases f with
    | forallE ty b m => exact absurd rfl (hf ty b m)
    | _ => rfl
  | a :: as, f, _ => piResult_mkAppN as (.app f a) (fun _ _ _ h => nomatch h)

/-- The family a constructor's stored type ends in, at a constructor stage's residual. -/
theorem family_of_residual {ty : Expr md} {k : Nat} {bs : List (Expr md × Ix.Kernel.BinderMeta)}
    {T : Key md} {us : List Level} {args : List (Expr md)}
    (h : ty.stripPis k = some (bs, Expr.mkAppN (.const T us) args)) :
    ty.piResult.getAppFn = .const T us := by
  rw [piResult_of_stripPis k h, piResult_mkAppN args (.const T us) (fun _ _ _ h => nomatch h),
    Ix.Kernel.Expr.getAppFn_mkAppN]
  rfl

/-! ## The invariant -/

/-- **No stored recursor's rule is at a constructor of `T`**: every rule of every stored
recursor is at a stored constructor whose type does not end in `T`. -/
def NoRuleFamily (env : Env md) (T : Key md) : Prop :=
  ∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules,
    ∀ cvj cnP cnF, env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      ∀ us, (cvj.type.piResult).getAppFn ≠ .const T us

/-- **A step's new recursors avoid `T`**: every recursor stored after the step under a key that
was free before it has its rules at constructors whose types do not end in `T`. -/
def NewRulesAvoid (env env' : Env md) (T : Key md) : Prop :=
  ∀ n cv mI rP rules, env'.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
    ∀ rl ∈ rules, ∀ cvj cnP cnF, env'.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      ∀ us, (cvj.type.piResult).getAppFn ≠ .const T us

/-- **Before `T` is stored, no rule is at a constructor of `T`**: a stored constructor's type
resolves, so the family it ends in is stored. -/
theorem noRuleFamily_of_fresh {env : Env md} {T : Key md} (h : StoreInv env)
    (hT : env.find? T = none) : NoRuleFamily env T := by
  intro n cv mI rP rules hf rl hrl cvj cnP cnF hc us heq
  have hres : cvj.type.constsResolve env = true :=
    (h.wf _ (Ix.Kernel.Semantics.Env.find?_mem hc)).2.2.1
  have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
  rw [heq] at h2
  simp [Ix.Kernel.Expr.constsResolve, hT] at h2

/-- **One step keeps the invariant** when it keeps the old lookups and its new recursors avoid
`T`. -/
theorem noRuleFamily_step {env env' : Env md} {T : Key md} (h : NoRuleFamily env T)
    (hrc : Ix.Kernel.RecCtorsStored env)
    (hfind : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c → env'.find? k = some c)
    (hn : NewRulesAvoid env env' T) : NoRuleFamily env' T := by
  intro n cv mI rP rules hf rl hrl cvj cnP cnF hc us
  cases hold : env.find? n with
  | none => exact hn n cv mI rP rules hf hold rl hrl cvj cnP cnF hc us
  | some ci =>
    have hf' := hfind hold
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨cvj', hc', -⟩ := (hrc n cv mI rP rules hold rl hrl).1
    have hc'' := hfind hc'
    rw [hc] at hc''
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc'')
    exact h n cv mI rP rules hold rl hrl _ _ _ hc' us

/-- A step that stores no recursor under a new key. -/
theorem newRulesAvoid_of_noNewRec {env env' : Env md} {T : Key md}
    (h : ∀ {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
      env'.find? n = some (.recInfo cv mI rP rules) →
      env.find? n = some (.recInfo cv mI rP rules)) : NewRulesAvoid env env' T := by
  intro n cv mI rP rules hf hn0
  rw [h hf] at hn0
  exact nomatch hn0

/-! ## The owner's condition at the rules -/

/-- **No ι step on `T`**: at an environment keeping `NoRuleFamily env T`, the constructor an ι
step's major premise is headed by (`Red.iota`'s `major.getAppFn = .const cj usj`,
`env.find? cj = some (.ctorInfo cvj cnP cnF)` and the rule found at `cj`) has a type that does
not end in `T`. -/
theorem iota_ctor_family_ne {env : Env md} {T : Key md} (h : NoRuleFamily env T)
    {c cj : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {rl : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat}
    (hc : env.find? c = some (.recInfo cv mI rP rules))
    (hcj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrl : rules.find? (fun r' => r'.ctor == cj) = some rl) :
    ∀ us, (cvj.type.piResult).getAppFn ≠ .const T us := by
  have hmem := List.mem_of_find?_eq_some hrl
  have hct : rl.ctor = cj := by simpa using List.find?_some hrl
  exact h c cv mI rP rules hc rl hmem cvj cnP cnF (by rw [hct]; exact hcj)

/-- **No recursor-reading rescue on `T`**: the K, structure-η and `And` rescues (`Red.rescueK`,
`Red.rescueEta`, `Red.rescueAnd`) each fire the single rule `rl` of a stored recursor at a
constructor whose type ends in the rescue's family `T'`; at an environment keeping
`NoRuleFamily env T`, `T'` is not `T`. -/
theorem rescue_family_ne {env : Env md} {T : Key md} (h : NoRuleFamily env T)
    {recName : Key md} {cv : ConstantVal md} {mI rP : Nat} {rl : RecRule md}
    {cvj : ConstantVal md} {cnP cnF : Nat} {T' : Key md} {tus : List Level}
    (hr : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hc : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hT' : (cvj.type.piResult).getAppFn = .const T' tus) : T' ≠ T := by
  intro he
  subst he
  exact h recName cv mI rP [rl] hr rl List.mem_cons_self cvj cnP cnF hc tus hT'

/-! ## The steps' new recursors -/

theorem find?_rec_of_cons {env : Env md} {c : ConstantInfo md} {n : Key md}
    {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : Env.find? ⟨c :: env.consts⟩ n = some (.recInfo cv mI rP rules))
    (hc : ∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) :
    env.find? n = some (.recInfo cv mI rP rules) := by
  rw [Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · exact absurd (Option.some.inj hf) (hc cv mI rP rules)
  · exact hf

theorem consSumCtors_rec {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {env : Env md} {n : Key md} {cv : ConstantVal md}
      {mI rP : Nat} {rules : List (RecRule md)},
      (Ix.Kernel.consSumCtors nP ctorsA env).find? n = some (.recInfo cv mI rP rules) →
      env.find? n = some (.recInfo cv mI rP rules)
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, _, _, _, _, _, h => by
    simp only [Ix.Kernel.consSumCtors] at h
    exact find?_rec_of_cons (consSumCtors_rec h) (fun _ _ _ _ heq => nomatch heq)

theorem nativeTable_rec {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {X X₂ : Env md}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : X₂.find? n = some (.recInfo cv mI rP rules)) :
    X.find? n = some (.recInfo cv mI rP rules) := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact find?_rec_of_cons hf (fun _ _ _ _ heq => nomatch heq)
    · obtain rfl := Except.ok.inj h
      exact hf
  · obtain rfl := Except.ok.inj h
    exact hf

theorem nativeTable_keep {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {X X₂ : Env md}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂)
    {k : Key md} {c : ConstantInfo md} (hf : X.find? k = some c) : X₂.find? k = some c := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact Ix.Kernel.Env.find?_cons_of_fresh hfresh hf
    · obtain rfl := Except.ok.inj h
      exact hf
  · obtain rfl := Except.ok.inj h
    exact hf

/-- The completed record's family is the recognised one. -/
theorem native_cvT {J : Judgements md} {env env₁ : Env md} {p₀ : NativeParts md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md} {p₁ : InductiveShape md}
    {kinds : List (List RecFieldKind)} {p : NativeParts md}
    (hInd : SumIndRunJ J env p₀.toInductiveShape capsOf env₁ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds) : p.cvT = p₀.cvT := by
  obtain ⟨_, s, _, _, _, rfl, _, _, _⟩ := hInd.shape
  subst hp
  simp [NativeParts.withKinds]

/-- **The native routes' former is fresh**: a family already stored is never a native block's
former again, so `T`'s own recursor cannot arrive through the native route once `T` is stored. -/
theorem nativeRoute_former_ne {J : Judgements md} {env env₂ : Env md} {p₀ : NativeParts md}
    {T : Key md} (hT : (env.find? T).isSome = true) (hrun : DeclNativeRunJ J env p₀ env₂) :
    p₀.cvT.name ≠ T := by
  obtain ⟨-, isRec, env₁, cvTa, p₁, -, -, -, -, -, -, -, -, -, hInd, -⟩ := hrun
  obtain ⟨-, -, hf, -⟩ := hInd.former
  intro he
  rw [← he, hf] at hT
  exact nomatch hT

/-- **The native route without a recursor record stores no recursor**, at any key. -/
theorem declNativeNoRecRunJ_noNewRec {J : Judgements md} {env env₂ : Env md}
    {p₀ : NativeParts md} (hrun : DeclNativeNoRecRunJ J env p₀ env₂) {n : Key md}
    {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env₂.find? n = some (.recInfo cv mI rP rules)) :
    env.find? n = some (.recInfo cv mI rP rules) := by
  obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, -, -, -, -, -, -,
    -, hTbl⟩ := hrun
  obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
  have h1 := consSumCtors_rec (nativeTable_rec hTbl hf)
  rw [henv₁] at h1
  exact find?_rec_of_cons h1 (fun _ _ _ _ heq => nomatch heq)

/-- **The native route's new recursor avoids every stored family**: its rules are at the
block's own constructors, whose types end in the block's former, which is fresh. -/
theorem declNativeRunJ_newRulesAvoid {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {p₀ : NativeParts md} (hrc : NativeRecog p₀) (h : StoreInv env)
    {T : Key md} (hT : (env.find? T).isSome = true) (hrun : DeclNativeRunJ J env p₀ env₂) :
    NewRulesAvoid env env₂ T := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, hp,
    hCtors, -, -, -, -, -, -, -, hRec, -, hTbl⟩ := hrun
  have hF := nativeFront hfr h hrc hnd hInd hp hCtors
  have hfreshT' : env.find? p.cvT.name = none := by
    rw [native_cvT hInd hp]
    exact hInd.former.2.2.1
  obtain ⟨_, _, _, _, _, _, henv₁, _, _⟩ := hInd.shape
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  have hfreshR : (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
    rw [hnR]; exact hfR
  intro n cv mI rP rules hf hn0 rl hrl cvj cnP cnF hc us heq
  have hR := nativeTable_rec hTbl hf
  rw [Ix.Kernel.Env.find?_cons] at hR
  split at hR
  · obtain ⟨-, -, -, hrules⟩ := ConstantInfo.recInfo.inj (Option.some.inj hR)
    subst hrules
    obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hrl
    obtain ⟨hfC, -, -, cbs, es, hres, -⟩ := hF.ctor j cA hj
    have hfC₂ := nativeTable_keep hTbl (Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfC)
    have hc' : env₂.find? cA.1.name = some (.ctorInfo cvj cnP cnF) := hc
    rw [hc'] at hfC₂
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfC₂)
    rw [family_of_residual hres] at heq
    injection heq with hTT _
    rw [hTT] at hfreshT'
    rw [hfreshT'] at hT
    simp at hT
  · have h1 := consSumCtors_rec hR
    rw [henv₁] at h1
    rw [find?_rec_of_cons h1 (fun _ _ _ _ heq => nomatch heq)] at hn0
    exact nomatch hn0

/-- A pinned recursor's rules are at constructors of reserved families, decided against the
block. -/
def basisRuleHeadsb (F : Env md) : ConstantInfo md → Bool
  | .recInfo _ _ _ rules => rules.all fun r =>
      match F.find? r.ctor with
      | some (.ctorInfo cvj _ _) =>
        match cvj.type.piResult.getAppFn with
        | .const T' _ => Ix.Kernel.reservedBasisNames.contains T'
        | _ => false
      | _ => false
  | _ => true

theorem basis_rule_heads (kind : BasisKind) :
    ∀ c ∈ kind.declsA (md := md), basisRuleHeadsb ⟨kind.declsA.reverse⟩ c = true := by
  cases kind <;> (cases md <;> decide +kernel)

/-- A basis block keeps the stored lookups. -/
theorem basisRun_find {env env₂ : Env md} {kind : BasisKind} (hrun : DeclBasisRun env kind env₂)
    {k : Key md} {c : ConstantInfo md} (hf : env.find? k = some c) : env₂.find? k = some c := by
  obtain ⟨-, hinst⟩ := hrun
  obtain ⟨rfl, hfresh⟩ := basisInstallRun_eq hinst
  rw [find?_prefix]
  cases hb : Env.find? ⟨kind.declsA.reverse⟩ k with
  | none => simpa using hf
  | some ci' =>
    exfalso
    have hmem : ci' ∈ kind.declsA :=
      List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
    have hname : ci'.name = k := Ix.Kernel.Semantics.Env.find?_name hb
    rw [← hname, hfresh ci' hmem] at hf
    exact nomatch hf

/-- **A basis block's recursors avoid every unreserved family.** -/
theorem basis_newRulesAvoid {env env₂ : Env md} {kind : BasisKind} {T : Key md}
    (hTres : Ix.Kernel.reservedBasisNames.contains T = false)
    (hrun : DeclBasisRun env kind env₂) : NewRulesAvoid env env₂ T := by
  obtain ⟨-, hinst⟩ := hrun
  obtain ⟨rfl, -⟩ := basisInstallRun_eq hinst
  intro n cv mI rP rules hf hn0 rl hrl cvj cnP cnF hc us heq
  rw [find?_prefix, hn0] at hf
  have hb : Env.find? ⟨kind.declsA.reverse⟩ n = some (.recInfo cv mI rP rules) := by
    cases hb0 : Env.find? ⟨kind.declsA.reverse⟩ n with
    | none => rw [hb0] at hf; simp at hf
    | some ci => rw [hb0] at hf; simpa using hf
  have hmem := List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
  have hh := basis_rule_heads kind _ hmem
  simp only [basisRuleHeadsb, List.all_eq_true] at hh
  have hr := hh rl hrl
  revert hr
  split
  · next cvj' cnP' cnF' hfc =>
    have hc' : Env.find? ⟨kind.declsA.reverse ++ env.consts⟩ rl.ctor
        = some (.ctorInfo cvj' cnP' cnF') := by
      rw [find?_prefix, hfc]
      rfl
    rw [hc] at hc'
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
    rw [heq]
    intro hres
    simp only at hres
    rw [hTres] at hres
    cases hres
  · intro hr
    simp at hr

/-- A fresh cons of a constant that is not a recursor keeps the lookups and stores no recursor. -/
theorem cons_nonRec {env : Env md} {c₀ : ConstantInfo md} (hfresh : env.find? c₀.name = none)
    (hc : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) {T : Key md} :
    (∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c →
      Env.find? ⟨c₀ :: env.consts⟩ k = some c) ∧ NewRulesAvoid env ⟨c₀ :: env.consts⟩ T :=
  ⟨fun hf => Ix.Kernel.Env.find?_cons_of_fresh hfresh hf,
    newRulesAvoid_of_noNewRec fun hf => find?_rec_of_cons hf hc⟩

/-! ## The install, and the run after it -/

theorem noRuleFamily_of_step {env env₂ : Env md} {T : Key md} (h : StoreInv env)
    (hT : (env.find? T).isSome = true) (hno : NoRuleFamily env T)
    (hfind : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c → env₂.find? k = some c)
    (hnew : NewRulesAvoid env env₂ T) : NoRuleFamily env₂ T ∧ (env₂.find? T).isSome = true := by
  refine ⟨noRuleFamily_step hno h.rec_ctors hfind hnew, ?_⟩
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
  rw [hfind hci]
  rfl

/-- **The owner's condition at the install**: after the native route without a recursor record,
no stored rule is at a constructor of the block's family, the family is stored and is no reserved
name, and the route stored no recursor at any key. -/
theorem noRuleFamily_noRec {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {nP : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (h : StoreInv env) (hdp : nativePartsNoRec? nP block = some p₀)
    (hrun : DeclNativeNoRecRunJ J env p₀ env₂) :
    NoRuleFamily env₂ p₀.cvT.name ∧ (env₂.find? p₀.cvT.name).isSome = true ∧
      Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false ∧
      (∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) →
        env.find? n = some (.recInfo cv mI rP rules)) := by
  have hrc := nativeRecog_noRec hdp
  have hnoNew : ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) →
      env.find? n = some (.recInfo cv mI rP rules) :=
    fun _ _ _ _ _ hf => declNativeNoRecRunJ_noNewRec hrun hf
  refine ⟨?_, ?_, hrc.2, hnoNew⟩
  · have hfresh : env.find? p₀.cvT.name = none := by
      obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, -⟩ := hrun
      exact hInd.former.2.2.1
    exact noRuleFamily_step (noRuleFamily_of_fresh h hfresh) h.rec_ctors
      (declNativeNoRecRunJ_envExt hrun).find
      (newRulesAvoid_of_noNewRec fun hf => declNativeNoRecRunJ_noNewRec hrun hf)
  · obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp,
      hCtors, -, -, -, -, -, hTbl⟩ := hrun
    have hF := nativeFront hfr h hrc hnd hInd hp hCtors
    obtain ⟨caps, hfT⟩ := hF.former
    rw [native_cvT hInd hp] at hfT
    rw [nativeTable_keep hTbl hfT]
    rfl

/-- **One declaration step keeps the owner's condition**, given that a modeled block the step
installs puts its new rules away from `T`. -/
theorem noRuleFamily_declRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {d : Declaration md} {T : Key md}
    (hTres : Ix.Kernel.reservedBasisNames.contains T = false) (h : StoreInv env)
    (hT : (env.find? T).isSome = true) (hno : NoRuleFamily env T)
    (hmod : ∀ block nP, d = .indDecl block nP → ∀ env₁, DeclIndRunJ J env block env₁ →
      NewRulesAvoid env env₁ T)
    (hrun : DeclRunJ J (IndRoutesJ J env) env d env₂) :
    NoRuleFamily env₂ T ∧ (env₂.find? T).isSome = true := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    obtain ⟨hf, hn⟩ := cons_nonRec (T := T)
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ _ _ heq => nomatch heq)
    exact noRuleFamily_of_step h hT hno hf hn
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    obtain ⟨hf, hn⟩ := cons_nonRec (T := T)
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ (J.thmValue value value'))
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ _ _ heq => nomatch heq)
    exact noRuleFamily_of_step h hT hno hf hn
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    obtain ⟨hf, hn⟩ := cons_nonRec (T := T) (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ _ _ heq => nomatch heq)
    exact noRuleFamily_of_step h hT hno hf hn
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact ⟨hno, hT⟩
    · obtain ⟨hf, hn⟩ := cons_nonRec (T := T) (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ _ _ heq => nomatch heq)
      exact noRuleFamily_of_step h hT hno hf hn
    · exact ⟨hno, hT⟩
  | basisDecl kind =>
    exact noRuleFamily_of_step h hT hno (basisRun_find hrun) (basis_newRulesAvoid hTres hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact noRuleFamily_of_step h hT hno (basisRun_find hrun) (basis_newRulesAvoid hTres hrun)
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
      · exact noRuleFamily_of_step h hT hno (declNativeRunJ_envExt hN).find
          (declNativeRunJ_newRulesAvoid hfr (nativeRecog_of hdp) h hT hN)
      · exact noRuleFamily_of_step h hT hno (declIndRunJ_envExt hM).find
          (hmod block nP rfl _ hM)
      · exact noRuleFamily_of_step h hT hno (declNativeNoRecRunJ_envExt hN).find
          (newRulesAvoid_of_noNewRec fun hf => declNativeNoRecRunJ_noNewRec hN hf)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact noRuleFamily_of_step h hT hno (basisRun_find hrun) (basis_newRulesAvoid hTres hrun)
    · subst hrun
      exact ⟨hno, hT⟩

/-- **The owner's condition along a run**: from an environment keeping it (the install's,
`noRuleFamily_noRec`), every declaration of the run keeps it, given the run's modeled blocks put
their new rules away from `T` (`NewRulesAvoid`, the reading's obligation). With
`iota_ctor_family_ne` and `rescue_family_ne`, no ι step and no K, structure-η or `And` rescue
ever fires on `T` in the run. -/
theorem noRuleFamily_declsRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {T : Key md} (hTres : Ix.Kernel.reservedBasisNames.contains T = false) :
    ∀ {env env' : Env md} {ds : List (Declaration md)},
      DeclsRunJ J (IndRoutesJ J) env ds env' →
      (∀ block nP, Declaration.indDecl block nP ∈ ds → ∀ env₀ env₁,
        DeclIndRunJ J env₀ block env₁ → NewRulesAvoid env₀ env₁ T) →
      StoreInv env → (env.find? T).isSome = true → NoRuleFamily env T →
      NoRuleFamily env' T := by
  intro env env' ds hds
  induction hds with
  | nil => intro _ _ _ h; exact h
  | cons hd _ ih =>
    intro hmod h hT hno
    obtain ⟨hno₁, hT₁⟩ := noRuleFamily_declRunJ hfr hTres h hT hno
      (fun block nP hd' env₁ hM => hmod block nP (by rw [hd']; exact List.mem_cons_self) _ env₁ hM)
      hd
    exact ih (fun block nP hm env₀ env₁ hM => hmod block nP (List.mem_cons_of_mem _ hm) env₀ env₁ hM)
      (storeInv_declRunJ hfr (fun hI => storeInv_indRoutesJ hfr h hI) h hd) hT₁ hno₁

end Ix.Kernel.Model
