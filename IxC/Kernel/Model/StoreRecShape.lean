module

public import IxC.Kernel.Model.StoreCompanions
/- `Ix.Kernel.PropWhen` seals its representation; the pinned blocks' facts are decided by
evaluating terms that carry it, so `import all` gives that view HERE only. -/
import all IxC.Kernel.PropWhen

@[expose] public section

/-!
# The stored recursors' major premise and rule bits, along a run, model-free

Four facts about every stored recursor, kept by every declaration step of a run over the
derivation package (`DeclsRunJ rulesJ (IndRoutesJ rulesJ)`), collected per recursor in `RecAt`:

* `plainIdx`: at a recursor without a model companion, a plain rule's major premise domain has,
  after the rule's parameters, the index binders' bound variables as its arguments (the
  trailing `mI - rP` variables). The parameters' part and the head are `Expr.recRulePlain`'s,
  which the install tested.
* `ctorHead`: at a recursor without a model companion, a rule's constructor's type ends in the
  family heading the major premise's domain.
* `eta`: every rule's η bit is the store's verdict `recRuleEtaOf` at the recursor's key, at every
  recursor.
* `kParams`: at a recursor without a model companion, a single rule with the K bit has `rP - 2`
  parameters: the recursor's prefix is its parameters, one motive and one minor premise.

The native route's recursor has the generated major premise (`NativeRecJ.majorOf`), whichever of
the generated and the declared type it stores; the pinned basis blocks' recursors are decided
(`basis_shape`). A modeled recursor's type is its model's and its rules are the model's
equations, which nothing reads syntactically, so `plainIdx`, `ctorHead` and `kParams` are not
claimed there (`HasModel`, which every modeled recursor has, `declIndRunJ_hasModel`).
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (Env Key Expr Level ConstantInfo ConstantVal RecRule Declaration BasisKind IndCaps
  InductiveShape NativeParts RecFieldKind EnvExt)

/-! ## The facts -/

/-- **The four facts at the recursor stored at `n`**, at the store `env`. -/
structure RecAt (env : Env md) (n : Key md) (cv : ConstantVal md) (mI rP : Nat)
    (rules : List (RecRule md)) : Prop where
  /-- every rule's η bit is the store's verdict -/
  eta : ∀ r ∈ rules, r.eta = Ix.Kernel.recRuleEtaOf env.find? n r.ctor
  /-- a plain rule's major premise domain ends in the index binders' variables -/
  plainIdx : ¬ HasModel env n → ∀ r ∈ rules, r.fire = .plain →
    ∃ bs D B m, cv.type.stripPis mI = some (bs, .forallE D B m) ∧
      D.getAppArgs.drop r.ctorParams =
        (List.range (mI - rP)).map fun i => (Expr.bvar (mI - rP - 1 - i) : Expr md)
  /-- a rule's constructor builds the family heading the major premise's domain -/
  ctorHead : ¬ HasModel env n → ∀ r ∈ rules, ∀ cvj a b,
    env.find? r.ctor = some (.ctorInfo cvj a b) →
    ∀ bs D B m, cv.type.stripPis mI = some (bs, .forallE D B m) →
      ∀ T us, D.getAppFn = .const T us → ∃ tus, (cvj.type.piResult).getAppFn = .const T tus
  /-- a single K rule's parameters are the recursor's -/
  kParams : ¬ HasModel env n → ∀ r, rules = [r] → r.k = true → r.ctorParams + 2 = rP

/-- **The four facts at every stored recursor.** -/
def RecShape (env : Env md) : Prop :=
  ∀ n cv mI rP rules, env.find? n = some (.recInfo cv mI rP rules) → RecAt env n cv mI rP rules

theorem RecShape.empty : RecShape (md := md) Env.empty :=
  fun _ _ _ _ _ h => by simp [Env.find?, Env.empty] at h

/-! ## Old recursors -/

/-- **The η verdict is kept** by an extension that keeps the constructor's lookup and, unless
the constructor's family is already found, stores no inductive type at the family's key. -/
theorem recRuleEtaOf_ext {f g : Key md → Option (ConstantInfo md)} {c n : Key md}
    (hext : ∀ {k : Key md} {x : ConstantInfo md}, f k = some x → g k = some x)
    {cvj : ConstantVal md} {a b : Nat} (hc : f c = some (.ctorInfo cvj a b))
    (hT : ∀ T us, (cvj.type.piResult).getAppFn = .const T us →
      (f T).isSome = true ∨ ∀ x, g T = some x → f T = none → NotInd x) :
    Ix.Kernel.recRuleEtaOf f n c = Ix.Kernel.recRuleEtaOf g n c := by
  unfold Ix.Kernel.recRuleEtaOf
  rw [hc, hext hc]
  dsimp only
  generalize hh : (cvj.type.piResult).getAppFn = hd
  cases hd with
  | const T us =>
    dsimp only
    rcases hT T us hh with hs | hn
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
      rw [hy, hext hy]
    · cases hfT : f T with
      | some y => rw [hext hfT]
      | none =>
        cases hgT : g T with
        | none => rfl
        | some x =>
          cases x with
          | indInfo cv caps => exact absurd rfl (hn _ hgT hfT cv caps)
          | _ => rfl
  | _ => rfl

/-- An old rule's η verdict is kept by every extension: its constructor is stored, and so is
the family its type ends in. -/
theorem recRuleEtaOf_stable {env env₂ : Env md} (h : StoreInv env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env.find? n = some (.recInfo cv mI rP rules)) {r : RecRule md} (hr : r ∈ rules)
    (m : Key md) :
    Ix.Kernel.recRuleEtaOf env.find? m r.ctor = Ix.Kernel.recRuleEtaOf env₂.find? m r.ctor := by
  obtain ⟨⟨cvj, hc, -⟩, -, -⟩ := h.rec_ctors n cv mI rP rules hf r hr
  refine recRuleEtaOf_ext hfind hc (fun T us heq => .inl ?_)
  have hres : cvj.type.constsResolve env = true :=
    (h.wf _ (Ix.Kernel.Semantics.Env.find?_mem hc)).2.2.1
  have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
  rw [heq] at h2
  simpa [Ix.Kernel.Expr.constsResolve] using h2

/-- **One step keeps the facts**, given those of the recursors it stores. -/
theorem recShape_step {env env₂ : Env md} (h : StoreInv env) (hS : RecShape env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (hnew : ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) →
      env.find? n = none → RecAt env₂ n cv mI rP rules) :
    RecShape env₂ := by
  intro n cv mI rP rules hf
  cases hold : env.find? n with
  | none => exact hnew n cv mI rP rules hf hold
  | some c =>
    have h2 := hfind hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    have ho := hS n cv mI rP rules hold
    refine ⟨fun r hr => ?_, fun hm => ho.plainIdx (fun hm' => hm (hm'.mono hfind)),
      fun hm r hr cvj a b hc => ?_, fun hm => ho.kParams (fun hm' => hm (hm'.mono hfind))⟩
    · rw [ho.eta r hr]
      exact recRuleEtaOf_stable h hfind hold hr n
    · obtain ⟨⟨cvj', hc', -⟩, -, -⟩ := h.rec_ctors n cv mI rP rules hold r hr
      have h3 := hfind hc'
      rw [hc] at h3
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj h3)
      exact ho.ctorHead (fun hm' => hm (hm'.mono hfind)) r hr _ _ _ hc'

/-- A step that stores no recursor keeps the facts. -/
theorem recShape_step_noRec {env env₂ : Env md} (h : StoreInv env) (hS : RecShape env)
    (hfind : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x → env₂.find? k = some x)
    (hno : NewSat env env₂ NotRec) : RecShape env₂ := by
  refine recShape_step h hS hfind ?_
  intro n cv mI rP rules hf hn
  rcases hno _ _ hf with h' | h'
  · rw [h'] at hn
    exact nomatch hn
  · exact absurd rfl (h' cv mI rP rules)

/-! ## The native route -/

theorem sumRules_length_of {find? : Key md → Option (ConstantInfo md)} {recName : Key md}
    {nP mI rP : Nat} {recTy : Expr md} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)},
      rhss.length = ctorsA.length →
      (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhss).length = ctorsA.length
  | [], _, _ => by simp [Ix.Kernel.sumRules]
  | _ :: _, [], h => by simp at h
  | _ :: cs, _ :: rhss, h => by
    simp only [Ix.Kernel.sumRules, List.length_cons]
    rw [sumRules_length_of (ctorsA := cs) (rhss := rhss) (by simpa using h)]

/-- **The native route's recursor**: its major premise is the generated one, the family applied
to the parameter and index variables (`NativeRecJ.majorOf`); each rule is at one of the block's
constructors, whose type ends in the family, with the block's parameter count; the rules are
one per constructor; the η bits are the verdict at the constructors' environment, which the
table keeps. -/
theorem native_recShape_new {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {p₀ : NativeParts md} (hrc : NativeRecog p₀) (h : StoreInv env)
    (hrun : DeclNativeRunJ J env p₀ env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      RecAt env₂ n cv mI rP rules := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, hp,
    hCtors, -, -, -, -, -, hFOk, -, hRec, hTbl, -⟩ := hrun
  have hF := nativeFront hfr h hrc hnd hInd hp hCtors
  obtain ⟨_, s, _, _, _, hp₁, ⟨_, henv₁, _⟩, _, _⟩ := hInd.shape
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  let envC := Ix.Kernel.consSumCtors p.nP ctorsA env₁
  have hfreshR : envC.find? cvRa.name = none := by rw [hnR]; exact hfR
  have hkeep : ∀ {k : Key md} {x : ConstantInfo md}, envC.find? k = some x → env₂.find? k = some x :=
    fun hk => nativeTable_keep hTbl (Ix.Kernel.Env.find?_cons_of_fresh hfreshR hk)
  have hk := nativeFieldsOk_length hFOk
  have hlenA : ctorsA.length = p.ctors.length := hCtors.1
  obtain ⟨bs₀, B₀, m₀, hmaj⟩ :=
    hRec.majorOf (let ⟨cvS, caps, hfT, _⟩ := hF.former; ⟨cvS, caps, hfT⟩) hk hlenA
  have hmr : p.majorIdx - p.rulePrefix = p.nIdx := Nat.add_sub_cancel_left p.rulePrefix p.nIdx
  intro n cv mI rP rules hf hn0
  have hR := nativeTable_rec hTbl hf
  rw [Ix.Kernel.Env.find?_cons] at hR
  split at hR
  · next hnm =>
    have hn : cvRa.name = n := hnm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hR)
    -- each rule: one of the block's constructors, at the block's parameter count
    have hrule : ∀ r ∈ Ix.Kernel.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix
        cvRa.type ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA ∧
          r.ctor = cA.1.name ∧ r.ctorParams = p.nP := by
      intro r hr
      obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
      exact ⟨j, cA, hj, rfl, rfl⟩
    refine ⟨fun r hr => ?_, fun _ r hr _ => ?_, fun _ r hr cvj a b hc bs D B m hs T us hD => ?_,
      fun _ r hrs _ => ?_⟩
    · -- the η bit
      obtain ⟨j, cA, hj, hctor, -⟩ := hrule r hr
      obtain ⟨hfC, -, -, -⟩ := hF.ctor j cA hj
      rw [(Ix.Kernel.sumRules_bits hr).2, ← hn]
      refine recRuleEtaOf_ext (cvj := cA.1) (a := p.nP) (b := cA.2) hkeep
        (by rw [hctor]; exact hfC) (fun T us heq => .inl ?_)
      have hres : cA.1.type.constsResolve envC = true :=
        (hF.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfC)).2.2.1
      have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
      rw [heq] at h2
      simpa [Ix.Kernel.Expr.constsResolve] using h2
    · -- the major premise's index arguments
      obtain ⟨_, _, -, -, hcp⟩ := hrule r hr
      refine ⟨bs₀, _, B₀, m₀, hmaj, ?_⟩
      rw [hcp, hmr]
      exact structFamI_args_drop
    · -- the constructor's family
      obtain ⟨j, cA, hj, hctor, -⟩ := hrule r hr
      obtain ⟨hfC, -, -, cbs, es, hres, -⟩ := hF.ctor j cA hj
      have hc' := hkeep hfC
      rw [← hctor, hc] at hc'
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
      rw [hmaj] at hs
      simp only [Option.some.injEq, Prod.mk.injEq, Expr.forallE.injEq] at hs
      obtain ⟨-, rfl, -, -⟩ := hs
      rw [structFamI_getAppFn] at hD
      injection hD with hT _
      subst hT
      exact ⟨_, family_of_residual hres⟩
    · -- one rule: one constructor, so the prefix is the parameters, a motive and a minor
      have hr : r ∈ Ix.Kernel.sumRules envC.find? cvRa.name p.nP p.majorIdx p.rulePrefix
          cvRa.type ctorsA rhss := by rw [hrs]; exact List.mem_singleton_self r
      obtain ⟨_, _, -, -, hcp⟩ := hrule r hr
      obtain ⟨-, -, -, hlenR, -⟩ := NativeRecJ.facts (hfr _).annot_syntax hRec
      have hl := sumRules_length_of (find? := envC.find?) (recName := cvRa.name) (nP := p.nP)
        (mI := p.majorIdx) (rP := p.rulePrefix) (recTy := cvRa.type)
        (by rw [hlenR, Ix.Kernel.nativeCtors4_length hk])
      rw [hrs, List.length_singleton, hlenA] at hl
      rw [hcp]
      show p.nP + 2 = p.nP + 1 + p.ctors.length
      omega
  · have h1 := consSumCtors_rec hR
    rw [henv₁] at h1
    rw [find?_rec_of_cons h1 (fun _ _ _ _ heq => nomatch heq)] at hn0
    exact nomatch hn0

/-! ## The modeled route -/

/-- A modeled recursor's rules carry the η verdict at the members' environment `envB`, at the
recursor's name. -/
def ModeledEta (envB : Env md) (x : ConstantInfo md) : Prop :=
  ∀ cv mI rP rules, x = .recInfo cv mI rP rules → ∀ r ∈ rules,
    ∃ cvj cnP cnF, envB.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
      r.eta = Ix.Kernel.recRuleEtaOf envB.find? cv.name r.ctor

theorem iotaRulesRunJ_eta {J : Judgements md} {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rs out : List (RecRule md)},
      IotaRulesRunJ J env' envSelf f cvName lps tyA mI rP j rs out →
      ∀ r ∈ out, ∃ cvj cnP cnF, env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
        r.eta = Ix.Kernel.recRuleEtaOf env'.find? cvName r.ctor
  | _, [], out, h => by
    obtain rfl : out = [] := h
    intro r hr
    exact nomatch hr
  | _, _ :: _, _, h => by
    obtain ⟨r'', rest', hrule, hrest, rfl⟩ := h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨cvj, cnP, cnF, rhsA, hc, -, -, -, -, -, -, -, -, fire, hbits, -⟩ := hrule
      subst hbits
      exact ⟨cvj, cnP, cnF, hc, rfl⟩
    · exact iotaRulesRunJ_eta hrest r hr

theorem indRecsFoldRunJ_eta {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} :
    ∀ {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))} {acc out : Env md},
      IndRecsFoldRunJ J blockNames envBase envSelf acc checked out →
      NewSat acc out (ModeledEta envBase)
  | [], acc, out, h => by
    obtain rfl : out = acc := h
    exact NewSat.refl _ _
  | _ :: _, _, _, h => by
    obtain ⟨rules', hrules, h'⟩ := h
    refine (NewSat.cons ?_).trans (indRecsFoldRunJ_eta h')
    intro cv mI rP rules heq r hr
    obtain ⟨rfl, -, -, rfl⟩ := ConstantInfo.recInfo.inj heq
    exact iotaRulesRunJ_eta hrules r hr

/-- **A modeled step's recursors**: their rules' η bits are the verdict at the step's end; the
other facts are not claimed (a modeled recursor carries a model companion). -/
theorem modeled_recShape_new {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (hrun : DeclIndRunJ J env block env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      RecAt env₂ n cv mI rP rules := by
  intro n cv mI rP rules hf hn0
  have hm := declIndRunJ_hasModel hrun hf hn0
  refine ⟨?_, fun h => absurd hm h, fun h => absurd hm h, fun h => absurd hm h⟩
  obtain ⟨-, envM, hmem, hrecs⟩ := hrun
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · rw [indMembersRunJ_rec hmem hf] at hn0
    exact nomatch hn0
  · have hextM : ∀ {k : Key md} {x : ConstantInfo md}, envM.find? k = some x → env₂.find? k = some x :=
      (indRecsFoldRunJ_envExt hprov hfold (fun _ => rfl) (Ix.Kernel.EnvExt.refl _)).find
    have hnM : envM.find? n = none := by
      cases hM : envM.find? n with
      | none => rfl
      | some c =>
        have h2 := hextM hM
        rw [hf] at h2
        obtain rfl := Option.some.inj h2
        rw [indMembersRunJ_rec hmem hM] at hn0
        exact nomatch hn0
    rcases indRecsFoldRunJ_eta hfold _ _ hf with h1 | h1
    · rw [h1] at hnM
      exact nomatch hnM
    · intro r hr
      obtain ⟨cvj, cnP, cnF, hc, he⟩ := h1 cv mI rP rules rfl r hr
      have hname : cv.name = n := Ix.Kernel.Semantics.Env.find?_name hf
      rw [he, hname]
      refine recRuleEtaOf_ext hextM hc (fun T us _ => .inr ?_)
      intro x hgT hfT
      rcases indRecsFoldRunJ_newSat (Q := NotInd) (fun _ _ _ _ _ _ heq => nomatch heq) hfold _ _ hgT
        with h2 | h2
      · rw [h2] at hfT
        exact nomatch hfT
      · exact h2

/-! ## The pinned basis blocks -/

/-- The major premise's domain ends in the index binders' variables. -/
def idxOkb (ty : Expr md) (mI rP cnP : Nat) : Bool :=
  match ty.stripPis mI with
  | some (_, .forallE D _ _) =>
    D.getAppArgs.drop cnP == (List.range (mI - rP)).map fun i => (Expr.bvar (mI - rP - 1 - i) : Expr md)
  | _ => false

/-- The rule's constructor's type ends in the family heading the major premise's domain. -/
def headOkb (F : Env md) (ty : Expr md) (mI : Nat) (ctor : Key md) : Bool :=
  match F.find? ctor, ty.stripPis mI with
  | some (.ctorInfo cvj _ _), some (_, .forallE D _ _) =>
    match D.getAppFn, (cvj.type.piResult).getAppFn with
    | .const T _, .const T' _ => decide (T' = T)
    | .const _ _, _ => false
    | _, _ => true
  | _, _ => true

/-- The four facts at one recursor of a pinned block, read off the block's own constants. -/
def recShapeb (F : Env md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) :
    Bool :=
  rules.all (fun r =>
    (r.eta == Ix.Kernel.recRuleEtaOf F.find? cv.name r.ctor) && kStableb F r.ctor &&
      (!firePlain r.fire || idxOkb cv.type mI rP r.ctorParams) &&
      headOkb F cv.type mI r.ctor) &&
  (rules.length != 1 || rules.all fun r => !r.k || r.ctorParams + 2 == rP)

/-- Every pinned block's recursors pass. -/
def basisShapeb {md : Ix.Kernel.Mode} (kind : BasisKind) : Bool :=
  (kind.declsA (md := md)).all fun c => match c with
    | .recInfo cv mI rP rules => recShapeb ⟨(kind.declsA (md := md)).reverse⟩ cv mI rP rules
    | _ => true

theorem basis_shape (kind : BasisKind) : basisShapeb (md := md) kind = true := by
  cases kind <;> (cases md <;> decide +kernel)

theorem idxOkb_sound {ty : Expr md} {mI rP cnP : Nat} (h : idxOkb ty mI rP cnP = true) :
    ∃ bs D B m, ty.stripPis mI = some (bs, .forallE D B m) ∧
      D.getAppArgs.drop cnP =
        (List.range (mI - rP)).map fun i => (Expr.bvar (mI - rP - 1 - i) : Expr md) := by
  unfold idxOkb at h
  split at h
  · next bs D B m hs => exact ⟨bs, D, B, m, hs, eq_of_beq h⟩
  · exact nomatch h

theorem headOkb_sound {F : Env md} {ty : Expr md} {mI : Nat} {ctor : Key md}
    (h : headOkb F ty mI ctor = true) {cvj : ConstantVal md} {a b : Nat}
    (hc : F.find? ctor = some (.ctorInfo cvj a b)) {bs : List (Expr md × Ix.Kernel.BinderMeta)}
    {D B : Expr md} {m : Ix.Kernel.BinderMeta} (hs : ty.stripPis mI = some (bs, .forallE D B m))
    {T : Key md} {us : List Level} (hD : D.getAppFn = .const T us) :
    ∃ tus, (cvj.type.piResult).getAppFn = .const T tus := by
  unfold headOkb at h
  rw [hc, hs] at h
  dsimp only at h
  rw [hD] at h
  revert h
  cases hcj : (cvj.type.piResult).getAppFn with
  | const T' us' =>
    intro h
    simp only [decide_eq_true_eq] at h
    exact ⟨us', by rw [h]⟩
  | _ => intro h; first | exact nomatch h | simp at h

/-- **A pinned block's recursor**, at any extension of the block's own lookups. -/
theorem recAt_of_recShapeb {F E : Env md}
    (hext : ∀ {k : Key md} {x : ConstantInfo md}, F.find? k = some x → E.find? k = some x)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hname : cv.name = n) (h : recShapeb F cv mI rP rules = true) :
    RecAt E n cv mI rP rules := by
  unfold recShapeb at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hr, hl⟩ := h
  have hr' : ∀ r ∈ rules,
      r.eta = Ix.Kernel.recRuleEtaOf F.find? cv.name r.ctor ∧ kStableb F r.ctor = true ∧
      (firePlain r.fire = true → idxOkb cv.type mI rP r.ctorParams = true) ∧
      headOkb F cv.type mI r.ctor = true := by
    intro r hmem
    have := hr r hmem
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    refine ⟨h1, h2, fun hp => ?_, h4⟩
    rcases h3 with h3 | h3
    · rw [hp] at h3
      exact nomatch h3
    · exact h3
  refine ⟨fun r hmem => ?_, fun _ r hmem hfire => ?_, fun _ r hmem cvj a b hc bs D B m hs T us hD => ?_,
    fun _ r hrs hk => ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := hr' r hmem
    obtain ⟨cvj, a, b, hc, hT⟩ := kStableb_inv h2
    rw [h1, hname]
    exact recRuleEtaOf_ext hext hc (fun T us heq => .inl (hT T us heq))
  · obtain ⟨-, -, h3, -⟩ := hr' r hmem
    exact idxOkb_sound (h3 (by rw [hfire]; rfl))
  · obtain ⟨-, h2, -, h4⟩ := hr' r hmem
    obtain ⟨cvj', a', b', hc', -⟩ := kStableb_inv h2
    have h5 := hext hc'
    rw [hc] at h5
    obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj h5)
    exact headOkb_sound h4 hc' hs hD
  · rw [hrs] at hl
    simp [hk] at hl
    exact hl

theorem basis_recShape_new {env env₂ : Env md} {kind : BasisKind}
    (hrun : DeclBasisRun env kind env₂) :
    ∀ n cv mI rP rules, env₂.find? n = some (.recInfo cv mI rP rules) → env.find? n = none →
      RecAt env₂ n cv mI rP rules := by
  obtain ⟨-, hinst⟩ := hrun
  obtain ⟨rfl, -⟩ := basisInstallRun_eq hinst
  intro n cv mI rP rules hf hn0
  have hpre : ∀ {k : Key md} {x : ConstantInfo md},
      Env.find? ⟨(kind.declsA (md := md)).reverse⟩ k = some x →
      Env.find? ⟨kind.declsA.reverse ++ env.consts⟩ k = some x := by
    intro k x hk
    rw [find?_prefix, hk]
    rfl
  rw [find?_prefix] at hf
  cases hb : Env.find? ⟨(kind.declsA (md := md)).reverse⟩ n with
  | none =>
    rw [hb, Option.none_or] at hf
    rw [hf] at hn0
    exact nomatch hn0
  | some c =>
    rw [hb, Option.some_or] at hf
    obtain rfl := Option.some.inj hf
    have hmem : ConstantInfo.recInfo cv mI rP rules ∈ kind.declsA :=
      List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
    have hall : recShapeb ⟨(kind.declsA (md := md)).reverse⟩ cv mI rP rules = true :=
      List.all_eq_true.mp (basis_shape (md := md) kind) _ hmem
    exact recAt_of_recShapeb hpre (Ix.Kernel.Semantics.Env.find?_name hb) hall

/-! ## The fold -/

/-- **One declaration step keeps the facts**, over the derivation package. -/
theorem recShape_declRunJ {env env₂ : Env md} {d : Declaration md} (h : StoreInv env)
    (hS : RecShape env) (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    RecShape env₂ := by
  have hext := declRunJ_envExt_routes hrun
  have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact recShape_step_noRec h hS hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact recShape_step_noRec h hS hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact recShape_step_noRec h hS hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact hS
    · exact recShape_step_noRec h hS hext.find (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
    · exact hS
  | basisDecl kind => exact recShape_step h hS hext.find (basis_recShape_new hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact recShape_step h hS hext.find (basis_recShape_new hrun)
    · rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
      · exact recShape_step h hS hext.find (native_recShape_new hfr (nativeRecog_of hdp) h hN)
      · exact recShape_step h hS hext.find (modeled_recShape_new hM)
      · exact recShape_step_noRec h hS hext.find
          (nativeNoRec_newSat (fun _ _ _ _ _ _ heq => nomatch heq)
            (fun _ _ _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hN)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact recShape_step h hS hext.find (basis_recShape_new hrun)
    · subst hrun
      exact hS

/-- **Along a run, the facts hold**, from an environment keeping them and the store invariant. -/
theorem recShape_declsRunJ {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env') :
    StoreInv env → RecShape env → RecShape env' := by
  induction hds with
  | nil => exact fun _ hS => hS
  | cons hd _ ih =>
    intro h hS
    have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
    exact ih (storeInv_declRunJ hfr (fun hI => storeInv_indRoutesJ hfr h hI) h hd)
      (recShape_declRunJ h hS hd)

/-- **Every environment a run over derivations reaches from the empty one has the facts.** -/
theorem recShape_of_run {env' : Env md} {ds : List (Declaration md)}
    (h : DeclsRunJ rulesJ (IndRoutesJ rulesJ) Env.empty ds env') : RecShape env' :=
  recShape_declsRunJ h StoreInv.empty RecShape.empty

end Ix.Kernel.Model
