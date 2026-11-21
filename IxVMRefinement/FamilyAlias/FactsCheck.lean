import IxVMRefinement.FamilyAlias.Facts

/-! # The family check's facts, found by evaluation

`familyFactsCheck` searches for a proof of `FamilyCheckFacts` and returns the proof it finds
(`familyFacts_of_check`). It is the companion of `famRecordCheck` (`FamilyAlias/Check.lean`) for
the facts: every stored-data field is decided as stated, and every judgement is discharged by a
run of IxC's executable checker at the verified mode on the term the fact names, with the level
parameters at positions, turned into a derivation by the rules bridge.

It is the means by which the facts are shown inhabited at a family's records; it is not complete
(`fuel` bounds the runs). A failed search returns the name of the first field it could not
establish.

`FamilyAdvice.ofTable` reads a family's advice off an alias table: the model of a member is the
target of the member's model key, the theorem of a rule the target of the rule's `iota` key. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  openPisAtFvars eqName eqA isEqHead auxKey)
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The advice of a family laid out by an alias table**: each member with the target of its
model key, and for each recursor the targets of its rules' `iota` keys. -/
def FamilyAdvice.ofTable (tbl : List (KKey × KKey)) (blk : List (ConstantInfo .anon)) :
    FamilyAdvice where
  models := blk.map fun ci => (ci.name, aliasMap tbl (auxKey ci.name .model))
  thms := (recsOf blk).map fun ci =>
    match ci with
    | .recInfo cv _ _ rules =>
      (List.range rules.length).map fun j =>
        aliasMap tbl (auxKey (auxKey cv.name .model) (.iota j))
    | _ => []

/-! ## The judgements, by runs at positions -/

/-- A typing of the positional package, by a run on the subject at positions. -/
def posInfer (fuel : Nat) (lbl : String) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (d : Nat) (e : KExpr) :
    Except String {t : KExpr // posRulesJ.infer env d e t} :=
  match hrun : Ix.Kernel.inferTypeCore .verified env fuel d (posOf ps e) with
  | Except.ok tpos =>
    .ok ⟨invPosOf ps tpos,
      posRulesJ_infer_of_pos hperm (Ix.Kernel.Rules.inferTypeCore_bridge hrun)⟩
  | Except.error _ => .error lbl

/-- A conversion of the positional package, by a run on the two terms at positions. -/
def posDefeq (fuel : Nat) (lbl : String) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (d : Nat) (a b : KExpr) :
    Except String (PLift (posRulesJ.defeq env d a b)) :=
  match hrun : Ix.Kernel.isDefEqCore .verified env fuel d (posOf ps a) (posOf ps b) with
  | Except.ok true =>
    .ok ⟨posRulesJ_defeq_of_pos hperm (Ix.Kernel.Rules.isDefEqCore_bridge hrun)⟩
  | _ => .error lbl

/-- A closed subject is typed at a type that reduces to a sort, in the positional package. -/
def posInferSort (fuel : Nat) (lbl : String) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (e : KExpr) :
    Except String (PLift (∃ stype u, posRulesJ.infer env 0 e stype ∧
      posRulesJ.sort env 0 stype u)) :=
  match hrun : Ix.Kernel.inferTypeCore .verified env fuel 0 (posOf ps e) with
  | Except.ok tpos =>
    match hw : Ix.Kernel.whnf .verified env fuel 0 tpos with
    | Except.ok (.sort upos) =>
      .ok ⟨⟨invPosOf ps tpos, invPosLevel ps upos,
        posRulesJ_infer_of_pos hperm (Ix.Kernel.Rules.inferTypeCore_bridge hrun),
        posRulesJ_sort_of_pos hperm (Ix.Kernel.Rules.whnf_bridge hw)⟩⟩
    | _ => .error (lbl ++ " (the inferred type does not reduce to a sort)")
  | Except.error _ => .error lbl

/-- Pairwise conversion of two spines in the positional package. -/
def posDefeqListCheck (fuel : Nat) (lbl : String) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (d : Nat) :
    (as bs : List KExpr) → Except String (PLift (DefEqListJ posRulesJ env d as bs))
  | [], [] => .ok ⟨trivial⟩
  | a :: as, b :: bs =>
    match posDefeq fuel lbl env hperm d a b, posDefeqListCheck fuel lbl env hperm d as bs with
    | .ok p, .ok q => .ok ⟨⟨p.down, q.down⟩⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | _, _ => .error (lbl ++ " (lengths differ)")

/-- Pairwise typing of a spine against expected types in the positional package. -/
def posTypedListCheck (fuel : Nat) (lbl : String) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (d : Nat) :
    (as bs : List KExpr) → Except String (PLift (TypedListJ posRulesJ env d as bs))
  | [], [] => .ok ⟨trivial⟩
  | a :: as, b :: bs =>
    match posInfer fuel lbl env hperm d a with
    | .error e => .error e
    | .ok r =>
      match posDefeq fuel lbl env hperm d r.1 b,
          posTypedListCheck fuel lbl env hperm d as bs with
      | .ok p, .ok q => .ok ⟨⟨⟨r.1, r.2, p.down⟩, q.down⟩⟩
      | .error e, _ => .error e
      | _, .error e => .error e
  | _, _ => .error (lbl ++ " (lengths differ)")

/-- The rule walks' comparisons and the two sides' typings, in the positional package. -/
def posIotaRunsCheck (fuel : Nat) (env : Env .anon) {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (depth : Nat)
    (idxL idxR domL domR preL preR lamL lamR : List KExpr)
    (rhsS rhsApplied alphaS lhsS : KExpr) :
    Except String (PLift (IotaRunsJ posRulesJ env depth idxL idxR domL domR
      preL preR lamL lamR rhsS rhsApplied alphaS lhsS)) := do
  let p1 ← posDefeqListCheck fuel "statement: index arguments" env hperm depth idxL idxR
  let p2 ← posDefeqListCheck fuel "statement: field domains" env hperm depth domL domR
  let p3 ← posDefeqListCheck fuel "statement: prefix domains" env hperm depth preL preR
  let p4 ← posDefeqListCheck fuel "statement: lambda domains" env hperm depth lamL lamR
  let p5 ← posDefeq fuel "statement: right side against the applied rule" env hperm depth
    rhsS rhsApplied
  let tl ← posInfer fuel "statement: typing of the left side" env hperm depth lhsS
  let q1 ← posDefeq fuel "statement: type of the left side" env hperm depth tl.1 alphaS
  let tr ← posInfer fuel "statement: typing of the right side" env hperm depth rhsS
  let q2 ← posDefeq fuel "statement: type of the right side" env hperm depth tr.1 alphaS
  return ⟨⟨p1.down, p2.down, p3.down, p4.down, p5.down, ⟨tl.1, tl.2, q1.down⟩,
    ⟨tr.1, tr.2, q2.down⟩⟩⟩

/-! ## The members -/

/-- One member against its model. -/
def memberFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey)
    (ci : ConstantInfo .anon) (tyA : KExpr) :
    Except String (PLift (MemberFacts env g ci tyA)) := do
  let hperm ← guardP "member: level parameters are not a permutation of the positions"
    (ci.toConstantVal.levelParams.Perm (List.range ci.toConstantVal.levelParams.length))
  let h1 ← guardP "member: free variable" (ci.toConstantVal.type.hasFvar = false)
  let h2 ← guardP "member: loose bound variable"
    (ci.toConstantVal.type.looseBVarsBounded 0 = true)
  let h3 ← guardP "member: annotation"
    ((IxVM.Consistency.annotatesCheck 4096 tyA ci.toConstantVal.type).isSome = true)
  let hlv ← guardP "member: level parameters of the type"
    (tyA.allLevelParamsDefined ci.toConstantVal.levelParams = true)
  let hs ← posInferSort fuel "member: the model's type is not typed" env hperm.down
    (tyA.renameConsts g)
  match hfind : env.find? (g ci.name) with
  | some (.defnInfo cvm mval hint) =>
    let hl ← guardP "member: level parameters of the model"
      (cvm.levelParams = List.range ci.toConstantVal.levelParams.length)
    let ht ← guardP "member: type of the model"
      (cvm.type = posOf ci.toConstantVal.levelParams (tyA.renameConsts g))
    return ⟨⟨hperm.down, h1.down, h2.down, IxVM.Consistency.annotates_of_check h3.down,
      hlv.down,
      ⟨cvm, mval, hint, hfind, hl.down ▸ List.Perm.refl _, by
        rw [hl.down, posOf_range, ht.down]
        exact ExprLvEq.refl _⟩, hs.down⟩⟩
  | _ => .error "member: the model is not a stored definition"

/-- The members against their models, in order. -/
def membersFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey) :
    (cis : List (ConstantInfo .anon)) → (tys : List KExpr) →
    Except String (PLift (MembersFacts env g cis tys))
  | [], [] => .ok ⟨trivial⟩
  | ci :: rest, tyA :: tys =>
    match memberFactsCheck fuel env g ci tyA, membersFactsCheck fuel env g rest tys with
    | .ok p, .ok q => .ok ⟨⟨p.down, q.down⟩⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | _, _ => .error "members: the annotated types do not match the members"

/-! ## The rules -/

/-- The constructor a rule names: stored, or a constructor of the block. -/
def ruleCtorCheck (env : Env .anon) (blk : List (ConstantInfo .anon)) (tys : List KExpr)
    (k : KKey) :
    Except String {x : ConstantVal .anon × Nat × Nat // RuleCtor env blk tys k x.1 x.2.1 x.2.2} :=
  match hf : env.find? k with
  | some (.ctorInfo cvj cnP cnF) => .ok ⟨(cvj, cnP, cnF), Or.inl hf⟩
  | _ =>
    match hb : blk[blk.findIdx (fun ci => ci.name == k)]?,
        ht : tys[blk.findIdx (fun ci => ci.name == k)]? with
    | some (.ctorInfo cv cnP cnF), some tyC =>
      if hk : cv.name = k then
        .ok ⟨(⟨cv.name, cv.levelParams, tyC⟩, cnP, cnF),
          Or.inr ⟨blk.findIdx (fun ci => ci.name == k), cv, tyC, hb, ht, hk, rfl⟩⟩
      else .error "rule: the constructor is not a constructor of the block"
    | _, _ => .error "rule: the constructor is neither stored nor a constructor of the block"

/-- A rule's theorem statement against the rule. -/
def statementFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey) (recKey : KKey)
    {lps : List LevelParam} (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr)
    (mI rP : Nat) (ctorKey : KKey) (rhsA : KExpr) (cvj : ConstantVal .anon) (cnP cnF : Nat)
    (lvls : List Level) (pins : List KExpr) (stmt : KExpr) :
    Except String (PLift (StatementFacts env g recKey lps tyA mI rP ctorKey rhsA cvj cnP cnF
      lvls pins stmt)) := do
  let op ← getSome "statement: telescope" (openPisAtFvars (rP + cnF) stmt 0)
  let he ← guardP "statement: not an equation" (isEqHead op.1.2.getAppFn = true)
  let h3 ← guardP "statement: the equation's arity" (op.1.2.getAppArgs.length = 3)
  let g1 ← guardP "statement: head of the left side"
    ((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppFn = Expr.const (g recKey) (lps.map .param))
  let g2 ← guardP "statement: arity of the left side"
    ((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length = mI + 1)
  let g3 ← guardP "statement: prefix of the left side"
    (((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).take rP = op.1.1.take rP)
  let g4 ← guardP "statement: major premise of the left side"
    (((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).getLastD (.bvar 0) =
      Expr.mkAppN (.const (g ctorKey) lvls)
        ((pins.map fun p =>
          Expr.instSpine (op.1.1.take rP) (rP - 1) (p.renameConsts g)) ++ op.1.1.drop rP))
  let k1 ← getSome "statement: constructor telescope at the major premise"
    (Expr.instPisAt
      ((pins.map fun p =>
        Expr.instSpine (op.1.1.take rP) (rP - 1) (p.renameConsts g)) ++ op.1.1.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts g))
  let k2 ← guardP "statement: constructor indices"
    (k1.1.2.getAppArgs.length = cnP + (mI - rP))
  let k3 ← getSome "statement: recursor telescope at the statement's prefix"
    (Expr.instPisAt (op.1.1.take rP) (tyA.renameConsts g))
  let k4 ← getSome "statement: recursor telescope" (openPisAtFvars rP tyA 0)
  let k5 ← getSome "statement: constructor telescope at the pins"
    (Expr.instPisAt (pins.map fun p => Expr.instSpine (k4.1.1.take rP) (rP - 1) p)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls))
  let k6 ← getSome "statement: constructor fields" (openPisAtFvars cnF k5.1.2 rP)
  let k6c ← guardP "statement: residual arity"
    (k6.1.2.getAppArgs.length = cnP + (mI - rP))
  let kfix ← guardP "statement: the renaming moves the annotation of a variable in a pin"
    ((pins.map fun p => Expr.instSpine (k4.1.1.take rP) (rP - 1) p).all (leavesFixedB g) = true)
  let k7 ← getSome "statement: lambdas of the right-hand side"
    (Expr.instLamsAt (k4.1.1 ++ k6.1.1) rhsA)
  let k8 ← posTypedListCheck fuel "statement: typing of a renamed pin" env hperm (rP + cnF)
    ((pins.map fun p => Expr.instSpine (k4.1.1.take rP) (rP - 1) p).map (·.renameConsts g))
    (k5.1.1.map (·.renameConsts g))
  let k9 ← posIotaRunsCheck fuel env hperm (rP + cnF)
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).drop rP).take (mI - rP))
    (k1.1.2.getAppArgs.drop cnP)
    ((op.1.1.drop rP).map Expr.fvarTypeD) (k1.1.1.drop cnP)
    ((op.1.1.take rP).map Expr.fvarTypeD) k3.1.1
    (((k4.1.1 ++ k6.1.1).map Expr.fvarTypeD).map (·.renameConsts g))
    (k7.1.1.map (·.renameConsts g))
    (op.1.2.getAppArgs.getD 2 (.bvar 0)) (Expr.mkAppN (rhsA.renameConsts g) op.1.1)
    (op.1.2.getAppArgs.getD 0 (.bvar 0)) (op.1.2.getAppArgs.getD 1 (.bvar 0))
  return ⟨⟨op.1.1, op.1.2, op.2, he.down, h3.down, g1.down, g2.down, g3.down, g4.down,
    k1.1.1, k1.1.2, k3.1.1, k3.1.2, k4.1.1, k4.1.2, k5.1.1, k5.1.2, k6.1.1, k6.1.2,
    k1.2, k2.down, k3.2, k4.2, k5.2, k6.2, k6c.down,
    (fun p hp => leavesFixed_of_b (List.all_eq_true.mp kfix.down p hp)),
    k7.1.1, k7.1.2, k7.2, k8.down, k9.down⟩⟩

/-- One rule of a recursor against its theorem. -/
def ruleFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (recKey : KKey)
    {lps : List LevelParam} (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr)
    (mI rP : Nat) (r : RecRule .anon) (rhsA : KExpr) (thm : KKey) :
    Except String (PLift (RuleFacts env g blk tys recKey lps tyA mI rP r rhsA thm)) := do
  let c ← ruleCtorCheck env blk tys r.ctor
  let h2 ← guardP "rule: field count" (r.nfields = c.1.2.2)
  let h3 ← guardP "rule: loose bound variable" (r.rhs.looseBVarsBounded 0 = true)
  let h4 ← guardP "rule: free variable" (r.rhs.hasFvar = false)
  let h5 ← guardP "rule: annotation"
    ((IxVM.Consistency.annotatesCheck 4096 rhsA r.rhs).isSome = true)
  let h6 ← guardP "rule: level parameters" (rhsA.allLevelParamsDefined lps = true)
  let h7 ← guardP "rule: lambdas" ((rhsA.stripLams (rP + c.1.2.2)).isSome = true)
  let ht ← posInfer fuel "rule: typing of the renamed right-hand side" env hperm 0
    (rhsA.renameConsts g)
  let sh ← getSome "rule: the major premise's shape" (majorShape tyA mI rP c.1.2.1)
  let h8 ← guardP "rule: levels of the major premise"
    (sh.1.1.all (Level.allParamsDefined lps) = true)
  let h9 ← guardP "rule: scope of a pin"
    (sh.1.2.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
      p.allLevelParamsDefined lps) = true)
  let h10 ← guardP "rule: constructor telescope"
    (Expr.ctorTeleOk c.1.1.type (c.1.2.1 + c.1.2.2) = true)
  match hfind : env.find? thm with
  | some (.thmInfo cvt vt) =>
    let hl ← guardP "rule: level parameters of the theorem"
      (cvt.levelParams = List.range lps.length)
    let htl ← guardP "rule: level parameters of the theorem type"
      (cvt.type.allLevelParamsDefined (List.range lps.length) = true)
    let hs ← statementFactsCheck fuel env g recKey hperm tyA mI rP r.ctor rhsA c.1.1 c.1.2.1
      c.1.2.2 sh.1.1 sh.1.2 (invPosOf lps cvt.type)
    return ⟨⟨c.1.1, c.1.2.1, c.1.2.2, sh.1.1, sh.1.2, c.2, h2.down, h3.down, h4.down,
      IxVM.Consistency.annotates_of_check h5.down, h6.down, h7.down, ⟨ht.1, ht.2⟩, sh.2,
      h8.down, h9.down, h10.down, cvt, vt, cvt.type, hfind, hl.down ▸ List.Perm.refl _,
      htl.down, by rw [hl.down, posOf_range]; exact ExprLvEq.refl _, hs.down⟩⟩
  | _ => .error "rule: the theorem is not a stored theorem"

/-- The rules of one recursor against their theorems, in order. -/
def rulesFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (recKey : KKey)
    {lps : List LevelParam} (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr)
    (mI rP : Nat) :
    (rules : List (RecRule .anon)) → (rhss : List KExpr) → (thms : List KKey) →
    Except String (PLift (RulesFacts env g blk tys recKey lps tyA mI rP rules rhss thms))
  | [], [], [] => .ok ⟨trivial⟩
  | r :: rs, rhsA :: rhss, thm :: thms =>
    match ruleFactsCheck fuel env g blk tys recKey hperm tyA mI rP r rhsA thm,
        rulesFactsCheck fuel env g blk tys recKey hperm tyA mI rP rs rhss thms with
    | .ok p, .ok q => .ok ⟨⟨p.down, q.down⟩⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | _, _, _ => .error "rules: the right-hand sides and theorems do not match the rules"

/-- The recursors' rules against their theorems. -/
def recsFactsCheck (fuel : Nat) (env : Env .anon) (g : KKey → KKey)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) :
    (recs : List (ConstantInfo .anon)) → (tysR : List KExpr) → (rhsss : List (List KExpr)) →
    (thss : List (List KKey)) →
    Except String (PLift (RecsFacts env g blk tys recs tysR rhsss thss))
  | [], [], [], [] => .ok ⟨trivial⟩
  | .recInfo cv mI rP rules :: rest, tyA :: tysR, rhss :: rhsss, ths :: thss => do
    let hperm ← guardP "recursor: level parameters are not a permutation of the positions"
      (cv.levelParams.Perm (List.range cv.levelParams.length))
    let hr ← rulesFactsCheck fuel env g blk tys cv.name hperm.down tyA mI rP rules rhss ths
    let ho ← recsFactsCheck fuel env g blk tys rest tysR rhsss thss
    return ⟨⟨hr.down, ho.down⟩⟩
  | _, _, _, _ =>
    .error "recursors: the types, right-hand sides and theorems do not match the recursors"

/-! ## The family -/

/-- **A proof of the family check's facts, if the search finds one.**

* `env`: the environment that stores the advice;
* `blk`: the family as read, types, constructors, recursors;
* `adv`: the advice;
* `tys`: the members' annotated types, in the family's order;
* `rhsss`: the annotated right-hand sides of each recursor's rules. -/
def familyFactsCheck (fuel : Nat) (env : Env .anon) (blk : List (ConstantInfo .anon))
    (adv : FamilyAdvice) (tys : List KExpr) (rhsss : List (List KExpr)) :
    Except String (PLift (FamilyCheckFacts env blk adv tys rhsss)) := do
  let h1 ← guardP "family: a recursor precedes another member"
    (blk = nonrecsOf blk ++ recsOf blk)
  let h2 ← guardP "family: a member that is no type, constructor or recursor"
    ((nonrecsOf blk).all isTypeOrCtor = true)
  let h3 ← guardP "family: the advice does not list the members"
    (adv.models.map (·.1) = blk.map (·.name))
  let h4 ← membersFactsCheck fuel env adv.ren blk tys
  let h5 ← guardP "family: a member's type names itself or a later member"
    (typesScopedB (blk.map (·.name)) tys = true)
  let h6 ← recsFactsCheck fuel env adv.ren blk tys (recsOf blk)
    (tys.drop (nonrecsOf blk).length) rhsss adv.thms
  return ⟨⟨h1.down, h2.down, h3.down, h4.down, h5.down, h6.down⟩⟩

/-- **A successful check is a proof of the facts.** -/
theorem familyFacts_of_check {fuel : Nat} {env : Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hc : isOk (familyFactsCheck fuel env blk adv tys rhsss) = true) :
    FamilyCheckFacts env blk adv tys rhsss := by
  cases hr : familyFactsCheck fuel env blk adv tys rhsss with
  | error e =>
    rw [hr] at hc
    have hc' : false = true := hc
    cases hc'
  | ok r => exact r.down

end IxVM.Refinement.Decl.FamilyAlias
