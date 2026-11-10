module

public import IxC.Kernel.Semantics.DeclJ
public import IxC.Kernel.Semantics.DeclIndRun
public import IxC.Kernel.Semantics.DeclExt

@[expose] public section

/-!
# The modeled inductive route over a judgement package

`DeclIndRun` (`Semantics/DeclIndRun.lean`) records what the kernel's fold
checked for an inductive block. Its second case is the **modeled route**: the
block's members are installed at an empty capability record, each with the
type of an earlier model declaration (the model's key is `auxKey n .model`),
the recursors are provisioned without rules, and each recursor rule is checked
against an earlier `iota` theorem (key `auxKey (auxKey R .model) (.iota j)`).
No projection function is installed.

This module states that case over a judgement package (`Judgements`,
`Semantics/DeclJ.lean`), as `DeclJ` does for the value kinds:

* each checker run the records mention becomes the package's relation: the
  annotation of a rule's right-hand side, its inferred type, the pairwise
  conversions of the rule walks (`DefEqListJ`), the typed pins of a nested
  rule (`TypedListJ`) and the walks' sides (`IotaRunsJ`);
* the stored-data guards (lookups, shapes, renamings, `nestedRuleShape`,
  `recRuleBits`) are unchanged.

`DeclIndRunJ J env block env₂` is the modeled route stated for every block:
the members at the empty capability record, then the recursors. The kernel's
second case of `DeclIndRun` gives it at the kernel's runs
(`declIndRun_modeled_runJ`). Every block of the modeled route installs fresh
constants that are not projection tables, so a step extends the environment
(`declIndRunJ_envExt`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel.Term Ix.Kernel.Verify

/-! ## The walks over a package -/

/-- Pairwise conversion of two spines over a package (`DefEqListOk`). -/
def DefEqListJ (J : Judgements md) (env : Env md) (d : Nat) :
    List (Expr md) → List (Expr md) → Prop
  | [], [] => True
  | a :: as, b :: bs => J.defeq env d a b ∧ DefEqListJ J env d as bs
  | _, _ => False

/-- Pairwise typing of a spine against expected types over a package
(`TypedListOk`). -/
def TypedListJ (J : Judgements md) (env : Env md) (d : Nat) :
    List (Expr md) → List (Expr md) → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    (∃ ty, J.infer env d a ty ∧ J.defeq env d ty b) ∧ TypedListJ J env d as bs
  | _, _ => False

/-- The rule walks' comparisons and the two sides' typings over a package
(`IotaRuns`). -/
def IotaRunsJ (J : Judgements md) (envSelf : Env md) (depth : Nat)
    (idxL idxR domL domR preL preR lamL lamR : List (Expr md))
    (rhsS rhsApplied alphaS lhsS : Expr md) : Prop :=
  DefEqListJ J envSelf depth idxL idxR ∧
  DefEqListJ J envSelf depth domL domR ∧
  DefEqListJ J envSelf depth preL preR ∧
  DefEqListJ J envSelf depth lamL lamR ∧
  J.defeq envSelf depth rhsS rhsApplied ∧
  (∃ tl, J.infer envSelf depth lhsS tl ∧ J.defeq envSelf depth tl alphaS) ∧
  (∃ tr, J.infer envSelf depth rhsS tr ∧ J.defeq envSelf depth tr alphaS)

theorem DefEqListJ.length {J : Judgements md} {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, DefEqListJ J env d as bs → as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => rfl
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨_, h⟩ => simpa using ih h

theorem DefEqListJ.pointwise {J : Judgements md} {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, DefEqListJ J env d as bs →
      ∀ (i : Nat) {a b : Expr md}, as[i]? = some a → bs[i]? = some b →
        J.defeq env d a b := by
  intro as
  induction as with
  | nil =>
    intro bs h i a b ha hb
    exact nomatch ha
  | cons a₀ as ih =>
    intro bs h i a b ha hb
    match bs, h with
    | b₀ :: bs, ⟨h₀, h⟩ =>
      match i, ha, hb with
      | 0, ha, hb =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        exact h₀
      | i + 1, ha, hb => exact ih h i (by simpa using ha) (by simpa using hb)

theorem DefEqListJ.take {J : Judgements md} {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)} (n : Nat), DefEqListJ J env d as bs →
      DefEqListJ J env d (as.take n) (bs.take n) := by
  intro as
  induction as with
  | nil =>
    intro bs n h
    match bs, h with
    | [], _ =>
      simp only [List.take_nil]
      trivial
  | cons a as ih =>
    intro bs n h
    match bs, h with
    | b :: bs, ⟨h₀, h⟩ =>
      cases n with
      | zero => trivial
      | succ n =>
        simp only [List.take_succ_cons]
        exact ⟨h₀, ih n h⟩

theorem TypedListJ.infer_of_mem {J : Judgements md} {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, TypedListJ J env d as bs →
      ∀ a ∈ as, ∃ ty, J.infer env d a ty := by
  intro as
  induction as with
  | nil => intro bs h a ha; cases ha
  | cons x xs ih =>
    intro bs h a ha
    match bs, h with
    | b :: bs, ⟨⟨ty, hty, _⟩, hrest⟩ =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨ty, hty⟩
      · exact ih hrest a ha

/-! ## The block members -/

/-- `MemberValRun` over a package: the member's front door and the pins of its
model declaration (pure lookups). -/
def MemberValRunJ (J : Judgements md) (env' : Env md)
    (blockNames : List (Key md)) (cv : ConstantVal md) (cvA : ConstantVal md) :
    Prop :=
  ∃ type',
    ConstantValRunJ J env' cv type' ∧
    cvA = ⟨cv.name, cv.levelParams, type'⟩ ∧
    cvA.name.isModelSuffix = false ∧
    ∃ cvm mval hint,
      env'.find? (auxKey cvA.name .model)
        = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams = cvA.levelParams ∧
      ((cvA.type.renameConsts fun n =>
          if blockNames.contains n then auxKey n .model else n)
          == cvm.type) = true

/-- `IndMembersRun` over a package: the non-recursor members, in order. -/
def IndMembersRunJ (J : Judgements md)
    (blockNames : List (Key md)) (caps : IndCaps md) :
    (Env md) → List (ConstantInfo md) → Env md → Prop
  | env', [], env₂ => env₂ = env'
  | env', ci :: rest, env₂ =>
    ∃ cvA, MemberValRunJ J env' blockNames ci.toConstantVal cvA ∧
      match ci with
      | .indInfo _ _ =>
        IndMembersRunJ J blockNames caps
          ⟨.indInfo cvA caps :: env'.consts⟩ rest env₂
      | .ctorInfo _ nP nF =>
        IndMembersRunJ J blockNames caps
          ⟨.ctorInfo cvA nP nF :: env'.consts⟩ rest env₂
      | _ => False

/-- `ProvisionRecsRun` over a package: the recursors, installed without rules. -/
def ProvisionRecsRunJ (J : Judgements md)
    (blockNames : List (Key md)) :
    (Env md) → List (ConstantInfo md) →
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) → Prop
  | envAcc, [], envSelf, checked =>
    envSelf = envAcc ∧ checked = []
  | envAcc, ci :: rest, envSelf, checked =>
    ∃ cvA mI rP rules rest',
      ci = .recInfo ci.toConstantVal mI rP rules ∧
      MemberValRunJ J envAcc blockNames ci.toConstantVal cvA ∧
      ProvisionRecsRunJ J blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest envSelf rest' ∧
      checked = (cvA, mI, rP, rules) :: rest'

/-! ## The rules -/

/-- `IotaThmRun` over a package: a canonical rule's `iota` theorem. -/
def IotaThmRunJ (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r : RecRule md)
    (cvj : ConstantVal md) (cnP cnF : Nat) (rhsA : Expr md) : Prop :=
  ∃ cvt fvs tbody,
    env'.findCV? (auxKey (auxKey cvName .model) (.iota j)) = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     (largs.getLastD (.bvar 0) == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs)) = true ∧
     (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
     ∃ cdoms cres rdoms fvsP cdomsP crestP xFvsP crest2 ldoms lrest,
       Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
       openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         DefEqListJ J envSelf depth
           ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP ∧
         IotaRunsJ J envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- `IotaThmNRun` over a package: a nested rule's `iota` theorem, with the pins
typed against the constructor's parameter domains (`TypedListJ`). -/
def IotaThmNRunJ (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r : RecRule md)
    (cvj : ConstantVal md) (cnP cnF : Nat) (rhsA : Expr md)
    (lvls : List Level) (pins : List (Expr md)) : Prop :=
  nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
    = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? (auxKey (auxKey cvName .model) (.iota j)) = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let pinsF := pins.map fun p =>
       Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     Expr.ErasedEq (largs.getLastD (.bvar 0))
       (Expr.mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)) ∧
     (∃ cbinders cbody0, cvj.type.stripPis (cnP + cnF)
        = some (cbinders, cbody0) ∧
       (match cbody0.getAppFn with
        | .const _ _ => true | _ => false) = true) ∧
     ∃ cdoms cres rdoms lrest fvsP crest2 cdomsP crestP xFvsP ldoms,
       Expr.instPisAt (pinsF ++ xFvs)
         ((cvj.type.instantiateLevelParams cvj.levelParams
           lvls).renameConsts f) = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       (let pinsP := pins.map fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p
        (∀ p ∈ pinsP, J.annot envSelf depth p p) ∧
        Expr.instPisAt pinsP
          (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        (ldoms.getAppArgs.length == cnP + (mI - rP)) = true) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt
           (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         TypedListJ J envSelf depth
           (pins.map fun p =>
             Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP ∧
         IotaRunsJ J envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- `IotaRuleRun` over a package: the rule's right-hand side annotated and
typed, and its fire mode with the matching `iota` theorem. -/
def IotaRuleRunJ (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r r' : RecRule md) :
    Prop :=
  ∃ cvj cnP cnF rhsA,
    env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    J.annot envSelf 0 r.rhs rhsA ∧
    rhsA.allLevelParamsDefined lps = true ∧
    rhsA.constsResolve envSelf = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    (∃ t', J.infer envSelf 0 rhsA t') ∧
    ∃ fire,
      r' = recRuleBits env'.find? cvName
        { r with rhs := rhsA, ctorParams := cnP, fire := fire,
                 paramsBlind := false } ∧
      ((Expr.recRulePlain tyA mI rP cnP = true ∧ fire = .plain ∧
          IotaThmRunJ J env' envSelf f cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP = false ∧
          ((fire = .inert ∧
            nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
              = none) ∨
           (∃ lvls pins, fire = .nested lvls pins ∧
             IotaThmNRunJ J env' envSelf f cvName lps tyA mI rP j r
               cvj cnP cnF rhsA lvls pins))))

/-- `IotaRulesRun` over a package. -/
def IotaRulesRunJ (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP : Nat) :
    Nat → List (RecRule md) → List (RecRule md) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleRunJ J env' envSelf f cvName lps tyA mI rP j r r' ∧
      IotaRulesRunJ J env' envSelf f cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- The recursor group's install fold over a package: each provisioned
recursor is stored with its checked rules. -/
def IndRecsFoldRunJ (J : Judgements md) (blockNames : List (Key md))
    (envBase envSelf : Env md) :
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) →
    (Env md) → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesRunJ J envBase envSelf
        (fun n => if blockNames.contains n then auxKey n .model else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        rules' ∧
      IndRecsFoldRunJ J blockNames envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- `IndRecsRun` over a package: provision the group, then install it with its
rules. -/
def IndRecsRunJ (J : Judgements md)
    (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (ConstantInfo md)) (env₃ : Env md) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRunJ J blockNames env₂ recs envSelf checked ∧
     IndRecsFoldRunJ J blockNames env₂ envSelf env₂ checked env₃)

/-! ## The block -/

/-- **The modeled route over a package**: the block lists its non-recursor
members before its recursors; the members are installed at the empty
capability record, then the recursors with their rules. No projection function
is installed. -/
def DeclIndRunJ (J : Judgements md) (env : Env md)
    (block : List (ConstantInfo md)) (env₂ : Env md) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ∃ envM,
    IndMembersRunJ J blockNames {} env nonrecs envM ∧
    IndRecsRunJ J blockNames envM recs env₂

/-! ## The kernel's records are the run instance -/

section RunInstance

variable {μ : CheckMode} {F : Nat}

theorem memberValRun_eq_runJ {env' : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} :
    MemberValRun μ F env' blockNames cv cvA =
      MemberValRunJ (runJ μ F) env' blockNames cv cvA := rfl

theorem defEqListOk_runJ {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, DefEqListOk μ F env d as bs →
      DefEqListJ (runJ μ F) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => trivial
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨h₀, h⟩ => exact ⟨h₀, ih h⟩

theorem typedListOk_runJ {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, TypedListOk μ F env d as bs →
      TypedListJ (runJ μ F) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => trivial
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨⟨ty, hty, hde⟩, h⟩ => exact ⟨⟨ty, hty, hde⟩, ih h⟩

theorem iotaRuns_runJ {envSelf : Env md} {depth : Nat}
    {idxL idxR domL domR preL preR lamL lamR : List (Expr md)}
    {rhsS rhsApplied alphaS lhsS : Expr md}
    (h : IotaRuns μ F envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS) :
    IotaRunsJ (runJ μ F) envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS :=
  let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨defEqListOk_runJ h1, defEqListOk_runJ h2, defEqListOk_runJ h3,
    defEqListOk_runJ h4, h5, h6, h7⟩

theorem indMembersRun_runJ {blockNames : List (Key md)} {caps : IndCaps md} :
    ∀ {env' : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRun μ F blockNames caps env' members env₂ →
      IndMembersRunJ (runJ μ F) blockNames caps env' members env₂
  | _, [], _, h => h
  | _, ci :: rest, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, hmv, ?_⟩
    cases ci with
    | indInfo cv caps' => exact indMembersRun_runJ hm
    | ctorInfo cv nP nF => exact indMembersRun_runJ hm
    | axiomInfo _ => exact hm
    | defnInfo _ _ _ => exact hm
    | thmInfo _ _ => exact hm
    | recInfo _ _ _ _ => exact hm
    | projInfo _ => exact hm

theorem provisionRecsRun_runJ {blockNames : List (Key md)} :
    ∀ {envAcc : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ProvisionRecsRunJ (runJ μ F) blockNames envAcc recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest', hci, hmv, hrec, hck⟩ := h
    exact ⟨cvA, mI, rP, rules, rest', hci, hmv, provisionRecsRun_runJ hrec, hck⟩

theorem iotaThmRun_runJ {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    (h : IotaThmRun μ F env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA) :
    IotaThmRunJ (runJ μ F) env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF
      rhsA := by
  obtain ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7,
    defEqListOk_runJ k8, iotaRuns_runJ k9⟩

theorem iotaThmNRun_runJ {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    {lvls : List Level} {pins : List (Expr md)}
    (h : IotaThmNRun μ F env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
      lvls pins) :
    IotaThmNRunJ (runJ μ F) env' envSelf f cvName lps tyA mI rP j r cvj cnP cnF
      rhsA lvls pins := by
  obtain ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7,
    typedListOk_runJ k8, iotaRuns_runJ k9⟩

theorem iotaRuleRun_runJ {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r r' : RecRule md}
    (h : IotaRuleRun μ F env' envSelf f cvName lps tyA mI rP j r r') :
    IotaRuleRunJ (runJ μ F) env' envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, h9, fire, h10,
    hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, h9, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨hp, ⟨hf, hn⟩ | ⟨lvls, pins, hf, ht⟩⟩
  · exact Or.inl ⟨hp, hf, iotaThmRun_runJ ht⟩
  · exact Or.inr ⟨hp, Or.inl ⟨hf, hn⟩⟩
  · exact Or.inr ⟨hp, Or.inr ⟨lvls, pins, hf, iotaThmNRun_runJ ht⟩⟩

theorem iotaRulesRun_runJ {env' envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRun μ F env' envSelf f cvName lps tyA mI rP j rules rules' →
      IotaRulesRunJ (runJ μ F) env' envSelf f cvName lps tyA mI rP j rules rules'
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨r', rest', hr, hrest, hout⟩ := h
    exact ⟨r', rest', iotaRuleRun_runJ hr, iotaRulesRun_runJ hrest, hout⟩

theorem indRecsFoldRun_runJ {blockNames : List (Key md)} {envBase envSelf : Env md} :
    ∀ {acc : Env md} {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
      {out : Env md},
      IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf acc checked out →
      IndRecsFoldRunJ (runJ μ F) blockNames envBase envSelf acc checked out
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨rules', hrules, hrest⟩ := h
    exact ⟨rules', iotaRulesRun_runJ hrules, indRecsFoldRun_runJ hrest⟩

theorem indRecsRun_runJ {blockNames : List (Key md)} {env₂ : Env md}
    {recs : List (ConstantInfo md)} {env₃ : Env md}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    IndRecsRunJ (runJ μ F) blockNames env₂ recs env₃ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, provisionRecsRun_runJ hprov,
      indRecsFoldRun_runJ hfold⟩

/-- **The kernel's modeled case is the restated record at its runs**: a block
the kernel installs by `DeclIndRun`'s second case (not one type with one
constructor) satisfies `DeclIndRunJ` at the kernel's runs. -/
theorem declIndRun_modeled_runJ {env env₂ : Env md} {block : List (ConstantInfo md)}
    (h : DeclIndRun μ F env block env₂)
    (hmod : ¬ (∃ cvT capsT cvC nP nF,
      block.filter (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
      block.filter (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false) = [.ctorInfo cvC nP nF])) :
    DeclIndRunJ (runJ μ F) env block env₂ := by
  obtain ⟨hsplit, hmain⟩ := h
  rcases hmain with ⟨cvT, capsT, cvC, nP, nF, hI, hC, -⟩ | ⟨-, envM, hmem, hrecs⟩
  · exact (hmod ⟨cvT, capsT, cvC, nP, nF, hI, hC⟩).elim
  · exact ⟨hsplit, envM, indMembersRun_runJ hmem, indRecsRun_runJ hrecs⟩

end RunInstance

/-! ## A modeled step extends the environment -/

/-- A member's front door gives a fresh cons that is not a projection table. -/
theorem envExt_of_memberValRunJ {J : Judgements md} {env : Env md}
    {blockNames : List (Key md)} {cv cvA : ConstantVal md}
    (h : MemberValRunJ J env blockNames cv cvA) {c : ConstantInfo md}
    (hc : c.name = cvA.name) : EnvExt env ⟨c :: env.consts⟩ := by
  obtain ⟨type', hcv, rfl, -⟩ := h
  exact envExt_of_constantValRunJ hcv hc

theorem indMembersRunJ_envExt {J : Judgements md} {blockNames : List (Key md)}
    {caps : IndCaps md} :
    ∀ {env' : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ J blockNames caps env' members env₂ → EnvExt env' env₂
  | _, [], _, h => by subst h; exact EnvExt.refl _
  | _, ci :: rest, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    cases ci with
    | indInfo cv caps' =>
      exact (envExt_of_memberValRunJ (c := .indInfo cvA caps) hmv rfl).trans
        (indMembersRunJ_envExt hm)
    | ctorInfo cv nP nF =>
      exact (envExt_of_memberValRunJ (c := .ctorInfo cvA nP nF) hmv rfl).trans
        (indMembersRunJ_envExt hm)
    | axiomInfo _ => exact nomatch hm
    | defnInfo _ _ _ => exact nomatch hm
    | thmInfo _ _ => exact nomatch hm
    | recInfo _ _ _ _ => exact nomatch hm
    | projInfo _ => exact nomatch hm

/-- Two environments storing the same names. -/
private theorem find?_isNone_cons {env₁ env₂ : Env md} {c₁ c₂ : ConstantInfo md}
    (hn : c₁.name = c₂.name)
    (h : ∀ n, (env₁.find? n).isNone = (env₂.find? n).isNone) :
    ∀ n, ((⟨c₁ :: env₁.consts⟩ : Env md).find? n).isNone
      = ((⟨c₂ :: env₂.consts⟩ : Env md).find? n).isNone := by
  intro n
  rw [Env.find?_cons, Env.find?_cons, hn]
  by_cases h₁ : c₂.name = n
  · simp [h₁]
  · simp only [if_neg h₁]
    exact h n

/-- The install fold conses the provisioned recursors, with their rules, in the
order they were provisioned, so each is fresh where it is stored. -/
theorem indRecsFoldRunJ_envExt {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} {E : Env md} :
    ∀ {recs : List (ConstantInfo md)} {envP envF out : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames envP recs envSelf checked →
      IndRecsFoldRunJ J blockNames envBase envSelf envF checked out →
      (∀ n, (envF.find? n).isNone = (envP.find? n).isNone) →
      EnvExt E envF → EnvExt E out
  | [], _, envF, out, _, hprov, hfold, _, hext => by
    obtain ⟨-, rfl⟩ := hprov
    obtain rfl : out = envF := hfold
    exact hext
  | _ :: _, envP, envF, _, _, hprov, hfold, hsame, hext => by
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', -, hfold'⟩ := hfold
    have hstep : EnvExt envF ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ := by
      obtain ⟨type', hcv, hcvA, -⟩ := hmv
      have hfresh : envP.find? cvA.name = none := by
        rw [hcvA]; exact Option.isNone_iff_eq_none.mp hcv.1
      refine EnvExt.cons ?_ ?_
      · show envF.find? cvA.name = none
        have hs := hsame cvA.name
        rw [hfresh] at hs
        exact Option.isNone_iff_eq_none.mp hs
      · intro T _ _ _ e
        have hshape := hcv.2.2.1
        have hsh : cvA.name.isProjFnShape = false := by rw [hcvA]; exact hshape
        change cvA.name = projTableName T at e
        rw [e, projTableName_isProjFnShape] at hsh
        exact nomatch hsh
    exact indRecsFoldRunJ_envExt hprov' hfold'
      (find?_isNone_cons rfl hsame) (hext.trans hstep)

/-- **A modeled step extends the environment**: every constant it adds is fresh
and none is a projection table, which discharges `declRunJ_envExt`'s inductive
premise for the modeled route. -/
theorem declIndRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRunJ J env block env₂) :
    EnvExt env env₂ := by
  obtain ⟨-, envM, hmem, hrecs⟩ := h
  have hM := indMembersRunJ_envExt hmem
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · exact hM
  · exact indRecsFoldRunJ_envExt hprov hfold (fun _ => rfl) hM

end Ix.Kernel.Semantics
