module

public import IxC.Kernel.Model.IndRenRecord

@[expose] public section

/-!
# The renamed modeled route, at given model and theorem keys

`DeclIndRenRunJ` (`Model/IndRenRecord.lean`) looks the model of block member `n` up at
`auxKey n .model`, renames the block by `fun n => if blockNames.contains n then auxKey n .model
else n`, and reads the `iota` theorem of recursor `R`'s rule `j` at
`auxKey (auxKey R .model) (.iota j)`. A checker that stores its models and theorems at keys of
its own needs the same record with those keys as parameters. This module states it:

* `blockRenAt g blockNames` renames a block name `n` to `g n` and fixes every other name;
* `MemberValRunJAt J g` looks the model up at `g n`, compares the type under `blockRenAt g`;
* the rule records read the theorem at `thmKey R j` (`IotaThmRunJAt`, `IotaThmNRenRunJAt`), and
  a nested rule's shape guard asks for that key (`nestedRuleShapeAt`);
* `DeclIndRenRunJAt J g thmKey` is `DeclIndRenRunJ` over these, with one more conjunct in place
  of the members' `isModelSuffix` guard: `g` maps every block name outside the block, so the
  block renaming is idempotent and no block name is its own model.

Each definition is its original's with the keys substituted, so every proof over the original
carries over by the same substitution. `DeclIndRunJAt` is the stored-data shape the renamed
record reads to (`DeclIndRenRunJAt.shape`). The model theorem is `declIndRenJAt`
(`Model/DeclIndRenAt.lean`); `declIndRenRunJ_at` there makes the original record an instance.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel.Term Ix.Kernel.Verify

variable {g : Key md → Key md} {thmKey : Key md → Nat → Key md}

/-! ## The block renaming at a model key -/

/-- **The block renaming at the model key `g`**: a block name `n` is renamed to `g n`, every
other name is fixed. -/
def blockRenAt (g : Key md → Key md) (blockNames : List (Key md)) (n : Key md) : Key md :=
  if blockNames.contains n then g n else n

theorem blockRenAt_pos {blockNames : List (Key md)} {n : Key md}
    (h : blockNames.contains n = true) : blockRenAt g blockNames n = g n := by
  simp only [blockRenAt, if_pos h]

theorem blockRenAt_neg {blockNames : List (Key md)} {n : Key md}
    (h : ¬ blockNames.contains n = true) : blockRenAt g blockNames n = n := by
  simp only [blockRenAt, if_neg h]

/-- The original block renaming is `blockRenAt` at the aux model key. -/
theorem blockRenAt_aux (blockNames : List (Key md)) :
    blockRenAt (fun n => auxKey n .model) blockNames
      = fun n => if blockNames.contains n then auxKey n .model else n := rfl

/-- **The block renaming is idempotent** when `g` maps block names outside the block. -/
theorem blockRenAt_idem {blockNames : List (Key md)}
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false) :
    ∀ n, blockRenAt g blockNames (blockRenAt g blockNames n) = blockRenAt g blockNames n := by
  intro n
  by_cases hn : blockNames.contains n = true
  · rw [blockRenAt_pos hn, blockRenAt_neg (by rw [hout n hn]; decide)]
  · rw [blockRenAt_neg hn, blockRenAt_neg hn]

/-! ## The nested rule's shape at a theorem key -/

/-- `nestedRuleShape` with its `iota` theorem guard at the key `tk`. -/
def nestedRuleShapeAt (env' envSelf : Env md) (tk : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP cnP : Nat) :
    Option (List Level × List (Expr md)) :=
  if (env'.findCV? tk).isSome ∧
      rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length = cnP + k ∧
            args.take cnP == pins.map (Expr.liftLooseBVars k 0) ∧
            args.drop cnP ==
              (List.range k).map (fun i => Expr.bvar (k - 1 - i)) ∧
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
              p.constsResolve envSelf && p.allLevelParamsDefined lps) ∧
            lvls.all (Level.allParamsDefined lps) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- Invert a successful `nestedRuleShape` computation into the facts
the stored rule's flag records: the prefix-major offset, the syntactic
well-formedness of the stored instantiations (lowered into the
rule-prefix context), and the recursor-type pin the instantiations
were read off — the major domain applies the family to the
instantiations' liftings past the index binders followed by the index
variables in order. -/
theorem nestedRuleShapeAt_inv {env' envSelf : Env md} {tk : Key md}
    {lps : List LevelParam} {tyA : Expr md} {mI rP cnP : Nat}
    {lvls : List Level} {pins : List (Expr md)}
    (h : nestedRuleShapeAt env' envSelf tk lps tyA mI rP cnP =
      some (lvls, pins)) :
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined lps = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined lps = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      tyA.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i)) ∧
      pins.length = cnP := by
  simp only [nestedRuleShapeAt] at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond1
  revert h
  match hstrip : tyA.stripPis mI with
  | none => intro h; exact nomatch h
  | some (pre, .bvar _) => intro h; exact nomatch h
  | some (pre, .fvar _ _) => intro h; exact nomatch h
  | some (pre, .sort _) => intro h; exact nomatch h
  | some (pre, .const _ _) => intro h; exact nomatch h
  | some (pre, .app _ _) => intro h; exact nomatch h
  | some (pre, .lam _ _ _) => intro h; exact nomatch h
  | some (pre, .letE _ _ _ _) => intro h; exact nomatch h
  | some (pre, .lit _) => intro h; exact nomatch h
  | some (pre, .proj _ _ _) => intro h; exact nomatch h
  | some (pre, .forallE dom body bm) => ?_
  intro h
  try dsimp only at h
  revert h
  match hfn : dom.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const D lvls' => ?_
  intro h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hlen, htake, hdrop, hpinsAll, hlvlsAll⟩ := hcond2
  have hplen : ((dom.getAppArgs.take cnP).map
      (Expr.lowerBVars (mI - rP) 0)).length = cnP := by
    rw [List.length_map, List.length_take, hlen]
    omega
  refine ⟨hcond1.2, ?_, ?_, pre, dom, body, bm, D, rfl, hfn,
    ?_, hplen⟩
  · intro l hl
    exact List.all_eq_true.mp hlvlsAll l hl
  · intro p hp
    have hall := List.all_eq_true.mp hpinsAll p hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
    exact ⟨hall.1.1.1, hall.2, hall.1.2, hall.1.1.2⟩
  · conv => lhs; rw [← List.take_append_drop cnP dom.getAppArgs]
    congr 1
    · exact eq_of_beq htake
    · exact eq_of_beq hdrop

/-! ## The block members -/

/-- `MemberValRun` over a package: the member's front door and the pins of its
model declaration (pure lookups). -/
def MemberValRunJAt (J : Judgements md) (g : Key md → Key md) (env' : Env md)
    (blockNames : List (Key md)) (cv : ConstantVal md) (cvA : ConstantVal md) :
    Prop :=
  ∃ type',
    ConstantValRunJ J env' cv type' ∧
    cvA = ⟨cv.name, cv.levelParams, type'⟩ ∧
    ∃ cvm mval hint,
      env'.find? (g cvA.name)
        = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams = cvA.levelParams ∧
      ((cvA.type.renameConsts (blockRenAt g blockNames))
          == cvm.type) = true

/-- `IndMembersRun` over a package: the non-recursor members, in order. -/
def IndMembersRunJAt (J : Judgements md) (g : Key md → Key md)
    (blockNames : List (Key md)) (caps : IndCaps md) :
    (Env md) → List (ConstantInfo md) → Env md → Prop
  | env', [], env₂ => env₂ = env'
  | env', ci :: rest, env₂ =>
    ∃ cvA, MemberValRunJAt J g env' blockNames ci.toConstantVal cvA ∧
      match ci with
      | .indInfo _ _ =>
        IndMembersRunJAt J g blockNames caps
          ⟨.indInfo cvA caps :: env'.consts⟩ rest env₂
      | .ctorInfo _ nP nF =>
        IndMembersRunJAt J g blockNames caps
          ⟨.ctorInfo cvA nP nF :: env'.consts⟩ rest env₂
      | _ => False

/-- `ProvisionRecsRun` over a package: the recursors, installed without rules. -/
def ProvisionRecsRunJAt (J : Judgements md) (g : Key md → Key md)
    (blockNames : List (Key md)) :
    (Env md) → List (ConstantInfo md) →
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) → Prop
  | envAcc, [], envSelf, checked =>
    envSelf = envAcc ∧ checked = []
  | envAcc, ci :: rest, envSelf, checked =>
    ∃ cvA mI rP rules rest',
      ci = .recInfo ci.toConstantVal mI rP rules ∧
      MemberValRunJAt J g envAcc blockNames ci.toConstantVal cvA ∧
      ProvisionRecsRunJAt J g blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest envSelf rest' ∧
      checked = (cvA, mI, rP, rules) :: rest'

/-! ## The rules -/

/-- `IotaThmRun` over a package: a canonical rule's `iota` theorem. -/
def IotaThmRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r : RecRule md)
    (cvj : ConstantVal md) (cnP cnF : Nat) (rhsA : Expr md) : Prop :=
  ∃ cvt fvs tbody,
    env'.findCV? (thmKey cvName j) = some cvt ∧
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
     Expr.ctorTeleOk cvj.type (cnP + cnF) = true ∧
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
typed against the constructor's parameter domains (`TypedListJ`). The kernel's
check that each pin is a fixed point of the annotation pass is not part of the
record: the model tier reads the pins through their typings only. -/
def IotaThmNRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r : RecRule md)
    (cvj : ConstantVal md) (cnP cnF : Nat) (rhsA : Expr md)
    (lvls : List Level) (pins : List (Expr md)) : Prop :=
  nestedRuleShapeAt env' envSelf (thmKey cvName j) lps tyA mI rP cnP
    = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? (thmKey cvName j) = some cvt ∧
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
def IotaRuleRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
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
      ((Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true ∧ fire = .plain ∧
          IotaThmRunJAt J env' envSelf f thmKey cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP cvj.levelParams = false ∧
          ∃ lvls pins, fire = .nested lvls pins ∧
            IotaThmNRunJAt J env' envSelf f thmKey cvName lps tyA mI rP j r
              cvj cnP cnF rhsA lvls pins))

/-- `IotaRulesRun` over a package. -/
def IotaRulesRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP : Nat) :
    Nat → List (RecRule md) → List (RecRule md) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleRunJAt J env' envSelf f thmKey cvName lps tyA mI rP j r r' ∧
      IotaRulesRunJAt J env' envSelf f thmKey cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- The recursor group's install fold over a package: each provisioned
recursor is stored with its checked rules. -/
def IndRecsFoldRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md) (blockNames : List (Key md))
    (envBase envSelf : Env md) :
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) →
    (Env md) → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesRunJAt J envBase envSelf
        (blockRenAt g blockNames) thmKey
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        rules' ∧
      IndRecsFoldRunJAt J g thmKey blockNames envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- `IndRecsRun` over a package: provision the group, then install it with its
rules. -/
def IndRecsRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md)
    (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (ConstantInfo md)) (env₃ : Env md) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRunJAt J g blockNames env₂ recs envSelf checked ∧
     IndRecsFoldRunJAt J g thmKey blockNames env₂ envSelf env₂ checked env₃)

/-! ## The block -/

/-- **The modeled route over a package**: the block lists its non-recursor
members before its recursors; the members are installed at the empty
capability record, then the recursors with their rules. No projection function
is installed. -/
def DeclIndRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md) (env : Env md)
    (block : List (ConstantInfo md)) (env₂ : Env md) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ∃ envM,
    IndMembersRunJAt J g blockNames {} env nonrecs envM ∧
    IndRecsRunJAt J g thmKey blockNames envM recs env₂


/-! ## The record -/

/-- `IotaThmNRunJ` with the rule's typings renamed: the pins, renamed, are typed against the
renamed constructor's parameter domains, and the other judgements are over `renameJ f J`. -/
def IotaThmNRenRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP j : Nat) (r : RecRule md)
    (cvj : ConstantVal md) (cnP cnF : Nat) (rhsA : Expr md)
    (lvls : List Level) (pins : List (Expr md)) : Prop :=
  nestedRuleShapeAt env' envSelf (thmKey cvName j) lps tyA mI rP cnP
    = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? (thmKey cvName j) = some cvt ∧
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
        Expr.instPisAt pinsP
          (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        (ldoms.getAppArgs.length == cnP + (mI - rP)) = true) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt
           (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         TypedListJ J envSelf depth
           ((pins.map fun p =>
             Expr.instSpine (fvsP.take rP) (rP - 1) p).map (·.renameConsts f))
           (cdomsP.map (·.renameConsts f)) ∧
         IotaRunsJ (renameJ f J) envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- `IotaRuleRunJ` with the rule's typings renamed: the right-hand side's typing and the
canonical rule's theorem over `renameJ f J`, a nested rule's theorem over `IotaThmNRenRunJ`. -/
def IotaRuleRenRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
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
    (∃ t', (renameJ f J).infer envSelf 0 rhsA t') ∧
    ∃ fire,
      r' = recRuleBits env'.find? cvName
        { r with rhs := rhsA, ctorParams := cnP, fire := fire,
                 paramsBlind := false } ∧
      ((Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true ∧ fire = .plain ∧
          IotaThmRunJAt (renameJ f J) env' envSelf f thmKey cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP cvj.levelParams = false ∧
          ∃ lvls pins, fire = .nested lvls pins ∧
            IotaThmNRenRunJAt J env' envSelf f thmKey cvName lps tyA mI rP j r
              cvj cnP cnF rhsA lvls pins))

/-- `IotaRulesRunJ` over the renamed rule record. -/
def IotaRulesRenRunJAt (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (thmKey : Key md → Nat → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP : Nat) :
    Nat → List (RecRule md) → List (RecRule md) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleRenRunJAt J env' envSelf f thmKey cvName lps tyA mI rP j r r' ∧
      IotaRulesRenRunJAt J env' envSelf f thmKey cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- `IndRecsFoldRunJ` over the renamed rule record. -/
def IndRecsFoldRenRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md) (blockNames : List (Key md))
    (envBase envSelf : Env md) :
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) →
    (Env md) → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesRenRunJAt J envBase envSelf
        (blockRenAt g blockNames) thmKey
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        rules' ∧
      IndRecsFoldRenRunJAt J g thmKey blockNames envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- `IndRecsRunJ` over the renamed record: the recursors' front doors over `renameJ`. -/
def IndRecsRenRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md)
    (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (ConstantInfo md)) (env₃ : Env md) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRunJAt
       (renameJ (blockRenAt g blockNames) J) g
       blockNames env₂ recs envSelf checked ∧
     IndRecsFoldRenRunJAt J g thmKey blockNames env₂ envSelf env₂ checked env₃)

/-- **The modeled route with the rule typings renamed**: `DeclIndRunJ` whose front doors and
rule judgements are over `renameJ f J` for the block renaming `f`, except a nested rule's pin
typing, which is on the renamed pins. -/
def DeclIndRenRunJAt (J : Judgements md) (g : Key md → Key md) (thmKey : Key md → Nat → Key md) (env : Env md)
    (block : List (ConstantInfo md)) (env₂ : Env md) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  (∀ n, blockNames.contains n = true → blockNames.contains (g n) = false) ∧
  ∃ envM,
    IndMembersRunJAt
      (renameJ (blockRenAt g blockNames) J) g
      blockNames {} env nonrecs envM ∧
    IndRecsRenRunJAt J g thmKey blockNames envM recs env₂


/-! ## A modeled step extends the environment -/

/-- A member's front door gives a fresh cons that is not a projection table. -/
theorem envExt_of_memberValRunJAt {J : Judgements md} {env : Env md}
    {blockNames : List (Key md)} {cv cvA : ConstantVal md}
    (h : MemberValRunJAt J g env blockNames cv cvA) {c : ConstantInfo md}
    (hc : c.name = cvA.name) : EnvExt env ⟨c :: env.consts⟩ := by
  obtain ⟨type', hcv, rfl, -⟩ := h
  exact envExt_of_constantValRunJ hcv hc

theorem indMembersRunJ_envExtAt {J : Judgements md} {blockNames : List (Key md)}
    {caps : IndCaps md} :
    ∀ {env' : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJAt J g blockNames caps env' members env₂ → EnvExt env' env₂
  | _, [], _, h => by subst h; exact EnvExt.refl _
  | _, ci :: rest, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    cases ci with
    | indInfo cv caps' =>
      exact (envExt_of_memberValRunJAt (c := .indInfo cvA caps) hmv rfl).trans
        (indMembersRunJ_envExtAt hm)
    | ctorInfo cv nP nF =>
      exact (envExt_of_memberValRunJAt (c := .ctorInfo cvA nP nF) hmv rfl).trans
        (indMembersRunJ_envExtAt hm)
    | axiomInfo _ => exact nomatch hm
    | defnInfo _ _ _ => exact nomatch hm
    | thmInfo _ _ => exact nomatch hm
    | recInfo _ _ _ _ => exact nomatch hm
    | projInfo _ => exact nomatch hm

/-- Two environments storing the same names. -/
private theorem find?_isNone_consAt {env₁ env₂ : Env md} {c₁ c₂ : ConstantInfo md}
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
theorem indRecsFoldRunJ_envExtAt {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} {E : Env md} :
    ∀ {recs : List (ConstantInfo md)} {envP envF out : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJAt J g blockNames envP recs envSelf checked →
      IndRecsFoldRunJAt J g thmKey blockNames envBase envSelf envF checked out →
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
    exact indRecsFoldRunJ_envExtAt hprov' hfold'
      (find?_isNone_consAt rfl hsame) (hext.trans hstep)

/-- **A modeled step extends the environment**: every constant it adds is fresh
and none is a projection table, which discharges `declRunJ_envExt`'s inductive
premise for the modeled route. -/
theorem declIndRunJ_envExtAt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRunJAt J g thmKey env block env₂) :
    EnvExt env env₂ := by
  obtain ⟨-, envM, hmem, hrecs⟩ := h
  have hM := indMembersRunJ_envExtAt hmem
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · exact hM
  · exact indRecsFoldRunJ_envExtAt hprov hfold (fun _ => rfl) hM


/-! ## The stored-data facts, over the shape package -/

section Shape

variable {J : Judgements md} {f : Key md → Key md}


theorem memberValRunJ_shapeAt {env : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (h : MemberValRunJAt (renameJ f J) g env blockNames cv cvA) :
    MemberValRunJAt (shapeJ f J) g env blockNames cv cvA :=
  let ⟨ty, hc, heq, cvm, value, hint, hfind, hlevels, htype⟩ := h
  ⟨ty, constantValRunJ_shape hc, heq, cvm, value, hint, hfind, hlevels, htype⟩

theorem indMembersRunJ_shapeAt {blockNames : List (Key md)} {caps : IndCaps md} :
    ∀ {env : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJAt (renameJ f J) g blockNames caps env members env₂ →
      IndMembersRunJAt (shapeJ f J) g blockNames caps env members env₂
  | _, [], _, h => h
  | _, ci :: _, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, memberValRunJ_shapeAt hmv, ?_⟩
    cases ci with
    | indInfo _ _ => exact indMembersRunJ_shapeAt hm
    | ctorInfo _ _ _ => exact indMembersRunJ_shapeAt hm
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ => exact hm

theorem provisionRecsRunJ_shapeAt {blockNames : List (Key md)} :
    ∀ {env : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJAt (renameJ f J) g blockNames env recs envSelf checked →
      ProvisionRecsRunJAt (shapeJ f J) g blockNames env recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest, hci, hmv, hrec, hchecked⟩ := h
    exact ⟨cvA, mI, rP, rules, rest, hci, memberValRunJ_shapeAt hmv,
      provisionRecsRunJ_shapeAt hrec, hchecked⟩

theorem iotaThmRunJ_shapeAt {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    (h : IotaThmRunJAt (renameJ f J) env envSelf f thmKey cvName lps tyA mI rP j r cvj cnP cnF rhsA) :
    IotaThmRunJAt (shapeJ f J) env envSelf f thmKey cvName lps tyA mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7,
    k8.shape, k9.shape⟩

theorem iotaThmNRenRunJ_shapeAt {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    {lvls : List Level} {pins : List (Expr md)}
    (h : IotaThmNRenRunJAt J env envSelf f thmKey cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins) :
    IotaThmNRunJAt (shapeJ f J) env envSelf f thmKey cvName lps tyA mI rP j r cvj cnP cnF rhsA
      lvls pins := by
  obtain ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7,
    TypedListJ.shape_of_map k8, k9.shape⟩

theorem iotaRuleRenRunJ_shapeAt {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r r' : RecRule md}
    (h : IotaRuleRenRunJAt J env envSelf f thmKey cvName lps tyA mI rP j r r') :
    IotaRuleRunJAt (shapeJ f J) env envSelf f thmKey cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, ⟨ty, h9⟩, fire, h10,
    hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8,
    ⟨ty, renameJ_infer_shape h9⟩, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨hp, lvls, pins, hf, ht⟩
  · exact Or.inl ⟨hp, hf, iotaThmRunJ_shapeAt ht⟩
  · exact Or.inr ⟨hp, lvls, pins, hf, iotaThmNRenRunJ_shapeAt ht⟩

theorem iotaRulesRenRunJ_shapeAt {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRenRunJAt J env envSelf f thmKey cvName lps tyA mI rP j rules rules' →
      IotaRulesRunJAt (shapeJ f J) env envSelf f thmKey cvName lps tyA mI rP j rules rules'
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨r', rest, hr, hrest, hout⟩ := h
    exact ⟨r', rest, iotaRuleRenRunJ_shapeAt hr, iotaRulesRenRunJ_shapeAt hrest, hout⟩

end Shape

theorem indRecsFoldRenRunJ_shapeAt {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} :
    ∀ {acc : Env md} {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
      {out : Env md},
      IndRecsFoldRenRunJAt J g thmKey blockNames envBase envSelf acc checked out →
      IndRecsFoldRunJAt
        (shapeJ (blockRenAt g blockNames) J) g thmKey
        blockNames envBase envSelf acc checked out
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨rules, hrules, hrest⟩ := h
    exact ⟨rules, iotaRulesRenRunJ_shapeAt hrules, indRecsFoldRenRunJ_shapeAt hrest⟩

theorem indRecsRenRunJ_shapeAt {J : Judgements md} {blockNames : List (Key md)} {env : Env md}
    {recs : List (ConstantInfo md)} {env₂ : Env md}
    (h : IndRecsRenRunJAt J g thmKey blockNames env recs env₂) :
    IndRecsRunJAt
      (shapeJ (blockRenAt g blockNames) J) g thmKey
      blockNames env recs env₂ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, provisionRecsRunJ_shapeAt hprov,
      indRecsFoldRenRunJ_shapeAt hfold⟩

/-- **The renamed record's stored-data facts**: it is `DeclIndRunJ` at the shape package, so
every consumer of `DeclIndRunJ` generic in its package (the environment extension, the
η-family closure, the store and companion invariants) applies to it. -/
theorem DeclIndRenRunJAt.shape {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJAt J g thmKey env block env₂) :
    DeclIndRunJAt (shapeJ (blockRenAt g (block.map (·.name))) J) g thmKey env block env₂ := by
  obtain ⟨hsplit, -, envM, hmem, hrecs⟩ := h
  exact ⟨hsplit, envM, indMembersRunJ_shapeAt hmem, indRecsRenRunJ_shapeAt hrecs⟩

/-- A modeled step on the renamed record extends the environment. -/
theorem declIndRenRunJ_envExtAt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJAt J g thmKey env block env₂) :
    EnvExt env env₂ :=
  declIndRunJ_envExtAt h.shape



/-! ## The original record at the aux keys

Every conjunct of the original records is its `At` twin's at `g = fun n => auxKey n .model` and
`thmKey = fun R j => auxKey (auxKey R .model) (.iota j)`, except the members' `isModelSuffix`
guard, which the twin drops. -/

section Aux

theorem nestedRuleShape_eq_at {env' envSelf : Env md} {cvName : Key md}
    {lps : List LevelParam} {tyA : Expr md} {mI rP cnP j : Nat} :
    nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
      = nestedRuleShapeAt env' envSelf (auxKey (auxKey cvName .model) (.iota j)) lps tyA mI rP
          cnP := rfl

theorem memberValRunJ_at {J : Judgements md} {env : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (h : MemberValRunJ J env blockNames cv cvA) :
    MemberValRunJAt J (fun n => auxKey n .model) env blockNames cv cvA :=
  let ⟨ty, hc, heq, _, cvm, value, hint, hfind, hlevels, htype⟩ := h
  ⟨ty, hc, heq, cvm, value, hint, hfind, hlevels, htype⟩

theorem indMembersRunJ_at {J : Judgements md} {blockNames : List (Key md)}
    {caps : IndCaps md} :
    ∀ {env : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ J blockNames caps env members env₂ →
      IndMembersRunJAt J (fun n => auxKey n .model) blockNames caps env members env₂
  | _, [], _, h => h
  | _, ci :: _, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, memberValRunJ_at hmv, ?_⟩
    cases ci with
    | indInfo _ _ => exact indMembersRunJ_at hm
    | ctorInfo _ _ _ => exact indMembersRunJ_at hm
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ => exact hm

theorem provisionRecsRunJ_at {J : Judgements md} {blockNames : List (Key md)} :
    ∀ {env : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames env recs envSelf checked →
      ProvisionRecsRunJAt J (fun n => auxKey n .model) blockNames env recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest, hci, hmv, hrec, hchecked⟩ := h
    exact ⟨cvA, mI, rP, rules, rest, hci, memberValRunJ_at hmv,
      provisionRecsRunJ_at hrec, hchecked⟩

theorem iotaThmNRenRunJ_at {J : Judgements md} {env envSelf : Env md}
    {f : Key md → Key md} {cvName : Key md} {lps : List LevelParam} {tyA : Expr md}
    {mI rP j : Nat} {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    {lvls : List Level} {pins : List (Expr md)}
    (h : IotaThmNRenRunJ J env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins) :
    IotaThmNRenRunJAt J env envSelf f (fun R j => auxKey (auxKey R .model) (.iota j)) cvName
      lps tyA mI rP j r cvj cnP cnF rhsA lvls pins :=
  ⟨nestedRuleShape_eq_at ▸ h.1, h.2⟩

theorem iotaRuleRenRunJ_at {J : Judgements md} {env envSelf : Env md}
    {f : Key md → Key md} {cvName : Key md} {lps : List LevelParam} {tyA : Expr md}
    {mI rP j : Nat} {r r' : RecRule md}
    (h : IotaRuleRenRunJ J env envSelf f cvName lps tyA mI rP j r r') :
    IotaRuleRenRunJAt J env envSelf f (fun R j => auxKey (auxKey R .model) (.iota j)) cvName
      lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, h9, fire, h10, hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, h9, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨hp, lvls, pins, hf, ht⟩
  · exact Or.inl ⟨hp, hf, ht⟩
  · exact Or.inr ⟨hp, lvls, pins, hf, iotaThmNRenRunJ_at ht⟩

theorem iotaRulesRenRunJ_at {J : Judgements md} {env envSelf : Env md}
    {f : Key md → Key md} {cvName : Key md} {lps : List LevelParam} {tyA : Expr md}
    {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRenRunJ J env envSelf f cvName lps tyA mI rP j rules rules' →
      IotaRulesRenRunJAt J env envSelf f (fun R j => auxKey (auxKey R .model) (.iota j))
        cvName lps tyA mI rP j rules rules'
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨r', rest, hr, hrest, hout⟩ := h
    exact ⟨r', rest, iotaRuleRenRunJ_at hr, iotaRulesRenRunJ_at hrest, hout⟩

theorem indRecsFoldRenRunJ_at {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} :
    ∀ {acc : Env md} {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
      {out : Env md},
      IndRecsFoldRenRunJ J blockNames envBase envSelf acc checked out →
      IndRecsFoldRenRunJAt J (fun n => auxKey n .model)
        (fun R j => auxKey (auxKey R .model) (.iota j)) blockNames envBase envSelf acc checked
        out
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨rules, hrules, hrest⟩ := h
    exact ⟨rules, iotaRulesRenRunJ_at hrules, indRecsFoldRenRunJ_at hrest⟩

theorem indRecsRenRunJ_at {J : Judgements md} {blockNames : List (Key md)} {env : Env md}
    {recs : List (ConstantInfo md)} {env₂ : Env md}
    (h : IndRecsRenRunJ J blockNames env recs env₂) :
    IndRecsRenRunJAt J (fun n => auxKey n .model)
      (fun R j => auxKey (auxKey R .model) (.iota j)) blockNames env recs env₂ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, provisionRecsRunJ_at hprov,
      indRecsFoldRenRunJ_at hfold⟩

end Aux

end Ix.Kernel.Semantics
