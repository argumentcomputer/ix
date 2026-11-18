import IxVMRefinement.FamilyAlias.Check

/-! # What the family check establishes: the seam between the circuit and the model

`FamilyCheckFacts env blk adv tys rhsss` is one proposition about a family as read (`blk`: the
block's types, its constructors and the recursors of its family record), the advice the check's
payload names (`adv`), and the environment `env` the check runs against, which stores the
advice. It is what an accepted `KernelModeled::check_family` run establishes, stated without the
run, the heap or the record store:

* on one side, a refinement of the circuit proves it from the observed run;
* on the other, the family step's conclusion (`Typing.FamilyAlias.FamilyStepTarget`) follows
  from it and the prefix invariant, with no further reference to the circuit.

**The form.** The circuit checks a family against its advice by renaming: every member of the
block and of its family record goes to its model (`adv.ren`, the circuit's `rename` over the
tables `src`, `dst`), and every typing and conversion is of renamed terms, which name advice and
earlier constants only. The facts are stated the same way:

* every term is in the level parameters of the member it belongs to; a judgement is one of the
  positional derivation package `posRulesJ`, at `env`;
* a member's model is a stored definition whose type is the member's annotated type, renamed, at
  positions (`MemberFacts`);
* a rule's facts (`RuleFacts`, `StatementFacts`) are the conjuncts of IxC's rule record
  `IotaThmNRenRunJ` read at the advice: the statement is the advice theorem's own type, the head
  of its left side the recursor's model, the constructor of its major premise the constructor's
  model, and the pins are the parameter arguments of the recursor's major premise
  (`majorShape`). One form covers a canonical rule, whose pins are the first prefix variables.

Nothing here is the in-process modeller's: `env` stores the advice as the fold stored it from
its records.

**What `env` is assumed to store.** Every judgement below is a derivation at `env`, and a
derivation reads the environment only by looking constants up. So `env` stores every constant
the derivations name:

1. the advice records of the check's payload: the members' models, the rules' theorems, and
   every definition, theorem, inductive block and recursor these are built from;
2. the constants outside the advice that the advice uses (the payload's witnessed references):
   the records of basis roles, members of the block's dependency closure, and the types,
   constructors and recursors of the containers a nested block nests through;
3. what the terms of the block and of its family record name outside the family;
4. the pinned equality, where the family has a recursor.

No field names the first three beyond the models and the theorems; the constructors of a
container appear as `RuleCtor`'s first case. The order of these constants in `env` is not read.
What is assumed is that all of them are stored before the alias group and the block are. The
check itself runs them in this order, each at the family check's own role context, hence at one
limit: the witnesses (a basis role's record with its closure; a container's recursor), then the
advice records in the payload's order, each of which uses only earlier advice, projections of
earlier advice blocks and witnessed references.

A family record with no recursor is covered as stated: `recs` and `eqStored` are then empty
conditions, and `adv.thms` is empty.

**The circuit this is stated against** is the family check after the final circuit change:
a family recursor's declared type accepted only as the reconstruction or its full consumption,
the auxiliary members in the derived order. Three fields need more than that source has; each
is marked `(change)` below with the assertion it needs. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  openPisAtFvars eqName eqA isEqHead)

set_option linter.unusedVariables false

/-! ## The advice a family check reads -/

/-- **The advice of a family, as the check's payload names it**: the model of each member of
the block and of the family record, in the block's order (types, constructors, recursors), and
for each recursor the theorem of each of its rules. -/
structure FamilyAdvice where
  /-- Each member's key with its model's key. -/
  models : List (KKey × KKey)
  /-- For each recursor, in order, the keys of its rules' theorems. -/
  thms : List (List KKey)

/-- **The renaming to the advice**: a member goes to its model, every other key stays. The first
pair at a key decides, as in the circuit's `rename_addr`. -/
def FamilyAdvice.ren (adv : FamilyAdvice) : KKey → KKey := aliasMap adv.models

/-! ## A member against its model -/

/-- **One member against its model** (`KernelModeled::member_val`, with the advice record's own
check). `tyA` is the member's annotated type.

* `perm`, `closed`, `bounded`, `annotated`: the member as loaded: its level parameters are the
  positions in some order, its declared type is closed, and the type the circuit holds is an
  annotation of it;
* `model`: the model is a stored definition at the positions, whose type is the member's
  annotated type renamed to the advice, at positions (the structural comparison of
  `member_val`);
* `modelTyped`: the model's type is a type. The family check does not type a member's type
  renamed; the advice record's own check typed it (`check_advice_record`). -/
structure MemberFacts (env : Env .anon) (g : KKey → KKey) (ci : ConstantInfo .anon)
    (tyA : KExpr) : Prop where
  perm : ci.toConstantVal.levelParams.Perm (List.range ci.toConstantVal.levelParams.length)
  closed : ci.toConstantVal.type.hasFvar = false
  bounded : ci.toConstantVal.type.looseBVarsBounded 0 = true
  annotated : IxVM.Consistency.Annotates tyA ci.toConstantVal.type
  model : ∃ (cvm : ConstantVal .anon) (mval : KExpr) (hint : ReducibilityHint),
    env.find? (g ci.name) = some (.defnInfo cvm mval hint) ∧
    cvm.levelParams = List.range ci.toConstantVal.levelParams.length ∧
    cvm.type = posOf ci.toConstantVal.levelParams (tyA.renameConsts g)
  modelTyped : ∃ stype u, posRulesJ.infer env 0 (tyA.renameConsts g) stype ∧
    posRulesJ.sort env 0 stype u

/-- The members against their models, one annotated type for each, in order. -/
def MembersFacts (env : Env .anon) (g : KKey → KKey) :
    List (ConstantInfo .anon) → List KExpr → Prop
  | [], [] => True
  | ci :: rest, tyA :: tys => MemberFacts env g ci tyA ∧ MembersFacts env g rest tys
  | _, _ => False

/-- Whether each annotated type names, of the listed keys, none from its own on: `names` are the
keys of the members from the first type's member on. -/
def typesScopedB : List KKey → List KExpr → Bool
  | [], [] => true
  | n :: ns, ty :: tys => (n :: ns).all (fun k => !ty.mentionsConst k) && typesScopedB ns tys
  | _, _ => false

/-! ## A rule against its theorem -/

/-- **The major premise of a recursor's type, as the rule check reads it**
(`KernelModeled::rec_major_pins`): after `mI` binders the domain is a constant at levels `lvls`
applied to `cnP` parameter arguments and to the `mI - rP` index variables in order; the
parameter arguments, lowered below the index binders, are the `pins`. It is
`Ix.Kernel.nestedRuleShape` without its guards on the environment. -/
def majorShape (tyA : KExpr) (mI rP cnP : Nat) : Option (List Level × List KExpr) :=
  if rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _ lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length = cnP + k ∧
            args.take cnP = pins.map (Expr.liftLooseBVars k 0) ∧
            args.drop cnP = (List.range k).map (fun i => Expr.bvar (k - 1 - i)) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- **A constructor a rule names**: stored before the block (a rule of an auxiliary member, whose
constructor is the container's), or a constructor of the block, at its annotated type. -/
def RuleCtor (env : Env .anon) (blk : List (ConstantInfo .anon)) (tys : List KExpr) (k : KKey)
    (cvj : ConstantVal .anon) (cnP cnF : Nat) : Prop :=
  env.find? k = some (.ctorInfo cvj cnP cnF) ∨
  ∃ (i : Nat) (cv : ConstantVal .anon) (tyC : KExpr),
    blk[i]? = some (.ctorInfo cv cnP cnF) ∧ tys[i]? = some tyC ∧ cv.name = k ∧
      cvj = ⟨cv.name, cv.levelParams, tyC⟩

/-- **A rule's theorem statement against the rule** (`KernelModeled::check_iota_rule`, from the
load of the theorem on). `stmt` is the advice theorem's type in the recursor's level parameters;
`g` is the renaming to the advice. These are the conjuncts of IxC's `IotaThmNRenRunJ` with `g`
for the block renaming and `posRulesJ` for the package:

* the statement opens to an equation of three arguments under `rP + cnF` binders;
* its left side is the recursor's model at the recursor's own level parameters, applied to the
  prefix variables, the index arguments and the major premise; the major premise is the
  constructor's model at the major's levels, applied to the pins (renamed, at the statement's
  prefix variables) and the field variables: structural equalities;
* the constructor's type, at the major's levels and renamed, instantiates at those arguments;
  its residual has an argument for each parameter and index;
* `pinsFixed`: the renaming fixes the annotation of every variable a pin mentions `(change)`:
  a pin mentions parameters only and a parameter's domain names no member of the block. The
  comparison with the reconstruction gives it only with a specification of the reconstruction;
  two assertions give it directly (no pin mentions a motive or a minor premise; the first
  parameter domains of a family recursor name no member);
* the pins, renamed, inhabit the renamed constructor's parameter domains
  (`inst_params_typed`);
* the walks (`IotaRunsJ`): the index arguments (`defeq_list_ok`), the statement's field and
  prefix domains (`defeq_tele`, twice), the rule's λ-domains against the recursor's prefix and
  the constructor's fields (`defeq_lam_tele`, twice), the right side against the rule applied,
  and both sides typed at the equation's type. The λ-walk is stated at the variables of the
  recursor's and the constructor's telescopes `(change)`: `defeq_lam_tele` has to extend its
  context with the Π-side domain, not the λ-side one. -/
def StatementFacts (env : Env .anon) (g : KKey → KKey) (recKey : KKey) (lps : List LevelParam)
    (tyA : KExpr) (mI rP : Nat) (ctorKey : KKey) (rhsA : KExpr) (cvj : ConstantVal .anon)
    (cnP cnF : Nat) (lvls : List Level) (pins : List KExpr) (stmt : KExpr) : Prop :=
  ∃ fvs tbody,
    openPisAtFvars (rP + cnF) stmt 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let pinsF := pins.map fun p =>
       Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts g)
     let largs := lhsS.getAppArgs
     lhsS.getAppFn = Expr.const (g recKey) (lps.map .param) ∧
     largs.length = mI + 1 ∧
     largs.take rP = fvs.take rP ∧
     largs.getLastD (.bvar 0) = Expr.mkAppN (.const (g ctorKey) lvls) (pinsF ++ xFvs) ∧
     ∃ cdoms cres rdoms lrest fvsP crest2 cdomsP crestP xFvsP ldoms,
       Expr.instPisAt (pinsF ++ xFvs)
         ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts g)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts g) = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       (let pinsP := pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p
        Expr.instPisAt pinsP (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        ldoms.getAppArgs.length = cnP + (mI - rP) ∧
        (∀ p ∈ pinsP, LeavesFixed g p) ∧
        ∃ ldomsL lrest2,
          Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
          TypedListJ posRulesJ env depth
            (pinsP.map (·.renameConsts g)) (cdomsP.map (·.renameConsts g)) ∧
          IotaRunsJ posRulesJ env depth
            ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
            (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
            ((fvs.take rP).map Expr.fvarTypeD) rdoms
            (((fvsP ++ xFvsP).map Expr.fvarTypeD).map (·.renameConsts g))
            (ldomsL.map (·.renameConsts g))
            rhsS (Expr.mkAppN (rhsA.renameConsts g) fvs)
            (targs.getD 0 (.bvar 0)) lhsS))

/-- **One rule of a recursor against its theorem** (`KernelModeled::check_rules_go` and
`check_iota_rule`). `r` is the rule as read, `rhsA` its annotated right-hand side, `thm` the key
of its advice theorem.

* the constructor the rule names, with its counts (`check_rules_go`: the constructor
  projection of the major's inductive at the rule's index; its parameter count is the
  inductive's and its field count the rule's);
* the rule as loaded: closed, annotated, its level parameters the recursor's, a λ-telescope over
  the prefix and the fields (`validate_expr_well_scoped`, `peel_n_lams_collect`);
* the rule, renamed, is typed (`k_infer`);
* the major premise's shape and the scope of its levels and pins (`rec_major_pins`, with the
  scope check of the recursor's type);
* the constructor's type has a binder for each parameter and field, and a constant at the head
  of its residual;
* the theorem is a stored advice theorem at the positions, and its statement, in the
  recursor's level parameters, has the facts of `StatementFacts`. -/
def RuleFacts (env : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (recKey : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (r : RecRule .anon) (rhsA : KExpr) (thm : KKey) : Prop :=
  ∃ (cvj : ConstantVal .anon) (cnP cnF : Nat) (lvls : List Level) (pins : List KExpr),
    RuleCtor env blk tys r.ctor cvj cnP cnF ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    IxVM.Consistency.Annotates rhsA r.rhs ∧
    rhsA.allLevelParamsDefined lps = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    (∃ t', posRulesJ.infer env 0 (rhsA.renameConsts g) t') ∧
    majorShape tyA mI rP cnP = some (lvls, pins) ∧
    lvls.all (Level.allParamsDefined lps) = true ∧
    pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP && p.allLevelParamsDefined lps)
      = true ∧
    Expr.ctorTeleOk cvj.type (cnP + cnF) = true ∧
    ∃ (cvt : ConstantVal .anon) (vt : KExpr),
      env.find? thm = some (.thmInfo cvt vt) ∧
      cvt.levelParams = List.range lps.length ∧
      StatementFacts env g recKey lps tyA mI rP r.ctor rhsA cvj cnP cnF lvls pins
        (invPosOf lps cvt.type)

/-- The rules of one recursor against their theorems, in order. -/
def RulesFacts (env : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (recKey : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat) :
    List (RecRule .anon) → List KExpr → List KKey → Prop
  | [], [], [] => True
  | r :: rs, rhsA :: rhss, thm :: thms =>
    RuleFacts env g blk tys recKey lps tyA mI rP r rhsA thm ∧
      RulesFacts env g blk tys recKey lps tyA mI rP rs rhss thms
  | _, _, _ => False

/-- The recursors' rules against their theorems: one annotated type, one list of annotated
right-hand sides and one list of theorem keys for each recursor, in order. -/
def RecsFacts (env : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) :
    List (ConstantInfo .anon) → List KExpr → List (List KExpr) → List (List KKey) → Prop
  | [], [], [], [] => True
  | .recInfo cv mI rP rules :: rest, tyA :: tysR, rhss :: rhsss, ths :: thss =>
    RulesFacts env g blk tys cv.name cv.levelParams tyA mI rP rules rhss ths ∧
      RecsFacts env g blk tys rest tysR rhsss thss
  | _, _, _, _ => False

/-! ## The family -/

/-- Whether a member is a type or a constructor. -/
def isTypeOrCtor : ConstantInfo .anon → Bool
  | .indInfo _ _ => true
  | .ctorInfo _ _ _ => true
  | _ => false

/-- **What the family check establishes** (module docstring). `blk` is the family as read, in
the circuit's order: the block's types, its constructors, then the recursors of the family
record. `tys` are the members' annotated types, in that order; `rhsss` the annotated right-hand
sides of each recursor's rules. `env` stores the advice.

* `split`, `kinds`: the family's layout (`check_family`: the block's members are inductive
  types, the family record's are recursors; the tables `src` and `dst` list types, constructors,
  recursors);
* `table`: the advice names a model for each member, in order (`get_addrs`, three times);
* `members`: each member against its model (`members_val`, three times);
* `scoped`: a member's annotated type names, of the family's members, only earlier ones. For a
  recursor this is `expr_mentions_addrs(ty, fam) = 0` in `check_recs`. For a type and a
  constructor `(change)`: the same assertion on a type's type against every member, and on a
  constructor's type against the constructors and the recursors;
* `recs`: each rule of each recursor against its theorem (`check_recs`, `check_rules`);
* `eqStored`: the pinned equality is stored (the statements are equations at the equality
  role's address, `check_iota_rule`). -/
structure FamilyCheckFacts (env : Env .anon) (blk : List (ConstantInfo .anon))
    (adv : FamilyAdvice) (tys : List KExpr) (rhsss : List (List KExpr)) : Prop where
  split : blk = nonrecsOf blk ++ recsOf blk
  kinds : (nonrecsOf blk).all isTypeOrCtor = true
  table : adv.models.map (·.1) = blk.map (·.name)
  members : MembersFacts env adv.ren blk tys
  scoped : typesScopedB (blk.map (·.name)) tys = true
  recs : RecsFacts env adv.ren blk tys (recsOf blk) (tys.drop (nonrecsOf blk).length) rhsss
    adv.thms
  eqStored : recsOf blk ≠ [] → env.find? eqName = some eqA

end IxVM.Refinement.Decl.FamilyAlias
