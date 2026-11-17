module

public import IxC.Kernel.Semantics.DeclIndJ

@[expose] public section

/-!
# The modeled route with the rule typings renamed

`DeclIndRunJ` (`Semantics/DeclIndJ.lean`) types each recursor rule in the public world: the
rule's right-hand side, its λ-domains against the recursor's prefix and the constructor's
fields, and the canonical rule's parameter domains or the nested rule's pins, all at the
environment where the family's recursors are stored without rules. A checker that types the
rule with the family's recursors loadable cannot supply those judgements. It can supply them
on the **renamed** terms: the block's types, constructors and recursors renamed to their model
definitions (`f`, the block renaming), where no recursor of the family occurs and no rule of
the family can fire.

This module states that record:

* `renameJ f J` adjoins to a package `J` the judgements of renamed subjects: `e` is typed at
  `t` when `J` types `e`, or `e` is closed and `J` types `e.renameConsts f` at `t`; `a` and `b`
  are convertible when `J` converts them or their renamings. Its annotations and sorts are
  `J`'s.
* `DeclIndRenRunJ J` is `DeclIndRunJ` with the members' and recursors' front doors and every
  rule judgement over `renameJ f J`, except a nested rule's pins: those are typed renamed,
  against the renamed constructor's parameter domains (`IotaThmNRenRunJ`), since a pin is an
  open term, which `renameJ` does not cover.

`DeclIndRenRunJ.shape` reads the record's stored-data facts over the shape package `shapeJ`,
so that every consumer of `DeclIndRunJ` generic in its package applies. The model theorem is
`declIndRenJ` (`Model/DeclIndRen.lean`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel.Term Ix.Kernel.Verify

/-! ## The packages -/

/-- **The renamed judgements adjoined**: `e` has type `t` when `J` says so of `e`, or `e` is
closed and `J` says so of its renaming; `a` and `b` are convertible when `J` converts them or
their renamings. The annotation, sort and other relations are `J`'s. -/
def renameJ (f : Key md → Key md) (J : Judgements md) : Judgements md where
  annot := J.annot
  infer env d e t := J.infer env d e t ∨ (e.hasFvar = false ∧ J.infer env d (e.renameConsts f) t)
  defeq env d a b := J.defeq env d a b ∨ J.defeq env d (a.renameConsts f) (b.renameConsts f)
  sort := J.sort
  isZero := J.isZero
  thmValue := J.thmValue

/-- **The shape package**: `J`'s typing of a subject or of its renaming, and every conversion.
The records' stored-data facts are read over it. -/
def shapeJ (f : Key md → Key md) (J : Judgements md) : Judgements md where
  annot := J.annot
  infer env d e t := J.infer env d e t ∨ J.infer env d (e.renameConsts f) t
  defeq _ _ _ _ := True
  sort := J.sort
  isZero := J.isZero
  thmValue := J.thmValue

/-! ## The record -/

/-- `IotaThmNRunJ` with the rule's typings renamed: the pins, renamed, are typed against the
renamed constructor's parameter domains, and the other judgements are over `renameJ f J`. -/
def IotaThmNRenRunJ (J : Judgements md) (env' envSelf : Env md)
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
def IotaRuleRenRunJ (J : Judgements md) (env' envSelf : Env md)
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
    (∃ t', (renameJ f J).infer envSelf 0 rhsA t') ∧
    ∃ fire,
      r' = recRuleBits env'.find? cvName
        { r with rhs := rhsA, ctorParams := cnP, fire := fire,
                 paramsBlind := false } ∧
      ((Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true ∧ fire = .plain ∧
          IotaThmRunJ (renameJ f J) env' envSelf f cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP cvj.levelParams = false ∧
          ∃ lvls pins, fire = .nested lvls pins ∧
            IotaThmNRenRunJ J env' envSelf f cvName lps tyA mI rP j r
              cvj cnP cnF rhsA lvls pins))

/-- `IotaRulesRunJ` over the renamed rule record. -/
def IotaRulesRenRunJ (J : Judgements md) (env' envSelf : Env md)
    (f : Key md → Key md) (cvName : Key md)
    (lps : List LevelParam) (tyA : Expr md) (mI rP : Nat) :
    Nat → List (RecRule md) → List (RecRule md) → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleRenRunJ J env' envSelf f cvName lps tyA mI rP j r r' ∧
      IotaRulesRenRunJ J env' envSelf f cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- `IndRecsFoldRunJ` over the renamed rule record. -/
def IndRecsFoldRenRunJ (J : Judgements md) (blockNames : List (Key md))
    (envBase envSelf : Env md) :
    (Env md) → List (ConstantVal md × Nat × Nat × List (RecRule md)) →
    (Env md) → Prop
  | acc, [], out => out = acc
  | acc, c :: rest, out =>
    ∃ rules',
      IotaRulesRenRunJ J envBase envSelf
        (fun n => if blockNames.contains n then auxKey n .model else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        rules' ∧
      IndRecsFoldRenRunJ J blockNames envBase envSelf
        ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- `IndRecsRunJ` over the renamed record: the recursors' front doors over `renameJ`. -/
def IndRecsRenRunJ (J : Judgements md)
    (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (ConstantInfo md)) (env₃ : Env md) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRunJ
       (renameJ (fun n => if blockNames.contains n then auxKey n .model else n) J)
       blockNames env₂ recs envSelf checked ∧
     IndRecsFoldRenRunJ J blockNames env₂ envSelf env₂ checked env₃)

/-- **The modeled route with the rule typings renamed**: `DeclIndRunJ` whose front doors and
rule judgements are over `renameJ f J` for the block renaming `f`, except a nested rule's pin
typing, which is on the renamed pins. -/
def DeclIndRenRunJ (J : Judgements md) (env : Env md)
    (block : List (ConstantInfo md)) (env₂ : Env md) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ∃ envM,
    IndMembersRunJ
      (renameJ (fun n => if blockNames.contains n then auxKey n .model else n) J)
      blockNames {} env nonrecs envM ∧
    IndRecsRenRunJ J blockNames envM recs env₂

/-! ## Entering the record from renamed judgements -/

section Enter

variable {J : Judgements md} {f : Key md → Key md} {env : Env md} {d : Nat}

/-- A conversion list of `J` enters `renameJ f J`. -/
theorem DefEqListJ.renameJ_of : ∀ {as bs : List (Expr md)},
    DefEqListJ J env d as bs → DefEqListJ (renameJ f J) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => trivial
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      obtain ⟨h₀, h₁⟩ := h
      exact ⟨Or.inl h₀, ih h₁⟩

/-- A conversion list of `J` on the renamed terms enters `renameJ f J` on the terms. -/
theorem DefEqListJ.renameJ_of_map : ∀ {as bs : List (Expr md)},
    DefEqListJ J env d (as.map (·.renameConsts f)) (bs.map (·.renameConsts f)) →
      DefEqListJ (renameJ f J) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => trivial
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      obtain ⟨h₀, h₁⟩ := h
      exact ⟨Or.inr h₀, ih h₁⟩

/-- The renamed typing of a closed subject is a typing of `renameJ f J`. -/
theorem renameJ_infer_of_renamed {e t : Expr md} (hc : e.hasFvar = false)
    (h : J.infer env d (e.renameConsts f) t) : (renameJ f J).infer env d e t :=
  Or.inr ⟨hc, h⟩

end Enter

/-! ## The stored-data facts, over the shape package -/

section Shape

variable {J : Judgements md} {f : Key md → Key md}

theorem renameJ_infer_shape {env : Env md} {d : Nat} {e t : Expr md}
    (h : (renameJ f J).infer env d e t) : (shapeJ f J).infer env d e t :=
  h.elim Or.inl (fun h => Or.inr h.2)

/-- Any conversion list of equal lengths is one of the shape package. -/
theorem DefEqListJ.shape {K : Judgements md} {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, DefEqListJ K env d as bs →
      DefEqListJ (shapeJ f J) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => trivial
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      obtain ⟨-, h₁⟩ := h
      exact ⟨trivial, ih h₁⟩

/-- The renamed typed list is a typed list of the shape package. -/
theorem TypedListJ.shape_of_map {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)},
      TypedListJ J env d (as.map (·.renameConsts f)) (bs.map (·.renameConsts f)) →
      TypedListJ (shapeJ f J) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => trivial
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      obtain ⟨⟨ty, hty, -⟩, h₁⟩ := h
      exact ⟨⟨ty, Or.inr hty, trivial⟩, ih h₁⟩

theorem IotaRunsJ.shape {envSelf : Env md} {depth : Nat}
    {idxL idxR domL domR preL preR lamL lamR : List (Expr md)}
    {rhsS rhsApplied alphaS lhsS : Expr md}
    (h : IotaRunsJ (renameJ f J) envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS) :
    IotaRunsJ (shapeJ f J) envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS :=
  let ⟨h1, h2, h3, h4, _, ⟨tl, hl, _⟩, ⟨tr, hr, _⟩⟩ := h
  ⟨h1.shape, h2.shape, h3.shape, h4.shape, trivial,
    ⟨tl, renameJ_infer_shape hl, trivial⟩, ⟨tr, renameJ_infer_shape hr, trivial⟩⟩

theorem constantValRunJ_shape {env : Env md} {cv : ConstantVal md} {type' : Expr md}
    (h : ConstantValRunJ (renameJ f J) env cv type') :
    ConstantValRunJ (shapeJ f J) env cv type' :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, stype, u, hi, hs⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, stype, u, renameJ_infer_shape hi, hs⟩

theorem memberValRunJ_shape {env : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (h : MemberValRunJ (renameJ f J) env blockNames cv cvA) :
    MemberValRunJ (shapeJ f J) env blockNames cv cvA :=
  let ⟨ty, hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩ := h
  ⟨ty, constantValRunJ_shape hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩

theorem indMembersRunJ_shape {blockNames : List (Key md)} {caps : IndCaps md} :
    ∀ {env : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ (renameJ f J) blockNames caps env members env₂ →
      IndMembersRunJ (shapeJ f J) blockNames caps env members env₂
  | _, [], _, h => h
  | _, ci :: _, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, memberValRunJ_shape hmv, ?_⟩
    cases ci with
    | indInfo _ _ => exact indMembersRunJ_shape hm
    | ctorInfo _ _ _ => exact indMembersRunJ_shape hm
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ => exact hm

theorem provisionRecsRunJ_shape {blockNames : List (Key md)} :
    ∀ {env : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ (renameJ f J) blockNames env recs envSelf checked →
      ProvisionRecsRunJ (shapeJ f J) blockNames env recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest, hci, hmv, hrec, hchecked⟩ := h
    exact ⟨cvA, mI, rP, rules, rest, hci, memberValRunJ_shape hmv,
      provisionRecsRunJ_shape hrec, hchecked⟩

theorem iotaThmRunJ_shape {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    (h : IotaThmRunJ (renameJ f J) env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA) :
    IotaThmRunJ (shapeJ f J) env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7,
    k8.shape, k9.shape⟩

theorem iotaThmNRenRunJ_shape {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    {lvls : List Level} {pins : List (Expr md)}
    (h : IotaThmNRenRunJ J env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins) :
    IotaThmNRunJ (shapeJ f J) env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA
      lvls pins := by
  obtain ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7,
    TypedListJ.shape_of_map k8, k9.shape⟩

theorem iotaRuleRenRunJ_shape {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r r' : RecRule md}
    (h : IotaRuleRenRunJ J env envSelf f cvName lps tyA mI rP j r r') :
    IotaRuleRunJ (shapeJ f J) env envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, ⟨ty, h9⟩, fire, h10,
    hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8,
    ⟨ty, renameJ_infer_shape h9⟩, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨hp, lvls, pins, hf, ht⟩
  · exact Or.inl ⟨hp, hf, iotaThmRunJ_shape ht⟩
  · exact Or.inr ⟨hp, lvls, pins, hf, iotaThmNRenRunJ_shape ht⟩

theorem iotaRulesRenRunJ_shape {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRenRunJ J env envSelf f cvName lps tyA mI rP j rules rules' →
      IotaRulesRunJ (shapeJ f J) env envSelf f cvName lps tyA mI rP j rules rules'
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨r', rest, hr, hrest, hout⟩ := h
    exact ⟨r', rest, iotaRuleRenRunJ_shape hr, iotaRulesRenRunJ_shape hrest, hout⟩

end Shape

theorem indRecsFoldRenRunJ_shape {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf : Env md} :
    ∀ {acc : Env md} {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
      {out : Env md},
      IndRecsFoldRenRunJ J blockNames envBase envSelf acc checked out →
      IndRecsFoldRunJ
        (shapeJ (fun n => if blockNames.contains n then auxKey n .model else n) J)
        blockNames envBase envSelf acc checked out
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨rules, hrules, hrest⟩ := h
    exact ⟨rules, iotaRulesRenRunJ_shape hrules, indRecsFoldRenRunJ_shape hrest⟩

theorem indRecsRenRunJ_shape {J : Judgements md} {blockNames : List (Key md)} {env : Env md}
    {recs : List (ConstantInfo md)} {env₂ : Env md}
    (h : IndRecsRenRunJ J blockNames env recs env₂) :
    IndRecsRunJ
      (shapeJ (fun n => if blockNames.contains n then auxKey n .model else n) J)
      blockNames env recs env₂ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, provisionRecsRunJ_shape hprov,
      indRecsFoldRenRunJ_shape hfold⟩

/-- **The renamed record's stored-data facts**: it is `DeclIndRunJ` at the shape package, so
every consumer of `DeclIndRunJ` generic in its package (the environment extension, the
η-family closure, the store and companion invariants) applies to it. -/
theorem DeclIndRenRunJ.shape {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJ J env block env₂) :
    DeclIndRunJ (shapeJ (fun n =>
      if (block.map (·.name)).contains n then auxKey n .model else n) J) env block env₂ := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  exact ⟨hsplit, envM, indMembersRunJ_shape hmem, indRecsRenRunJ_shape hrecs⟩

/-- A modeled step on the renamed record extends the environment. -/
theorem declIndRenRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRenRunJ J env block env₂) :
    EnvExt env env₂ :=
  declIndRunJ_envExt h.shape

end Ix.Kernel.Semantics
