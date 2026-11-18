import IxVMRefinement.FamilyAlias.Enter
import IxVMRefinement.FamilyAlias.Install
import IxVMRefinement.FamilyAlias.Roots
import IxC.Kernel.Verify.Rules.Bridge
import Ix.IxVM.Consistency.StoredCheck

/-! # The family record over the alias package, found by evaluation

`famRecordCheck` searches for a proof of IxC's renamed record `DeclIndRenRunJ (famJ h)` of a block
at an environment that stores the block's model aliases, and returns the proof it finds together
with the environment after the block. It is sound by construction: what it returns is a proof
(`famRecord_of_check`). A closed instance is then proved by evaluating the check.

Every stored-data conjunct of the record (lookups, telescope openings, shapes, level lists) is
decided as the record states it. Every judgement of the record is discharged by a run of IxC's
executable checker (`inferTypeCore`, `isDefEqCore`, `whnf` at the verified mode) on the subject
the family package asks for: the term renamed by the block renaming and by the alias renaming,
with the level parameters at positions. The run is turned into a derivation by the rules bridge
(`Ix.Kernel.Rules.inferTypeCore_bridge`, `isDefEqCore_bridge`, `whnf_bridge`) and enters the
package by the lemmas of `FamilyAlias/Enter.lean`. So an accepted check exhibits, for each
judgement, a real derivation on the positional terms over the alias targets.

The alias renaming is given by a table of pairs (alias key, target key), `aliasMap`. That it
moves stored aliases only (`AliasEnv`) is decided on the table (`aliasTableCheck`).

The check is not complete: `fuel` bounds the executable checker's runs, and an erased equality of
the record is looked for as an equality.

A failed check returns the name of the first conjunct it could not establish.
-/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam EnvExt ReducibilityHint Derived openPisAtFvars eqName eqA auxKey nestedRuleShape
  recRuleBits isEqHead)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Outcomes -/

/-- Whether a search succeeded. -/
def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- The reason a search failed, or the empty string. -/
def failureOf {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-- A decidable proposition, proved or named as the failure. -/
def guardP (lbl : String) (p : Prop) [Decidable p] : Except String (PLift p) :=
  if hp : p then .ok ⟨hp⟩ else .error lbl

/-- The content of an option, with the equation that it is the content. -/
def getSome {α : Type} (lbl : String) (o : Option α) : Except String {x : α // o = some x} :=
  match o with
  | some x => .ok ⟨x, rfl⟩
  | none => .error lbl

/-! ## The alias renaming of a table -/

/-- The renaming of a table of pairs (alias key, target key): the first pair at a key decides. -/
def aliasMap : List (KKey × KKey) → KKey → KKey
  | [], k => k
  | p :: rest, k => if k = p.1 then p.2 else aliasMap rest k

/-- `a` is stored as an alias of `t`: a definition whose value is `t` at the definition's own
level parameters, which are a permutation of the positions, the target stored with the positions
as its parameters. -/
def AliasEntry (env : Env .anon) (a t : KKey) : Prop :=
  ∃ (lps : List LevelParam) (ty : KExpr) (hint : ReducibilityHint) (ci : ConstantInfo .anon),
    env.find? a = some (.defnInfo ⟨a, lps, ty⟩ (.const t (lps.map .param)) hint) ∧
    lps.Perm (List.range lps.length) ∧
    env.find? t = some ci ∧
    ci.toConstantVal.levelParams = List.range lps.length

/-- A proof that `a` is stored as an alias of `t`, if it is. -/
def aliasEntryCheck (env : Env .anon) (a t : KKey) : Except String (PLift (AliasEntry env a t)) :=
  match hfa : env.find? a with
  | some (.defnInfo cv v hint) =>
    match hft : env.find? t with
    | some ci =>
      if hc : cv.name = a ∧ v = .const t (cv.levelParams.map .param) ∧
          cv.levelParams.Perm (List.range cv.levelParams.length) ∧
          ci.toConstantVal.levelParams = List.range cv.levelParams.length then
        .ok ⟨⟨cv.levelParams, cv.type, hint, ci, by
          obtain ⟨h1, h2, -, -⟩ := hc
          subst h1
          subst h2
          exact hfa, hc.2.2.1, hft, hc.2.2.2⟩⟩
      else .error "alias table: an entry is not the alias of its target"
    | none => .error "alias table: a target is not stored"
  | _ => .error "alias table: an alias key does not store a definition"

/-- A proof that every pair of the table is a stored alias, if each is. -/
def aliasTableCheck (env : Env .anon) :
    (tbl : List (KKey × KKey)) → Except String (PLift (∀ p ∈ tbl, AliasEntry env p.1 p.2))
  | [] => .ok ⟨fun _ hp => nomatch hp⟩
  | p :: rest =>
    match aliasEntryCheck env p.1 p.2, aliasTableCheck env rest with
    | .ok h1, .ok h2 => .ok ⟨fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h1.down
        · exact h2.down q hq⟩
    | .error e, _ => .error e
    | _, .error e => .error e

/-- **The renaming of a table of stored aliases moves stored aliases only.** -/
theorem aliasEnv_of_table {env : Env .anon} :
    ∀ {tbl : List (KKey × KKey)}, (∀ p ∈ tbl, AliasEntry env p.1 p.2) →
      AliasEnv env (aliasMap tbl)
  | [], _ => fun k hk => absurd rfl hk
  | p :: rest, hall => by
    intro k hk
    by_cases hkp : k = p.1
    · subst hkp
      have hm : aliasMap (p :: rest) p.1 = p.2 := ite_eq_left rfl
      rw [hm]
      exact hall p List.mem_cons_self
    · have hm : aliasMap (p :: rest) k = aliasMap rest k :=
        ite_eq_right hkp
      rw [hm] at hk ⊢
      exact aliasEnv_of_table (fun q hq => hall q (List.mem_cons_of_mem _ hq)) k hk

/-! ## Leaf annotations the renaming fixes, decided -/

/-- Whether the renaming fixes every leaf annotation of `e`. -/
def leavesFixedB (h : KKey → KKey) (e : KExpr) : Bool :=
  e.fvarLeaves.all fun l => decide (l.2.renameConsts h = l.2)

theorem leavesFixed_of_b {h : KKey → KKey} {e : KExpr} (hb : leavesFixedB h e = true) :
    LeavesFixed h e := by
  intro l hl
  exact of_decide_eq_true (List.all_eq_true.mp hb l hl)

/-! ## The block renaming -/

/-- The block renaming of the record: a block name goes to its model key. -/
abbrev blockRen (bn : List KKey) : KKey → KKey :=
  fun n => if bn.contains n then auxKey n .model else n

/-- The recursors of a block, as the record selects them. -/
abbrev recsOf (block : List (ConstantInfo .anon)) : List (ConstantInfo .anon) :=
  block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)

/-- The other members of a block, as the record selects them. -/
abbrev nonrecsOf (block : List (ConstantInfo .anon)) : List (ConstantInfo .anon) :=
  block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)

/-! ## The judgements, by runs on the renamed positional subjects -/

/-- A conversion of the record's package, by a run on the two terms renamed by the block renaming
and the alias renaming, at positions. -/
def defeqRen (fuel : Nat) (f h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) (a b : KExpr) :
    Except String (PLift ((renameJ f (famJ h)).defeq env d a b)) :=
  match hrun : Ix.Kernel.isDefEqCore .verified env fuel d
      (posOf ps ((a.renameConsts f).renameConsts h))
      (posOf ps ((b.renameConsts f).renameConsts h)) with
  | Except.ok true =>
    .ok ⟨famJ_defeq_of_pos hA hperm (Ix.Kernel.Rules.isDefEqCore_bridge hrun)⟩
  | _ => .error lbl

/-- A conversion of the family package, by a run on the two terms renamed by the alias renaming,
at positions. -/
def defeqFam (fuel : Nat) (h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) (a b : KExpr) :
    Except String (PLift ((famJ h).defeq env d a b)) :=
  match hrun : Ix.Kernel.isDefEqCore .verified env fuel d
      (posOf ps (a.renameConsts h)) (posOf ps (b.renameConsts h)) with
  | Except.ok true =>
    .ok ⟨⟨hA, ps, hperm, Ix.Kernel.Rules.isDefEqCore_bridge hrun⟩⟩
  | _ => .error lbl

/-- A typing of the family package for a subject whose leaf annotations the alias renaming fixes,
by a run on the subject renamed by the alias renaming, at positions. -/
def inferFam (fuel : Nat) (h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) (e : KExpr) :
    Except String {t : KExpr // (famJ h).infer env d e t} :=
  if hfix : leavesFixedB h e = true then
    match hrun : Ix.Kernel.inferTypeCore .verified env fuel d (posOf ps (e.renameConsts h)) with
    | Except.ok tpos =>
      .ok ⟨invPosOf ps tpos, famJ_infer_of_pos hA hperm (leavesFixed_of_b hfix)
        (Ix.Kernel.Rules.inferTypeCore_bridge hrun)⟩
    | Except.error _ => .error lbl
  else .error (lbl ++ " (a leaf annotation is moved by the alias renaming)")

/-- The same typing, as one of the record's package. -/
def inferRenOpen (fuel : Nat) (f h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) (e : KExpr) :
    Except String {t : KExpr // (renameJ f (famJ h)).infer env d e t} :=
  match inferFam fuel h lbl hA hperm d e with
  | .ok r => .ok ⟨r.1, Or.inl r.2⟩
  | .error msg => .error msg

/-- A typing of the record's package for a closed subject, by a run on the subject renamed by the
block renaming and the alias renaming, at positions. -/
def inferRenClosed (fuel : Nat) (f h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) (e : KExpr) :
    Except String {t : KExpr // (renameJ f (famJ h)).infer env d e t} :=
  if hc : e.hasFvar = false then
    match hrun : Ix.Kernel.inferTypeCore .verified env fuel d
        (posOf ps ((e.renameConsts f).renameConsts h)) with
    | Except.ok tpos =>
      .ok ⟨invPosOf ps tpos, famJ_infer_closed_of_pos hA hperm hc
        (Ix.Kernel.Rules.inferTypeCore_bridge hrun)⟩
    | Except.error _ => .error lbl
  else .error (lbl ++ " (the subject is not closed)")

/-- A closed subject of the record's package is typed at a type that reduces to a sort. -/
def inferSortRenClosed (fuel : Nat) (f h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (e : KExpr) :
    Except String (PLift (∃ stype u, (renameJ f (famJ h)).infer env 0 e stype ∧
      (renameJ f (famJ h)).sort env 0 stype u)) :=
  if hc : e.hasFvar = false then
    match hrun : Ix.Kernel.inferTypeCore .verified env fuel 0
        (posOf ps ((e.renameConsts f).renameConsts h)) with
    | Except.ok tpos =>
      match hw : Ix.Kernel.whnf .verified env fuel 0 tpos with
      | Except.ok (.sort upos) =>
        .ok ⟨⟨invPosOf ps tpos, invPosLevel ps upos,
          famJ_infer_closed_of_pos hA hperm hc (Ix.Kernel.Rules.inferTypeCore_bridge hrun),
          famJ_sort_of_pos hperm (Ix.Kernel.Rules.whnf_bridge hw)⟩⟩
      | _ => .error (lbl ++ " (the inferred type does not reduce to a sort)")
    | Except.error _ => .error lbl
  else .error (lbl ++ " (the subject is not closed)")

/-- Pairwise conversion of two spines in the record's package. -/
def defeqListCheck (fuel : Nat) (f h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) :
    (as bs : List KExpr) → Except String (PLift (DefEqListJ (renameJ f (famJ h)) env d as bs))
  | [], [] => .ok ⟨trivial⟩
  | a :: as, b :: bs =>
    match defeqRen fuel f h lbl hA hperm d a b, defeqListCheck fuel f h lbl hA hperm d as bs with
    | .ok p, .ok q => .ok ⟨⟨p.down, q.down⟩⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | _, _ => .error (lbl ++ " (lengths differ)")

/-- Pairwise typing of a spine against expected types in the family package. -/
def typedListCheck (fuel : Nat) (h : KKey → KKey) (lbl : String) {env : Env .anon}
    (hA : AliasEnv env h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (d : Nat) :
    (as bs : List KExpr) → Except String (PLift (TypedListJ (famJ h) env d as bs))
  | [], [] => .ok ⟨trivial⟩
  | a :: as, b :: bs =>
    match inferFam fuel h lbl hA hperm d a with
    | .error e => .error e
    | .ok r =>
      match defeqFam fuel h lbl hA hperm d r.1 b, typedListCheck fuel h lbl hA hperm d as bs with
      | .ok p, .ok q => .ok ⟨⟨⟨r.1, r.2, p.down⟩, q.down⟩⟩
      | .error e, _ => .error e
      | _, .error e => .error e
  | _, _ => .error (lbl ++ " (lengths differ)")

/-- The rule walks' comparisons and the two sides' typings, in the record's package. -/
def iotaRunsCheck (fuel : Nat) (f h : KKey → KKey) {envSelf : Env .anon}
    (hA : AliasEnv envSelf h) {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (depth : Nat) (idxL idxR domL domR preL preR lamL lamR : List KExpr)
    (rhsS rhsApplied alphaS lhsS : KExpr) :
    Except String (PLift (IotaRunsJ (renameJ f (famJ h)) envSelf depth idxL idxR domL domR
      preL preR lamL lamR rhsS rhsApplied alphaS lhsS)) := do
  let p1 ← defeqListCheck fuel f h "rule: index arguments" hA hperm depth idxL idxR
  let p2 ← defeqListCheck fuel f h "rule: field domains" hA hperm depth domL domR
  let p3 ← defeqListCheck fuel f h "rule: prefix domains" hA hperm depth preL preR
  let p4 ← defeqListCheck fuel f h "rule: lambda domains" hA hperm depth lamL lamR
  let p5 ← defeqRen fuel f h "rule: right side against the applied rule" hA hperm depth
    rhsS rhsApplied
  let tl ← inferRenOpen fuel f h "rule: typing of the left side" hA hperm depth lhsS
  let q1 ← defeqRen fuel f h "rule: type of the left side" hA hperm depth tl.1 alphaS
  let tr ← inferRenOpen fuel f h "rule: typing of the right side" hA hperm depth rhsS
  let q2 ← defeqRen fuel f h "rule: type of the right side" hA hperm depth tr.1 alphaS
  return ⟨⟨p1.down, p2.down, p3.down, p4.down, p5.down, ⟨tl.1, tl.2, q1.down⟩,
    ⟨tr.1, tr.2, q2.down⟩⟩⟩

/-! ## The members -/

/-- A member's front door, in the record's package. `type'` is the annotated type. -/
def constantValCheck (fuel : Nat) (f h : KKey → KKey) {env : Env .anon} (hA : AliasEnv env h)
    (cv : ConstantVal .anon) (type' : KExpr) :
    Except String (PLift (ConstantValRunJ (renameJ f (famJ h)) env cv type')) := do
  let hperm ← guardP "member: level parameters are not a permutation of the positions"
    (cv.levelParams.Perm (List.range cv.levelParams.length))
  let h1 ← guardP "member: the name is stored" ((env.find? cv.name).isNone = true)
  let h2 ← guardP "member: reserved name"
    (Ix.Kernel.reservedBasisNames.contains cv.name = false)
  let h3 ← guardP "member: projection-function name" (cv.name.isProjFnShape = false)
  let h4 ← guardP "member: level parameters repeat" (LevelParam.nodup cv.levelParams = true)
  let h5 ← guardP "member: loose bound variable" (cv.type.looseBVarsBounded 0 = true)
  let h6 ← guardP "member: free variable" (cv.type.hasFvar = false)
  let h7 ← guardP "member: annotation"
    ((IxVM.Consistency.annotatesCheck 4096 type' cv.type).isSome = true)
  let h8 ← guardP "member: level parameters of the type"
    (type'.allLevelParamsDefined cv.levelParams = true)
  let h9 ← guardP "member: constants of the type" (type'.constsResolve env = true)
  let hs ← inferSortRenClosed fuel f h "member: the type is not a type" hA hperm.down type'
  return ⟨⟨h1.down, h2.down, h3.down, h4.down, h5.down, h6.down,
    annot_of_annotates (IxVM.Consistency.annotates_of_check h7.down) h6.down h5.down 0,
    h8.down, h9.down, hs.down⟩⟩

/-- A member's record: its front door, and its alias at the model key with the member's own level
parameters and the renamed annotated type. -/
def memberValCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) {env' : Env .anon}
    (hA : AliasEnv env' h) (cv : ConstantVal .anon) (type' : KExpr) :
    Except String (PLift (MemberValRunJ (renameJ (blockRen bn) (famJ h)) env' bn cv
      ⟨cv.name, cv.levelParams, type'⟩)) := do
  let hcv ← constantValCheck fuel (blockRen bn) h hA cv type'
  let hsuf ← guardP "member: model-suffixed name" (cv.name.isModelSuffix = false)
  match hfind : env'.find? (auxKey cv.name .model) with
  | some (.defnInfo cvm mval hint) =>
    let hl ← guardP "member: level parameters of the alias" (cvm.levelParams = cv.levelParams)
    let ht ← guardP "member: type of the alias"
      ((type'.renameConsts (blockRen bn) == cvm.type) = true)
    return ⟨⟨type', hcv.down, rfl, hsuf.down, cvm, mval, hint, hfind, hl.down, ht.down⟩⟩
  | _ => .error "member: no alias definition at the model key"

/-- The non-recursor members, in order, with the environment they leave. -/
def membersCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) :
    (env' : Env .anon) → AliasEnv env' h → (ms : List (ConstantInfo .anon)) →
    (tys : List KExpr) →
    Except String {envM : Env .anon // AliasEnv envM h ∧
      IndMembersRunJ (renameJ (blockRen bn) (famJ h)) bn {} env' ms envM}
  | env', hA, [], _ => .ok ⟨env', hA, rfl⟩
  | env', hA, .indInfo cv caps₀ :: rest, ty' :: tys => do
    let hm ← memberValCheck fuel h bn hA cv ty'
    let hfr ← guardP "member: the name is stored" ((env'.find? cv.name).isNone = true)
    have hfresh : env'.find? (ConstantInfo.indInfo (md := .anon) ⟨cv.name, cv.levelParams, ty'⟩
        {}).name = none := Option.isNone_iff_eq_none.mp hfr.down
    let r ← membersCheck fuel h bn
      ⟨.indInfo ⟨cv.name, cv.levelParams, ty'⟩ {} :: env'.consts⟩
      (hA.mono (fun hk => Ix.Kernel.Env.find?_cons_of_fresh hfresh hk)) rest tys
    return ⟨r.1, r.2.1, ⟨⟨cv.name, cv.levelParams, ty'⟩, hm.down, r.2.2⟩⟩
  | env', hA, .ctorInfo cv nP nF :: rest, ty' :: tys => do
    let hm ← memberValCheck fuel h bn hA cv ty'
    let hfr ← guardP "member: the name is stored" ((env'.find? cv.name).isNone = true)
    have hfresh : env'.find? (ConstantInfo.ctorInfo (md := .anon) ⟨cv.name, cv.levelParams, ty'⟩
        nP nF).name = none := Option.isNone_iff_eq_none.mp hfr.down
    let r ← membersCheck fuel h bn
      ⟨.ctorInfo ⟨cv.name, cv.levelParams, ty'⟩ nP nF :: env'.consts⟩
      (hA.mono (fun hk => Ix.Kernel.Env.find?_cons_of_fresh hfresh hk)) rest tys
    return ⟨r.1, r.2.1, ⟨⟨cv.name, cv.levelParams, ty'⟩, hm.down, r.2.2⟩⟩
  | _, _, _, _ => .error "members: not a type or a constructor, or no annotated type given"

/-- The recursors, provisioned without rules, with the environment they leave and the list the
install fold walks. -/
def provisionCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) :
    (envAcc : Env .anon) → AliasEnv envAcc h → (recs : List (ConstantInfo .anon)) →
    (tys : List KExpr) →
    Except String
      {out : Env .anon × List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)) //
        AliasEnv out.1 h ∧
        ProvisionRecsRunJ (renameJ (blockRen bn) (famJ h)) bn envAcc recs out.1 out.2}
  | envAcc, hA, [], _ => .ok ⟨(envAcc, []), hA, rfl, rfl⟩
  | envAcc, hA, .recInfo cv mI rP rules :: rest, ty' :: tys => do
    let hm ← memberValCheck fuel h bn hA cv ty'
    let hfr ← guardP "recursor: the name is stored" ((envAcc.find? cv.name).isNone = true)
    have hfresh : envAcc.find? (ConstantInfo.recInfo (md := .anon)
        ⟨cv.name, cv.levelParams, ty'⟩ mI rP []).name = none :=
      Option.isNone_iff_eq_none.mp hfr.down
    let r ← provisionCheck fuel h bn
      ⟨.recInfo ⟨cv.name, cv.levelParams, ty'⟩ mI rP [] :: envAcc.consts⟩
      (hA.mono (fun hk => Ix.Kernel.Env.find?_cons_of_fresh hfresh hk)) rest tys
    return ⟨(r.1.1, (⟨cv.name, cv.levelParams, ty'⟩, mI, rP, rules) :: r.1.2), r.2.1,
      ⟨⟨cv.name, cv.levelParams, ty'⟩, mI, rP, rules, r.1.2, rfl, hm.down, r.2.2, rfl⟩⟩
  | _, _, _, _ => .error "recursors: not a recursor, or no annotated type given"

/-! ## The rules -/

/-- A canonical rule's theorem record, in the record's package: the theorem copy at the `iota`
key, its literal shape, and the rule's judgements. -/
def iotaThmCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) (env' : Env .anon)
    {envSelf : Env .anon} (hA : AliasEnv envSelf h) (cvName : KKey) {lps : List LevelParam}
    (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr) (mI rP j : Nat)
    (r : RecRule .anon) (cvj : ConstantVal .anon) (cnP cnF : Nat) (rhsA : KExpr) :
    Except String (PLift (IotaThmRunJ (renameJ (blockRen bn) (famJ h)) env' envSelf
      (blockRen bn) cvName lps tyA mI rP j r cvj cnP cnF rhsA)) := do
  let cvt ← getSome "rule: no theorem copy at the iota key"
    (env'.findCV? (auxKey (auxKey cvName .model) (.iota j)))
  let hl ← guardP "rule: level parameters of the theorem copy" (cvt.1.levelParams = lps)
  let op ← getSome "rule: telescope of the theorem copy"
    (openPisAtFvars (rP + cnF) cvt.1.type 0)
  let he ← guardP "rule: the theorem copy is not an equation"
    (isEqHead op.1.2.getAppFn = true)
  let h3 ← guardP "rule: the equation's arity" (op.1.2.getAppArgs.length = 3)
  let g1 ← guardP "rule: head of the left side"
    (((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (blockRen bn cvName) (lps.map .param)) = true)
  let g2 ← guardP "rule: arity of the left side"
    ((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length = mI + 1)
  let g3 ← guardP "rule: prefix of the left side"
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).take rP == op.1.1.take rP) = true)
  let g4 ← guardP "rule: major premise of the left side"
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).getLastD (.bvar 0) ==
      Expr.mkAppN (.const (blockRen bn r.ctor) (cvj.levelParams.map .param))
        (op.1.1.take cnP ++ op.1.1.drop rP)) = true)
  let g5 ← guardP "rule: constructor telescope" (Expr.ctorTeleOk cvj.type (cnP + cnF) = true)
  let k1 ← getSome "rule: constructor telescope at the major premise"
    (Expr.instPisAt (op.1.1.take cnP ++ op.1.1.drop rP) (cvj.type.renameConsts (blockRen bn)))
  let k2 ← guardP "rule: constructor indices" (k1.1.2.getAppArgs.length = cnP + (mI - rP))
  let k3 ← getSome "rule: recursor telescope at the statement's prefix"
    (Expr.instPisAt (op.1.1.take rP) (tyA.renameConsts (blockRen bn)))
  let k4 ← getSome "rule: recursor telescope" (openPisAtFvars rP tyA 0)
  let k5 ← getSome "rule: constructor telescope at the recursor's parameters"
    (Expr.instPisAt (k4.1.1.take cnP) cvj.type)
  let k6 ← getSome "rule: constructor fields" (openPisAtFvars cnF k5.1.2 rP)
  let k7 ← getSome "rule: lambdas of the right-hand side"
    (Expr.instLamsAt (k4.1.1 ++ k6.1.1) rhsA)
  let k8 ← defeqListCheck fuel (blockRen bn) h "rule: parameter domains" hA hperm (rP + cnF)
    ((k4.1.1.take cnP).map Expr.fvarTypeD) k5.1.1
  let k9 ← iotaRunsCheck fuel (blockRen bn) h hA hperm (rP + cnF)
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).drop rP).take (mI - rP))
    (k1.1.2.getAppArgs.drop cnP)
    ((op.1.1.drop rP).map Expr.fvarTypeD) (k1.1.1.drop cnP)
    ((op.1.1.take rP).map Expr.fvarTypeD) k3.1.1
    ((k4.1.1 ++ k6.1.1).map Expr.fvarTypeD) k7.1.1
    (op.1.2.getAppArgs.getD 2 (.bvar 0)) (Expr.mkAppN (rhsA.renameConsts (blockRen bn)) op.1.1)
    (op.1.2.getAppArgs.getD 0 (.bvar 0)) (op.1.2.getAppArgs.getD 1 (.bvar 0))
  return ⟨⟨cvt.1, op.1.1, op.1.2, cvt.2, hl.down, op.2, he.down, h3.down,
    g1.down, g2.down, g3.down, g4.down, g5.down,
    k1.1.1, k1.1.2, k3.1.1, k4.1.1, k5.1.1, k5.1.2, k6.1.1, k4.1.2, k6.1.2, k3.1.2,
    k1.2, k2.down, k3.2, k4.2, k5.2, k6.2, k7.1.1, k7.1.2, k7.2, k8.down, k9.down⟩⟩

/-- A nested rule's theorem record over the family package: the theorem copy at the `iota` key,
its literal shape with the renamed pins, the renamed pins' typings, and the rule's judgements. -/
def iotaThmNCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) (env' : Env .anon)
    {envSelf : Env .anon} (hA : AliasEnv envSelf h) (cvName : KKey) {lps : List LevelParam}
    (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr) (mI rP j : Nat)
    (r : RecRule .anon) (cvj : ConstantVal .anon) (cnP cnF : Nat) (rhsA : KExpr)
    (lvls : List Level) (pins : List KExpr)
    (hshape : nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j = some (lvls, pins)) :
    Except String (PLift (IotaThmNRenRunJ (famJ h) env' envSelf (blockRen bn) cvName lps tyA
      mI rP j r cvj cnP cnF rhsA lvls pins)) := do
  let cvt ← getSome "nested rule: no theorem copy at the iota key"
    (env'.findCV? (auxKey (auxKey cvName .model) (.iota j)))
  let hl ← guardP "nested rule: level parameters of the theorem copy" (cvt.1.levelParams = lps)
  let op ← getSome "nested rule: telescope of the theorem copy"
    (openPisAtFvars (rP + cnF) cvt.1.type 0)
  let he ← guardP "nested rule: the theorem copy is not an equation"
    (isEqHead op.1.2.getAppFn = true)
  let h3 ← guardP "nested rule: the equation's arity" (op.1.2.getAppArgs.length = 3)
  let g1 ← guardP "nested rule: head of the left side"
    (((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (blockRen bn cvName) (lps.map .param)) = true)
  let g2 ← guardP "nested rule: arity of the left side"
    ((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length = mI + 1)
  let g3 ← guardP "nested rule: prefix of the left side"
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).take rP == op.1.1.take rP) = true)
  let g4 ← guardP "nested rule: major premise of the left side"
    (((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).getLastD (.bvar 0) =
      Expr.mkAppN (.const (blockRen bn r.ctor) lvls)
        ((pins.map fun p =>
          Expr.instSpine (op.1.1.take rP) (rP - 1) (p.renameConsts (blockRen bn))) ++
          op.1.1.drop rP))
  let g5 ← guardP "nested rule: constructor telescope"
    (Expr.ctorTeleOk cvj.type (cnP + cnF) = true)
  let k1 ← getSome "nested rule: constructor telescope at the major premise"
    (Expr.instPisAt
      ((pins.map fun p =>
        Expr.instSpine (op.1.1.take rP) (rP - 1) (p.renameConsts (blockRen bn))) ++
        op.1.1.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts (blockRen bn)))
  let k2 ← guardP "nested rule: constructor indices"
    (k1.1.2.getAppArgs.length = cnP + (mI - rP))
  let k3 ← getSome "nested rule: recursor telescope at the statement's prefix"
    (Expr.instPisAt (op.1.1.take rP) (tyA.renameConsts (blockRen bn)))
  let k4 ← getSome "nested rule: recursor telescope" (openPisAtFvars rP tyA 0)
  let k5 ← getSome "nested rule: constructor telescope at the pins"
    (Expr.instPisAt (pins.map fun p => Expr.instSpine (k4.1.1.take rP) (rP - 1) p)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls))
  let k6 ← getSome "nested rule: constructor fields" (openPisAtFvars cnF k5.1.2 rP)
  let k6c ← guardP "nested rule: residual arity"
    ((k6.1.2.getAppArgs.length == cnP + (mI - rP)) = true)
  let k7 ← getSome "nested rule: lambdas of the right-hand side"
    (Expr.instLamsAt (k4.1.1 ++ k6.1.1) rhsA)
  let k8 ← typedListCheck fuel h "nested rule: typing of a renamed pin" hA hperm (rP + cnF)
    ((pins.map fun p => Expr.instSpine (k4.1.1.take rP) (rP - 1) p).map
      (·.renameConsts (blockRen bn)))
    (k5.1.1.map (·.renameConsts (blockRen bn)))
  let k9 ← iotaRunsCheck fuel (blockRen bn) h hA hperm (rP + cnF)
    ((((op.1.2.getAppArgs.getD 1 (.bvar 0)).getAppArgs).drop rP).take (mI - rP))
    (k1.1.2.getAppArgs.drop cnP)
    ((op.1.1.drop rP).map Expr.fvarTypeD) (k1.1.1.drop cnP)
    ((op.1.1.take rP).map Expr.fvarTypeD) k3.1.1
    ((k4.1.1 ++ k6.1.1).map Expr.fvarTypeD) k7.1.1
    (op.1.2.getAppArgs.getD 2 (.bvar 0)) (Expr.mkAppN (rhsA.renameConsts (blockRen bn)) op.1.1)
    (op.1.2.getAppArgs.getD 0 (.bvar 0)) (op.1.2.getAppArgs.getD 1 (.bvar 0))
  return ⟨⟨hshape, cvt.1, op.1.1, op.1.2, cvt.2, hl.down, op.2, he.down, h3.down,
    g1.down, g2.down, g3.down, Expr.ErasedEq.of_eq g4.down,
    (by
      obtain ⟨bs, body, c, us, hs, hb⟩ := Expr.ctorTeleOk_head g5.down
      exact ⟨bs, body, hs, by first | (rw [hb]; done) | (rw [hb]; rfl) | simp [hb]⟩),
    k1.1.1, k1.1.2, k3.1.1, k3.1.2, k4.1.1, k4.1.2, k5.1.1, k5.1.2, k6.1.1, k6.1.2,
    k1.2, k2.down, k3.2, k4.2, ⟨k5.2, k6.2, k6c.down⟩,
    k7.1.1, k7.1.2, k7.2, k8.down, k9.down⟩⟩

/-- One rule: its right-hand side annotated and typed, its fire mode decided as the record
decides it, and the matching theorem record. `rhsA` is the annotated right-hand side. -/
def ruleCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) (env' : Env .anon)
    {envSelf : Env .anon} (hA : AliasEnv envSelf h) (cvName : KKey) {lps : List LevelParam}
    (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr) (mI rP j : Nat)
    (r : RecRule .anon) (rhsA : KExpr) :
    Except String {r' : RecRule .anon // IotaRuleRenRunJ (famJ h) env' envSelf (blockRen bn)
      cvName lps tyA mI rP j r r'} :=
  match hctor : env'.find? r.ctor with
  | some (.ctorInfo cvj cnP cnF) => do
    let h2 ← guardP "rule: field count" (r.nfields = cnF)
    let h3 ← guardP "rule: loose bound variable" (r.rhs.looseBVarsBounded 0 = true)
    let h4 ← guardP "rule: free variable" (r.rhs.hasFvar = false)
    let h5 ← guardP "rule: annotation"
      ((IxVM.Consistency.annotatesCheck 4096 rhsA r.rhs).isSome = true)
    let h6 ← guardP "rule: level parameters" (rhsA.allLevelParamsDefined lps = true)
    let h7 ← guardP "rule: constants" (rhsA.constsResolve envSelf = true)
    let h8 ← guardP "rule: lambdas" ((rhsA.stripLams (rP + cnF)).isSome = true)
    let ht' ← inferRenClosed fuel (blockRen bn) h "rule: typing of the right-hand side" hA
      hperm 0 rhsA
    if hp : Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true then do
      let ht ← iotaThmCheck fuel h bn env' hA cvName hperm tyA mI rP j r cvj cnP cnF rhsA
      return ⟨recRuleBits env'.find? cvName
          { r with rhs := rhsA, ctorParams := cnP, fire := .plain, paramsBlind := false },
        ⟨cvj, cnP, cnF, rhsA, hctor, h2.down, h3.down, h4.down,
          annot_of_annotates (IxVM.Consistency.annotates_of_check h5.down) h4.down h3.down 0,
          h6.down, h7.down, h8.down, ⟨ht'.1, ht'.2⟩, .plain, rfl,
          Or.inl ⟨hp, rfl, ht.down⟩⟩⟩
    else
      match hshape : nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j with
      | some (lvls, pins) => do
        let ht ← iotaThmNCheck fuel h bn env' hA cvName hperm tyA mI rP j r cvj cnP cnF rhsA
          lvls pins hshape
        return ⟨recRuleBits env'.find? cvName
            { r with rhs := rhsA, ctorParams := cnP, fire := .nested lvls pins,
                     paramsBlind := false },
          ⟨cvj, cnP, cnF, rhsA, hctor, h2.down, h3.down, h4.down,
            annot_of_annotates (IxVM.Consistency.annotates_of_check h5.down) h4.down h3.down 0,
            h6.down, h7.down, h8.down, ⟨ht'.1, ht'.2⟩, .nested lvls pins, rfl,
            Or.inr ⟨Bool.eq_false_of_ne_true hp, lvls, pins, rfl, ht.down⟩⟩⟩
      | none => .error "rule: neither canonical nor of the certified nested shape"
  | _ => .error "rule: the constructor is not stored"

/-- The rules of one recursor, in order. `rhss` are the annotated right-hand sides. -/
def rulesCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) (env' : Env .anon)
    {envSelf : Env .anon} (hA : AliasEnv envSelf h) (cvName : KKey) {lps : List LevelParam}
    (hperm : lps.Perm (List.range lps.length)) (tyA : KExpr) (mI rP : Nat) :
    (j : Nat) → (rules : List (RecRule .anon)) → (rhss : List KExpr) →
    Except String {out : List (RecRule .anon) // IotaRulesRenRunJ (famJ h) env' envSelf
      (blockRen bn) cvName lps tyA mI rP j rules out}
  | _, [], _ => .ok ⟨[], rfl⟩
  | j, r :: rest, rhsA :: rhss => do
    let hr ← ruleCheck fuel h bn env' hA cvName hperm tyA mI rP j r rhsA
    let hrest ← rulesCheck fuel h bn env' hA cvName hperm tyA mI rP (j + 1) rest rhss
    return ⟨hr.1 :: hrest.1, ⟨hr.1, hrest.1, hr.2, hrest.2, rfl⟩⟩
  | _, _, _ => .error "rules: no annotated right-hand side given"

/-- The install fold of the recursors, with the environment it leaves. `rhsss` are the annotated
right-hand sides, per recursor. -/
def recsFoldCheck (fuel : Nat) (h : KKey → KKey) (bn : List KKey) (envBase : Env .anon)
    {envSelf : Env .anon} (hA : AliasEnv envSelf h) :
    (acc : Env .anon) →
    (checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))) →
    (rhsss : List (List KExpr)) →
    Except String {out : Env .anon //
      IndRecsFoldRenRunJ (famJ h) bn envBase envSelf acc checked out}
  | acc, [], _ => .ok ⟨acc, rfl⟩
  | acc, c :: rest, rhss :: rhsss => do
    let hperm ← guardP "recursor: level parameters are not a permutation of the positions"
      (c.1.levelParams.Perm (List.range c.1.levelParams.length))
    let hr ← rulesCheck fuel h bn envBase hA c.1.name hperm.down c.1.type c.2.1 c.2.2.1 0
      c.2.2.2 rhss
    let ho ← recsFoldCheck fuel h bn envBase hA
      ⟨.recInfo c.1 c.2.1 c.2.2.1 hr.1 :: acc.consts⟩ rest rhsss
    return ⟨ho.1, ⟨hr.1, hr.2, ho.2⟩⟩
  | _, _, _ => .error "recursors: no annotated right-hand sides given"

/-! ## The block -/

/-- **A proof of the renamed record of a block over the family package, if the search finds
one**, with the environment after the block.

* `tbl`: the alias table (alias key, target key); the package is `famJ (aliasMap tbl)`;
* `envAl`: the environment the block is installed in, the aliases stored;
* `block`: the block as read;
* `tysM`, `tysR`: the annotated types of the non-recursor members and of the recursors, in the
  block's order;
* `rhsss`: the annotated right-hand sides of each recursor's rules. -/
def famRecordCheck (fuel : Nat) (tbl : List (KKey × KKey)) (envAl : Env .anon)
    (block : List (ConstantInfo .anon)) (tysM tysR : List KExpr) (rhsss : List (List KExpr)) :
    Except String {env₂ : Env .anon // AliasEnv envAl (aliasMap tbl) ∧
      DeclIndRenRunJ (famJ (aliasMap tbl)) envAl block env₂} := do
  let hT ← aliasTableCheck envAl tbl
  have hA : AliasEnv envAl (aliasMap tbl) := aliasEnv_of_table hT.down
  let hsplit ← guardP "block: a recursor precedes another member"
    (block = nonrecsOf block ++ recsOf block)
  let mem ← membersCheck fuel (aliasMap tbl) (block.map (·.name)) envAl hA (nonrecsOf block) tysM
  if hnil : (recsOf block).isEmpty = true then
    return ⟨mem.1, hA, by
      set_option smartUnfolding false in
      exact ⟨hsplit.down, mem.1, mem.2.2, Or.inl ⟨List.isEmpty_iff.mp hnil, rfl⟩⟩⟩
  else do
    let heq ← guardP "block: the pinned equality is not stored"
      (mem.1.find? eqName = some eqA)
    let prov ← provisionCheck fuel (aliasMap tbl) (block.map (·.name)) mem.1 mem.2.1
      (recsOf block) tysR
    let fold ← recsFoldCheck fuel (aliasMap tbl) (block.map (·.name)) mem.1 prov.2.1 mem.1
      prov.1.2 rhsss
    return ⟨fold.1, hA, by
      set_option smartUnfolding false in
      exact ⟨hsplit.down, mem.1, mem.2.2,
        Or.inr ⟨fun he => hnil (List.isEmpty_iff.mpr he), heq.down, prov.1.1, prov.1.2, prov.2.2,
          fold.2⟩⟩⟩

/-- **A successful check is a proof**: the alias renaming moves stored aliases only, and the
renamed record holds over the family package, at the environment the check returns. -/
theorem famRecord_of_check {fuel : Nat} {tbl : List (KKey × KKey)} {envAl : Env .anon}
    {block : List (ConstantInfo .anon)} {tysM tysR : List KExpr} {rhsss : List (List KExpr)}
    (hc : isOk (famRecordCheck fuel tbl envAl block tysM tysR rhsss) = true) :
    ∃ env₂ : Env .anon, AliasEnv envAl (aliasMap tbl) ∧
      DeclIndRenRunJ (famJ (aliasMap tbl)) envAl block env₂ := by
  cases hr : famRecordCheck fuel tbl envAl block tysM tysR rhsss with
  | error e =>
    rw [hr] at hc
    have hc' : false = true := hc
    cases hc'
  | ok r => exact ⟨r.1, r.2⟩

/-! ## The members as stored -/

/-- A proof that each listed constant is stored in `env₂` under its name as a constant that
stores it (`IxVM.Consistency.StoredAs`: the annotated type, and a recursor's rules with their
annotated right-hand sides), if the search finds one. -/
def storedBlockCheck (env₂ : Env .anon) :
    (blk : List (ConstantInfo .anon)) →
    Except String (PLift (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧
      IxVM.Consistency.StoredAs c ci))
  | [] => .ok ⟨fun _ hc => nomatch hc⟩
  | ci :: rest => do
    let c ← getSome "block: a member is not stored after the block" (env₂.find? ci.name)
    match IxVM.Consistency.storedAsCheck 4096 c.1 ci with
    | some p =>
      let ih ← storedBlockCheck env₂ rest
      return ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c.1, c.2, p.down⟩
        · exact ih.down x hx⟩
    | none => .error "block: a stored member does not store its reading"

/-- **The family step's record, searched**: the renamed record over the family package
(`famRecordCheck`), and each member of the block stored after it as a constant that stores the
member as read. -/
def famStepCheck (fuel : Nat) (tbl : List (KKey × KKey)) (envAl : Env .anon)
    (block : List (ConstantInfo .anon)) (tysM tysR : List KExpr) (rhsss : List (List KExpr)) :
    Except String {env₂ : Env .anon // AliasEnv envAl (aliasMap tbl) ∧
      DeclIndRenRunJ (famJ (aliasMap tbl)) envAl block env₂ ∧
      ∀ ci ∈ block, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci} := do
  let r ← famRecordCheck fuel tbl envAl block tysM tysR rhsss
  let s ← storedBlockCheck r.1 block
  return ⟨r.1, r.2.1, r.2.2, s.down⟩

/-- **A successful check of the step is a proof.** -/
theorem famStep_of_check {fuel : Nat} {tbl : List (KKey × KKey)} {envAl : Env .anon}
    {block : List (ConstantInfo .anon)} {tysM tysR : List KExpr} {rhsss : List (List KExpr)}
    (hc : isOk (famStepCheck fuel tbl envAl block tysM tysR rhsss) = true) :
    ∃ env₂ : Env .anon, AliasEnv envAl (aliasMap tbl) ∧
      DeclIndRenRunJ (famJ (aliasMap tbl)) envAl block env₂ ∧
      ∀ ci ∈ block, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci := by
  cases hr : famStepCheck fuel tbl envAl block tysM tysR rhsss with
  | error e =>
    rw [hr] at hc
    have hc' : false = true := hc
    cases hc'
  | ok r => exact ⟨r.1, r.2⟩

/-! ## The alias group -/

/-- A derived key that is not a projection table's. -/
theorem auxKey_ne_projTableName {n : KKey} {d : Derived} (hd : d ≠ .projTable) (T : KKey) :
    auxKey n d ≠ Ix.Kernel.projTableName T := by
  intro heq
  have heq' : Key.aux n d = Key.aux T Derived.projTable := heq
  exact hd (Key.aux.inj heq').2

/-- **A proof that the listed definitions are an alias group over `env` for the table's
renaming, if the search finds one.** The table lists the aliases in the list's order, newest
first: each a definition at a derived key by its target at the definition's own level
parameters. -/
def aliasGroupCheck (env : Env .anon) :
    (tbl : List (KKey × KKey)) → (as : List (ConstantInfo .anon)) →
    Except String (PLift (AliasGroup env (aliasMap tbl) as))
  | [], [] => .ok ⟨AliasGroup.nil (fun _ => rfl)⟩
  | (.aux n d, tgt) :: tbl, .defnInfo ⟨k, lps, ty⟩ v hint :: as => do
    let ih ← aliasGroupCheck env tbl as
    let hshape ← guardP "alias group: an alias is not the definition of its key by its target"
      (k = auxKey n d ∧ v = .const tgt (lps.map .param) ∧ hint = .abbrev)
    let hperm ← guardP "alias group: level parameters are not a permutation of the positions"
      (lps.Perm (List.range lps.length))
    let hfr ← guardP "alias group: an alias key is stored"
      (((⟨as ++ env.consts⟩ : Env .anon).find? (auxKey n d)).isNone = true)
    let hd ← guardP "alias group: a projection table's key" (d ≠ .projTable)
    let src ← getSome "alias group: a target is not stored"
      ((⟨as ++ env.consts⟩ : Env .anon).find? tgt)
    let hlps ← guardP "alias group: a target's level parameters are not the positions"
      (src.1.toConstantVal.levelParams = List.range lps.length)
    let htf ← guardP "alias group: free variable in an alias type" (ty.hasFvar = false)
    let htp ← guardP "alias group: level parameters of an alias type"
      (ty.allLevelParamsDefined lps = true)
    let htr ← guardP "alias group: constants of an alias type"
      (ty.constsResolve (⟨as ++ env.consts⟩ : Env .anon) = true)
    let htb ← guardP "alias group: loose bound variable in an alias type"
      (ty.looseBVarsBounded 0 = true)
    let hty ← guardP "alias group: an alias type is not its target's type at positions"
      (posOf lps (ty.renameConsts (aliasMap tbl)) = src.1.toConstantVal.type)
    return ⟨by
      obtain ⟨hk, hv, hh⟩ := hshape.down
      subst hk
      subst hv
      subst hh
      exact AliasGroup.cons ih.down hperm.down (Option.isNone_iff_eq_none.mp hfr.down)
        (auxKey_ne_projTableName hd.down) src.2 hlps.down htf.down htp.down htr.down htb.down
        hty.down (ite_eq_left rfl) (fun x hx => ite_eq_right hx)⟩
  | _, _ => .error "alias group: the table and the aliases do not correspond"

/-- **A successful check is an alias group.** -/
theorem aliasGroup_of_check {env : Env .anon} {tbl : List (KKey × KKey)}
    {as : List (ConstantInfo .anon)} (hc : isOk (aliasGroupCheck env tbl as) = true) :
    AliasGroup env (aliasMap tbl) as := by
  cases hr : aliasGroupCheck env tbl as with
  | error e =>
    rw [hr] at hc
    have hc' : false = true := hc
    cases hc'
  | ok r => exact r.down

end IxVM.Refinement.Decl.FamilyAlias
