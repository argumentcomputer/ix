import IxVMRefinement.FamilyAlias.RuleCopyBody
import IxVMRefinement.FamilyAlias.AliasGroupFacts
import IxVMRefinement.FamilyAlias.MembersFromScope
import IxC.Kernel.Verify.Denote.IndFrame
import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateSplitJ

/-! # The alias of a rule: admissible after the aliases before it

The alias at the `iota` key of rule `j` of a recursor is the definition, at the recursor's level
parameters, of the rule copy of the advice statement (`ruleAlias`), by the advice theorem. This
module shows it extends an alias group (`aliasGroup_ruleAlias`): the alias premise of the rule
copy.

* `RuleWitness`: a rule's facts (`RuleFacts`, `FamilyAlias/Facts.lean`) with their data named:
  the constructor, the counts, the major premise's levels and pins, the advice theorem.
* `majorShape_inv`: what the major premise's shape says of the recursor's type.
* `pins_renamed_resolve`: the pins, renamed to the advice, resolve where the recursor's type
  does: they are arguments of its major premise.
* `aliasGroup_ruleAlias`: from a rule's witness, the prefix's well-formedness, an alias group
  whose renaming sends each member's model key to the member's model, and the freshness of the
  rule's `iota` key, the group extended by the rule's alias. The copy's type equation is
  `ruleCopy_spec`'s first conclusion; its four scope conditions are transported along the
  renaming from the advice statement's (`scope_of_renamed`). -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta EnvWF
  Derived auxKey openPisAtFvars isEqHead)

set_option linter.unusedVariables false

/-! ## Keys -/

/-- The key of the alias of rule `j` of the recursor `R`. -/
abbrev iotaKey (R : KKey) (j : Nat) : KKey := auxKey (auxKey R .model) (.iota j)

theorem iotaKey_inj {R R' : KKey} {j j' : Nat} (h : iotaKey R j = iotaKey R' j') :
    R = R' ∧ j = j' := by
  have h1 := Key.aux.inj (h : Key.aux (Key.aux R Derived.model) (Derived.iota j) =
    Key.aux (Key.aux R' Derived.model) (Derived.iota j'))
  exact ⟨(Key.aux.inj h1.1).1, Derived.iota.inj h1.2⟩

theorem iotaKey_ne_model (R : KKey) (j : Nat) (k : KKey) : iotaKey R j ≠ auxKey k .model := by
  intro h
  have h1 := Key.aux.inj (h : Key.aux (Key.aux R Derived.model) (Derived.iota j) =
    Key.aux k Derived.model)
  exact nomatch h1.2

/-! ## A rule's facts, with their data named -/

/-- **A rule's facts with their data**: the conjuncts of `RuleFacts` at a named constructor
`cvj` with its counts, major premise levels `lvls` and pins `pins`, and advice theorem `cvt`. -/
structure RuleWitness (env : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (recKey : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (r : RecRule .anon) (rhsA : KExpr) (thm : KKey) (cvj : ConstantVal .anon) (cnP cnF : Nat)
    (lvls : List Level) (pins : List KExpr) (cvt : ConstantVal .anon) (vt tty₀ : KExpr) : Prop where
  ctor : RuleCtor env blk tys r.ctor cvj cnP cnF
  nfields : r.nfields = cnF
  bounded : r.rhs.looseBVarsBounded 0 = true
  closed : r.rhs.hasFvar = false
  annotated : IxVM.Consistency.Annotates rhsA r.rhs
  levels : rhsA.allLevelParamsDefined lps = true
  lams : (rhsA.stripLams (rP + cnF)).isSome = true
  typed : ∃ t', posRulesJ.infer env 0 (rhsA.renameConsts g) t'
  major : majorShape tyA mI rP cnP = some (lvls, pins)
  majorLevels : lvls.all (Level.allParamsDefined lps) = true
  pinsScoped : pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
    p.allLevelParamsDefined lps) = true
  ctorTele : Expr.ctorTeleOk cvj.type (cnP + cnF) = true
  thm : env.find? thm = some (.thmInfo cvt vt)
  thmLevels : cvt.levelParams.Perm (List.range lps.length)
  thmTypeLevels : tty₀.allLevelParamsDefined (List.range lps.length) = true
  thmTypeEq : ExprLvEq tty₀ (posOf cvt.levelParams cvt.type)
  statement : StatementFacts env g recKey lps tyA mI rP r.ctor rhsA cvj cnP cnF lvls pins
    (invPosOf lps tty₀)

/-- A rule's facts have such data. -/
theorem RuleFacts.witness {env : Env .anon} {g : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr} {recKey : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {r : RecRule .anon} {rhsA : KExpr} {thm : KKey}
    (h : RuleFacts env g blk tys recKey lps tyA mI rP r rhsA thm) :
    ∃ cvj cnP cnF lvls pins cvt vt tty₀,
      RuleWitness env g blk tys recKey lps tyA mI rP r rhsA thm cvj cnP cnF lvls pins cvt vt
        tty₀ := by
  obtain ⟨cvj, cnP, cnF, lvls, pins, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, cvt, vt,
    tty₀, h13, h14, h14b, h14c, h15⟩ := h
  exact ⟨cvj, cnP, cnF, lvls, pins, cvt, vt, tty₀,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h14b, h14c, h15⟩⟩

/-- The pins of a rule are closed and bounded by the rule prefix. -/
theorem RuleWitness.pins_scope {env : Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {recKey : KKey} {lps : List LevelParam}
    {tyA : KExpr} {mI rP : Nat} {r : RecRule .anon} {rhsA : KExpr} {thm : KKey}
    {cvj : ConstantVal .anon} {cnP cnF : Nat} {lvls : List Level} {pins : List KExpr}
    {cvt : ConstantVal .anon} {vt tty₀ : KExpr}
    (hw : RuleWitness env g blk tys recKey lps tyA mI rP r rhsA thm cvj cnP cnF lvls pins cvt vt
      tty₀) :
    ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true := by
  intro p hp
  have h0 := List.all_eq_true.mp hw.pinsScoped p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-! ## The major premise's shape -/

/-- **What the major premise's shape says of the recursor's type**: after `mI` binders the
domain is a constant at the levels, applied to the pins lifted over the index binders and to
the index variables. -/
theorem majorShape_inv {tyA : KExpr} {mI rP cnP : Nat} {lvls : List Level} {pins : List KExpr}
    (h : majorShape tyA mI rP cnP = some (lvls, pins)) :
    rP ≤ mI ∧ ∃ (bsT : List (KExpr × BinderMeta)) (dom body : KExpr) (mb : BinderMeta)
      (D : KKey),
      tyA.stripPis mI = some (bsT, .forallE dom body mb) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs.length = cnP + (mI - rP) ∧
      pins = (dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0) ∧
      dom.getAppArgs.take cnP = pins.map (Expr.liftLooseBVars (mI - rP) 0) ∧
      dom.getAppArgs.drop cnP =
        (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)) := by
  unfold majorShape at h
  by_cases hle : rP ≤ mI
  · rw [ite_eq_left hle] at h
    cases hstrip : tyA.stripPis mI with
    | none => rw [hstrip] at h; exact nomatch h
    | some p =>
      obtain ⟨bsT, e⟩ := p
      rw [hstrip] at h
      cases e with
      | forallE dom body mb =>
        dsimp only at h
        cases hfn : dom.getAppFn with
        | const D lvls' =>
          rw [hfn] at h
          dsimp only at h
          split at h
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hle, bsT, dom, body, mb, D, rfl, hfn, hcond.1, rfl, hcond.2.1, hcond.2.2⟩
          · exact nomatch h
        | _ => rw [hfn] at h; exact nomatch h
      | _ => exact nomatch h
  · rw [ite_eq_right hle] at h
    exact nomatch h

/-- **The pins, renamed to the advice, resolve where the recursor's renamed type does**: lifted
over the index binders they are arguments of its major premise. -/
theorem pins_renamed_resolve {env : Env .anon} {g : KKey → KKey} {tyA : KExpr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List KExpr}
    (hsh : majorShape tyA mI rP cnP = some (lvls, pins))
    (hres : (tyA.renameConsts g).constsResolve env = true) :
    ∀ p ∈ pins, (p.renameConsts g).constsResolve env = true := by
  obtain ⟨-, bsT, dom, body, mb, D, hstrip, -, -, -, htake, -⟩ := majorShape_inv hsh
  have hs := Ix.Kernel.Verify.stripPis_renameConsts (f := g) mI hstrip
  have hb := (Ix.Kernel.Expr.constsResolve_stripPis mI hs hres).2
  have hdom : (dom.renameConsts g).constsResolve env = true := by
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hb
    exact hb.1
  have hargs := (constsResolve_getApp hdom).2
  rw [getAppArgs_renameConsts] at hargs
  intro p hp
  have hmem : p.liftLooseBVars (mI - rP) 0 ∈ dom.getAppArgs := by
    have h1 : p.liftLooseBVars (mI - rP) 0 ∈ pins.map (Expr.liftLooseBVars (mI - rP) 0) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [← htake] at h1
    exact List.mem_of_mem_take h1
  have h2 : ((p.liftLooseBVars (mI - rP) 0).renameConsts g).constsResolve env = true :=
    hargs _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  rw [renameConsts_liftLooseBVars, Ix.Kernel.Semantics.constsResolve_liftLooseBVars] at h2
  exact h2

/-! ## The scope of a term, from the scope of its renaming -/

/-- **A term is closed, bounded and level-closed where its renaming is, and resolves in an
environment that stores every key whose image the first environment stores.** -/
theorem scope_of_renamed {env E : Env .anon} {h : KKey → KKey} {e s : KExpr}
    {lps : List LevelParam} (hren : e.renameConsts h = s)
    (hmono : ∀ k, (env.find? k).isSome = true → (E.find? k).isSome = true)
    (hE : ∀ k, (env.find? (h k)).isSome = true → (E.find? k).isSome = true)
    (hs : s.hasFvar = false ∧ s.looseBVarsBounded 0 = true ∧ s.constsResolve env = true ∧
      s.allLevelParamsDefined lps = true) :
    e.hasFvar = false ∧ e.allLevelParamsDefined lps = true ∧ e.constsResolve E = true ∧
      e.looseBVarsBounded 0 = true := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  subst hren
  exact ⟨(Ix.Kernel.hasFvar_renameConsts h e).symm.trans h1,
    (allLevelParamsDefined_renameConsts h lps e).symm.trans h4,
    constsResolve_of_renamed hE hmono e h3,
    (looseBVarsBounded_renameConsts h 0 e).symm.trans h2⟩

/-- **The advice statement of a stored theorem, in the recursor's level parameters, has the
theorem's scope.** -/
theorem statement_scope {env : Env .anon} {thm : KKey} {cvt : ConstantVal .anon} {vt tty₀ : KExpr}
    {lps : List LevelParam} (hwf : EnvWF env) (hfind : env.find? thm = some (.thmInfo cvt vt))
    (hperm : lps.Perm (List.range lps.length))
    (htl : tty₀.allLevelParamsDefined (List.range lps.length) = true)
    (heq : ExprLvEq tty₀ (posOf cvt.levelParams cvt.type)) :
    (invPosOf lps tty₀).hasFvar = false ∧
      (invPosOf lps tty₀).looseBVarsBounded 0 = true ∧
      (invPosOf lps tty₀).constsResolve env = true ∧
      (invPosOf lps tty₀).allLevelParamsDefined lps = true := by
  have hcw := hwf _ (List.mem_of_find?_eq_some hfind)
  have h1 : tty₀.hasFvar = false := by
    rw [exprLvEq_hasFvar heq]
    exact (hasFvar_instantiateLevelParams _ _ cvt.type).trans hcw.1
  have h3 : tty₀.constsResolve env = true := by
    rw [exprLvEq_constsResolve env heq, constsResolve_posOf]
    exact hcw.2.2.1
  have h4 : tty₀.looseBVarsBounded 0 = true := by
    rw [exprLvEq_looseBVarsBounded heq 0]
    exact (looseBVarsBounded_instantiateLevelParams _ _ 0 cvt.type).trans hcw.2.2.2.1
  refine ⟨(hasFvar_instantiateLevelParams _ _ tty₀).trans h1,
    (looseBVarsBounded_instantiateLevelParams _ _ 0 tty₀).trans h4, ?_,
    allLevelParamsDefined_of_posOf_perm hperm (by rw [posOf_invPosOf hperm]; exact htl)⟩
  have h5 : (invPosOf lps tty₀).constsResolve env = tty₀.constsResolve env :=
    Ix.Kernel.Expr.constsResolve_instantiateLevelParams ..
  rw [h5]
  exact h3

/-! ## The alias -/

/-- **The alias of rule `j` of the recursor `recKey`**: the definition at the `iota` key, at the
recursor's level parameters, of the rule copy of the advice statement `thmType` (as read, level
parameters at positions), by the advice theorem `thm`. Its type is
`ruleCopyOfAdvice lps recKey (fun _ => copyMajor …) thmType`. -/
def ruleAlias (bn : List KKey) (recKey : KKey) (lps : List LevelParam) (j : Nat)
    (ctorKey : KKey) (lvls : List Level) (cnF : Nat) (pins : List KExpr) (thm : KKey)
    (thmType : KExpr) : ConstantInfo .anon :=
  .defnInfo
    ⟨iotaKey recKey j, lps,
      copyStatement (auxKey recKey .model) lps
        (fun _ => copyMajor (blockRen bn) ctorKey lvls cnF pins) (invPosOf lps thmType)⟩
    (.const thm (lps.map .param)) .abbrev

theorem ruleAlias_type (bn : List KKey) (recKey : KKey) (lps : List LevelParam) (j : Nat)
    (ctorKey : KKey) (lvls : List Level) (cnF : Nat) (pins : List KExpr) (thm : KKey)
    (thmType : KExpr) :
    (ruleAlias bn recKey lps j ctorKey lvls cnF pins thm thmType).toConstantVal.type =
      ruleCopyOfAdvice lps recKey (fun _ => copyMajor (blockRen bn) ctorKey lvls cnF pins)
        thmType := rfl

/-- **The alias of a rule extends an alias group** (module docstring). `tbl` is the table of the
aliases `as` installed before it; its renaming sends each member's model key to the member's
model (`htarget`). -/
theorem aliasGroup_ruleAlias {env : Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {bn : List KKey} {recKey : KKey}
    {lps : List LevelParam} {tyA : KExpr} {mI rP j : Nat} {r : RecRule .anon} {rhsA : KExpr}
    {thm : KKey} {cvj : ConstantVal .anon} {cnP cnF : Nat} {lvls : List Level}
    {pins : List KExpr} {cvt : ConstantVal .anon} {vt tty₀ : KExpr}
    {as : List (ConstantInfo .anon)} {tbl : List (KKey × KKey)}
    (hw : RuleWitness env g blk tys recKey lps tyA mI rP r rhsA thm cvj cnP cnF lvls pins cvt vt
      tty₀)
    (hwf : EnvWF env) (hperm : lps.Perm (List.range lps.length))
    (hg : AliasGroup env (aliasMap tbl) as)
    (hfresh : (⟨as ++ env.consts⟩ : Env .anon).find? (iotaKey recKey j) = none)
    (hout : ∀ k, bn.contains k = false → g k = k)
    (htarget : ∀ k, bn.contains k = true → aliasMap tbl (auxKey k .model) = g k)
    (hrecbn : bn.contains recKey = true)
    (hblk : ∀ ci ∈ blk, bn.contains ci.name = true)
    (hpinsres : ∀ p ∈ pins, (p.renameConsts g).constsResolve env = true) :
    AliasGroup env (aliasMap ((iotaKey recKey j, thm) :: tbl))
      (ruleAlias bn recKey lps j r.ctor lvls cnF pins thm tty₀ :: as) := by
  obtain ⟨hclosed, hbnd, hres, hlvl⟩ :=
    statement_scope hwf hw.thm hperm hw.thmTypeLevels hw.thmTypeEq
  obtain ⟨fvs, tbody, hop, heq, h3, hrest⟩ := hw.statement
  dsimp only at hrest
  obtain ⟨hfn, hlen, -, hmajor, -⟩ := hrest
  have htargs := eq_three_of_length (Expr.bvar 0) tbody.getAppArgs h3
  have hfix := hg.fixes_prefix
  -- the constructor's key under the block renaming goes to its advice key
  have hctor : aliasMap tbl (blockRen bn r.ctor) = g r.ctor := by
    cases hb : bn.contains r.ctor with
    | true =>
      have hk : blockRen bn r.ctor = auxKey r.ctor .model := ite_eq_left hb
      rw [hk]
      exact htarget r.ctor hb
    | false =>
      have hk : blockRen bn r.ctor = r.ctor :=
        ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
      rw [hk, hout r.ctor hb]
      rcases hw.ctor with hc | ⟨i, cv, tyC, hbi, -, hname, -⟩
      · exact hfix r.ctor (by rw [hc]; rfl)
      · exfalso
        have hmem : (ConstantInfo.ctorInfo cv cnP cnF : ConstantInfo .anon) ∈ blk :=
          List.mem_of_getElem? hbi
        have hin : bn.contains cv.name = true := hblk _ hmem
        rw [hname, hb] at hin
        exact Bool.false_ne_true hin
  -- the copy, renamed, is the statement
  obtain ⟨hren, -⟩ := ruleCopy_spec (f := blockRen bn) hclosed hbnd hres hop heq htargs hfn hlen
    hmajor hw.pins_scope hfix (htarget recKey hrecbn) hctor
    (fun p hp => comp_of_renamed_resolves hout htarget hfix (hpinsres p hp))
  obtain ⟨c1, c2, c3, c4⟩ := scope_of_renamed (E := ⟨as ++ env.consts⟩) hren hg.stored_prefix
    hg.stored_of_target ⟨hclosed, hbnd, hres, hlvl⟩
  have htyEq : ExprLvEq
      (posOf lps
        ((copyStatement (auxKey recKey .model) lps
          (fun _ => copyMajor (blockRen bn) r.ctor lvls cnF pins) (invPosOf lps tty₀)).renameConsts
          (aliasMap tbl)))
      (posOf cvt.levelParams cvt.type) := by
    rw [hren, posOf_invPosOf hperm tty₀]
    exact hw.thmTypeEq
  exact AliasGroup.cons hg hperm hfresh (fun T => ne_projTableName_auxKey_iota _ T j)
    (hg.find_prefix thm _ hw.thm) hw.thmLevels c1 c2 c3 c4 htyEq
    (ite_eq_left rfl) (fun x hx => ite_eq_right hx)

end IxVM.Refinement.Decl.FamilyAlias
