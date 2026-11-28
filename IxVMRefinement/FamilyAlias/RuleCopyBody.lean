import IxVMRefinement.FamilyAlias.TeleClose
import IxVMRefinement.Decl.NativeEnv
import IxCK.Kernel.Verify.Inductives.StructRec
import IxCK.Kernel.Verify.Inductives.FixRec
import IxCK.Kernel.Verify.InstSpine
import IxCK.Kernel.Verify.BridgeWfImp
import IxCK.Kernel.Model.Inductives.FixCtorReads
import IxCK.Kernel.Model.Open.Iota

/-! # The rule copy: its opening, and its renaming to the advice statement

The alias at an `iota` key of the family record is a copy of the rule's advice statement
(`ruleCopyOfAdvice`, `FamilyAlias/RuleCopy.lean`) whose major premise is built from the rule's
own data (`copyMajor`): the constructor's key under the block renaming at the major's levels,
applied to the rule's pins (renamed, lifted over the field binders) and to the field variables.
Nothing of the statement's own major premise is kept, so no inverse of the renaming to the
advice is used.

`ruleCopy_spec` is the general theorem. For a statement that opens, under `rP + cnF` binders,
to an equation whose left side is the recursor's model applied to arguments ending in the
constructor's model at the pins and the field variables (what the family check establishes of
an advice statement):

* the copy, with the aliases renamed to their targets, **is** the statement. So the alias
  group's equation holds, and the copy is closed, bounded, level-closed and resolves wherever
  the statement does, by transport along the renaming;
* the copy opens at the statement's own variables, to the statement's equation with the head
  of the left side and the major premise replaced: the literal conjuncts IxCK's rule record
  asks of the theorem at the `iota` key.

The passage between the opened statement and its closed form is `closeN_instSeq_closed`
(`FamilyAlias/TeleClose.lean`): the statement's body is recovered by closing the opened body,
piece by piece. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key Level LevelParam BinderMeta openPisAtFvars auxKey isEqHead eqName)

set_option linter.unusedVariables false

/-! ## The copy's major premise -/

/-- **The major premise of a rule copy**, under the statement's binders (the rule prefix, then
`cnF` fields): the constructor's key under the renaming `r` at the major's levels, applied to
the pins (renamed, lifted over the field binders) and to the field variables. -/
def copyMajor (r : KKey → KKey) (ctorKey : KKey) (lvls : List Level) (cnF : Nat)
    (pins : List KExpr) : KExpr :=
  Expr.mkAppN (.const (r ctorKey) lvls)
    ((pins.map fun p => (p.renameConsts r).liftLooseBVars cnF 0) ++
      (List.range cnF).map fun j => Expr.bvar (cnF - 1 - j))

/-- The major premise instantiated at prefix variables `pre` and field variables `xs`. -/
theorem instSeq_copyMajor (r : KKey → KKey) (ctorKey : KKey) (lvls : List Level)
    (pins pre xs : List KExpr)
    (hpre : ∀ a ∈ pre, a.looseBVarsBounded 0 = true)
    (hxs : ∀ a ∈ xs, a.looseBVarsBounded 0 = true)
    (hpins : ∀ p ∈ pins, p.looseBVarsBounded pre.length = true) :
    Expr.instSeq (pre ++ xs) (pre.length + xs.length - 1)
        (copyMajor r ctorKey lvls xs.length pins) =
      Expr.mkAppN (.const (r ctorKey) lvls)
        ((pins.map fun p => Expr.instSpine pre (pre.length - 1) (p.renameConsts r)) ++ xs) := by
  have hfield : ((List.range xs.length).map fun j => Expr.bvar (xs.length - 1 - j)).map
      (fun x => Expr.instSeq (pre ++ xs) (pre.length + xs.length - 1) x) = xs := by
    have h0 := Ix.Kernel.map_instSeq_fieldBvars xs xs.length hxs rfl
    rw [List.map_map] at h0 ⊢
    refine Eq.trans (List.map_congr_left (fun j hj => ?_)) h0
    have hj' : j < xs.length := List.mem_range.mp hj
    show Expr.instSeq (pre ++ xs) (pre.length + xs.length - 1) (Expr.bvar (xs.length - 1 - j)) =
      Expr.instSeq xs (xs.length - 1) (Expr.bvar (xs.length - 1 - j))
    rw [Ix.Kernel.Expr.instSeq_append,
      Ix.Kernel.instSeq_bvar_lt pre (pre.length + xs.length - 1) (xs.length - 1 - j) (by omega),
      show pre.length + xs.length - 1 - pre.length = xs.length - 1 by omega]
  have hpin : (pins.map fun p => (p.renameConsts r).liftLooseBVars xs.length 0).map
      (fun x => Expr.instSeq (pre ++ xs) (pre.length + xs.length - 1) x) =
      pins.map fun p => Expr.instSpine pre (pre.length - 1) (p.renameConsts r) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    show Expr.instSeq (pre ++ xs) (pre.length + xs.length - 1)
        ((p.renameConsts r).liftLooseBVars xs.length 0) =
      Expr.instSpine pre (pre.length - 1) (p.renameConsts r)
    rw [Ix.Kernel.Expr.instSpine_eq_instSeq]
    exact Ix.Kernel.Expr.instSeq_liftLooseBVars_prefix pre xs hpre
      ((looseBVarsBounded_renameConsts r pre.length p).trans (hpins p hp))
  unfold copyMajor
  rw [Ix.Kernel.Expr.instSeq_mkAppN, Ix.Kernel.Open.instSeq_const', List.map_append, hpin,
    hfield]

/-- The major premise instantiated at the variables of an opening of `rP + cnF` binders. -/
theorem instSeq_copyMajor_at (r : KKey → KKey) (ctorKey : KKey) (lvls : List Level)
    (pins : List KExpr) {fvs : List KExpr} {rP cnF : Nat} (hlen : fvs.length = rP + cnF)
    (hcl : ∀ a ∈ fvs, a.looseBVarsBounded 0 = true)
    (hpins : ∀ p ∈ pins, p.looseBVarsBounded rP = true) :
    Expr.instSeq fvs (rP + cnF - 1) (copyMajor r ctorKey lvls cnF pins) =
      Expr.mkAppN (.const (r ctorKey) lvls)
        ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts r)) ++
          fvs.drop rP) := by
  have h1 : (fvs.take rP).length = rP := by rw [List.length_take, hlen]; omega
  have h2 : (fvs.drop rP).length = cnF := by rw [List.length_drop, hlen]; omega
  have h := instSeq_copyMajor r ctorKey lvls pins (fvs.take rP) (fvs.drop rP)
    (fun a ha => hcl a (List.mem_of_mem_take ha)) (fun a ha => hcl a (List.mem_of_mem_drop ha))
    (fun p hp => by rw [h1]; exact hpins p hp)
  rw [List.take_append_drop, h1, h2] at h
  exact h

/-- The major premise has no free variable, and its loose bound variables are the statement's
binders. -/
theorem copyMajor_scope (r : KKey → KKey) (ctorKey : KKey) (lvls : List Level) {rP : Nat}
    (cnF : Nat) (pins : List KExpr)
    (hpins : ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true) :
    (copyMajor r ctorKey lvls cnF pins).hasFvar = false ∧
      (copyMajor r ctorKey lvls cnF pins).looseBVarsBounded (rP + cnF) = true := by
  unfold copyMajor
  refine ⟨hasFvar_mkAppN _ _ rfl (fun x hx => ?_),
    looseBVarsBounded_mkAppN _ _ _ rfl (fun x hx => ?_)⟩
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      rw [Ix.Kernel.hasFvar_liftLooseBVars, Ix.Kernel.hasFvar_renameConsts]
      exact (hpins p hp).1
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      rfl
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact Ix.Kernel.Expr.looseBVarsBounded_liftLooseBVars cnF _
        ((looseBVarsBounded_renameConsts r rP p).trans (hpins p hp).2)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hj' : j < cnF := List.mem_range.mp hj
      simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
      omega

/-- Renaming the major premise built at `r` gives the one built at `r'`, where the renaming
takes the constructor's key and each renamed pin there. -/
theorem copyMajor_renameConsts (r h r' : KKey → KKey) (ctorKey : KKey) (lvls : List Level)
    (cnF : Nat) (pins : List KExpr) (hctor : h (r ctorKey) = r' ctorKey)
    (hpins : ∀ p ∈ pins, (p.renameConsts r).renameConsts h = p.renameConsts r') :
    (copyMajor r ctorKey lvls cnF pins).renameConsts h = copyMajor r' ctorKey lvls cnF pins := by
  unfold copyMajor
  rw [IxVM.Refinement.Decl.mkAppN_renameConsts, List.map_append, List.map_map, List.map_map]
  have h1 : (Expr.const (r ctorKey) lvls : KExpr).renameConsts h = .const (r' ctorKey) lvls := by
    show Expr.const (h (r ctorKey)) lvls = _
    rw [hctor]
  rw [h1]
  refine congrArg (Expr.mkAppN _) (congrArg₂ (· ++ ·)
    (List.map_congr_left (fun p hp => ?_)) (List.map_congr_left (fun j _ => rfl)))
  show ((p.renameConsts r).liftLooseBVars cnF 0).renameConsts h =
    (p.renameConsts r').liftLooseBVars cnF 0
  rw [renameConsts_liftLooseBVars, hpins p hp]

/-! ## The copy of a statement, through its telescope -/

section Statement

variable {K : KKey} {lps : List LevelParam} {M : KExpr → KExpr}

/-- The copy keeps the statement's binders; its body is the copied equation. -/
theorem copyStatement_stripPis :
    ∀ (n : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {x y : KExpr},
      e.stripPis n = some (bs, .app x y) →
      (copyStatement K lps M e).stripPis n = some (bs, copyEquation K lps M (.app x y)) := by
  intro n
  induction n with
  | zero =>
    intro e bs x y hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rfl
  | succ n ih =>
    intro e bs x y hs
    match e, hs with
    | .forallE ty b mb, hs =>
      simp only [Expr.stripPis] at hs
      cases hs1 : b.stripPis n with
      | none => rw [hs1] at hs; exact nomatch hs
      | some p1 =>
        rw [hs1] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, hbody⟩ := hs
        have hs1' : b.stripPis n = some (p1.1, .app x y) := by rw [hs1, ← hbody]
        simp only [copyStatement, Expr.stripPis, ih hs1', Option.map_some]

/-- The copy, renamed, is the statement, where the renaming fixes the binder domains and takes
the copied equation to the statement's. -/
theorem copyStatement_renameConsts {h : KKey → KKey} :
    ∀ (n : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {x y : KExpr},
      e.stripPis n = some (bs, .app x y) →
      (∀ b ∈ bs, b.1.renameConsts h = b.1) →
      (copyEquation K lps M (.app x y)).renameConsts h = .app x y →
      (copyStatement K lps M e).renameConsts h = e := by
  intro n
  induction n with
  | zero =>
    intro e bs x y hs _ hbody
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact hbody
  | succ n ih =>
    intro e bs x y hs hdoms hbody
    match e, hs with
    | .forallE ty b mb, hs =>
      simp only [Expr.stripPis] at hs
      cases hs1 : b.stripPis n with
      | none => rw [hs1] at hs; exact nomatch hs
      | some p1 =>
        rw [hs1] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, hb⟩ := hs
        have hs1' : b.stripPis n = some (p1.1, .app x y) := by rw [hs1, ← hb]
        have hty : ty.renameConsts h = ty := hdoms (ty, mb) List.mem_cons_self
        have hrec := ih hs1' (fun b' hb' => hdoms b' (List.mem_cons_of_mem _ hb')) hbody
        show Expr.forallE (ty.renameConsts h) ((copyStatement K lps M b).renameConsts h) mb =
          Expr.forallE ty b mb
        rw [hty, hrec]

/-- The copy has the statement's binder domains. -/
theorem sameTele_copyStatement :
    ∀ (n : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {body : KExpr},
      e.stripPis n = some (bs, body) → SameTele n e (copyStatement K lps M e) := by
  intro n
  induction n with
  | zero => intro e bs body _; exact SameTele.zero _ _
  | succ n ih =>
    intro e bs body hs
    match e, hs with
    | .forallE ty b mb, hs =>
      simp only [Expr.stripPis] at hs
      cases hs1 : b.stripPis n with
      | none => rw [hs1] at hs; exact nomatch hs
      | some p1 =>
        show SameTele (n + 1) (.forallE ty b mb) (.forallE ty (copyStatement K lps M b) mb)
        exact SameTele.succ (ih (bs := p1.1) (body := p1.2) hs1)

end Statement

/-! ## The left side of the copied equation -/

/-- The copied left side, renamed, is the statement's: the head goes to the statement's head,
the arguments before the last are fixed, and the major premise goes to the statement's. -/
theorem copyLhs_renameConsts {h : KKey → KKey} {K k' : KKey} {ls : List Level}
    {args : List KExpr} {cm : KExpr} (hK : h K = k') (hne : args ≠ [])
    (hfix : args.map (fun x => x.renameConsts h) = args)
    (hlast : args.getLastD (.bvar 0) = cm.renameConsts h) :
    (Expr.mkAppN (.const K ls) (args.dropLast ++ [cm])).renameConsts h =
      Expr.mkAppN (.const k' ls) args := by
  rw [IxVM.Refinement.Decl.mkAppN_renameConsts]
  have h1 : (Expr.const K ls : KExpr).renameConsts h = .const k' ls := by
    show Expr.const (h K) ls = _
    rw [hK]
  rw [h1]
  refine congrArg (Expr.mkAppN _) ?_
  rw [List.map_append, map_dropLast_eq, hfix]
  show args.dropLast ++ [cm.renameConsts h] = args
  rw [← hlast]
  exact dropLast_append_getLastD args (.bvar 0) hne

/-- The copied left side, instantiated: the arguments before the last instantiate to the
opened statement's, the major premise to its own instance. -/
theorem copyLhs_instSeq {fvs : List KExpr} {t : Nat} {K : KKey} {ls : List Level}
    {args largs : List KExpr} {cm maj : KExpr}
    (hmap : args.map (fun x => Expr.instSeq fvs t x) = largs)
    (hm : Expr.instSeq fvs t cm = maj) :
    Expr.instSeq fvs t (Expr.mkAppN (.const K ls) (args.dropLast ++ [cm])) =
      Expr.mkAppN (.const K ls) (largs.dropLast ++ [maj]) := by
  rw [Ix.Kernel.Expr.instSeq_mkAppN, Ix.Kernel.Open.instSeq_const']
  refine congrArg (Expr.mkAppN _) ?_
  rw [List.map_append, map_dropLast_eq, hmap]
  show largs.dropLast ++ [Expr.instSeq fvs t cm] = largs.dropLast ++ [maj]
  rw [hm]

/-- The pinned equality's head. -/
theorem isEqHead_const {e : KExpr} (h : isEqHead e = true) : ∃ ℓ, e = .const eqName [ℓ] := by
  cases e with
  | const c ls =>
    match ls, h with
    | [ℓ], h => exact ⟨ℓ, by rw [eq_of_beq (show (c == eqName) = true from h)]⟩
    | [], h => exact nomatch h
    | _ :: _ :: _, h => exact nomatch h
  | _ => exact nomatch h

/-! ## The general theorem -/

/-- **The rule copy of an advice statement** (module docstring). `stmt` is the statement in the
recursor's level parameters; it opens under `rP + cnF` binders at the variables `fvs` to the
equation `tbody` of arguments `α`, `lhsS`, `rhsS`. `g` is the renaming to the advice, `f` the
renaming the copy is built at, `h` the renaming of the aliases to their targets.

The hypotheses on `h`: it fixes what `env` stores (`hfix`), it takes the recursor's model key
and the constructor's key under `f` to their advice keys (`hrec`, `hctor`), and it takes each
pin renamed by `f` to the pin renamed by `g` (`hpinsren`). -/
theorem ruleCopy_spec {env : Env .anon} {g f h : KKey → KKey} {recKey ctorKey : KKey}
    {lps : List LevelParam} {lvls : List Level} {pins : List KExpr} {mI rP cnF : Nat}
    {stmt tbody α lhsS rhsS : KExpr} {fvs : List KExpr}
    (hclosed : stmt.hasFvar = false) (hbnd : stmt.looseBVarsBounded 0 = true)
    (hres : stmt.constsResolve env = true)
    (hop : openPisAtFvars (rP + cnF) stmt 0 = some (fvs, tbody))
    (heq : isEqHead tbody.getAppFn = true)
    (htargs : tbody.getAppArgs = [α, lhsS, rhsS])
    (hfn : lhsS.getAppFn = .const (g recKey) (lps.map .param))
    (hlen : lhsS.getAppArgs.length = mI + 1)
    (hmajor : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (g ctorKey) lvls)
        ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts g)) ++
          fvs.drop rP))
    (hpins : ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true)
    (hfix : ∀ k, (env.find? k).isSome = true → h k = k)
    (hrec : h (auxKey recKey .model) = g recKey)
    (hctor : h (f ctorKey) = g ctorKey)
    (hpinsren : ∀ p ∈ pins, (p.renameConsts f).renameConsts h = p.renameConsts g) :
    (copyStatement (auxKey recKey .model) lps
        (fun _ => copyMajor f ctorKey lvls cnF pins) stmt).renameConsts h = stmt ∧
    openPisAtFvars (rP + cnF)
        (copyStatement (auxKey recKey .model) lps
          (fun _ => copyMajor f ctorKey lvls cnF pins) stmt) 0 =
      some (fvs, .app (.app (.app tbody.getAppFn α)
        (Expr.mkAppN (.const (auxKey recKey .model) (lps.map .param))
          (lhsS.getAppArgs.dropLast ++
            [Expr.mkAppN (.const (f ctorKey) lvls)
              ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
                fvs.drop rP)])))
        rhsS) := by
  -- the opening: its variables, the statement's body, and the body recovered by closing
  obtain ⟨-, -, hidx⟩ := openPisAtFvars_fvars_closed (rP + cnF) hbnd hop
  have hv : OpenVars 0 fvs := openVars_of_getElem fvs 0 hidx
  obtain ⟨bs, body₀, hstrip, hflen, -, -⟩ :=
    Ix.Kernel.Verify.openPisAtFvars_stripPis (rP + cnF) hop
  have htb : tbody = Expr.instSeq fvs (rP + cnF - 1) body₀ :=
    Ix.Kernel.Verify.openPisAtFvars_instSeq (rP + cnF) hop hstrip
  have hb0f : body₀.hasFvar = false :=
    (Ix.Kernel.stripPis_not_hasFvar (rP + cnF) hstrip hclosed).2
  have hb0b : body₀.looseBVarsBounded (rP + cnF) = true := by
    have hb := Ix.Kernel.Expr.stripPis_body_bounded (rP + cnF) hstrip hbnd
    rwa [Nat.zero_add] at hb
  obtain ⟨hdomsr, hb0r⟩ := Ix.Kernel.Expr.constsResolve_stripPis (rP + cnF) hstrip hres
  have hclose : Expr.closeN (rP + cnF) tbody 0 = body₀ := by
    have h1 := closeN_instSeq_closed hv hb0f (by rw [hflen]; exact hb0b)
    rw [hflen] at h1
    rw [htb]
    exact h1
  -- the opened statement is an equation of three arguments, and so is the closed body
  obtain ⟨ℓ, hhd⟩ := isEqHead_const heq
  have htbody : tbody = .app (.app (.app (.const eqName [ℓ]) α) lhsS) rhsS := by
    have h0 := Ix.Kernel.Expr.mkAppN_getApp tbody
    rw [hhd, htargs] at h0
    exact h0.symm
  have hb0 : body₀ = .app (.app (.app (.const eqName [ℓ]) (Expr.closeN (rP + cnF) α 0))
      (Expr.closeN (rP + cnF) lhsS 0)) (Expr.closeN (rP + cnF) rhsS 0) := by
    have h0 := hclose
    rw [htbody] at h0
    exact h0.symm
  -- the closed pieces instantiate back to the opened ones
  have hcomp : Expr.instSeq fvs (rP + cnF - 1) body₀ =
      .app (.app (.app (.const eqName [ℓ])
        (Expr.instSeq fvs (rP + cnF - 1) (Expr.closeN (rP + cnF) α 0)))
        (Expr.instSeq fvs (rP + cnF - 1) (Expr.closeN (rP + cnF) lhsS 0)))
        (Expr.instSeq fvs (rP + cnF - 1) (Expr.closeN (rP + cnF) rhsS 0)) := by
    rw [hb0, Ix.Kernel.Expr.instSeq_app, Ix.Kernel.Expr.instSeq_app,
      Ix.Kernel.Expr.instSeq_app, Ix.Kernel.Open.instSeq_const']
  have e0 := htbody.symm.trans (htb.trans hcomp)
  injection e0 with e1 hR
  injection e1 with e2 hL
  injection e2 with _ hA
  -- the left side: the recursor's model at its arguments, closed argument by argument
  have hne : lhsS.getAppArgs ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hlen]; omega)
  have hlhs : lhsS = Expr.mkAppN (.const (g recKey) (lps.map .param)) lhsS.getAppArgs := by
    have h0 := Ix.Kernel.Expr.mkAppN_getApp lhsS
    rw [hfn] at h0
    exact h0.symm
  have hl0 : Expr.closeN (rP + cnF) lhsS 0 =
      Expr.mkAppN (.const (g recKey) (lps.map .param))
        (lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0) := by
    have h0 := closeN_mkAppN (rP + cnF) 0 lhsS.getAppArgs (.const (g recKey) (lps.map .param))
    rw [← hlhs] at h0
    exact h0
  have hargs0 : (Expr.closeN (rP + cnF) lhsS 0).getAppArgs =
      lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0 := by
    rw [hl0, Ix.Kernel.Expr.getAppArgs_mkAppN]; rfl
  have hlargs : (lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0).map
      (fun x => Expr.instSeq fvs (rP + cnF - 1) x) = lhsS.getAppArgs := by
    have h0 := Ix.Kernel.Model.Expr.getAppArgs_instSeq_fvars fvs (rP + cnF - 1)
      (Expr.closeN (rP + cnF) lhsS 0) hv.fvars
    rw [← hL, hargs0] at h0
    exact h0.symm
  -- the copied equation
  have hceq : copyEquation (auxKey recKey .model) lps
      (fun _ => copyMajor f ctorKey lvls cnF pins) body₀ =
      .app (.app (.app (.const eqName [ℓ]) (Expr.closeN (rP + cnF) α 0))
        (Expr.mkAppN (.const (auxKey recKey .model) (lps.map .param))
          ((lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0).dropLast ++
            [copyMajor f ctorKey lvls cnF pins])))
        (Expr.closeN (rP + cnF) rhsS 0) := by
    rw [hb0]
    show Expr.app (.app (.app (.const eqName [ℓ]) (Expr.closeN (rP + cnF) α 0))
        (Expr.mkAppN (.const (auxKey recKey .model) (lps.map .param))
          ((Expr.closeN (rP + cnF) lhsS 0).getAppArgs.dropLast ++
            [copyMajor f ctorKey lvls cnF pins])))
        (Expr.closeN (rP + cnF) rhsS 0) = _
    rw [hargs0]
  have hstrip' : stmt.stripPis (rP + cnF) = some (bs, .app (.app (.app (.const eqName [ℓ])
      (Expr.closeN (rP + cnF) α 0)) (Expr.closeN (rP + cnF) lhsS 0))
      (Expr.closeN (rP + cnF) rhsS 0)) := by
    rw [← hb0]
    exact hstrip
  -- the major premise: instantiated, and the statement's own in closed form
  have hmajf := instSeq_copyMajor_at f ctorKey lvls pins hflen hv.bounded
    (fun p hp => (hpins p hp).2)
  have hmajg := instSeq_copyMajor_at g ctorKey lvls pins hflen hv.bounded
    (fun p hp => (hpins p hp).2)
  have hlast : (lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0).getLastD (.bvar 0) =
      (copyMajor f ctorKey lvls cnF pins).renameConsts h := by
    rw [copyMajor_renameConsts f h g ctorKey lvls cnF pins hctor hpinsren,
      getLastD_map (fun x => Expr.closeN (rP + cnF) x 0) (.bvar 0) (.bvar 0) lhsS.getAppArgs hne,
      hmajor, ← hmajg]
    have hsc := copyMajor_scope g ctorKey lvls cnF pins hpins
    have hcl := closeN_instSeq_closed hv hsc.1 (by rw [hflen]; exact hsc.2)
    rw [hflen] at hcl
    exact hcl
  refine ⟨?_, ?_⟩
  · -- renamed, the copy is the statement
    rw [hb0] at hb0r
    simp only [Expr.constsResolve, Bool.and_eq_true] at hb0r
    obtain ⟨⟨⟨hce, hαr⟩, hlr⟩, hrr⟩ := hb0r
    have hargsr := (constsResolve_getApp hlr).2
    rw [hargs0] at hargsr
    have hargsfix : (lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0).map
        (fun x => x.renameConsts h) =
        lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0 :=
      (List.map_congr_left (fun a ha =>
        (renameConsts_eq_self_of_constsResolve hfix a (hargsr a ha) :
          a.renameConsts h = id a))).trans (List.map_id _)
    have hne0 : (lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0) ≠ [] :=
      fun he => hne (List.map_eq_nil_iff.mp he)
    refine copyStatement_renameConsts (rP + cnF) hstrip'
      (fun b hb => renameConsts_eq_self_of_constsResolve hfix b.1 (hdomsr b hb)) ?_
    rw [← hb0, hceq, hb0]
    show Expr.app (.app (.app (.const (h eqName) [ℓ])
        ((Expr.closeN (rP + cnF) α 0).renameConsts h))
        ((Expr.mkAppN (.const (auxKey recKey .model) (lps.map .param))
          ((lhsS.getAppArgs.map fun x => Expr.closeN (rP + cnF) x 0).dropLast ++
            [copyMajor f ctorKey lvls cnF pins])).renameConsts h))
        ((Expr.closeN (rP + cnF) rhsS 0).renameConsts h) = _
    rw [hfix eqName hce, renameConsts_eq_self_of_constsResolve hfix _ hαr,
      renameConsts_eq_self_of_constsResolve hfix _ hrr,
      copyLhs_renameConsts hrec hne0 hargsfix hlast, hl0]
  · -- the copy opens at the statement's variables, to the copied equation instantiated
    obtain ⟨b', hopc⟩ := openPisAtFvars_sameTele (rP + cnF) 0
      (sameTele_copyStatement (K := auxKey recKey .model) (lps := lps)
        (M := fun _ => copyMajor f ctorKey lvls cnF pins) (rP + cnF) hstrip) hop
    have hcs := copyStatement_stripPis (K := auxKey recKey .model) (lps := lps)
      (M := fun _ => copyMajor f ctorKey lvls cnF pins) (rP + cnF) hstrip'
    have hb' := Ix.Kernel.Verify.openPisAtFvars_instSeq (rP + cnF) hopc hcs
    rw [← hb0, hceq, Ix.Kernel.Expr.instSeq_app, Ix.Kernel.Expr.instSeq_app,
      Ix.Kernel.Expr.instSeq_app, Ix.Kernel.Open.instSeq_const',
      copyLhs_instSeq hlargs hmajf, ← hA, ← hR] at hb'
    rw [hopc, hb', hhd]

end IxVM.Refinement.Decl.FamilyAlias
