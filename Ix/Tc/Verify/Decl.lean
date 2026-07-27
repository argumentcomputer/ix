import Ix.Tc.Verify.World
import Ix.Tc.Verify.Level
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Raw, pending, and trusted declarations

This is the additive G1b boundary between a catalogued declaration and a
Theory declaration.  The distinction is deliberately sharp:

* `RawExprRel` is syntax-directed.  In particular, it has no typing premises,
  no level-well-formedness premises, and no literal-well-formedness premises.
  Constant and projection heads must nevertheless resolve in the current
  trusted `VEnv`; that is representation linkage, not a typing judgment.
* `RawDeclRel` preserves the standalone declaration kind and translates its
  type and (for definitions) value.  This slice covers axioms and the three
  definition kinds.  Quotient and inductive-family declarations require an
  atomic multi-target relation and are intentionally left to the corresponding
  block milestone.
* `PendingDecl` contains raw correspondence, catalog closure, and absence of
  the target from both the trusted index and the Theory constant table.  It
  contains no `VConstant.WF`, `VDecl.WF`, or equivalent field.
* `TrustedDecl` is intentionally stronger: it records an actual `VDecl.WF`
  transition whose result is installed in the world's `VEnv`.

The adversarial fixture at the end of the file is a raw axiom whose type is
`Sort (param 0)` while the declaration has zero universe parameters.  It is
catalogued, pending, and raw-translatable, but cannot be a well-formed Theory
declaration in the empty trusted environment.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLevel VEnv VConstant VConstVal VDefVal VDecl)

/-- The abstract projection component used by raw expression translation.
It has the same shape as the projection parameter of `TrKExprS`, but carries
no closure or typing contract at the raw boundary. -/
abbrev RawProjRel :=
  List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop

namespace RawProjRel

/-- A projection relation suitable for fixtures containing no projections. -/
def none : RawProjRel := fun _ _ _ _ _ => False

end RawProjRel

/-- Raw syntax translation from `KExpr` to Theory `VExpr`.

Unlike `TrKExprS`, this relation is intentionally usable before the checker
has established typing.  Bound variables translate by index even when they
are loose; universe levels translate without a `VLevel.WF` premise; and the
structural application/binder cases carry no `HasType`/`IsType` evidence.

There is no `fvar` constructor because Theory `VExpr` has no free-variable
node.  A valid top-level declaration is closed, while an invalid declaration
with an `fvar` simply has no raw Theory representation. -/
inductive RawExprRel (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) : List VExpr → KExpr .anon → VExpr → Prop
  | var {ctx : List VExpr} {i : UInt64} {nm : Mode.anon.F Name}
      {md : ExprInfo .anon} :
    RawExprRel env nameOf trProj ctx (.var i nm md) (.bvar i.toNat)
  | sort {ctx : List VExpr} {u : KUniv .anon} {md : ExprInfo .anon} :
    RawExprRel env nameOf trProj ctx (.sort u md) (.sort u.toVLevel)
  | const {ctx : List VExpr} {id : KId .anon}
      {us : Array (KUniv .anon)} {md : ExprInfo .anon}
      {name : Lean.Name} {ci : VConstant} :
    nameOf id.addr = some name →
    env.constants name = some ci →
    us.size = ci.uvars →
    RawExprRel env nameOf trProj ctx (.const id us md)
      (.const name (us.toList.map KUniv.toVLevel))
  | app {ctx : List VExpr} {f a : KExpr .anon} {md : ExprInfo .anon}
      {f' a' : VExpr} :
    RawExprRel env nameOf trProj ctx f f' →
    RawExprRel env nameOf trProj ctx a a' →
    RawExprRel env nameOf trProj ctx (.app f a md) (.app f' a')
  | lam {ctx : List VExpr} {nm : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {ty body : KExpr .anon}
      {md : ExprInfo .anon} {ty' body' : VExpr} :
    RawExprRel env nameOf trProj ctx ty ty' →
    RawExprRel env nameOf trProj (ty' :: ctx) body body' →
    RawExprRel env nameOf trProj ctx (.lam nm bi ty body md)
      (.lam ty' body')
  | all {ctx : List VExpr} {nm : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {ty body : KExpr .anon}
      {md : ExprInfo .anon} {ty' body' : VExpr} :
    RawExprRel env nameOf trProj ctx ty ty' →
    RawExprRel env nameOf trProj (ty' :: ctx) body body' →
    RawExprRel env nameOf trProj ctx (.all nm bi ty body md)
      (.forallE ty' body')
  | letE {ctx : List VExpr} {nm : Mode.anon.F Name}
      {ty val body : KExpr .anon} {nonDep : Bool} {md : ExprInfo .anon}
      {ty' val' body' : VExpr} :
    RawExprRel env nameOf trProj ctx ty ty' →
    RawExprRel env nameOf trProj ctx val val' →
    RawExprRel env nameOf trProj (ty' :: ctx) body body' →
    RawExprRel env nameOf trProj ctx (.letE nm ty val body nonDep md)
      (body'.inst val')
  | prj {ctx : List VExpr} {id : KId .anon} {field : UInt64}
      {val : KExpr .anon} {md : ExprInfo .anon} {name : Lean.Name}
      {ci : VConstant} {val' out : VExpr} :
    nameOf id.addr = some name →
    env.constants name = some ci →
    RawExprRel env nameOf trProj ctx val val' →
    trProj ctx name field.toNat val' out →
    RawExprRel env nameOf trProj ctx (.prj id field val md) out
  | nat {ctx : List VExpr} {n : Nat} {blob : Address}
      {md : ExprInfo .anon} :
    RawExprRel env nameOf trProj ctx (.nat n blob md) (.natLit n)
  | str {ctx : List VExpr} {s : String} {blob : Address}
      {md : ExprInfo .anon} :
    RawExprRel env nameOf trProj ctx (.str s blob md)
      (.trLiteral (.strVal s))

namespace RawExprRel

/-- Raw translation is monotone in the trusted Theory environment.  The
proof transports only constant-table lookups; it never manufactures typing
evidence. -/
theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {ctx : List VExpr} {e : KExpr .anon} {e' : VExpr}
    (h : RawExprRel env nameOf trProj ctx e e') :
    RawExprRel env' nameOf trProj ctx e e' := by
  induction h with
  | var => exact .var
  | sort => exact .sort
  | const hname hlookup harity =>
    exact .const hname (henv.constants hlookup) harity
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihval ihbody => exact .letE ihty ihval ihbody
  | prj hname hlookup _ hproj ihval =>
    exact .prj hname (henv.constants hlookup) ihval hproj
  | nat => exact .nat
  | str => exact .str

end RawExprRel

/-! ## Declaration references and catalog closure -/

/-- A direct constant/projection reference occurring in an expression. -/
def KExpr.References (e : KExpr .anon) (id : KId .anon) : Prop :=
  match e with
  | .var .. | .fvar .. | .sort .. | .nat .. | .str .. => False
  | .const ref .. => ref = id
  | .app f a _ => f.References id ∨ a.References id
  | .lam _ _ ty body _ | .all _ _ ty body _ =>
    ty.References id ∨ body.References id
  | .letE _ ty val body _ _ =>
    ty.References id ∨ val.References id ∨ body.References id
  | .prj ref _ val _ => ref = id ∨ val.References id

/-- Every expression reference admitted by raw translation resolves in the
current Theory environment.  This is a lookup fact only, not a WF fact. -/
theorem RawExprRel.reference_resolved
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {ctx : List VExpr} {e : KExpr .anon}
    {e' : VExpr} (h : RawExprRel env nameOf trProj ctx e e')
    {id : KId .anon} (href : e.References id) :
    ∃ name ci, nameOf id.addr = some name ∧
      env.constants name = some ci := by
  induction h with
  | var => simp [KExpr.References] at href
  | sort => simp [KExpr.References] at href
  | const hname hlookup _ =>
    simp only [KExpr.References] at href
    subst id
    exact ⟨_, _, hname, hlookup⟩
  | app _ _ ihf iha =>
    rcases href with href | href
    · exact ihf href
    · exact iha href
  | lam _ _ ihty ihbody | all _ _ ihty ihbody =>
    rcases href with href | href
    · exact ihty href
    · exact ihbody href
  | letE _ _ _ ihty ihval ihbody =>
    rcases href with href | href | href
    · exact ihty href
    · exact ihval href
    · exact ihbody href
  | prj hname hlookup _ _ ihval =>
    rcases href with href | href
    · subst id
      exact ⟨_, _, hname, hlookup⟩
    · exact ihval href
  | nat => simp [KExpr.References] at href
  | str => simp [KExpr.References] at href

/-- A raw expression cannot refer to an id whose assigned Theory name is
absent from the environment. -/
theorem RawExprRel.not_references_of_absent
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {ctx : List VExpr} {e : KExpr .anon}
    {e' : VExpr} (h : RawExprRel env nameOf trProj ctx e e')
    {id : KId .anon} {name : Lean.Name}
    (hname : nameOf id.addr = some name)
    (habsent : env.constants name = none) :
    ¬e.References id := by
  intro href
  obtain ⟨name', ci, hname', hlookup⟩ := h.reference_resolved href
  rw [hname] at hname'
  cases hname'
  rw [habsent] at hlookup
  cases hlookup

/-- Every constant id consulted directly by declaration checking.  Besides
expression occurrences this includes block/member links and constructor ids. -/
def KConst.References (c : KConst .anon) (id : KId .anon) : Prop :=
  match c with
  | .defn (ty := ty) (val := val) (block := block) .. =>
    ty.References id ∨ val.References id ∨ block = id
  | .recr (block := block) (ty := ty) (rules := rules) .. =>
    block = id ∨ ty.References id ∨
      ∃ rule ∈ rules, rule.rhs.References id
  | .axio (ty := ty) .. | .quot (ty := ty) .. => ty.References id
  | .indc (block := block) (ty := ty) (ctors := ctors) .. =>
    block = id ∨ ty.References id ∨ id ∈ ctors
  | .ctor (induct := induct) (ty := ty) .. =>
    induct = id ∨ ty.References id

/-- Expression occurrences that could justify a target through Theory
constant lookup or unfolding.  Coordination links (`block`, `induct`, and
constructor arrays) remain in `KConst.References`, but are excluded here. -/
def KConst.ExprReferences (c : KConst .anon) (id : KId .anon) : Prop :=
  match c with
  | .defn (ty := ty) (val := val) .. =>
    ty.References id ∨ val.References id
  | .recr (ty := ty) (rules := rules) .. =>
    ty.References id ∨ ∃ rule ∈ rules, rule.rhs.References id
  | .axio (ty := ty) .. | .quot (ty := ty) .. |
    .indc (ty := ty) .. | .ctor (ty := ty) .. => ty.References id

/-- Every declaration reference is committed by the immutable catalog. -/
def CatalogClosed (catalog : Catalog) (c : KConst .anon) : Prop :=
  ∀ ⦃id⦄, c.References id → Catalog.Contains catalog id

/-! ## Raw declaration correspondence -/

/-- Preservation of Ix's three definition kinds in Theory declarations.
Theorems and opaque definitions are both non-unfolding Theory declarations;
ordinary definitions install their definitional equation. -/
inductive RawDefKindRel (ci : VDefVal) : Ix.DefKind → VDecl → Prop
  | defn : RawDefKindRel ci .defn (.def ci)
  | opaq : RawDefKindRel ci .opaq (.opaque ci)
  | thm : RawDefKindRel ci .thm (.opaque ci)

/-- Raw standalone declaration correspondence.

No constructor asks for `ci.WF` or `d.WF`.  Quotients and inductive-family
members cannot be represented soundly one constant at a time in
Lean4Lean.Theory, so they intentionally have no constructor here; their
future relation is atomic at the block level. -/
inductive RawDeclRel (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : RawProjRel) (id : KId .anon) : KConst .anon → VDecl → Prop
  | axiom {nm : Mode.anon.F Name} {lps : Mode.anon.F (Array Name)}
      {isUnsafe : Bool} {lvls : UInt64} {ty : KExpr .anon}
      {name : Lean.Name} {ty' : VExpr} :
    nameOf id.addr = some name →
    RawExprRel env nameOf trProj [] ty ty' →
    RawDeclRel env nameOf trProj id (.axio nm lps isUnsafe lvls ty)
      (.axiom { name, uvars := lvls.toNat, type := ty' })
  | defn {nm : Mode.anon.F Name} {lps : Mode.anon.F (Array Name)}
      {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {lvls : UInt64}
      {ty val : KExpr .anon} {leanAll : Mode.anon.F (Array (KId .anon))}
      {block : KId .anon} {name : Lean.Name} {ty' val' : VExpr}
      {d : VDecl} :
    nameOf id.addr = some name →
    RawExprRel env nameOf trProj [] ty ty' →
    RawExprRel env nameOf trProj [] val val' →
    RawDefKindRel
      { name, uvars := lvls.toNat, type := ty', value := val' } kind d →
    RawDeclRel env nameOf trProj id
      (.defn nm lps kind safety hints lvls ty val leanAll block) d

namespace RawDeclRel

/-- Every raw standalone declaration has the target's ghost name. -/
theorem nameOf {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {d : VDecl} (h : RawDeclRel env nameOf trProj id c d) :
    ∃ name, nameOf id.addr = some name := by
  cases h with
  | «axiom» hname _ => exact ⟨_, hname⟩
  | defn hname _ _ _ => exact ⟨_, hname⟩

/-- Raw declaration correspondence is monotone in the trusted `VEnv`. -/
theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {d : VDecl}
    (h : RawDeclRel env nameOf trProj id c d) :
    RawDeclRel env' nameOf trProj id c d := by
  cases h with
  | «axiom» hname hty => exact .axiom hname (hty.mono henv)
  | defn hname hty hval hkind =>
    exact .defn hname (hty.mono henv) (hval.mono henv) hkind

/-- A WF transition for a raw standalone declaration extends its input
environment.  Lean4Lean does not provide this for arbitrary `VDecl.WF`
(notably, its abstract `addInduct` has no extension theorem), but it follows
constructively for exactly the axiom/definition/opaque cases admitted by
`RawDeclRel`. -/
theorem wf_le {env env' : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {d : VDecl} (hraw : RawDeclRel env nameOf trProj id c d)
    (hwf : VDecl.WF env d env') : env ≤ env' := by
  cases hraw with
  | «axiom» =>
    cases hwf with
    | «axiom» _ hadd => exact Lean4Lean.VEnv.addConst_le hadd
  | defn _ _ _ hkind =>
    cases hkind with
    | defn =>
      cases hwf with
      | «def» _ hadd =>
        exact (Lean4Lean.VEnv.addConst_le hadd).trans
          Lean4Lean.VEnv.addDefEq_le
    | opaq | thm =>
      cases hwf with
      | «opaque» _ hadd => exact Lean4Lean.VEnv.addConst_le hadd

/-- Target freshness rules out self-reference in every expression translated
by a raw standalone declaration. -/
theorem no_self_expr_reference
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {d : VDecl} (h : RawDeclRel env nameOf trProj id c d)
    (hfresh : ∀ ⦃name⦄, nameOf id.addr = some name →
      env.constants name = none) :
    ¬c.ExprReferences id := by
  cases h with
  | «axiom» hname hty =>
    exact hty.not_references_of_absent hname (hfresh hname)
  | defn hname hty hval _ =>
    intro href
    rcases href with href | href
    · exact hty.not_references_of_absent hname (hfresh hname) href
    · exact hval.not_references_of_absent hname (hfresh hname) href

end RawDeclRel

/-! ## Pending versus trusted -/

/-- The target's Theory name is not already installed.  Together with an
untrusted target id, this blocks self-justification through constant lookup.
Warm-cache provenance and isolation are state-specific G4 obligations. -/
def TargetFresh (world : VerifyWorld) (id : KId .anon) : Prop :=
  ∀ ⦃name⦄, world.nameOf id.addr = some name →
    world.venv.constants name = none

/-- A declaration ready to be checked but not yet admitted.

The conjunct list is itself the important interface: there is no
declaration-WF premise. -/
def PendingDecl (trProj : RawProjRel) (world : VerifyWorld)
    (id : KId .anon) (d : VDecl) : Prop :=
  ∃ concrete,
    world.catalog id = some concrete ∧
    RawDeclRel world.venv world.nameOf trProj id concrete d ∧
    ¬world.trusted id ∧
    CatalogClosed world.catalog concrete ∧
    TargetFresh world id

/-- A declaration already admitted to the semantic world.  Unlike
`PendingDecl`, this status contains the actual Theory WF transition and proof
that its result is present in the world's `VEnv`. -/
def TrustedDecl (trProj : RawProjRel) (world : VerifyWorld)
    (id : KId .anon) (d : VDecl) : Prop :=
  ∃ concrete before after,
    world.catalog id = some concrete ∧
    RawDeclRel world.venv world.nameOf trProj id concrete d ∧
    world.trusted id ∧
    VDecl.WF before d after ∧
    after ≤ world.venv

/-- The single Theory constant installed by a standalone declaration. -/
inductive VDeclInstalls : VDecl → Lean.Name → VConstant → Prop
  | axiom (ci : VConstVal) :
    VDeclInstalls (.axiom ci) ci.name ci.toVConstant
  | defn (ci : VDefVal) :
    VDeclInstalls (.def ci) ci.name ci.toVConstant
  | opaque (ci : VDefVal) :
    VDeclInstalls (.opaque ci) ci.name ci.toVConstant

namespace TrustedDecl

/-- Trusted standalone lookup reaches the exact constant installed by its
recorded WF transition. -/
theorem lookup {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {d : VDecl} (h : TrustedDecl trProj world id d) :
    ∃ name ci,
      VDeclInstalls d name ci ∧
      world.nameOf id.addr = some name ∧
      world.venv.constants name = some ci := by
  obtain ⟨c, before, after, hcat, hraw, htrusted, hwf, hinstalled⟩ := h
  cases hraw with
  | «axiom» hname hty =>
    cases hwf with
    | «axiom» hconstant hadd =>
      exact ⟨_, _, .axiom _, hname,
        hinstalled.constants (Lean4Lean.VEnv.addConst_self hadd)⟩
  | defn hname hty hval hkind =>
    cases hkind with
    | defn =>
      cases hwf with
      | «def» hconstant hadd =>
        exact ⟨_, _, .defn _, hname,
          hinstalled.constants
            (Lean4Lean.VEnv.addDefEq_le.constants
              (Lean4Lean.VEnv.addConst_self hadd))⟩
    | opaq | thm =>
      cases hwf with
      | «opaque» hconstant hadd =>
        exact ⟨_, _, .opaque _, hname,
          hinstalled.constants (Lean4Lean.VEnv.addConst_self hadd)⟩

end TrustedDecl

namespace PendingDecl

theorem catalogued {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {d : VDecl} (h : PendingDecl trProj world id d) :
    Catalog.Contains world.catalog id := by
  obtain ⟨concrete, hcatalog, _⟩ := h
  exact ⟨concrete, hcatalog⟩

/-- A pending target has no constant-table entry under its assigned name. -/
theorem no_target_lookup {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {d : VDecl} (h : PendingDecl trProj world id d) :
    ∃ name, world.nameOf id.addr = some name ∧
      world.venv.constants name = none := by
  obtain ⟨_, _, hraw, _, _, hfresh⟩ := h
  obtain ⟨name, hname⟩ := hraw.nameOf
  exact ⟨name, hname, hfresh hname⟩

/-- The pending target cannot occur as a constant/projection head in its own
translated type or value.  This is the G1b self-unfolding barrier; cache
provenance and collision-mediated aliasing are addressed in G4/G3. -/
theorem no_self_expr_reference {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {d : VDecl} (h : PendingDecl trProj world id d) :
    ∃ concrete, world.catalog id = some concrete ∧
      ¬concrete.ExprReferences id := by
  obtain ⟨concrete, hcatalog, hraw, _, _, hfresh⟩ := h
  exact ⟨concrete, hcatalog, hraw.no_self_expr_reference hfresh⟩

/-- Pending and trusted status are disjoint without inspecting any typing
derivation. -/
theorem not_trustedDecl {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {d : VDecl} (h : PendingDecl trProj world id d) :
    ¬TrustedDecl trProj world id d := by
  obtain ⟨_, _, _, huntrusted, _, _⟩ := h
  rintro ⟨_, _, _, _, _, htrusted, _⟩
  exact huntrusted htrusted

end PendingDecl

/-! ## Adversarial non-WF pending fixture -/

namespace IllTypedPending

def targetName : Lean.Name := `Ix.Tc.Verify.illTypedPending

/-- A fixed 32-byte address keeps the fixture independent of the Blake3 FFI
and its generated `native_decide` axiom.  Address coherence is a separate
ingress obligation; only typing is under attack here. -/
def fixtureAddress : Address :=
  ⟨⟨Array.replicate 32 0⟩⟩

def targetId : KId .anon := ⟨fixtureAddress, ()⟩

def badLevel : KUniv .anon := .param 0 () fixtureAddress

def exprInfo : ExprInfo .anon where
  addr := fixtureAddress
  lbr := 0
  count0 := 0
  hasFVars := false
  mdata := ()
  metaAddr := ()

def badType : KExpr .anon := .sort badLevel exprInfo

def concrete : KConst .anon := .axio () () false 0 badType

def theoryConstant : VConstVal where
  name := targetName
  uvars := 0
  type := .sort (.param 0)

def theoryDecl : VDecl := .axiom theoryConstant

def catalog : Catalog := fun _ => some concrete

def world : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := fun _ => some targetName
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h

theorem raw : RawDeclRel world.venv world.nameOf RawProjRel.none
    targetId concrete theoryDecl := by
  apply RawDeclRel.axiom rfl
  exact RawExprRel.sort

theorem pending : PendingDecl RawProjRel.none world targetId theoryDecl := by
  refine ⟨concrete, rfl, raw, (fun h => h), ?_, ?_⟩
  · intro id href
    exact ⟨concrete, rfl⟩
  · intro name hname
    rfl

/-- The raw target type uses universe parameter zero while declaring zero
universe parameters, so the Theory constant is not well-formed. -/
theorem theoryConstant_not_wf :
    ¬theoryConstant.toVConstant.WF world.venv := by
  intro hwf
  have hlevel : (VLevel.param 0).WF 0 :=
    hwf.sort_inv Lean4Lean.VEnv.Ordered.empty
  exact (Nat.not_lt_zero 0) hlevel

/-- Consequently there is no Theory declaration-WF step from the pending
world. -/
theorem theoryDecl_not_wf :
    ¬∃ env', VDecl.WF world.venv theoryDecl env' := by
  rintro ⟨env', hwf⟩
  cases hwf with
  | «axiom» hconstant _ => exact theoryConstant_not_wf hconstant

/-- Machine-checked G1b acceptance witness: raw correspondence and pending
status are constructible for a declaration whose Theory WF judgment is
false. -/
theorem pending_but_not_wf :
    PendingDecl RawProjRel.none world targetId theoryDecl ∧
      ¬∃ env', VDecl.WF world.venv theoryDecl env' :=
  ⟨pending, theoryDecl_not_wf⟩

section Loaded

variable [LawfulBEq (KId .anon)] [LawfulHashable (KId .anon)]

/-- The same ill-typed pending target may already be present in the concrete
lazy-load cache; loading still does not confer trust or WF. -/
theorem loaded_pending_but_not_wf :
    LoadedAgrees world.catalog
        (({} : KEnv .anon).insert targetId concrete) ∧
      PendingDecl RawProjRel.none world targetId theoryDecl ∧
      ¬∃ env', VDecl.WF world.venv theoryDecl env' :=
  ⟨LoadedAgrees.insert (LoadedAgrees.empty catalog) rfl,
    pending, theoryDecl_not_wf⟩

end Loaded

end IllTypedPending

end Ix.Tc
