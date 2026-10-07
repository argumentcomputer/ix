import Ix.CompileCert.Indexed
import Ix.CompileCert.AnnotationTrace

/-! # W+: changed constants (M5)

W (`SourceCorrespondence`) asks that the export of every Lean declaration be an
entry of the certified reader's output. A *changed* constant breaks that in
three ways (`plans/PLAN-proofs.md` §1, `docs/compiler-passes.md` §4–§5):

* a Lean **theorem** whose Ix proof term differs (theorem images, carried
  `eq_def`s, theorems proved through transported cliques);
* a Lean **recursor** of a changed block whose Ix row is a *definition*, its
  image (Def 3.4);
* a Lean **definition** whose Ix value is a different term (image-kind
  auxiliaries `casesOn`/`recOn`/`below`/`brecOn`/`.go` by Def 3.5, their users,
  transported clique members).

The faithfulness criterion for them is Lean's: the Ix constant has Lean's kind
and type, and Lean's defining equations hold. This module decides it with no
new trust, by **theorem rows checked by the certified checker**:

* `ThmStatementMatch`: a Lean theorem matches a reader theorem entry with its
  exported header (name, universe telescope, statement). The proof term is not
  compared: the checker verified the Ix proof, and proofs are irrelevant.
* `EquationMatch`: a Lean recursor (resp. definition) matches a reader
  *definition* entry with its exported header, and every defining equation of
  the Lean constant is the statement of a theorem row: for a recursor, one row
  per computation rule, stated by `leanRuleStatement` (a pure function of
  Lean's `RecursorVal` and the constructor's `ConstructorVal`, exported by the
  same `exportExpr` as everything else); for a definition, the row
  `@Eq.{ℓ} T c value` (exported type, constant and value; `ℓ` is the
  certifier's and the checker validated it when it typed the row) or the
  statement of Lean's own `c.eq_def`. The rows are reader entries of the
  admitted artifact or of **support** declarations (`thmDecl`, proof
  `Eq.refl`) that the certifier builds and the certified checker folds on top
  of the artifact (`FoldedSupport`). Accepting a `rfl` row *is* the
  conversion check; nothing about conversion is proved here.
* `ChangedBlockMatch`: an inductive of a changed block. Each member and
  constructor is exported; every recursor of the Lean block is claimed an image
  (`ExportContext.images`, checked by the map); the reader block holding each
  member contains it with its index count and its constructors in Lean's order,
  and holds nothing that is not the export of a member or constructor of this
  Lean block (containment). The reader block's recursors (the canonical `_ix`
  ones) are not compared. **Trusted here, proved in M7 L2a/L1:** that the
  block transformation itself (reorder, split, collapse) preserves the meaning
  of the types.

`AcceptedAssociation'` is W with the four-way correspondence
(`SourceCorrespondence'`: direct ∨ raw ∨ theorem ∨ equations) and the two-way
block correspondence; `checkIndexed'` decides it with `checkIndexed`'s indexed
procedures (small contexts, positions, `allPar`) and `checkIndexed'_sound`
states it. The old `AcceptedAssociation`, `checkIndexed`, `checkIndexed_sound`
and `faithful_sound` are unchanged; `AcceptedAssociation'.toAccepted` recovers
the old structure when every declaration matched by the old routes.

`AcceptedAssociation'.model_equations` is the semantic corollary: every
equation a Certified changed constant was matched by is installed by the
certified fold, and in **every** strong model of the folded environment each
typed instance of it relates equal values (`StrongInstalledModel.theorem_eq`).
The uniqueness of the function the equations define is **not** claimed (it is
the model-level content of M7 L2a and of the well-founded uniqueness of
cliques).
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-! ## Lean-side equations, as pure functions of the Lean declarations

Reference operations on `Lean.Expr` (no `MetaM`, no runtime
`instantiate`/`instantiateLevelParams`): the substitution and lifting of
`Translate.lean` (`sourceInstantiate`, `sourceLift`) and a level substitution. -/

/-- Universe-parameter substitution on a Lean level. -/
def sourceLevelSubst (params : List Lean.Name) (levels : List Lean.Level) : Lean.Level → Lean.Level
  | .zero => .zero
  | .succ u => .succ (sourceLevelSubst params levels u)
  | .max u v => .max (sourceLevelSubst params levels u) (sourceLevelSubst params levels v)
  | .imax u v => .imax (sourceLevelSubst params levels u) (sourceLevelSubst params levels v)
  | .param p => ((params.zip levels).lookup p).getD (.param p)
  | .mvar m => .mvar m

/-- Universe-parameter substitution on a Lean expression. -/
def sourceInstLevels (params : List Lean.Name) (levels : List Lean.Level) : Lean.Expr → Lean.Expr
  | .sort u => .sort (sourceLevelSubst params levels u)
  | .const n us => .const n (us.map (sourceLevelSubst params levels))
  | .app f a => .app (sourceInstLevels params levels f) (sourceInstLevels params levels a)
  | .lam n t b bi => .lam n (sourceInstLevels params levels t) (sourceInstLevels params levels b) bi
  | .forallE n t b bi =>
    .forallE n (sourceInstLevels params levels t) (sourceInstLevels params levels b) bi
  | .letE n t v b nd => .letE n (sourceInstLevels params levels t)
      (sourceInstLevels params levels v) (sourceInstLevels params levels b) nd
  | .proj n i e => .proj n i (sourceInstLevels params levels e)
  | .mdata md e => .mdata md (sourceInstLevels params levels e)
  | e => e

/-- Metadata at the head, dropped (the export erases it anyway). -/
def sourceDropMData : Lean.Expr → Lean.Expr
  | .mdata _ e => sourceDropMData e
  | e => e

/-- The first `k` Π-binders (each domain in the context of the binders before
it) and the body under them. -/
def sourcePiPrefix : Lean.Expr → Nat → Option (List (Lean.Name × Lean.Expr × Lean.BinderInfo) × Lean.Expr)
  | e, 0 => some ([], e)
  | .forallE n t b bi, k + 1 => (sourcePiPrefix b k).map fun (bs, r) => ((n, t, bi) :: bs, r)
  | .mdata _ e, k + 1 => sourcePiPrefix e (k + 1)
  | _, _ + 1 => none

/-- Rebuild a Π-telescope. -/
def sourceMkForalls (binders : List (Lean.Name × Lean.Expr × Lean.BinderInfo)) (body : Lean.Expr) :
    Lean.Expr :=
  binders.foldr (fun (n, t, bi) acc => .forallE n t acc bi) body

/-- Instantiate the outermost Π-binders, in order, with values living in the
context outside the telescope. -/
def sourceInstForalls : List Lean.Expr → Lean.Expr → Option Lean.Expr
  | [], e => some e
  | v :: vs, e =>
    match sourceDropMData e with
    | .forallE _ _ b _ => sourceInstForalls vs (sourceInstantiate v 0 b)
    | _ => none

/-- Head and arguments of an application. -/
def sourceSpine : Lean.Expr → Lean.Expr × List Lean.Expr
  | .app f a => ((sourceSpine f).1, (sourceSpine f).2 ++ [a])
  | .mdata _ e => sourceSpine e
  | e => (e, [])

/-- The universe of the sort a Π-type ends in. -/
def sourceResultSort : Lean.Expr → Option Lean.Level
  | .forallE _ _ b _ => sourceResultSort b
  | .mdata _ e => sourceResultSort e
  | .sort u => some u
  | _ => none

/-- Stands for an index variable while the major premise's container arguments
are read off the recursor's type. `exportExpr` refuses it (a free variable),
so a constructor argument depending on an index makes the export fail. -/
def sourceIndexPlaceholder : Lean.Expr := .fvar ⟨`_ix_eq_index⟩

/-- **Lean's computation rule** of recursor `r` for constructor `c`, as a
closed statement over `r`'s universe parameters:

`∀ (params motives minors) (fields), @Eq.{ℓ} carrier (r params motives minors idx (c args fields)) (rule.rhs params motives minors fields)`

The prefix binders are `r`'s own; `ℓ` is the universe of the sort the first
motive's type ends in; the major premise's container arguments `args` and the
universe arguments of its inductive are read off `r`'s major premise type (the
index binders instantiated by a placeholder); the fields and the result indices
`idx` come from `c`'s type instantiated at those; `carrier` is `r`'s return
type instantiated at `idx` and the constructor application. The right-hand
side is the rule's applied, not β-reduced. This is the statement the compiler
builds for its images (`Ix.Compile.Image.RuleStmt`, β-reduced there), written
here independently over `Lean.Expr`. -/
def leanRuleStatement (r : Lean.RecursorVal) (c : Lean.ConstructorVal) (rule : Lean.RecursorRule) :
    Except String Lean.Expr := do
  unless rule.ctor == c.name do throw s!"rule constructor mismatch: {rule.ctor}"
  unless rule.nfields == c.numFields do throw s!"rule field count mismatch: {rule.ctor}"
  let p := r.numParams + r.numMotives + r.numMinors
  let some (pre, rest) := sourcePiPrefix r.type p
    | throw "recursor type shorter than its parameters, motives and minors"
  let some (_, motive, _) := pre[r.numParams]? | throw "recursor without a motive"
  let some level := sourceResultSort motive | throw "motive type does not end in a sort"
  let some majorPi := sourceInstForalls (List.replicate r.numIndices sourceIndexPlaceholder) rest
    | throw "recursor type shorter than its indices"
  let .forallE _ majorType _ _ := sourceDropMData majorPi | throw "recursor without a major premise"
  let (head, args) := sourceSpine majorType
  let .const inductName levels := sourceDropMData head
    | throw "major premise type is not an inductive application"
  unless inductName == c.induct do throw s!"major premise is not of the constructor's type: {c.name}"
  unless args.length == c.numParams + r.numIndices do throw "major premise type arity"
  let parameters := args.take c.numParams
  let some fieldsType := sourceInstForalls parameters (sourceInstLevels c.levelParams levels c.type)
    | throw "constructor type shorter than its parameters"
  let nf := c.numFields
  let some (fields, result) := sourcePiPrefix fieldsType nf | throw "constructor type shorter than its fields"
  let indices := (sourceSpine result).2.drop c.numParams
  unless indices.length == r.numIndices do throw "constructor result index count"
  let prefixVars := (List.range p).map fun i => Lean.Expr.bvar (p - 1 - i + nf)
  let fieldVars := (List.range nf).map fun j => Lean.Expr.bvar (nf - 1 - j)
  let major := sourceApps (.const c.name levels) (parameters.map (sourceLift nf 0) ++ fieldVars)
  let lhs := sourceApps (.const r.name (r.levelParams.map .param)) (prefixVars ++ indices ++ [major])
  let rhs := sourceApps rule.rhs (prefixVars ++ fieldVars)
  let some carrier := sourceInstForalls (indices ++ [major]) (sourceLift nf 0 rest)
    | throw "recursor type shorter than its indices and major premise"
  return sourceMkForalls pre (sourceMkForalls fields (sourceApps (.const ``Eq [level]) [carrier, lhs, rhs]))

/-! ## Exports of headers and equations -/

/-- The header `directExport` builds (exported name, universe telescope, type), alone. -/
def directHeader (cx : ExportContext) (ci : Lean.ConstantInfo) : ExportM Kernel.ConstantVal := do
  unless sourceSupported ci do throw s!"unsupported source safety: {ci.name}"
  unless ci.levelParams.eraseDups.length == ci.levelParams.length do
    throw s!"duplicate source universe parameters: {ci.name}"
  let levels ← cx.levels ci
  let tc : TermContext := ⟨cx, ci.levelParams, levels⟩
  return ⟨← cx.name ci.name, levels, ← exportExpr tc ci.type⟩

/-- The exported computation rules of a recursor, one per rule, in order. -/
def ruleStatements (cx : ExportContext) (r : Lean.RecursorVal) : ExportM (List Kernel.Expr) := do
  let levels ← cx.levels (.recInfo r)
  r.rules.mapM fun rule => do
    let some (.ctorInfo c) := cx.source.find rule.ctor | throw s!"missing rule constructor: {rule.ctor}"
    exportExpr ⟨cx, r.levelParams, levels⟩ (← leanRuleStatement r c rule)

/-- The two sides of a definition's defining equation, `c.{us}` and its value, exported. -/
def definitionSides (cx : ExportContext) (d : Lean.DefinitionVal) (levels : List Kernel.Name) :
    ExportM (Kernel.Expr × Kernel.Expr) := do
  let tc : TermContext := ⟨cx, d.levelParams, levels⟩
  return (← exportExpr tc (.const d.name (d.levelParams.map .param)), ← exportExpr tc d.value)

theorem except_mapM_length {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    cases hf : f a with
    | error e => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [List.mapM_cons, hf, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [List.mapM_cons, hf, hl, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        simp [except_mapM_length hl]

/-- One exported statement per rule of the recursor. -/
theorem ruleStatements_length {cx : ExportContext} {r : Lean.RecursorVal} {statements : List Kernel.Expr}
    (h : ruleStatements cx r = .ok statements) : statements.length = r.rules.length := by
  unfold ruleStatements at h
  cases hl : cx.levels (.recInfo r) with
  | error e => simp [hl, bind, Except.bind] at h
  | ok levels =>
    simp only [hl, bind, Except.bind] at h
    exact except_mapM_length h

/-! ## Kernel-side statements and rows -/

/-- `@Eq.{level} carrier left right`, with the checker's `Eq`. -/
def kernelEq (level : Kernel.Level) (carrier left right : Kernel.Expr) : Kernel.Expr :=
  .app (.app (.app (.const Kernel.eqName [level]) carrier) left) right

/-- The parts of an `Eq` statement over the checker's `Eq`. -/
def eqParts : Kernel.Expr → Option (Kernel.Level × Kernel.Expr × Kernel.Expr × Kernel.Expr)
  | .app (.app (.app (.const n [level]) carrier) left) right =>
    if n = Kernel.eqName then some (level, carrier, left, right) else none
  | _ => none

theorem eqParts_kernelEq (level : Kernel.Level) (carrier left right : Kernel.Expr) :
    eqParts (kernelEq level carrier left right) = some (level, carrier, left, right) := by
  simp [eqParts, kernelEq]

theorem eqParts_sound {e : Kernel.Expr} {level : Kernel.Level} {carrier left right : Kernel.Expr}
    (h : eqParts e = some (level, carrier, left, right)) : e = kernelEq level carrier left right := by
  unfold eqParts at h
  split at h
  · rename_i n l t a b
    by_cases hn : n = Kernel.eqName
    · simp only [hn, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      subst hn
      rfl
    · simp [hn] at h
  · simp at h

/-- The statement is a Π-telescope ending in the checker's `Eq`: the shape
`StrongInstalledModel.theorem_eq` reads. -/
def endsInEq : Kernel.Expr → Bool
  | .forallE _ b _ => endsInEq b
  | e => (eqParts e).isSome

/-- The head constant of the left side of an equation under its Π-telescope. -/
def eqLeftHead : Kernel.Expr → Option Kernel.Name
  | .forallE _ b _ => eqLeftHead b
  | e => (eqParts e).bind fun (_, _, left, _) =>
    match left.getAppFn with
    | .const n _ => some n
    | _ => none

/-- A theorem entry of `rows` with universe telescope `levels` and statement
`statement`, whatever its name and proof. -/
def HasTheoremRow (rows : List DirectEntry) (levels : List Kernel.Name) (statement : Kernel.Expr) : Prop :=
  ∃ name proof, DirectEntry.thm ⟨name, levels, statement⟩ proof ∈ rows

def isTheoremRow (levels : List Kernel.Name) (statement : Kernel.Expr) : DirectEntry → Bool
  | .thm cv _ => decide (cv.levelParams = levels) && decide (cv.type = statement)
  | _ => false

theorem isTheoremRow_iff {levels : List Kernel.Name} {statement : Kernel.Expr} {e : DirectEntry} :
    isTheoremRow levels statement e = true ↔ ∃ name proof, e = .thm ⟨name, levels, statement⟩ proof := by
  cases e with
  | thm cv proof =>
    obtain ⟨name, ls, type⟩ := cv
    simp only [isTheoremRow, Bool.and_eq_true, decide_eq_true_eq, DirectEntry.thm.injEq,
      Kernel.ConstantVal.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨name, proof, ⟨rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl⟩
  | _ => simp [isTheoremRow]

theorem hasTheoremRow_iff {rows : List DirectEntry} {levels : List Kernel.Name} {statement : Kernel.Expr} :
    HasTheoremRow rows levels statement ↔ rows.any (isTheoremRow levels statement) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨name, proof, mem⟩
    exact ⟨_, mem, isTheoremRow_iff.mpr ⟨name, proof, rfl⟩⟩
  · rintro ⟨e, mem, row⟩
    obtain ⟨name, proof, rfl⟩ := isTheoremRow_iff.mp row
    exact ⟨name, proof, mem⟩

instance (rows : List DirectEntry) (levels : List Kernel.Name) (statement : Kernel.Expr) :
    Decidable (HasTheoremRow rows levels statement) :=
  decidable_of_iff _ hasTheoremRow_iff.symm

/-- A theorem entry stating `@Eq.{ℓ} carrier left right` for some `ℓ`. -/
def HasRflRow (rows : List DirectEntry) (levels : List Kernel.Name) (carrier left right : Kernel.Expr) : Prop :=
  ∃ name proof level, DirectEntry.thm ⟨name, levels, kernelEq level carrier left right⟩ proof ∈ rows

def isRflRow (levels : List Kernel.Name) (carrier left right : Kernel.Expr) : DirectEntry → Bool
  | .thm cv _ => decide (cv.levelParams = levels) &&
    match eqParts cv.type with
    | some (_, t, l, r) => decide (t = carrier) && decide (l = left) && decide (r = right)
    | none => false
  | _ => false

theorem isRflRow_iff {levels : List Kernel.Name} {carrier left right : Kernel.Expr} {e : DirectEntry} :
    isRflRow levels carrier left right e = true ↔
      ∃ name proof level, e = .thm ⟨name, levels, kernelEq level carrier left right⟩ proof := by
  cases e with
  | thm cv proof =>
    obtain ⟨name, ls, type⟩ := cv
    constructor
    · intro h
      simp only [isRflRow, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      cases hp : eqParts type with
      | none => simp [hp] at h
      | some parts =>
        obtain ⟨level, t, l, r⟩ := parts
        simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨name, proof, level, by rw [eqParts_sound hp]⟩
    · rintro ⟨_, _, level, h⟩
      simp only [DirectEntry.thm.injEq, Kernel.ConstantVal.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      simp [isRflRow, eqParts_kernelEq]
  | _ => simp [isRflRow]

theorem hasRflRow_iff {rows : List DirectEntry} {levels : List Kernel.Name} {carrier left right : Kernel.Expr} :
    HasRflRow rows levels carrier left right ↔ rows.any (isRflRow levels carrier left right) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨name, proof, level, mem⟩
    exact ⟨_, mem, isRflRow_iff.mpr ⟨name, proof, level, rfl⟩⟩
  · rintro ⟨e, mem, row⟩
    obtain ⟨name, proof, level, rfl⟩ := isRflRow_iff.mp row
    exact ⟨name, proof, level, mem⟩

instance (rows : List DirectEntry) (levels : List Kernel.Name) (carrier left right : Kernel.Expr) :
    Decidable (HasRflRow rows levels carrier left right) :=
  decidable_of_iff _ hasRflRow_iff.symm

/-- A **type row**: a theorem entry stating `@Eq.{_} (Sort _) ixType leanType`.
The checker accepted that the declared type of an Ix constant is convertible
to Lean's exported type. Found on compiler output: a changed block's
`brecOn`/`brecOn.go`/`_f` types mention `below`, which Pass 3 inlines in the
compiled type as well (hereditary substitution of the image), so the compiled
type is convertible to Lean's, not syntactically equal. -/
def HasTypeRow (rows : List DirectEntry) (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) : Prop :=
  ∃ name proof eqLevel sortLevel,
    DirectEntry.thm ⟨name, levels, kernelEq eqLevel (.sort sortLevel) ixType leanType⟩ proof ∈ rows

def isTypeRow (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) : DirectEntry → Bool
  | .thm cv _ => decide (cv.levelParams = levels) &&
    match eqParts cv.type with
    | some (_, .sort _, l, r) => decide (l = ixType) && decide (r = leanType)
    | _ => false
  | _ => false

theorem isTypeRow_iff {levels : List Kernel.Name} {ixType leanType : Kernel.Expr} {e : DirectEntry} :
    isTypeRow levels ixType leanType e = true ↔
      ∃ name proof eqLevel sortLevel,
        e = .thm ⟨name, levels, kernelEq eqLevel (.sort sortLevel) ixType leanType⟩ proof := by
  cases e with
  | thm cv proof =>
    obtain ⟨name, ls, type⟩ := cv
    constructor
    · intro h
      simp only [isTypeRow, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      cases hp : eqParts type with
      | none => simp [hp] at h
      | some parts =>
        obtain ⟨level, carrier, l, r⟩ := parts
        cases carrier with
        | sort s =>
          simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨name, proof, level, s, by rw [eqParts_sound hp]⟩
        | _ => simp [hp] at h
    · rintro ⟨_, _, eqLevel, sortLevel, h⟩
      simp only [DirectEntry.thm.injEq, Kernel.ConstantVal.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      simp [isTypeRow, eqParts_kernelEq]
  | _ => simp [isTypeRow]

theorem hasTypeRow_iff {rows : List DirectEntry} {levels : List Kernel.Name} {ixType leanType : Kernel.Expr} :
    HasTypeRow rows levels ixType leanType ↔ rows.any (isTypeRow levels ixType leanType) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨name, proof, eqLevel, sortLevel, mem⟩
    exact ⟨_, mem, isTypeRow_iff.mpr ⟨name, proof, eqLevel, sortLevel, rfl⟩⟩
  · rintro ⟨e, mem, row⟩
    obtain ⟨name, proof, eqLevel, sortLevel, rfl⟩ := isTypeRow_iff.mp row
    exact ⟨name, proof, eqLevel, sortLevel, mem⟩

instance (rows : List DirectEntry) (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) :
    Decidable (HasTypeRow rows levels ixType leanType) :=
  decidable_of_iff _ hasTypeRow_iff.symm

/-- The declared type of the Ix constant is Lean's exported type, or a type
row equates them. -/
def TypeAgrees (rows : List DirectEntry) (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) : Prop :=
  ixType = leanType ∨ HasTypeRow rows levels ixType leanType

instance (rows : List DirectEntry) (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) :
    Decidable (TypeAgrees rows levels ixType leanType) :=
  inferInstanceAs (Decidable (ixType = leanType ∨ HasTypeRow rows levels ixType leanType))

/-- A reader **definition** entry with the exported name and universe telescope
whose declared type agrees with the exported type (any value, any hint). -/
def DefinitionHeaderMatch (entries rows : List DirectEntry) (header : Kernel.ConstantVal) : Prop :=
  ∃ type value hint, DirectEntry.defn ⟨header.name, header.levelParams, type⟩ value hint ∈ entries ∧
    TypeAgrees rows header.levelParams type header.type

def isDefinitionHeader (rows : List DirectEntry) (header : Kernel.ConstantVal) : DirectEntry → Bool
  | .defn cv _ _ => decide (cv.name = header.name) && decide (cv.levelParams = header.levelParams) &&
    decide (TypeAgrees rows header.levelParams cv.type header.type)
  | _ => false

theorem definitionHeaderMatch_iff {entries rows : List DirectEntry} {header : Kernel.ConstantVal} :
    DefinitionHeaderMatch entries rows header ↔ entries.any (isDefinitionHeader rows header) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨type, value, hint, mem, agrees⟩
    exact ⟨_, mem, by simp [isDefinitionHeader, agrees]⟩
  · rintro ⟨e, mem, row⟩
    cases e with
    | defn cv value hint =>
      obtain ⟨n, ls, t⟩ := cv
      simp only [isDefinitionHeader, Bool.and_eq_true, decide_eq_true_eq] at row
      obtain ⟨⟨rfl, rfl⟩, agrees⟩ := row
      exact ⟨t, value, hint, mem, agrees⟩
    | _ => simp [isDefinitionHeader] at row

instance (entries rows : List DirectEntry) (header : Kernel.ConstantVal) :
    Decidable (DefinitionHeaderMatch entries rows header) :=
  decidable_of_iff _ definitionHeaderMatch_iff.symm

/-- A reader **theorem** entry with the exported name and universe telescope
whose statement agrees with the exported statement (any proof). -/
def TheoremHeaderMatch (entries rows : List DirectEntry) (header : Kernel.ConstantVal) : Prop :=
  ∃ type proof, DirectEntry.thm ⟨header.name, header.levelParams, type⟩ proof ∈ entries ∧
    TypeAgrees rows header.levelParams type header.type

def isTheoremHeader (rows : List DirectEntry) (header : Kernel.ConstantVal) : DirectEntry → Bool
  | .thm cv _ => decide (cv.name = header.name) && decide (cv.levelParams = header.levelParams) &&
    decide (TypeAgrees rows header.levelParams cv.type header.type)
  | _ => false

theorem theoremHeaderMatch_iff {entries rows : List DirectEntry} {header : Kernel.ConstantVal} :
    TheoremHeaderMatch entries rows header ↔ entries.any (isTheoremHeader rows header) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨type, proof, mem, agrees⟩
    exact ⟨_, mem, by simp [isTheoremHeader, agrees]⟩
  · rintro ⟨e, mem, row⟩
    cases e with
    | thm cv proof =>
      obtain ⟨n, ls, t⟩ := cv
      simp only [isTheoremHeader, Bool.and_eq_true, decide_eq_true_eq] at row
      obtain ⟨⟨rfl, rfl⟩, agrees⟩ := row
      exact ⟨t, proof, mem, agrees⟩
    | _ => simp [isTheoremHeader] at row

instance (entries rows : List DirectEntry) (header : Kernel.ConstantVal) :
    Decidable (TheoremHeaderMatch entries rows header) :=
  decidable_of_iff _ theoremHeaderMatch_iff.symm

/-! ## The three matches -/

def isThmInfo : Lean.ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- **A Lean theorem whose Ix proof may differ**: the reader stream has a
*theorem* entry with the theorem's exported name and universe telescope, whose
statement is the exported statement or is equated to it by a type row. Kind is
compared; the proof is not. -/
def ThmStatementMatch (cx : ExportContext) (entries rows : List DirectEntry) (ci : Lean.ConstantInfo) : Prop :=
  isThmInfo ci = true ∧
    match directHeader cx ci with
    | .ok header => TheoremHeaderMatch entries rows header
    | .error _ => False

instance (cx : ExportContext) (entries rows : List DirectEntry) (ci : Lean.ConstantInfo) :
    Decidable (ThmStatementMatch cx entries rows ci) := by
  unfold ThmStatementMatch
  split <;> infer_instance

/-- A definition's defining equation by conversion: a theorem row
`@Eq.{ℓ} T c.{us} value` with `T`, `c.{us}` and `value` exported. -/
def RflEquation (cx : ExportContext) (rows : List DirectEntry) (d : Lean.DefinitionVal)
    (header : Kernel.ConstantVal) : Prop :=
  match definitionSides cx d header.levelParams with
  | .ok (left, right) => HasRflRow rows header.levelParams header.type left right
  | .error _ => False

instance (cx : ExportContext) (rows : List DirectEntry) (d : Lean.DefinitionVal)
    (header : Kernel.ConstantVal) : Decidable (RflEquation cx rows d header) := by
  unfold RflEquation
  split <;> infer_instance

/-- A definition's defining equation by Lean's own unfolding lemma: Lean's
`c.eq_def` is a source theorem, its statement is an equation about `c`, and a
theorem row states exactly its export. -/
def EqDefEquation (cx : ExportContext) (rows : List DirectEntry) (d : Lean.DefinitionVal)
    (header : Kernel.ConstantVal) : Prop :=
  match cx.source.find (d.name.str "eq_def") with
  | some (.thmInfo t) =>
    match directHeader cx (.thmInfo t) with
    | .ok h => eqLeftHead h.type = some header.name ∧ HasTheoremRow rows h.levelParams h.type
    | .error _ => False
  | _ => False

instance (cx : ExportContext) (rows : List DirectEntry) (d : Lean.DefinitionVal)
    (header : Kernel.ConstantVal) : Decidable (EqDefEquation cx rows d header) := by
  unfold EqDefEquation
  split
  · split <;> infer_instance
  · infer_instance

/-- **A Lean recursor or definition whose Ix row is a different term**: the
reader stream has a *definition* entry with the constant's exported header, its type up to a type row (a
recursor's image is a definition, a definition's is a definition; any other
kind fails), and each of Lean's defining equations is the statement of a
theorem row of `rows` (the artifact's stream followed by the support):
for a recursor, every computation rule (`ruleStatements`), shaped `∀…, Eq …`;
for a definition, `c = value` by conversion or Lean's `c.eq_def`. -/
def EquationMatch (cx : ExportContext) (entries rows : List DirectEntry) (ci : Lean.ConstantInfo) : Prop :=
  match directHeader cx ci with
  | .error _ => False
  | .ok header =>
    DefinitionHeaderMatch entries rows header ∧
    match ci with
    | .recInfo r =>
      match ruleStatements cx r with
      | .ok statements => ∀ s ∈ statements, endsInEq s = true ∧ HasTheoremRow rows header.levelParams s
      | .error _ => False
    | .defnInfo d => RflEquation cx rows d header ∨ EqDefEquation cx rows d header
    | _ => False

instance (cx : ExportContext) (entries rows : List DirectEntry) (ci : Lean.ConstantInfo) :
    Decidable (EquationMatch cx entries rows ci) := by
  unfold EquationMatch
  split
  · infer_instance
  · refine @instDecidableAnd _ _ _ ?_
    split
    · split <;> infer_instance
    · infer_instance
    · infer_instance

/-- One member of a changed block: its export, its exported name, its index
count and its exported constructor names in Lean's order. -/
structure ChangedMember where
  entry : DirectEntry
  name : Kernel.Name
  numIndices : Nat
  ctors : List Kernel.Name

/-- The exported members and constructors of a Lean inductive block, and the
names of its recursors. All ordering comes from the source. -/
def exportChangedBlock (cx : ExportContext) (owner : Lean.InductiveVal) :
    ExportM (List DirectEntry × List ChangedMember × List Lean.Name) := do
  unless owner.all.contains owner.name do throw "inductive is absent from its source block"
  let mut entries := []
  let mut members := []
  for n in owner.all do
    let some (.inductInfo iv) := cx.source.find n | throw s!"missing inductive member: {n}"
    unless iv.all == owner.all && iv.numParams == owner.numParams do
      throw s!"inconsistent source inductive membership: {n}"
    let e ← directExport cx (.inductInfo iv)
    let name ← cx.name n
    let ctorNames ← iv.ctors.mapM cx.name
    entries := entries ++ [e]
    members := members ++ [ChangedMember.mk e name iv.numIndices ctorNames]
    for (ctor, index) in iv.ctors.zipIdx do
      let some (.ctorInfo cv) := cx.source.find ctor | throw s!"missing constructor: {ctor}"
      unless cv.induct == n && cv.cidx == index && cv.numParams == iv.numParams do
        throw s!"inconsistent constructor owner or position: {ctor}"
      entries := entries ++ [← directExport cx (.ctorInfo cv)]
  let nested := (List.range owner.numNested).filterMap
    (fun i => owner.all.head?.map (·.str s!"rec_{i + 1}"))
  return (entries, members, owner.all.map (·.str "rec") ++ nested)

/-- The reader block holding a member: it contains the member's export with its
index count and constructor list, and nothing but exports of this Lean block's
members and constructors (its recursors, the canonical ones, are not compared). -/
def ChangedMemberMatch (entries : List DirectEntry) (member : ChangedMember) :
    Option Kernel.Frontend.InModel.BlockRec → Prop
  | none => False
  | some actual =>
    (∃ t ∈ actual.types, DirectEntry.induct t.cv t.nP = member.entry ∧
      t.nIdx = member.numIndices ∧ t.ctors = member.ctors) ∧
    (∀ t ∈ actual.types, DirectEntry.induct t.cv t.nP ∈ entries) ∧
    (∀ c ∈ actual.ctors, DirectEntry.ctor c.cv c.nP c.nF ∈ entries)

instance (entries : List DirectEntry) (member : ChangedMember)
    (actual : Option Kernel.Frontend.InModel.BlockRec) :
    Decidable (ChangedMemberMatch entries member actual) := by
  unfold ChangedMemberMatch
  split <;> infer_instance

/-- **An inductive of a changed block** (Def 3.1: members reordered, split or
collapsed by Pass 1). Every recursor of the Lean block is claimed an image
(and the map check holds each claim to a definition record), and each member's
reader block contains it and nothing foreign (`ChangedMemberMatch`). -/
def ChangedBlockMatch (cx : ExportContext) (state : Kernel.Reader.State) (ci : Lean.ConstantInfo) : Prop :=
  match ci with
  | .inductInfo iv =>
    match exportChangedBlock cx iv with
    | .ok (entries, members, recursors) =>
      (∀ n ∈ recursors, cx.images n = true) ∧
      ∀ m ∈ members, ChangedMemberMatch entries m (state.indBlocks[m.name]?)
    | .error _ => False
  | _ => True

instance (cx : ExportContext) (state : Kernel.Reader.State) (ci : Lean.ConstantInfo) :
    Decidable (ChangedBlockMatch cx state ci) := by
  unfold ChangedBlockMatch
  split
  · split <;> infer_instance
  · infer_instance

/-- W+'s correspondence: every source declaration matches directly, through its
raw record, as a theorem by statement, or by its equations. -/
def SourceCorrespondence' (cx : ExportContext) (reader : Kernel.Reader.Ctx)
    (constants : List (Address × Ixon.Constant)) (decls : Array Kernel.Declaration)
    (rows : List DirectEntry) : Prop :=
  ∀ ci ∈ cx.source.declarations,
    DirectMatch cx (streamEntries decls) ci ∨ RawSourceMatch cx reader constants ci ∨
      ThmStatementMatch cx (streamEntries decls) rows ci ∨ EquationMatch cx (streamEntries decls) rows ci

instance (cx : ExportContext) (reader : Kernel.Reader.Ctx) (constants : List (Address × Ixon.Constant))
    (decls : Array Kernel.Declaration) (rows : List DirectEntry) :
    Decidable (SourceCorrespondence' cx reader constants decls rows) :=
  inferInstanceAs (Decidable (∀ ci ∈ cx.source.declarations,
    DirectMatch cx (streamEntries decls) ci ∨ RawSourceMatch cx reader constants ci ∨
      ThmStatementMatch cx (streamEntries decls) rows ci ∨ EquationMatch cx (streamEntries decls) rows ci))

/-- W+'s block correspondence: whole-block match, or a changed block. -/
def BlockCorrespondence' (cx : ExportContext) (state : Kernel.Reader.State) : Prop :=
  ∀ ci ∈ cx.source.declarations, BlockMatch cx state ci ∨ ChangedBlockMatch cx state ci

instance (cx : ExportContext) (state : Kernel.Reader.State) : Decidable (BlockCorrespondence' cx state) :=
  inferInstanceAs (Decidable (∀ ci ∈ cx.source.declarations,
    BlockMatch cx state ci ∨ ChangedBlockMatch cx state ci))

/-! ## Refinement in small contexts -/

theorem directHeader_refines {cx cy : ExportContext} (h : Extends cx cy) (ci : Lean.ConstantInfo) :
    Refines (directHeader cy ci) (directHeader cx ci) := by
  unfold directHeader
  try dsimp only
  refines

theorem ruleStatements_refines {cx cy : ExportContext} (h : Extends cx cy) (r : Lean.RecursorVal) :
    Refines (ruleStatements cy r) (ruleStatements cx r) := by
  unfold ruleStatements
  try dsimp only
  refines

theorem definitionSides_refines {cx cy : ExportContext} (h : Extends cx cy) (d : Lean.DefinitionVal)
    (levels : List Kernel.Name) :
    Refines (definitionSides cy d levels) (definitionSides cx d levels) := by
  unfold definitionSides
  try dsimp only
  refines

theorem exportChangedBlock_refines {cx cy : ExportContext} (h : Extends cx cy) (owner : Lean.InductiveVal) :
    Refines (exportChangedBlock cy owner) (exportChangedBlock cx owner) := by
  unfold exportChangedBlock
  try dsimp only
  refines

theorem changedBlockMatch_transfer {cx cy : ExportContext} (h : Extends cx cy) {state : State}
    {ci : Lean.ConstantInfo} (hb : ChangedBlockMatch cy state ci) : ChangedBlockMatch cx state ci := by
  cases ci with
  | inductInfo iv =>
    unfold ChangedBlockMatch at hb ⊢
    dsimp only at hb ⊢
    cases he : exportChangedBlock cy iv with
    | error _ => simp [he] at hb
    | ok result =>
      rw [exportChangedBlock_refines h iv _ he]
      simp only [he] at hb
      obtain ⟨entries, members, recursors⟩ := result
      dsimp only at hb ⊢
      rw [← h.images]
      exact hb
  | _ => trivial

/-! ## Membership through the hint-quotiented stream -/

theorem mem_of_compatible_thm {stream : List DirectEntry} {header : Kernel.ConstantVal} {proof : Kernel.Expr}
    (mem : DirectEntry.thm header proof ∈ compatibleEntries stream) : DirectEntry.thm header proof ∈ stream := by
  obtain ⟨a, ha, same⟩ := List.mem_map.mp mem
  cases a with
  | thm cv v =>
    have : DirectEntry.thm cv v = DirectEntry.thm header proof := same
    rw [← this]
    exact ha
  | defn cv v hint => simp [DirectEntry.withoutHint] at same
  | «axiom» cv => exact absurd same (by simp [DirectEntry.withoutHint])
  | «opaque» cv v => exact absurd same (by simp [DirectEntry.withoutHint])
  | quot k cv => exact absurd same (by simp [DirectEntry.withoutHint])
  | induct cv n => exact absurd same (by simp [DirectEntry.withoutHint])
  | ctor cv n m => exact absurd same (by simp [DirectEntry.withoutHint])
  | recursor cv a b rules => exact absurd same (by simp [DirectEntry.withoutHint])

theorem mem_of_compatible_defn {stream : List DirectEntry} {header : Kernel.ConstantVal} {value : Kernel.Expr}
    {hint : Kernel.ReducibilityHint} (mem : DirectEntry.defn header value hint ∈ compatibleEntries stream) :
    ∃ original, DirectEntry.defn header value original ∈ stream := by
  obtain ⟨a, ha, same⟩ := List.mem_map.mp mem
  cases a with
  | defn cv v original =>
    simp only [DirectEntry.withoutHint, DirectEntry.defn.injEq] at same
    obtain ⟨rfl, rfl, -⟩ := same
    exact ⟨original, ha⟩
  | thm cv v => exact absurd same (by simp [DirectEntry.withoutHint])
  | «axiom» cv => exact absurd same (by simp [DirectEntry.withoutHint])
  | «opaque» cv v => exact absurd same (by simp [DirectEntry.withoutHint])
  | quot k cv => exact absurd same (by simp [DirectEntry.withoutHint])
  | induct cv n => exact absurd same (by simp [DirectEntry.withoutHint])
  | ctor cv n m => exact absurd same (by simp [DirectEntry.withoutHint])
  | recursor cv a b rules => exact absurd same (by simp [DirectEntry.withoutHint])

theorem streamEntries_append (decls support : Array Kernel.Declaration) :
    streamEntries (decls ++ support) = streamEntries decls ++ streamEntries support := by
  simp [streamEntries, Array.toList_append, List.flatMap_append]

theorem mem_rows_thm {rows : Array DirectEntry} {stream support : List DirectEntry}
    (hr : rows.toList = compatibleEntries stream ++ support) {position : Nat}
    {header : Kernel.ConstantVal} {proof : Kernel.Expr}
    (hp : rows[position]? = some (.thm header proof)) : DirectEntry.thm header proof ∈ stream ++ support := by
  have mem : DirectEntry.thm header proof ∈ rows.toList := Array.mem_def.mp (Array.mem_of_getElem? hp)
  rw [hr, List.mem_append] at mem
  rw [List.mem_append]
  exact mem.imp mem_of_compatible_thm id

/-! ## Decisions at hinted positions -/

/-- A theorem row at one of the hinted positions of `rows`. -/
def rowAt (rows : Array DirectEntry) (positions : List Nat) (levels : List Kernel.Name)
    (statement : Kernel.Expr) : Bool :=
  positions.any fun p =>
    match rows[p]? with
    | some e => isTheoremRow levels statement e
    | none => false

theorem rowAt_sound {rows : Array DirectEntry} {stream support : List DirectEntry}
    (hr : rows.toList = compatibleEntries stream ++ support) {positions : List Nat}
    {levels : List Kernel.Name} {statement : Kernel.Expr} (hq : rowAt rows positions levels statement = true) :
    HasTheoremRow (stream ++ support) levels statement := by
  obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hq
  cases ho : rows[p]? with
  | none => simp [ho] at hp
  | some e =>
    simp only [ho] at hp
    obtain ⟨name, proof, rfl⟩ := isTheoremRow_iff.mp hp
    exact ⟨name, proof, mem_rows_thm hr ho⟩

/-- A `rfl` row at one of the hinted positions of `rows`. -/
def rflAt (rows : Array DirectEntry) (positions : List Nat) (levels : List Kernel.Name)
    (carrier left right : Kernel.Expr) : Bool :=
  positions.any fun p =>
    match rows[p]? with
    | some e => isRflRow levels carrier left right e
    | none => false

theorem rflAt_sound {rows : Array DirectEntry} {stream support : List DirectEntry}
    (hr : rows.toList = compatibleEntries stream ++ support) {positions : List Nat}
    {levels : List Kernel.Name} {carrier left right : Kernel.Expr}
    (hq : rflAt rows positions levels carrier left right = true) :
    HasRflRow (stream ++ support) levels carrier left right := by
  obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hq
  cases ho : rows[p]? with
  | none => simp [ho] at hp
  | some e =>
    simp only [ho] at hp
    obtain ⟨name, proof, level, rfl⟩ := isRflRow_iff.mp hp
    exact ⟨name, proof, level, mem_rows_thm hr ho⟩

/-- A type row at one of the hinted positions of `rows`. -/
def typeRowAt (rows : Array DirectEntry) (positions : List Nat) (levels : List Kernel.Name)
    (ixType leanType : Kernel.Expr) : Bool :=
  positions.any fun p =>
    match rows[p]? with
    | some e => isTypeRow levels ixType leanType e
    | none => false

theorem typeRowAt_sound {rows : Array DirectEntry} {stream support : List DirectEntry}
    (hr : rows.toList = compatibleEntries stream ++ support) {positions : List Nat}
    {levels : List Kernel.Name} {ixType leanType : Kernel.Expr}
    (hq : typeRowAt rows positions levels ixType leanType = true) :
    HasTypeRow (stream ++ support) levels ixType leanType := by
  obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hq
  cases ho : rows[p]? with
  | none => simp [ho] at hp
  | some e =>
    simp only [ho] at hp
    obtain ⟨name, proof, eqLevel, sortLevel, rfl⟩ := isTypeRow_iff.mp hp
    exact ⟨name, proof, eqLevel, sortLevel, mem_rows_thm hr ho⟩

/-- A reader header agrees with the exported one: same name and universe
telescope, and the type is equal or a type row at the hinted positions
equates them. -/
def headerAgreesAt (rows : Array DirectEntry) (positions : List Nat) (header cv : Kernel.ConstantVal) : Bool :=
  decide (cv.name = header.name) && decide (cv.levelParams = header.levelParams) &&
    (decide (cv.type = header.type) || typeRowAt rows positions header.levelParams cv.type header.type)

theorem headerAgreesAt_sound {rows : Array DirectEntry} {stream support : List DirectEntry}
    (hr : rows.toList = compatibleEntries stream ++ support) {positions : List Nat}
    {header cv : Kernel.ConstantVal} (hq : headerAgreesAt rows positions header cv = true) :
    cv.name = header.name ∧ cv.levelParams = header.levelParams ∧
      TypeAgrees (stream ++ support) header.levelParams cv.type header.type := by
  simp only [headerAgreesAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨sameName, sameLevels⟩, agrees⟩ := hq
  refine ⟨sameName, sameLevels, ?_⟩
  rcases agrees with same | row
  · exact .inl same
  · exact .inr (typeRowAt_sound hr row)

/-- `DefinitionHeaderMatch` at the hinted stream position. -/
def defnHeaderAt (rows : Array DirectEntry) (positions : List Nat) (header : Kernel.ConstantVal) :
    Option DirectEntry → Bool
  | some (.defn cv _ _) => headerAgreesAt rows positions header cv
  | _ => false

theorem defnHeaderAt_sound {entries rows : Array DirectEntry} {stream support : List DirectEntry}
    (he : entries.toList = compatibleEntries stream) (hr : rows.toList = compatibleEntries stream ++ support)
    {position : Nat} {positions : List Nat} {header : Kernel.ConstantVal}
    (hq : defnHeaderAt rows positions header entries[position]? = true) :
    DefinitionHeaderMatch stream (stream ++ support) header := by
  cases hp : entries[position]? with
  | none => simp [hp, defnHeaderAt] at hq
  | some e =>
    cases e with
    | defn cv value hint =>
      simp only [hp, defnHeaderAt] at hq
      obtain ⟨sameName, sameLevels, agrees⟩ := headerAgreesAt_sound hr hq
      have mem : DirectEntry.defn cv value hint ∈ compatibleEntries stream := by
        rw [← he]
        exact Array.mem_def.mp (Array.mem_of_getElem? hp)
      obtain ⟨original, mem⟩ := mem_of_compatible_defn mem
      obtain ⟨n, ls, t⟩ := cv
      simp only at sameName sameLevels agrees
      subst sameName sameLevels
      exact ⟨t, value, original, mem, agrees⟩
    | _ => simp [hp, defnHeaderAt] at hq

/-- `TheoremHeaderMatch` at the hinted stream position. -/
def thmHeaderAt (rows : Array DirectEntry) (positions : List Nat) (header : Kernel.ConstantVal) :
    Option DirectEntry → Bool
  | some (.thm cv _) => headerAgreesAt rows positions header cv
  | _ => false

theorem thmHeaderAt_sound {entries rows : Array DirectEntry} {stream support : List DirectEntry}
    (he : entries.toList = compatibleEntries stream) (hr : rows.toList = compatibleEntries stream ++ support)
    {position : Nat} {positions : List Nat} {header : Kernel.ConstantVal}
    (hq : thmHeaderAt rows positions header entries[position]? = true) :
    TheoremHeaderMatch stream (stream ++ support) header := by
  cases hp : entries[position]? with
  | none => simp [hp, thmHeaderAt] at hq
  | some e =>
    cases e with
    | thm cv proof =>
      simp only [hp, thmHeaderAt] at hq
      obtain ⟨sameName, sameLevels, agrees⟩ := headerAgreesAt_sound hr hq
      have mem : DirectEntry.thm cv proof ∈ compatibleEntries stream := by
        rw [← he]
        exact Array.mem_def.mp (Array.mem_of_getElem? hp)
      have mem := mem_of_compatible_thm mem
      obtain ⟨n, ls, t⟩ := cv
      simp only at sameName sameLevels agrees
      subst sameName sameLevels
      exact ⟨t, proof, mem, agrees⟩
    | _ => simp [hp, thmHeaderAt] at hq

/-- `ThmStatementMatch` at the hinted stream position (type rows at the hinted row positions). -/
def thmAt (cy : ExportContext) (entries rows : Array DirectEntry) (position : Nat) (positions : List Nat)
    (ci : Lean.ConstantInfo) : Bool :=
  isThmInfo ci &&
    match directHeader cy ci with
    | .ok header => thmHeaderAt rows positions header entries[position]?
    | .error _ => false

theorem thmAt_sound {cx cy : ExportContext} (h : Extends cx cy) {entries rows : Array DirectEntry}
    {stream support : List DirectEntry} (he : entries.toList = compatibleEntries stream)
    (hr : rows.toList = compatibleEntries stream ++ support) {position : Nat} {positions : List Nat}
    {ci : Lean.ConstantInfo} (hq : thmAt cy entries rows position positions ci = true) :
    ThmStatementMatch cx stream (stream ++ support) ci := by
  simp only [thmAt, Bool.and_eq_true] at hq
  refine ⟨hq.1, ?_⟩
  have rest := hq.2
  cases hd : directHeader cy ci with
  | error _ => simp [hd] at rest
  | ok header =>
    rw [directHeader_refines h ci header hd]
    simp only [hd] at rest
    exact thmHeaderAt_sound he hr rest

/-- `EqDefEquation` with the row at a hinted position. -/
def eqDefAt (cy : ExportContext) (rows : Array DirectEntry) (positions : List Nat)
    (d : Lean.DefinitionVal) (header : Kernel.ConstantVal) : Bool :=
  match cy.source.find (d.name.str "eq_def") with
  | some (.thmInfo t) =>
    match directHeader cy (.thmInfo t) with
    | .ok h => decide (eqLeftHead h.type = some header.name) && rowAt rows positions h.levelParams h.type
    | .error _ => false
  | _ => false

theorem eqDefAt_sound {cx cy : ExportContext} (h : Extends cx cy) {rows : Array DirectEntry}
    {stream support : List DirectEntry} (hr : rows.toList = compatibleEntries stream ++ support)
    {positions : List Nat} {d : Lean.DefinitionVal} {header : Kernel.ConstantVal}
    (hq : eqDefAt cy rows positions d header = true) : EqDefEquation cx (stream ++ support) d header := by
  unfold eqDefAt at hq
  unfold EqDefEquation
  cases hf : cy.source.find (d.name.str "eq_def") with
  | none => simp [hf] at hq
  | some c =>
    rw [h.source _ _ hf]
    cases c with
    | thmInfo t =>
      simp only [hf] at hq
      dsimp only
      cases hh : directHeader cy (.thmInfo t) with
      | error _ => simp [hh] at hq
      | ok eqHeader =>
        rw [directHeader_refines h _ eqHeader hh]
        simp only [hh, Bool.and_eq_true, decide_eq_true_eq] at hq
        exact ⟨hq.1, rowAt_sound hr hq.2⟩
    | _ => simp [hf] at hq

/-- `EquationMatch` with the header at the hinted stream position and the rows
at the hinted row positions. -/
def equationsAt (cy : ExportContext) (entries rows : Array DirectEntry) (position : Nat)
    (positions : List Nat) (ci : Lean.ConstantInfo) : Bool :=
  match directHeader cy ci with
  | .error _ => false
  | .ok header =>
    defnHeaderAt rows positions header entries[position]? &&
    match ci with
    | .recInfo r =>
      match ruleStatements cy r with
      | .ok statements => statements.all fun s => endsInEq s && rowAt rows positions header.levelParams s
      | .error _ => false
    | .defnInfo d =>
      (match definitionSides cy d header.levelParams with
        | .ok (left, right) => rflAt rows positions header.levelParams header.type left right
        | .error _ => false) ||
      eqDefAt cy rows positions d header
    | _ => false

theorem equationsAt_sound {cx cy : ExportContext} (h : Extends cx cy) {entries rows : Array DirectEntry}
    {stream support : List DirectEntry} (he : entries.toList = compatibleEntries stream)
    (hr : rows.toList = compatibleEntries stream ++ support) {position : Nat} {positions : List Nat}
    {ci : Lean.ConstantInfo} (hq : equationsAt cy entries rows position positions ci = true) :
    EquationMatch cx stream (stream ++ support) ci := by
  unfold equationsAt at hq
  unfold EquationMatch
  cases hd : directHeader cy ci with
  | error _ => simp [hd] at hq
  | ok header =>
    rw [directHeader_refines h ci header hd]
    simp only [hd, Bool.and_eq_true] at hq
    refine ⟨defnHeaderAt_sound he hr hq.1, ?_⟩
    have rest := hq.2
    cases ci with
    | recInfo r =>
      dsimp only at rest ⊢
      cases hs : ruleStatements cy r with
      | error _ => simp [hs] at rest
      | ok statements =>
        rw [ruleStatements_refines h r statements hs]
        simp only [hs, List.all_eq_true, Bool.and_eq_true] at rest
        intro s hm
        exact ⟨(rest s hm).1, rowAt_sound hr (rest s hm).2⟩
    | defnInfo d =>
      dsimp only at rest ⊢
      simp only [Bool.or_eq_true] at rest
      rcases rest with byRfl | byEqDef
      · left
        unfold RflEquation
        cases hsd : definitionSides cy d header.levelParams with
        | error _ => simp [hsd] at byRfl
        | ok sides =>
          rw [definitionSides_refines h d _ sides hsd]
          obtain ⟨left, right⟩ := sides
          simp only [hsd] at byRfl
          exact rflAt_sound hr byRfl
      · right
        exact eqDefAt_sound h hr byEqDef
    | _ => simp at rest

/-! ## Support folded on top of the admitted artifact -/

/-- The certified checker's fold of the admitted declarations (behind the
prelude) followed by the support declarations. This is `AdmittedSupport`'s
fold without its row-preservation receipt, which W+ does not use and which is
quadratic to decide on a library (`Kernel.Env.find?` is a list search and the
comparison structural): the equation rows are theorems read in the model of
this folded environment itself. -/
structure FoldedSupport (base support : Array Kernel.Declaration) where
  pins : List Kernel.NatOpPinSet
  pins_checked : builtinNatOpPins = .ok pins
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified pins (base ++ support) = .ok env

inductive FoldError where
  | setup (reason : String)
  | checking (error : Kernel.CheckError) (position : Nat)

/-- Fold the support on top of the admitted artifact; the empty support reuses
the artifact's own fold (no second fold). -/
def foldSupport {input : ArtifactInput} (artifact : AdmittedArtifact input) (support : Array Kernel.Declaration) :
    Except FoldError
      (FoldedSupport (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations) support) :=
  match hp : builtinNatOpPins with
  | .error reason => .error (.setup reason)
  | .ok pins =>
    if h : support = #[] then
      .ok { pins, pins_checked := hp, env := artifact.env
            checked := by
              subst h
              obtain ⟨natPins, hn, hc⟩ := artifact.checked_declarations
              have same : natPins = pins := Except.ok.inj (hn.symm.trans hp)
              subst same
              simpa using hc }
    else
      match hc : Kernel.Cached.checkDecls .verified pins
          (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations ++ support) with
      | .error (error, position) => .error (.checking error position)
      | .ok env => .ok ⟨pins, hp, env, hc⟩

/-! ## The association -/

/-- W+ for one input: the admitted artifact, the support folded on top of it,
the closed domain, the map (with its image claims), the four-way source
correspondence, the two-way block correspondence and the definition groups. -/
structure AcceptedAssociation' (input : Input) (images : Lean.Name → Bool)
    (support : Array Kernel.Declaration) extends AdmittedArtifact input.toArtifactInput where
  folded : FoldedSupport (Kernel.Frontend.preparePrelude prelude.ix declarations) support
  domain : DirectDomain input.source input.roots input.map
  map_agrees : MapAgrees ⟨input.source, input.map, pins, images⟩
    (streamContext pins prelude constants input.blobs input.hint)
  correspondence : SourceCorrespondence' ⟨input.source, input.map, pins, images⟩
    (streamContext pins prelude constants input.blobs input.hint) constants declarations
    (streamEntries (declarations ++ support))
  block_correspondence : BlockCorrespondence' ⟨input.source, input.map, pins, images⟩ readerState
  definition_groups : DefinitionGroupsCovered ⟨input.source, input.map, pins, images⟩ constants

inductive Decline' where
  | base (reason : Decline)
  | fold (error : FoldError)

/-- `checkIndexed`'s shared data, with the row pool: the hint-quotiented reader
stream followed by the support's entries. -/
structure SharedW extends Shared where
  rows : Array DirectEntry

def SharedW.ofArtifact (input : Input) (images : Lean.Name → Bool)
    (artifact : AdmittedArtifact input.toArtifactInput) (support : Array Kernel.Declaration) : SharedW :=
  { cx := ⟨input.source, input.map, artifact.pins, images⟩
    reader := streamContext artifact.pins artifact.prelude artifact.constants input.blobs input.hint
    state := artifact.readerState
    srcArr := input.source.declarations.toArray
    mapArr := input.map.toArray
    entries := (compatibleEntries (streamEntries artifact.declarations)).toArray
    constants := artifact.constants.toArray
    rows := (compatibleEntries (streamEntries artifact.declarations)).toArray ++
      (streamEntries support).toArray }

theorem SharedW.small_extends {input : Input} {images : Lean.Name → Bool}
    {artifact : AdmittedArtifact input.toArtifactInput} {support : Array Kernel.Declaration}
    (domain : DirectDomain input.source input.roots input.map) (hints : Hints) (n : Lean.Name) :
    Extends (SharedW.ofArtifact input images artifact support).cx
      ((SharedW.ofArtifact input images artifact support).small hints n) :=
  smallContext_extends (List.toList_toArray) (List.toList_toArray) domain.1.1 domain.2.1 _ _

theorem SharedW.rows_toList {input : Input} {images : Lean.Name → Bool}
    {artifact : AdmittedArtifact input.toArtifactInput} {support : Array Kernel.Declaration} :
    (SharedW.ofArtifact input images artifact support).rows.toList =
      compatibleEntries (streamEntries artifact.declarations) ++ streamEntries support := by
  simp [SharedW.ofArtifact]

/-- Hints with, per source name, the positions of its equation rows in the row pool. -/
structure HintsW extends Hints where
  rowsAt : Lean.Name → List Nat := fun _ => []

/-- One source declaration under W+: a correspondence route (direct, raw,
theorem, equations), its block (whole or changed) and its definition group. -/
def SharedW.declCheck' (sh : SharedW) (hints : HintsW) (ci : Lean.ConstantInfo) : Bool :=
  let cy := sh.small hints.toHints ci.name
  (directAt cy sh.entries (hints.entryAt ci.name) ci ||
    rawAt cy sh.constants (hints.recordAt ci.name) sh.reader ci ||
    thmAt cy sh.entries sh.rows (hints.entryAt ci.name) (hints.rowsAt ci.name) ci ||
    equationsAt cy sh.entries sh.rows (hints.entryAt ci.name) (hints.rowsAt ci.name) ci) &&
  (decide (BlockMatch cy sh.state ci) || decide (ChangedBlockMatch cy sh.state ci)) &&
  (definitionGroupImage cy ci).isSome

/-- W+ decided by the indexed procedures; the support is folded last, once,
only after every other check passed. -/
def checkIndexed' (input : Input) (images : Lean.Name → Bool)
    (artifact : AdmittedArtifact input.toArtifactInput) (support : Array Kernel.Declaration)
    (hints : HintsW) : Except Decline' (AcceptedAssociation' input images support) :=
  if hd : domainFast hints.workers input.source input.roots input.map = true then
    let sh := SharedW.ofArtifact input images artifact support
    if hm : allPar (sh.entryCheck hints.toHints) hints.workers input.map = true then
      if hn : addressesNodup (artifact.constants.map Prod.fst) = true then
        if hs : allPar (sh.declCheck' hints) hints.workers input.source.declarations = true then
          let blocks := addressSet (input.map.map (·.target.block))
          let targets := Std.HashSet.ofList (input.map.map MapEntry.target)
          if hg : artifact.constants.all (fun row => coveredFast blocks targets row.1 row.2) = true then
            match foldSupport artifact support with
            | .error e => .error (.fold e)
            | .ok folded =>
              have domain := domainFast_sound hd
              have ext := SharedW.small_extends (images := images) (artifact := artifact)
                (support := support) domain hints.toHints
              .ok { toAdmittedArtifact := artifact
                    folded
                    domain
                    map_agrees := fun e he => by
                      have c := List.all_eq_true.mp (allPar_true hm) e he
                      simp only [Shared.entryCheck, Bool.and_eq_true, decide_eq_true_eq] at c
                      exact ⟨c.1.1, nameAgrees_transfer (ext e.source) c.1.2,
                        sourceRecordFlags_transfer (ext e.source) c.2⟩
                    correspondence := fun ci hci => by
                      have c := List.all_eq_true.mp (allPar_true hs) ci hci
                      simp only [SharedW.declCheck', Bool.and_eq_true, Bool.or_eq_true] at c
                      rcases c.1.1 with ((direct | raw) | thm) | eqn
                      · exact .inl (directAt_sound (ext ci.name) List.toList_toArray direct)
                      · exact .inr (.inl (rawAt_sound (ext ci.name) List.toList_toArray
                          (addressesNodup_sound hn) raw))
                      · refine .inr (.inr (.inl ?_))
                        rw [streamEntries_append]
                        exact thmAt_sound (ext ci.name) List.toList_toArray SharedW.rows_toList thm
                      · refine .inr (.inr (.inr ?_))
                        rw [streamEntries_append]
                        exact equationsAt_sound (ext ci.name) List.toList_toArray SharedW.rows_toList eqn
                    block_correspondence := fun ci hci => by
                      have c := List.all_eq_true.mp (allPar_true hs) ci hci
                      simp only [SharedW.declCheck', Bool.and_eq_true, Bool.or_eq_true,
                        decide_eq_true_eq] at c
                      rcases c.1.2 with whole | changed
                      · exact .inl (blockMatch_transfer (ext ci.name) whole)
                      · exact .inr (changedBlockMatch_transfer (ext ci.name) changed)
                    definition_groups :=
                      ⟨fun ci hci => by
                        have c := List.all_eq_true.mp (allPar_true hs) ci hci
                        simp only [SharedW.declCheck', Bool.and_eq_true] at c
                        exact groupImage_transfer (ext ci.name) c.2,
                      fun row hrow => by
                        have c := List.all_eq_true.mp hg row hrow
                        rw [← coveredFast_eq]
                        exact c⟩ }
          else .error (.base .definitionGroupCorrespondence)
        else .error (.base .correspondence)
      else .error (.base (.setup "decoded records repeat an address"))
    else .error (.base .mapMismatch)
  else .error (.base .sourceDomain)

/-- **What a W+ Certified verdict means.** Success of `checkIndexed'` gives:
the exact record bytes are admitted, the support is checked by the certified
fold on top of them, the source is closed and the map covers it and agrees with
the reader (image claims included), every source declaration matches directly,
through its raw record, as a theorem by statement, or by its equations, every
inductive's block matches whole or as a changed block, and the touched
definition groups are covered. -/
theorem checkIndexed'_sound {input : Input} {images : Lean.Name → Bool}
    {artifact : AdmittedArtifact input.toArtifactInput} {support : Array Kernel.Declaration}
    {hints : HintsW} {accepted : AcceptedAssociation' input images support}
    (_h : checkIndexed' input images artifact support hints = .ok accepted) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    Kernel.Cached.checkDecls .verified accepted.folded.pins
      (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations ++ support) =
        .ok accepted.folded.env ∧
    DirectDomain input.source input.roots input.map ∧
    MapAgrees ⟨input.source, input.map, accepted.pins, images⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint) ∧
    (∀ ci ∈ input.source.declarations,
      DirectMatch ⟨input.source, input.map, accepted.pins, images⟩
          (streamEntries accepted.declarations) ci ∨
        RawSourceMatch ⟨input.source, input.map, accepted.pins, images⟩
          (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
          accepted.constants ci ∨
        ThmStatementMatch ⟨input.source, input.map, accepted.pins, images⟩
          (streamEntries accepted.declarations) (streamEntries (accepted.declarations ++ support)) ci ∨
        EquationMatch ⟨input.source, input.map, accepted.pins, images⟩
          (streamEntries accepted.declarations) (streamEntries (accepted.declarations ++ support)) ci) ∧
    BlockCorrespondence' ⟨input.source, input.map, accepted.pins, images⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins, images⟩ accepted.constants :=
  ⟨accepted.admitted, accepted.folded.checked, accepted.domain, accepted.map_agrees,
    accepted.correspondence, accepted.block_correspondence, accepted.definition_groups⟩

/-- With no image claim, every declaration matched by the old routes and every
block whole, W+ is W: the old structure, hence `faithful_sound`'s conclusion
(`AcceptedAssociation.faithful`). -/
def AcceptedAssociation'.toAccepted {input : Input} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input noImages support)
    (direct : SourceCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations)
    (blocks : BlockCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩ accepted.readerState) :
    AcceptedAssociation input :=
  ⟨accepted.toAdmittedArtifact, accepted.domain, accepted.map_agrees, direct, blocks,
    accepted.definition_groups⟩

theorem AcceptedAssociation'.unchanged_faithful {input : Input} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input noImages support)
    (direct : SourceCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations)
    (blocks : BlockCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩ accepted.readerState) :
    checkBytes input.limits input.records input.blobs input.hint = .ok accepted.env ∧
    DirectDomain input.source input.roots input.map ∧
    SourceCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩
      (streamContext accepted.pins accepted.prelude accepted.constants input.blobs input.hint)
      accepted.constants accepted.declarations ∧
    BlockCorrespondence ⟨input.source, input.map, accepted.pins, noImages⟩ accepted.readerState ∧
    DefinitionGroupsCovered ⟨input.source, input.map, accepted.pins, noImages⟩ accepted.constants :=
  (accepted.toAccepted direct blocks).faithful

/-! ## The semantic corollary -/

/-- A theorem entry of the stream or the support is a declaration of the fold. -/
theorem thm_mem_folded {decls support : Array Kernel.Declaration} {pre : Kernel.Frontend.PreludeIx}
    {header : Kernel.ConstantVal} {proof : Kernel.Expr}
    (row : DirectEntry.thm header proof ∈ streamEntries (decls ++ support)) :
    Kernel.Declaration.thmDecl header proof ∈ Kernel.Frontend.preparePrelude pre decls ++ support := by
  obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp row
  have hdecl : d = .thmDecl header proof := by
    cases d with
    | thmDecl cv v =>
      simp only [readerEntries, List.mem_singleton, DirectEntry.thm.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rfl
    | indDecl block np =>
      simp only [readerEntries, List.mem_filterMap] at he
      obtain ⟨c, -, hc⟩ := he
      cases c <;> simp at hc
    | _ => simp [readerEntries] at he
  subst hdecl
  rw [Array.toList_append, List.mem_append] at hd
  rcases hd with h | h
  · exact Array.mem_append_left _ (Kernel.Frontend.mem_preparePrelude (Array.mem_toList_iff.mp h))
  · exact Array.mem_append_right _ (Array.mem_toList_iff.mp h)

/-- **An equation holds in every strong model of `env`.** The certified fold
installed a theorem whose raw statement is exactly `statement` (over the
universe telescope `levels`): `AnnotationTrace.TheoremInstalled`, i.e. the
checker's annotation of `statement` is installed as a theorem; and for every
strong model and every installed form of that theorem, every typed instance
of its statement ending in `@Eq level carrier left right` relates equal
values. -/
def EquationHolds.{u} (env : Kernel.Env) (levels : List Kernel.Name) (statement : Kernel.Expr) : Prop :=
  ∃ name proof, AnnotationTrace.TheoremInstalled .verified ⟨name, levels, statement⟩ proof env ∧
    ∀ (V : Type u) [Kernel.SetTheory V] (strong : StrongInstalledModel V env) (annotated : Kernel.Expr),
      Kernel.ConstantInfo.thmInfo ⟨name, levels, annotated⟩ proof ∈ env.consts →
      ∀ {valuation : Kernel.Name → Nat} {ρ finalρ : Nat → V} {arguments : List V} {level : Kernel.Level}
        {carrier left right : Kernel.Expr} {leftValue rightValue : V},
        InstalledTelescope strong.public.cval env valuation ρ annotated arguments finalρ
          (kernelEq level carrier left right) →
        Kernel.Denotes strong.public.cval env valuation finalρ left leftValue →
        Kernel.Denotes strong.public.cval env valuation finalρ right rightValue →
        leftValue = rightValue

theorem equationHolds_of_installed {env : Kernel.Env} {levels : List Kernel.Name}
    {statement : Kernel.Expr} {name : Kernel.Name} {proof : Kernel.Expr}
    (installed : AnnotationTrace.TheoremInstalled .verified ⟨name, levels, statement⟩ proof env) :
    EquationHolds.{u} env levels statement :=
  ⟨name, proof, installed, by
    intro V _ strong annotated present valuation ρ finalρ arguments level carrier left right
      leftValue rightValue typed leftRead rightRead
    exact strong.theorem_eq ⟨name, levels, annotated⟩ proof present typed leftRead rightRead⟩

/-- The declared type of an Ix constant denotes Lean's exported type in every
strong model of `env`: it is that type, or a type row equating the two holds. -/
def TypeHolds.{u} (env : Kernel.Env) (levels : List Kernel.Name) (ixType leanType : Kernel.Expr) : Prop :=
  ixType = leanType ∨
    ∃ eqLevel sortLevel, EquationHolds.{u} env levels (kernelEq eqLevel (.sort sortLevel) ixType leanType)

/-- Every theorem row of the artifact's stream or of the support is installed by
the fold and holds in every strong model. -/
theorem AcceptedAssociation'.row_holds.{u} {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (accepted : AcceptedAssociation' input images support)
    {levels : List Kernel.Name} {s : Kernel.Expr}
    (row : HasTheoremRow (streamEntries (accepted.declarations ++ support)) levels s) :
    EquationHolds.{u} accepted.folded.env levels s := by
  obtain ⟨name, proof, mem⟩ := row
  exact equationHolds_of_installed
    (AnnotationTrace.theorem_checked (thm_mem_folded mem) accepted.folded.checked)

theorem AcceptedAssociation'.type_holds.{u} {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (accepted : AcceptedAssociation' input images support)
    {levels : List Kernel.Name} {ixType leanType : Kernel.Expr}
    (agrees : TypeAgrees (streamEntries (accepted.declarations ++ support)) levels ixType leanType) :
    TypeHolds.{u} accepted.folded.env levels ixType leanType := by
  rcases agrees with same | ⟨name, proof, eqLevel, sortLevel, mem⟩
  · exact .inl same
  · exact .inr ⟨eqLevel, sortLevel, accepted.row_holds ⟨name, proof, mem⟩⟩

/-- **The semantic corollary (M5).** A constant that `AcceptedAssociation'`
matched by its equations has, under its exported name and universe telescope,
a reader *definition* entry whose declared type denotes Lean's type in every
strong model (`TypeHolds`), and each of Lean's defining equations (every
computation rule of a recursor; a definition's `c = value` or Lean's
`c.eq_def`) is installed by the certified fold of the artifact and its support
and holds in every strong model of it (`EquationHolds`). Uniqueness of the
function these equations define is not claimed. -/
theorem AcceptedAssociation'.model_equations.{u} {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (accepted : AcceptedAssociation' input images support)
    {ci : Lean.ConstantInfo}
    (equations : EquationMatch ⟨input.source, input.map, accepted.pins, images⟩
      (streamEntries accepted.declarations) (streamEntries (accepted.declarations ++ support)) ci) :
    ∃ header, directHeader ⟨input.source, input.map, accepted.pins, images⟩ ci = .ok header ∧
      (∃ type value hint,
        DirectEntry.defn ⟨header.name, header.levelParams, type⟩ value hint ∈ streamEntries accepted.declarations ∧
        TypeHolds.{u} accepted.folded.env header.levelParams type header.type) ∧
      match ci with
      | .recInfo r =>
        ∃ statements, ruleStatements ⟨input.source, input.map, accepted.pins, images⟩ r = .ok statements ∧
          statements.length = r.rules.length ∧
          ∀ s ∈ statements, EquationHolds.{u} accepted.folded.env header.levelParams s
      | .defnInfo d =>
        (∃ left right level,
          definitionSides ⟨input.source, input.map, accepted.pins, images⟩ d header.levelParams =
            .ok (left, right) ∧
          EquationHolds.{u} accepted.folded.env header.levelParams (kernelEq level header.type left right)) ∨
        (∃ t eqHeader, input.source.find (d.name.str "eq_def") = some (.thmInfo t) ∧
          directHeader ⟨input.source, input.map, accepted.pins, images⟩ (.thmInfo t) = .ok eqHeader ∧
          eqLeftHead eqHeader.type = some header.name ∧
          EquationHolds.{u} accepted.folded.env eqHeader.levelParams eqHeader.type)
      | _ => False := by
  unfold EquationMatch at equations
  cases hd : directHeader ⟨input.source, input.map, accepted.pins, images⟩ ci with
  | error _ => simp [hd] at equations
  | ok header =>
    simp only [hd] at equations
    obtain ⟨⟨type, value, hint, mem, agrees⟩, rest⟩ := equations
    refine ⟨header, rfl, ⟨type, value, hint, mem, accepted.type_holds agrees⟩, ?_⟩
    cases ci with
    | recInfo r =>
      dsimp only at rest ⊢
      cases hs : ruleStatements ⟨input.source, input.map, accepted.pins, images⟩ r with
      | error _ => simp [hs] at rest
      | ok statements =>
        simp only [hs] at rest
        exact ⟨statements, rfl, ruleStatements_length hs, fun s hm => accepted.row_holds (rest s hm).2⟩
    | defnInfo d =>
      dsimp only at rest ⊢
      rcases rest with byRfl | byEqDef
      · left
        unfold RflEquation at byRfl
        cases hsd : definitionSides ⟨input.source, input.map, accepted.pins, images⟩ d header.levelParams with
        | error _ => simp [hsd] at byRfl
        | ok sides =>
          obtain ⟨left, right⟩ := sides
          simp only [hsd] at byRfl
          obtain ⟨name, proof, level, row⟩ := byRfl
          exact ⟨left, right, level, rfl, accepted.row_holds ⟨name, proof, row⟩⟩
      · right
        unfold EqDefEquation at byEqDef
        cases hf : input.source.find (d.name.str "eq_def") with
        | none => simp [hf] at byEqDef
        | some c =>
          cases c with
          | thmInfo t =>
            simp only [hf] at byEqDef
            cases hh : directHeader ⟨input.source, input.map, accepted.pins, images⟩ (.thmInfo t) with
            | error _ => simp [hh] at byEqDef
            | ok eqHeader =>
              simp only [hh] at byEqDef
              exact ⟨t, eqHeader, rfl, hh, byEqDef.1, accepted.row_holds byEqDef.2⟩
          | _ => simp [hf] at byEqDef
    | _ => simp at rest

/-- The semantic reading of a theorem matched by its statement: under its
exported name and universe telescope the reader stream has a *theorem* whose
statement denotes Lean's statement in every strong model (`TypeHolds`); the
theorem holds in the model by the checker's own soundness. -/
theorem AcceptedAssociation'.model_statement.{u} {input : Input} {images : Lean.Name → Bool}
    {support : Array Kernel.Declaration} (accepted : AcceptedAssociation' input images support)
    {ci : Lean.ConstantInfo}
    (statement : ThmStatementMatch ⟨input.source, input.map, accepted.pins, images⟩
      (streamEntries accepted.declarations) (streamEntries (accepted.declarations ++ support)) ci) :
    ∃ header, directHeader ⟨input.source, input.map, accepted.pins, images⟩ ci = .ok header ∧
      ∃ type proof,
        DirectEntry.thm ⟨header.name, header.levelParams, type⟩ proof ∈ streamEntries accepted.declarations ∧
        TypeHolds.{u} accepted.folded.env header.levelParams type header.type := by
  obtain ⟨_, rest⟩ := statement
  cases hd : directHeader ⟨input.source, input.map, accepted.pins, images⟩ ci with
  | error _ => simp [hd] at rest
  | ok header =>
    simp only [hd] at rest
    obtain ⟨type, proof, mem, agrees⟩ := rest
    exact ⟨header, rfl, type, proof, mem, accepted.type_holds agrees⟩

end Ix.CompileCert
