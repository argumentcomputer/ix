/-
  Ix.AuxGen.BRecOn: canonical `.brecOn` generation for alpha-collapsed
  inductive blocks.

  Port of `crates/compile/src/compile/aux_gen/brecon.rs` (all 2843 lines):
  `generate_brecon_constants` and everything reachable from it.

  **Prop-level** (inductive predicates): generates a single theorem per class.
    `I_i.brecOn = λ params motives t F_1..F_n => F_i t (I_i.rec below_motives below_minors t)`
    Reference: `refs/lean4/src/Lean/Meta/IndPredBelow.lean:185-208`

  **Type-level** (large eliminators): generates `.brecOn.go` + `.brecOn` +
  `.brecOn.eq` per class.
    `.brecOn.go` uses PProd-wrapped motives; `.brecOn` projects first component.
    Reference: `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:191-308`

  NOT here (already ported, reused):
  - the data model `BRecOnDef` (brecon.rs:47) lives in `Ix.AuxGen.Types`;
  - `mk_level_succ`/`mk_pprod`/`mk_pprod_mk`/`mk_punit_unit`/`punit_const`
    live in `Ix.AuxGen.Levels`;
  - `aux_rec_suffix_idx` (below.rs:31) lives in `Ix.AuxGen.Below`;
  - `LocalDecl`/`abstract_fvar`/`subst_fvar`/telescopes/`find_motive_fvar`/
    `decompose_apps`/`beta_reduce` live in `Ix.AuxGen.ExprUtils`;
  - the TcScope kernel bridge lives in `Ix.AuxGen.Kernel`.

  Environment access: Rust threads `lean_env: &LeanEnv` and
  `stt: &CompileState`; the Lean port reads the base compile environment
  via `lookupConst?` / `getCompileEnv` under KBridgeM, and the kernel via
  `TcScopeSt` + `AddrMaps` (mirroring `stt`/`kctx`).

  Deviations (behavioral no-ops):
  - the `IX_BRECON_DEBUG` stderr dumps (brecon.rs:363-371/:667-674) have no
    CompileM IO channel and are dropped;
  - `debug_assert!` (brecon.rs:244-248) has no Lean counterpart;
  - `CompileError.missingConstant` has no `caller` slot for the Rust
    context strings (same note as `Ix.AuxGen.Below`);
  - `try_nat_to_usize` checked conversions vanish — `RecursorVal` counts
    are native `Nat`s.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkParam`,
  ...) so the embedded blake3 hashes stay bit-identical with the Rust
  compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.Nested
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Below
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-! ## Level utilities (brecon.rs:2779) -/

/-- Mirrors Rust `subst_level` (brecon.rs:2829).

    Substitute a named level parameter with a concrete level. NOTE the
    deliberate asymmetry: the `Succ` arm rebuilds with the SMART
    `mkLevelSucc` (distributes over Max) while `Max`/`Imax` use the RAW
    constructors — preserved exactly. -/
partial def substLevelParam (lvl : Level) (param : Name) (replacement : Level)
    : Level :=
  match lvl with
  | .param n _ => if n == param then replacement else lvl
  | .succ l _ => mkLevelSucc (substLevelParam l param replacement)
  | .max l1 l2 _ =>
    Level.mkMax (substLevelParam l1 param replacement)
      (substLevelParam l2 param replacement)
  | .imax l1 l2 _ =>
    Level.mkIMax (substLevelParam l1 param replacement)
      (substLevelParam l2 param replacement)
  | _ => lvl

/-- Mirrors Rust `subst_level_in_expr` (brecon.rs:2787).

    Substitute a named level parameter with a concrete level throughout an
    expression. Used for Prop brecOn: the recursor type has
    `Level::param(u)` for large elimination, but brecOn specializes to
    Prop, so `u -> Level::zero()`.

    NOTE: the Rust catch-all `_ => expr.clone()` does NOT descend into
    `Proj`/`Mdata`/leaf nodes — preserved exactly. -/
partial def substLevelInExpr (expr : Expr) (param : Name) (replacement : Level)
    : Expr :=
  match expr with
  | .sort lvl _ => Expr.mkSort (substLevelParam lvl param replacement)
  | .const n lvls _ =>
    Expr.mkConst n (lvls.map (substLevelParam · param replacement))
  | .app f a _ =>
    Expr.mkApp (substLevelInExpr f param replacement)
      (substLevelInExpr a param replacement)
  | .forallE n d b bi _ =>
    Expr.mkForallE n (substLevelInExpr d param replacement)
      (substLevelInExpr b param replacement) bi
  | .lam n d b bi _ =>
    Expr.mkLam n (substLevelInExpr d param replacement)
      (substLevelInExpr b param replacement) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (substLevelInExpr t param replacement)
      (substLevelInExpr v param replacement)
      (substLevelInExpr b param replacement) nd
  | _ => expr

/-! ## Eq/HEq application builders (brecon.rs:1284) -/

/-- Mirrors Rust `mk_eq` (brecon.rs:1285). Build `@Eq.{u} α a b`. -/
def mkEq (u : Level) (alpha a b : Expr) : Expr :=
  let eq := mkConst (Name.mkStr .mkAnon "Eq") #[u]
  Expr.mkApp (Expr.mkApp (Expr.mkApp eq alpha) a) b

/-- Mirrors Rust `mk_eq_refl` (brecon.rs:1297).
    Build `@Eq.refl.{u} α a : Eq.{u} α a a`. -/
def mkEqRefl (u : Level) (alpha a : Expr) : Expr :=
  let eqRefl := mkConst (Name.mkStr (Name.mkStr .mkAnon "Eq") "refl") #[u]
  Expr.mkApp (Expr.mkApp eqRefl alpha) a

/-- Mirrors Rust `mk_eq_symm` (brecon.rs:1306).
    Build `@Eq.symm.{u} α a b h : Eq b a` given `h : Eq a b`. -/
def mkEqSymm (u : Level) (alpha a b h : Expr) : Expr :=
  let eqSymm := mkConst (Name.mkStr (Name.mkStr .mkAnon "Eq") "symm") #[u]
  Expr.mkApp
    (Expr.mkApp (Expr.mkApp (Expr.mkApp eqSymm alpha) a) b) h

/-- Mirrors Rust `mk_eq_ndrec` (brecon.rs:1330).

    Build `@Eq.ndrec.{u_1, u_2} α a motive prf b h : motive b`.
    `u1` is the motive's result universe, `u2` is the type `α`'s
    universe. -/
def mkEqNdrec (u1 u2 : Level) (alpha a motive prf b h : Expr) : Expr :=
  let ndrec := mkConst (Name.mkStr (Name.mkStr .mkAnon "Eq") "ndrec")
    #[u1, u2]
  mkAppN ndrec #[alpha, a, motive, prf, b, h]

/-- Mirrors Rust `mk_heq` (brecon.rs:1358). Build `@HEq.{u} α a β b`. -/
def mkHeq (u : Level) (alpha a beta b : Expr) : Expr :=
  let heq := mkConst (Name.mkStr .mkAnon "HEq") #[u]
  mkAppN heq #[alpha, a, beta, b]

/-- Mirrors Rust `mk_heq_refl` (brecon.rs:1373).
    Build `@HEq.refl.{u} α a : HEq a a`. -/
def mkHeqRefl (u : Level) (alpha a : Expr) : Expr :=
  let heqRefl := mkConst (Name.mkStr (Name.mkStr .mkAnon "HEq") "refl") #[u]
  Expr.mkApp (Expr.mkApp heqRefl alpha) a

/-- Mirrors Rust `mk_eq_of_heq` (brecon.rs:1382).
    Build `@eq_of_heq.{u} α a b h : Eq a b` given `h : HEq a b`. -/
def mkEqOfHeq (u : Level) (alpha a b h : Expr) : Expr :=
  let eqOfHeq := mkConst (Name.mkStr .mkAnon "eq_of_heq") #[u]
  mkAppN eqOfHeq #[alpha, a, b, h]

/-! ## Cases-tactic simulation substrate (brecon.rs:2067-2267) -/

/-- Mirrors Rust `expr_contains_fvar` (brecon.rs:2068).
    Whether an expression contains a free variable with the given name. -/
partial def exprContainsFVar (expr : Expr) (fvarName : Name) : Bool :=
  match expr with
  | .fvar n _ => n == fvarName
  | .app f a _ => exprContainsFVar f fvarName || exprContainsFVar a fvarName
  | .lam _ t b _ _ | .forallE _ t b _ _ =>
    exprContainsFVar t fvarName || exprContainsFVar b fvarName
  | .letE _ t v b _ _ =>
    exprContainsFVar t fvarName || exprContainsFVar v fvarName
      || exprContainsFVar b fvarName
  | .proj _ _ e _ | .mdata _ e _ => exprContainsFVar e fvarName
  | _ => false

/-- Mirrors Rust `build_specialized_major_type` (brecon.rs:2090).
    Build `I <params> <args>` — the major type with the given index args. -/
def buildSpecializedMajorType (majorType : Expr) (indexFvars : Array Expr)
    (retArgs : Array Expr) : Expr := Id.run do
  let (head, args) := decomposeApps majorType
  let nIndices := indexFvars.size
  let nParamArgs := args.size - nIndices -- saturating, as in Rust
  let mut spec := head
  for p in args.extract 0 nParamArgs do
    spec := Expr.mkApp spec p
  for r in retArgs do
    spec := Expr.mkApp spec r
  return spec

/-- Mirrors Rust `EqBinderKind` (brecon.rs:2131).
    Classified shape of an `Eq` or `HEq` binder's domain. -/
inductive EqBinderKind where
  /-- `@Eq.{u} α lhs rhs`. -/
  | eq (alpha lhs rhs : Expr) (level : Level)
  /-- `@HEq.{u} α a β b`. -/
  | heq (alpha a beta b : Expr) (level : Level)

/-- Mirrors Rust `subst_in_eq_binder_kind` (brecon.rs:2145).
    Apply a FVar → expression substitution across an `EqBinderKind`. -/
def substInEqBinderKind (kind : EqBinderKind) (fvarName : Name)
    (replacement : Expr) : EqBinderKind :=
  match kind with
  | .eq alpha lhs rhs level =>
    .eq (substFVar alpha fvarName replacement)
      (substFVar lhs fvarName replacement)
      (substFVar rhs fvarName replacement) level
  | .heq alpha a beta b level =>
    .heq (substFVar alpha fvarName replacement)
      (substFVar a fvarName replacement)
      (substFVar beta fvarName replacement)
      (substFVar b fvarName replacement) level

/-- Mirrors Rust `build_refl_proof` (brecon.rs:2172).

    Build `@Eq.refl.{u} α lhs` for a goal `@Eq.{u} α lhs rhs`. Mirrors
    `MVarId.refl` (`refs/lean4/src/Lean/Meta/Tactic/Refl.lean:25-39`),
    which always uses the LHS of the equation. -/
def buildReflProof (goalEq : Expr) : Option Expr := Id.run do
  let (head, args) := decomposeApps goalEq
  if args.size != 3 then
    return none
  let level ← match head with
    | .const name lvls _ =>
      if name == Name.mkStr .mkAnon "Eq" && lvls.size == 1 then
        pure lvls[0]!
      else
        return none
    | _ => return none
  let alpha := args[0]!
  let lhs := args[1]!
  -- rhs is args[2] — not used because Eq.refl uses LHS.
  return some (mkEqRefl level alpha lhs)

/-- Sentinel mirroring Rust `usize::MAX` in `determine_symm`'s
    order-lookup default (brecon.rs:2212-2213). Only its ordering relative
    to real (small) order indices matters. -/
def USIZE_MAX : Nat := 18446744073709551615

/-- Mirrors Rust `determine_symm` (brecon.rs:2205).

    Determine `substCore`'s `symm` direction for an `Eq` binder, per
    `substEq` (`refs/lean4/src/Lean/Meta/Tactic/UnifyEq.lean:127-134`):
    - both fvars → `symm = aDecl.index < bDecl.index`
    - `(fvar, _)` → `symm = false`
    - `(_, fvar)` → `symm = true`
    - `(expr, expr)` → unreachable in the `.brecOn.eq` cases flow

    Returns `(symm, abstractedFvarName, replacement)`. -/
def determineSymm (lhs rhs : Expr) (fvarOrder : Std.HashMap Name Nat)
    : Option (Bool × Name × Expr) :=
  match lhs, rhs with
  | .fvar lname _, .fvar rname _ =>
    let lorder := (fvarOrder.get? lname).getD USIZE_MAX
    let rorder := (fvarOrder.get? rname).getD USIZE_MAX
    if lorder < rorder then
      -- symm=true: abstract rhs (the later-intro'd fvar), replace with lhs
      some (true, rname, lhs)
    else
      -- symm=false: abstract lhs, replace with rhs
      some (false, lname, rhs)
  | .fvar lname _, _ =>
    -- (fvar, expr) → symm=false: abstract lhs, replace with rhs
    some (false, lname, rhs)
  | _, .fvar rname _ =>
    -- (expr, fvar) → symm=true: abstract rhs, replace with lhs
    some (true, rname, lhs)
  | _, _ => none

/-- Mirrors Rust `collect_forward_deps` (brecon.rs:2248).

    Compute forward dependencies of `abstractedFvarName` in
    `localContext` (Lean's `collectForwardDeps`,
    `refs/lean4/src/Lean/MetavarContext.lean:1372`): a fvar is a forward
    dependency if its type references the abstracted fvar (directly) or a
    previously-collected forward dependency (transitively), returned in
    `localContext` order. -/
def collectForwardDeps (abstractedFvarName : Name)
    (localContext : Array LocalDecl) : Array LocalDecl := Id.run do
  let mut deps : Array LocalDecl := #[]
  let mut depNames : Std.HashSet Name := {}
  depNames := depNames.insert abstractedFvarName
  for d in localContext do
    if d.fvarName == abstractedFvarName then
      continue
    let depends := depNames.toList.any fun n => exprContainsFVar d.domain n
    if depends then
      deps := deps.push d
      depNames := depNames.insert d.fvarName
  return deps

/-- Mirrors Rust `HArgSource` (brecon.rs:2341).
    Describes how the `h_arg` (eq proof) of `Eq.ndrec` is constructed
    from the binder fvar. -/
inductive HArgSource where
  /-- The binder is an `Eq` fvar — use it directly (possibly
      `Eq.symm`-ed). -/
  | eqFvar
  /-- The binder is an `HEq` fvar — wrap with `eq_of_heq` inline
      (matching Lean's beta-reduced `heqToEq'` form). -/
  | eqOfHeq

mutual

/-- Mirrors Rust `build_proof_for_remaining` (brecon.rs:2281).

    Build the proof term for the "remaining" `∀`-chain `∀ rest. body`.
    Outside-in recursive construction simulating Lean's `unifyEqs?` loop
    (`refs/lean4/src/Lean/Meta/Tactic/Cases.lean:231-239`). -/
partial def buildProofForRemaining
    (remaining : List (EqBinderKind × LocalDecl)) (body : Expr)
    (localContext : Array LocalDecl) (fvarOrder : Std.HashMap Name Nat)
    (ctorIdx depth : Nat) : Option Expr :=
  match remaining with
  | [] => buildReflProof body
  | (kind, decl) :: rest =>
    match kind with
    | .eq alpha lhs rhs level =>
      handleSubstcoreStep decl rest body alpha lhs rhs level .eqFvar
        localContext fvarOrder ctorIdx depth
    | .heq alpha a _beta b level =>
      -- For HEq binders, Lean's `heqToEq'` converts to an `Eq` via
      -- `eq_of_heq`, and the ensuing `substCore` uses `eq_of_heq heq`
      -- inline (Lean's `instantiateMVars` beta-reduces the revert+intro
      -- redex — `Lean.MetavarContext:1473`). `HArgSource.eqOfHeq`
      -- reproduces the post-beta form.
      handleSubstcoreStep decl rest body alpha a b level .eqOfHeq
        localContext fvarOrder ctorIdx depth

/-- Mirrors Rust `handle_substcore_step` (brecon.rs:2368).

    Handle a single substCore step — either for an `Eq` binder (using the
    fvar directly) or a converted `HEq` binder (using `eq_of_heq heq`
    inline). Output shape:

    ```text
    λ binder_decl.
      (@Eq.ndrec.{0, level} α a_ndrec motive continuation b_ndrec h_arg)
        orig_forward_dep_1 orig_forward_dep_2 ...
    ``` -/
partial def handleSubstcoreStep (decl : LocalDecl)
    (rest : List (EqBinderKind × LocalDecl)) (body : Expr)
    (alpha lhs rhs : Expr) (level : Level) (hArgSource : HArgSource)
    (localContext : Array LocalDecl) (fvarOrder : Std.HashMap Name Nat)
    (ctorIdx depth : Nat) : Option Expr := Id.run do
  let some (symm, abstractedFvarName, replacement) :=
      determineSymm lhs rhs fvarOrder
    | return none

  -- Defensive invariant: for `.brecOn.eq`, we expect `depElim = false`
  -- (the goal doesn't depend on the eq-fvar itself). Lean's substCore
  -- would branch to `mkEqRec` (7 args, 2-binder motive) if it did.
  let eqFvarUsedInRestOrBody := exprContainsFVar body decl.fvarName
    || rest.any fun (_, d) => exprContainsFVar d.domain decl.fvarName
  if eqFvarUsedInRestOrBody then
    return none

  -- Forward dependencies — context fvars depending transitively on
  -- `abstractedFvar` (Lean's `revert` pulls these in automatically).
  let forwardDeps := collectForwardDeps abstractedFvarName localContext

  -- Motive body: the FULL current goal (`∀ forward_deps. ∀ rest. body`)
  -- with `abstractedFvar` abstracted.
  let motiveBinders : Array LocalDecl :=
    forwardDeps ++ (rest.map (·.2)).toArray
  let currentGoalType := mkForall body motiveBinders
  let motiveBody := abstractFVar currentGoalType abstractedFvarName 0

  -- The motive's λ binder TYPE is the abstracted fvar's *actual stored
  -- type* from the local context — not the `α` passed in (they can
  -- differ syntactically even when def-equal; see the Rust comment on
  -- `CategoryTheory.FreeBicategory.Hom₂`). -/
  let binderType :=
    match localContext.find? (fun d => d.fvarName == abstractedFvarName) with
    | some d => d.domain
    | none => alpha
  let motive := Expr.mkLam (Name.mkStr .mkAnon "x") binderType motiveBody
    .default

  -- Substituted continuation state: `abstractedFvar := replacement` in
  -- forward-dep domains, rest binder domains, and body.
  let newForwardDeps : Array LocalDecl := forwardDeps.map fun d =>
    { d with domain := substFVar d.domain abstractedFvarName replacement }
  let newBody := substFVar body abstractedFvarName replacement
  let newRest : List (EqBinderKind × LocalDecl) := rest.map fun (k, d) =>
    (substInEqBinderKind k abstractedFvarName replacement,
     { d with domain := substFVar d.domain abstractedFvarName replacement })

  -- Continuation local context: forward deps replaced by their
  -- substituted versions; the abstracted fvar removed (`clearH := true`).
  let newLocalContext : Array LocalDecl := localContext.filterMap fun d =>
    if d.fvarName == abstractedFvarName then
      none
    else
      match newForwardDeps.find? (fun nd => nd.fvarName == d.fvarName) with
      | some newD => some newD
      | none => some d

  let some innerProof := buildProofForRemaining newRest newBody
      newLocalContext fvarOrder ctorIdx (depth + 1)
    | return none

  -- λ forward_deps — matching motive(a_ndrec)'s ∀-binders.
  let continuation := mkLambda innerProof newForwardDeps

  let binderAsExpr : Expr :=
    match hArgSource with
    | .eqFvar => Expr.mkFVar decl.fvarName
    | .eqOfHeq =>
      -- `eq_of_heq.{level} α a b heq` — the inlined post-beta form.
      mkEqOfHeq level alpha lhs rhs (Expr.mkFVar decl.fvarName)

  -- Per substCore's symm convention:
  --   symm=false → a_ndrec = rhs, b_ndrec = lhs, h_arg = Eq.symm _
  --   symm=true  → a_ndrec = lhs, b_ndrec = rhs, h_arg = _
  let (aNdrec, bNdrec, hArg) :=
    if symm then
      (lhs, rhs, binderAsExpr)
    else
      (rhs, lhs, mkEqSymm level alpha lhs rhs binderAsExpr)

  -- 6-arg Eq.ndrec, then the ORIGINAL forward-dep fvars as extra args.
  let mut ndrec := mkEqNdrec Level.mkZero level alpha aNdrec motive
    continuation bNdrec hArg
  for fd in forwardDeps do
    ndrec := Expr.mkApp ndrec (Expr.mkFVar fd.fvarName)

  return some (mkLambda ndrec #[decl])

end

/-- Mirrors Rust `build_minor_via_cases_sim` (brecon.rs:2568).

    Build a single indexed `.brecOn.eq` minor's body by simulating Lean's
    `cases + refl` tactic flow. Returns `λ non_ih_fields. proof` where
    `proof` has type `∀ eq_0 ... eq_{n-1} ∀ heq. outer_eq_body`. Returns
    `none` on any structural precondition violation (propagates as the
    indexed-eq construction falling back to the non-indexed path). -/
def buildMinorViaCasesSim (ctorIdx : Nat) (nonIhDecls : Array LocalDecl)
    (retArgs : Array Expr) (ctorApplied : Expr) (outerEqBody : Expr)
    (indexFvars : Array Expr) (indexDecls : Array LocalDecl)
    (indexSortLevels : Array Level) (outerMajor : Expr) (majorType : Expr)
    (majorLevel : Level) (paramFvars motiveFvars fFvars : Array Expr)
    (idxIsHeq : Array Bool) : Option Expr := Id.run do
  let nIndices := indexDecls.size

  -- Extract fvar names for outer indices and major.
  let indexFvarNames : Array Name := indexFvars.filterMap fun e =>
    match e with
    | .fvar n _ => some n
    | _ => none
  if indexFvarNames.size != nIndices then
    return none
  let outerMajorName ← match outerMajor with
    | .fvar n _ => pure n
    | _ => return none

  let idxSort := fun (i : Nat) =>
    (indexSortLevels[i]?).getD (Level.mkSucc Level.mkZero)

  -- Build eq/heq binder decls for each index, mirroring `mw_decls`'s
  -- per-index choice (via `idxIsHeq`). When the motive used `HEq` (types
  -- not defEq), the casesOn-applied position specializes the ret-side
  -- type by substituting `outer_idx[j] → ret[j]` for `j < i`.
  let mut eqDecls : Array LocalDecl := #[]
  let mut eqRetTypes : Array Expr := #[]
  for i in [0:nIndices] do
    let eqTy ←
      if idxIsHeq[i]! then do
        let mut retType := indexDecls[i]!.domain
        for j in [0:i] do
          if let .fvar outerName _ := indexFvars[j]! then
            retType := substFVar retType outerName retArgs[j]!
        eqRetTypes := eqRetTypes.push retType
        pure (mkHeq (idxSort i) indexDecls[i]!.domain indexFvars[i]! retType
          retArgs[i]!)
      else do
        eqRetTypes := eqRetTypes.push indexDecls[i]!.domain
        pure (mkEq (idxSort i) indexDecls[i]!.domain indexFvars[i]!
          retArgs[i]!)
    let (fvName, _) := freshFVar s!"ieq_eq_c{ctorIdx}" i
    eqDecls := eqDecls.push
      { fvarName := fvName, binderName := Name.mkStr .mkAnon "h",
        domain := eqTy, info := .default }

  -- The heq binder decl.
  let ctorRetType := buildSpecializedMajorType majorType indexFvars retArgs
  let heqTy := mkHeq majorLevel majorType outerMajor ctorRetType ctorApplied
  let (heqName, _) := freshFVar s!"ieq_heq_c{ctorIdx}" 0
  let heqDecl : LocalDecl :=
    { fvarName := heqName, binderName := Name.mkStr .mkAnon "h_m",
      domain := heqTy, info := .default }

  -- fvar_order for symm determination. Canonical introduction order:
  -- params < motives < F's < outer_idxs < outer_major < non_ih.
  let mut fvarOrder : Std.HashMap Name Nat := {}
  let mut orderCounter := 0
  for fv in paramFvars ++ motiveFvars ++ fFvars do
    if let .fvar name _ := fv then
      fvarOrder := fvarOrder.insert name orderCounter
      orderCounter := orderCounter + 1
  for name in indexFvarNames do
    fvarOrder := fvarOrder.insert name orderCounter
    orderCounter := orderCounter + 1
  fvarOrder := fvarOrder.insert outerMajorName orderCounter
  orderCounter := orderCounter + 1
  for d in nonIhDecls do
    fvarOrder := fvarOrder.insert d.fvarName orderCounter
    orderCounter := orderCounter + 1

  -- The full remaining-binder list: eq_0 ... eq_{n-1}, heq. Each binder
  -- is Eq or HEq per `idxIsHeq[i]` (must match `eqDecls`).
  let mut remaining : Array (EqBinderKind × LocalDecl) := #[]
  for (decl, i) in eqDecls.zipIdx do
    let kind :=
      if idxIsHeq[i]! then
        EqBinderKind.heq indexDecls[i]!.domain indexFvars[i]! eqRetTypes[i]!
          retArgs[i]! (idxSort i)
      else
        EqBinderKind.eq indexDecls[i]!.domain indexFvars[i]! retArgs[i]!
          (idxSort i)
    remaining := remaining.push (kind, decl)
  let heqKind := EqBinderKind.heq majorType outerMajor ctorRetType
    ctorApplied majorLevel
  remaining := remaining.push (heqKind, heqDecl)

  -- local_context — outer fvars visible at the start of the minor,
  -- ordered by introduction: outer indices, major, non-IH fields.
  let mut localContext : Array LocalDecl := #[]
  for (idxDecl, i) in indexDecls.zipIdx do
    if let .fvar fname _ := indexFvars[i]! then
      localContext := localContext.push
        { fvarName := fname, binderName := idxDecl.binderName,
          domain := idxDecl.domain, info := idxDecl.info }
  if let .fvar majName _ := outerMajor then
    localContext := localContext.push
      { fvarName := majName, binderName := Name.mkStr .mkAnon "t",
        domain := majorType, info := .default }
  for d in nonIhDecls do
    localContext := localContext.push d

  -- Recursively build the proof term.
  let some proof := buildProofForRemaining remaining.toList outerEqBody
      localContext fvarOrder ctorIdx 0
    | return none

  -- Wrap with `λ non_ih_fields` — the outer intros of `inductionCasesOn`.
  return some (mkLambda proof nonIhDecls)

/-! ## Indexed-inductive `.brecOn.eq` value construction (brecon.rs:1718) -/

/-- Mirrors Rust `build_indexed_eq_value` (brecon.rs:1747).

    Build the value of `.brecOn.eq` for an indexed inductive — replicates
    the output of Lean's `cases` tactic applied to an indexed inductive:
    `generalizeIndices` followed by `casesOn` with one `refl` per case
    (`refs/lean4/src/Lean/Meta/Tactic/Cases.lean`).

    (Rust also receives `_motive_decls`/`_ctor_counts`, both unused —
    dropped here.) -/
def buildIndexedEqValue (ci : Nat) (targetCtors : Array Name)
    (breconName goName : Name) (recUnivs : Array Level)
    (paramFvars motiveFvars indexFvars : Array Expr)
    (indexDecls : Array LocalDecl) (indexSortLevels : Array Level)
    (majorFvars : Array Expr) (majorDecls : Array LocalDecl)
    (fFvars : Array Expr) (allDecls : Array LocalDecl)
    (minorDoms : Array Expr) (minorOffset : Nat)
    (elimLevel majorLevel : Level) (casesOnName : Name)
    (casesOnUnivs : Array Level) (casesOnSpecParams : Array Expr)
    (recLevelParams : Array Name) (maps : AddrMaps)
    : KBridgeM (Option Expr) := do
  let nIndices := indexDecls.size
  let outerMajor := majorFvars[0]!
  let majorType := majorDecls[0]!.domain
  -- Defensive: one level per index decl, else fall back to `Sort 1` (the
  -- historical hard-coded value) rather than panicking.
  let idxSort := fun (i : Nat) =>
    (indexSortLevels[i]?).getD (Level.mkSucc Level.mkZero)

  -- Validate that `indexFvars` are all FVars — required for `fvar_order`
  -- tracking in `buildMinorViaCasesSim`'s symm determination.
  let nFvarIndices := indexFvars.foldl
    (fun acc e => if e matches .fvar .. then acc + 1 else acc) 0
  if nFvarIndices != nIndices then
    return none
  -- Validate that `outerMajor` is a FVar (same requirement).
  if !(outerMajor matches .fvar ..) then
    return none

  -- OUTER_Eq_body: `Eq (motive outer_idxs outer_major) (brecOn …) (F_1 …)`
  let outerEqBody := Id.run do
    let allFvarsOuter : Array Expr :=
      paramFvars ++ motiveFvars ++ indexFvars ++ #[outerMajor] ++ fFvars
    let breconApp := mkAppN (mkConst breconName recUnivs) allFvarsOuter
    let goApp := mkAppN (mkConst goName recUnivs) allFvarsOuter
    let goSnd := Expr.mkProj (Name.mkStr .mkAnon "PProd") 1 goApp
    let motiveCiApp := mkAppN (mkAppN motiveFvars[ci]! indexFvars)
      #[outerMajor]
    let mut fCiApp := fFvars[ci]!
    fCiApp := mkAppN fCiApp indexFvars
    fCiApp := Expr.mkApp fCiApp outerMajor
    fCiApp := Expr.mkApp fCiApp goSnd
    return mkEq elimLevel motiveCiApp breconApp fCiApp

  -- --- motive_wrapped: λ new_idxs new_major. ∀h_i. ∀h_major. OUTER_Eq_body
  --
  -- For dependently-indexed inductives, the TYPE of a later index depends
  -- on EARLIER indices: substitute `outer_idx_j → new_idx_fvar_j` for
  -- `j < i` when building each `new_idx_i`'s domain (matching Lean's
  -- `generalizeIndices`).
  let mut newIdxDecls : Array LocalDecl := #[]
  let mut newIdxFvars : Array Expr := #[]
  for (idxDecl, i) in indexDecls.zipIdx do
    let (fvName, fv) := freshFVar "ieq_ni" i
    let mut freshDomain := idxDecl.domain
    for j in [0:i] do
      if let .fvar outerName _ := indexFvars[j]! then
        freshDomain := substFVar freshDomain outerName newIdxFvars[j]!
    newIdxDecls := newIdxDecls.push
      { fvarName := fvName, binderName := idxDecl.binderName,
        domain := freshDomain, info := idxDecl.info }
    newIdxFvars := newIdxFvars.push fv
  let newMajorType := buildSpecializedMajorType majorType indexFvars
    newIdxFvars
  let (newMajorName, newMajorFvar) := freshFVar "ieq_nm" 0
  let newMajorDecl : LocalDecl :=
    { fvarName := newMajorName, binderName := Name.mkStr .mkAnon "x",
      domain := newMajorType, info := .default }

  -- Decide between `Eq` and `HEq` for each index's equality binder,
  -- matching Lean's `mkEqAndProof`
  -- (`refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-37`): `isDefEq` on
  -- the outer and new index types decides — Eq if defEq, HEq otherwise.
  let eqTc ← TcScopeSt.new allDecls recLevelParams maps
  let mut idxIsHeq : Array Bool := #[]
  let mut idxNewTypes : Array Expr := #[]
  let mut mwDecls : Array LocalDecl := #[]
  for (idxDecl, i) in indexDecls.zipIdx do
    let outerType := idxDecl.domain
    let newType := newIdxDecls[i]!.domain
    let typesDefeq ← eqTc.isDefEq outerType newType
    let eqTy :=
      if typesDefeq then
        mkEq (idxSort i) outerType indexFvars[i]! newIdxFvars[i]!
      else
        mkHeq (idxSort i) outerType indexFvars[i]! newType newIdxFvars[i]!
    let (hName, _) := freshFVar "ieq_h" i
    mwDecls := mwDecls.push
      { fvarName := hName, binderName := Name.mkStr .mkAnon "h",
        domain := eqTy, info := .default }
    idxIsHeq := idxIsHeq.push !typesDefeq
    idxNewTypes := idxNewTypes.push newType
  -- (Rust `drop(eq_tc)` — a no-op here; the next `TcScopeSt.new` resets.)
  let heqTy := mkHeq majorLevel majorType outerMajor newMajorType
    newMajorFvar
  let (hmName, _) := freshFVar "ieq_hm" 0
  mwDecls := mwDecls.push
    { fvarName := hmName, binderName := Name.mkStr .mkAnon "h",
      domain := heqTy, info := .default }
  let mwBody := mkForall outerEqBody mwDecls
  let motiveBinders : Array LocalDecl := newIdxDecls.push newMajorDecl
  let motiveWrapped := mkLambda mwBody motiveBinders

  -- --- casesOn head with params + motive + outer indices + outer major
  let mut eqVal := mkConst casesOnName casesOnUnivs
  if !casesOnSpecParams.isEmpty then
    eqVal := mkAppN eqVal casesOnSpecParams
  else
    eqVal := mkAppN eqVal paramFvars
  eqVal := Expr.mkApp eqVal motiveWrapped
  eqVal := mkAppN eqVal indexFvars
  eqVal := Expr.mkApp eqVal outerMajor

  -- --- Each minor via `buildMinorViaCasesSim` (Lean's `cases + refl`
  -- from `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:288-300`).
  for (_ctorName, ctorIdx) in targetCtors.zipIdx do
    let mi := minorOffset + ctorIdx
    if mi >= minorDoms.size then
      break
    let minorDom := minorDoms[mi]!

    -- Open the minor's field binders, filter to non-IH (casesOn strips
    -- IH). Head-reduce field domains — same rationale as
    -- `build_below_minor`.
    let nMinorFields := countForalls minorDom
    let (_mfieldFvars, mfieldDecls0, minorRet) :=
      forallTelescope minorDom nMinorFields s!"ieqf{mi}" 0
    let mfieldDecls := mfieldDecls0.map fun d =>
      { d with domain := betaReduce d.domain }
    let nonIhDecls : Array LocalDecl := mfieldDecls.filter fun d =>
      (findMotiveFVar d.domain motiveFvars).isNone

    -- Ctor's return-indices from `minorRet` (`motive_ci <ret_idxs>
    -- <major>` — first `nIndices` args after the motive head).
    let (_, minorRetArgs) := decomposeApps minorRet
    if minorRetArgs.size < nIndices then
      return none
    let retArgs := minorRetArgs.extract 0 nIndices

    -- `C (spec_params|params) non_ih_fields`.
    let ctorName := targetCtors[ctorIdx]!
    let ctorUnivs : Array Level :=
      if !casesOnSpecParams.isEmpty then
        casesOnUnivs.extract 1 casesOnUnivs.size
      else
        recUnivs.extract 1 recUnivs.size
    let mut ctorApplied := mkConst ctorName ctorUnivs
    if !casesOnSpecParams.isEmpty then
      ctorApplied := mkAppN ctorApplied casesOnSpecParams
    else
      ctorApplied := mkAppN ctorApplied paramFvars
    for decl in nonIhDecls do
      ctorApplied := Expr.mkApp ctorApplied (Expr.mkFVar decl.fvarName)

    let some minorValue := buildMinorViaCasesSim ctorIdx nonIhDecls retArgs
        ctorApplied outerEqBody indexFvars indexDecls indexSortLevels
        outerMajor majorType majorLevel paramFvars motiveFvars fFvars
        idxIsHeq
      | return none

    eqVal := Expr.mkApp eqVal minorValue

  -- --- Discharge Eq/HEq generalizations with the matching refl
  -- (`refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-47`).
  for (pair, i) in (indexDecls.zip indexFvars).zipIdx do
    let (idxDecl, idxFv) := pair
    let refl :=
      if idxIsHeq[i]! then
        mkHeqRefl (idxSort i) idxDecl.domain idxFv
      else
        mkEqRefl (idxSort i) idxDecl.domain idxFv
    eqVal := Expr.mkApp eqVal refl
  eqVal := Expr.mkApp eqVal (mkHeqRefl majorLevel majorType outerMajor)

  return some (mkLambda eqVal allDecls)

/-! ## Type-level `.brecOn.eq` (brecon.rs:1396) -/

/-- Mirrors Rust `build_type_brecon_eq_fvar` (brecon.rs:1401).

    Build `.brecOn.eq` type and value (FVar-based).
    Type: `∀ binders, @Eq (motive_ci args) (brecOn args) (F_ci args (go args).2)`
    Value: recursor-based case-split proof with Eq.refl minors (simple
    path), or the cases-sim indexed construction.

    `majorLevel` is the major's sort level — the `u` in `HEq.{u}` /
    `Eq.ndrec.{_, u}` etc. that generalize the major premise.

    (Rust also receives `_rec_val`/`_param_decls`/`_f_decls`/
    `_below_names`/`n_minors`, all unused — dropped here.) -/
def buildTypeBreconEqFvar (ci : Nat) (targetIndName breconName goName : Name)
    (recUnivs : Array Level) (paramFvars motiveFvars : Array Expr)
    (motiveDecls : Array LocalDecl) (indexFvars : Array Expr)
    (indexDecls : Array LocalDecl) (indexSortLevels : Array Level)
    (majorFvars : Array Expr) (majorDecls : Array LocalDecl)
    (fFvars : Array Expr) (allDecls : Array LocalDecl)
    (allFvars : Array Expr) (minorDoms : Array Expr) (motiveCiApp : Expr)
    (elimLevel majorLevel : Level) (casesOnSpecParams : Array Expr)
    (recLevelParams : Array Name) (maps : AddrMaps)
    : KBridgeM (Expr × Expr) := do
  let majorFvar := majorFvars[0]!

  -- --- Type ---
  -- @Eq.{elim_level} motive_ci_app (brecOn all_fvars)
  --   (F_ci indices major (go all_fvars).2)
  let breconApp := mkAppN (mkConst breconName recUnivs) allFvars
  let goApp := mkAppN (mkConst goName recUnivs) allFvars
  let goSnd := Expr.mkProj (Name.mkStr .mkAnon "PProd") 1 goApp

  let mut fCiApp := fFvars[ci]!
  fCiApp := mkAppN fCiApp indexFvars
  fCiApp := Expr.mkApp fCiApp majorFvar
  fCiApp := Expr.mkApp fCiApp goSnd

  let eqTypeBody := Expr.mkApp
    (Expr.mkApp
      (Expr.mkApp (mkConst (Name.mkStr .mkAnon "Eq") #[elimLevel])
        motiveCiApp)
      breconApp)
    fCiApp
  let eqType := mkForall eqTypeBody allDecls

  -- Target constructor list and counts (shared by both value paths).
  let mut ctorCounts : Array Nat := #[]
  for md in motiveDecls do
    let mut ty := md.domain
    let mut lastDom := ty
    repeat
      match ty with
      | .forallE _ dom body _ _ =>
        lastDom := dom
        ty := body
      | _ => break
    let (head, _) := decomposeApps lastDom
    let count ← match head with
      | .const name _ _ | .fvar name _ =>
        match ← lookupConst? name with
        | some (.inductInfo v) => pure v.ctors.size
        | _ => pure 0
      | _ => pure (0 : Nat)
    ctorCounts := ctorCounts.push count
  let targetCtors : Array Name ← match ← lookupConst? targetIndName with
    | some (.inductInfo v) => pure v.ctors
    | _ => pure #[]
  let minorOffset : Nat := (ctorCounts.extract 0 ci).foldl (· + ·) 0

  -- casesOn universe args (shared between simple and indexed paths).
  let eqCasesUnivs : Array Level := Id.run do
    let (head, _) := decomposeApps majorDecls[0]!.domain
    if let .const _ lvls _ := head then
      return #[Level.mkZero] ++ lvls
    else
      return #[Level.mkZero] ++ recUnivs.extract 1 recUnivs.size
  let casesOnName := Name.mkStr targetIndName "casesOn"

  -- --- Indexed path (brecon.rs:1531-1579) ---
  let nIndices := indexDecls.size
  if nIndices > 0 then
    let eqValueOpt ← buildIndexedEqValue ci targetCtors breconName goName
      recUnivs paramFvars motiveFvars indexFvars indexDecls
      indexSortLevels majorFvars majorDecls fFvars allDecls minorDoms
      minorOffset elimLevel majorLevel casesOnName eqCasesUnivs
      casesOnSpecParams recLevelParams maps
    if let some eqValue := eqValueOpt then
      return (eqType, eqValue)
    -- Fall through to the simple path if the indexed construction
    -- couldn't be completed (e.g., missing ctor info).

  -- --- Simple value path (non-indexed) ---
  -- Build via casesOn (matching Lean's `cases` tactic + `refl`).
  -- casesOn binder order: params, motive, indices, major, minors.
  let mut eqVal := mkConst casesOnName eqCasesUnivs

  if !casesOnSpecParams.isEmpty then
    -- Nested auxiliary: the spec params cover the casesOn's param slots.
    eqVal := mkAppN eqVal casesOnSpecParams
  else
    -- Original member: apply block params as casesOn params.
    eqVal := mkAppN eqVal paramFvars

  -- Apply target motive (only one motive in casesOn):
  -- λ targs => @Eq (motive_ci targs) (brecOn ... targs ...)
  --   (F_ci targs (go ... targs ...).2)
  let eqMotiveLam := Id.run do
    let mt := motiveDecls[ci]!.domain
    let nma := countForalls mt
    let (targFvars, targDecls, _) := forallTelescope mt nma "tbeqmc" 0

    let innerAll : Array Expr :=
      paramFvars ++ motiveFvars ++ targFvars ++ fFvars
    let innerBrecon := mkAppN (mkConst breconName recUnivs) innerAll
    let innerGo := mkAppN (mkConst goName recUnivs) innerAll
    let innerGoSnd := Expr.mkProj (Name.mkStr .mkAnon "PProd") 1 innerGo
    let mut innerFCi := fFvars[ci]!
    innerFCi := mkAppN innerFCi targFvars
    innerFCi := Expr.mkApp innerFCi innerGoSnd

    let innerMotiveApp := mkAppN motiveFvars[ci]! targFvars

    let eqMotiveBody := Expr.mkApp
      (Expr.mkApp
        (Expr.mkApp (mkConst (Name.mkStr .mkAnon "Eq") #[elimLevel])
          innerMotiveApp)
        innerBrecon)
      innerFCi

    return mkLambda eqMotiveBody targDecls
  eqVal := Expr.mkApp eqVal eqMotiveLam

  -- Apply indices and major (in casesOn these come BEFORE minors).
  eqVal := mkAppN eqVal indexFvars
  eqVal := Expr.mkApp eqVal majorFvar

  -- Apply target minors only; each minor body is Eq.refl.
  for (_ctorName, ctorIdx) in targetCtors.zipIdx do
    let mi := minorOffset + ctorIdx
    if mi >= minorDoms.size then
      break
    let minorDom := minorDoms[mi]!

    -- Open minor fields; head-reduce (same rationale as
    -- `build_below_minor`); filter to non-IH (casesOn strips IH).
    let nMinorFields := countForalls minorDom
    let (_mfieldFvars, mfieldDecls0, minorRet) :=
      forallTelescope minorDom nMinorFields s!"tbeqf{mi}" 0
    let mfieldDecls := mfieldDecls0.map fun d =>
      { d with domain := betaReduce d.domain }
    let nonIhDecls : Array LocalDecl := mfieldDecls.filter fun d =>
      (findMotiveFVar d.domain motiveFvars).isNone

    -- @Eq.refl.{elim_level} (motive_ci ctor_ret_args)
    --   (brecOn ... ctor_ret_args ...)
    let (_, ctorRetArgs) := decomposeApps minorRet

    let innerAll : Array Expr :=
      paramFvars ++ motiveFvars ++ ctorRetArgs ++ fFvars
    let innerBrecon := mkAppN (mkConst breconName recUnivs) innerAll
    let motiveApp := mkAppN motiveFvars[ci]! ctorRetArgs

    let minorBody := Expr.mkApp
      (Expr.mkApp
        (mkConst (Name.mkStr (Name.mkStr .mkAnon "Eq") "refl") #[elimLevel])
        motiveApp)
      innerBrecon

    eqVal := Expr.mkApp eqVal (mkLambda minorBody nonIhDecls)

  let eqValue := mkLambda eqVal allDecls
  return (eqType, eqValue)

/-! ## Type-level minor premises (brecon.rs:1092) -/

/-- Mirrors Rust `replace_motive_with_pprod_fvar` (brecon.rs:1232).

    Replace a motive application with PProd(motive, below) (FVar-based).
    If `dom` is `motive_j args`, produce
    `PProd (motive_j args) (below_j params motives args)`; handles forall
    wrapping. -/
def replaceMotiveWithPProdFvar (dom : Expr)
    (paramFvars motiveFvars : Array Expr) (belowNames : Array Name)
    (recUnivs : Array Level) (rtc : TcScopeSt)
    : KBridgeM (Expr × TcScopeSt) := do
  let nInner := countForalls dom
  let (_innerFvars, innerDecls, leaf) := forallTelescope dom nInner "tpp" 0

  let some jPrime := findMotiveFVar leaf motiveFvars
    | throw (CompileError.unsupportedExpr
        "brecOn pprod: leaf expression has no motive fvar head")
  let (_, args) := decomposeApps leaf

  -- motive_app: motiveFvars[j'] args
  let mut motiveApp := motiveFvars[jPrime]!
  for a in args do
    motiveApp := Expr.mkApp motiveApp a

  -- below_app: belowNames[j'] params motives args
  let mut belowApp := mkConst belowNames[jPrime]! recUnivs
  belowApp := mkAppN belowApp paramFvars
  belowApp := mkAppN belowApp motiveFvars
  for a in args do
    belowApp := Expr.mkApp belowApp a

  -- Infer PProd levels via TC, matching Lean's mkPProd (PProdN.lean:37-38).
  let mut rtc := rtc
  if !innerDecls.isEmpty then
    rtc ← rtc.pushLocals innerDecls
  let lvl1 ← rtc.getLevel motiveApp
  let lvl2 ← rtc.getLevel belowApp
  if !innerDecls.isEmpty then
    rtc ← rtc.popLocals innerDecls

  let pprod := mkPProd lvl1 lvl2 motiveApp belowApp

  return (if innerDecls.isEmpty then pprod else mkForall pprod innerDecls,
    rtc)

/-- Mirrors Rust `build_type_minor_premise_fvar` (brecon.rs:1098).

    Build a Type-level brecOn minor premise (FVar-based). For each IH
    field: replaces domain with PProd(motive, below), creates
    PProdN-packed body with `PProd.mk (F_j args b) b`.

    `rlvl` is the single level derived from the recursor's single major
    premise — Lean's `buildBRecOnMinorPremise` threads this one value
    through all minors (NOT specialised per motive). -/
def buildTypeMinorPremiseFvar (minorDom : Expr)
    (paramFvars motiveFvars fFvars : Array Expr) (belowNames : Array Name)
    (recUnivs : Array Level) (rlvl : Level) (rtc : TcScopeSt)
    : KBridgeM (Expr × TcScopeSt) := do
  let nFields := countForalls minorDom
  let (fieldFvars, fieldDecls0, returnType) :=
    forallTelescope minorDom nFields "tmf" 0

  -- Head-reduce field domains to match Lean's stored .brecOn.go shape
  -- (same rationale as `build_below_minor` — `mkLambdaFVars` normalises
  -- lambda-application redexes in field binder types).
  let fieldDecls := fieldDecls0.map fun d =>
    { d with domain := betaReduce d.domain }

  -- Which class the return type targets.
  let some retMotiveIdx := findMotiveFVar returnType motiveFvars
    | throw (CompileError.unsupportedExpr
        "brecOn minor: return type has no motive fvar head")

  -- Classify fields and build modified binders.
  let mut lambdaDecls : Array LocalDecl := #[]
  let mut lambdaFvars : Array Expr := #[]
  -- (fvar, lambda_index) for IH fields
  let mut prodEntries : Array (Expr × Nat) := #[]
  let mut rtc := rtc

  for (pair, fi) in (fieldDecls.zip fieldFvars).zipIdx do
    let (decl, fvar) := pair
    if (findMotiveFVar decl.domain motiveFvars).isSome then
      -- IH field: replace domain with PProd(motive, below).
      let (pprodDom, rtc') ← replaceMotiveWithPProdFvar decl.domain
        paramFvars motiveFvars belowNames recUnivs rtc
      rtc := rtc'
      let (ihFvName, ihFv) := freshFVar "tmih" fi
      lambdaDecls := lambdaDecls.push
        { fvarName := ihFvName, binderName := decl.binderName,
          domain := pprodDom, info := decl.info }
      lambdaFvars := lambdaFvars.push ihFv
      prodEntries := prodEntries.push (ihFv, lambdaDecls.size - 1)
    else
      lambdaDecls := lambdaDecls.push decl
      lambdaFvars := lambdaFvars.push fvar

  -- PProdN.mk of prod entries (right-fold of VALUES). Lean's mkPProdMk
  -- (PProdN.lean:44-53) infers universe levels via getLevel — push the
  -- lambda decls (with replaced IH domains) so FVars resolve.
  rtc ← rtc.pushLocals lambdaDecls

  let (b, bType) ←
    if prodEntries.isEmpty then
      -- PUnit.{rlvl} : Sort rlvl
      pure (mkPUnitUnit rlvl, punitConst rlvl)
    else if prodEntries.size == 1 then
      let (fv, declIdx) := prodEntries[0]!
      pure (fv, lambdaDecls[declIdx]!.domain)
    else do
      -- Right-fold with mkPProdMk, inferring levels per-pair via TC.
      let lastIdx := prodEntries.size - 1
      let (lastFv, lastDeclIdx) := prodEntries[lastIdx]!
      let mut foldVal := lastFv
      let mut foldTy := lambdaDecls[lastDeclIdx]!.domain
      for (fv, declIdx) in (prodEntries.extract 0 lastIdx).reverse do
        let fvTy := lambdaDecls[declIdx]!.domain
        let fvSort ← rtc.getLevel fvTy
        let foldSort ← rtc.getLevel foldTy
        let packed := mkPProdMk fvSort foldSort fvTy foldTy fv foldVal
        let packedTy := mkPProd fvSort foldSort fvTy foldTy
        foldVal := packed
        foldTy := packedTy
      pure (foldVal, foldTy)

  -- Conclusion: PProd.mk (F_{ret_idx} ret_args b) b
  let (_, retArgs) := decomposeApps returnType

  let mut fApp := fFvars[retMotiveIdx]!
  for a in retArgs do
    fApp := Expr.mkApp fApp a
  fApp := Expr.mkApp fApp b

  -- motive_ci ret_args — the type of (F ret_args b).
  let motiveApp := mkAppN motiveFvars[retMotiveIdx]! retArgs

  -- Outer PProd.mk wraps (F result, b); levels via TC (PProdN.lean:44-53).
  let lvlA ← rtc.getLevel motiveApp
  let lvlB ← rtc.getLevel bType
  let body := mkPProdMk lvlA lvlB motiveApp bType fApp b

  rtc ← rtc.popLocals lambdaDecls

  return (mkLambda body lambdaDecls, rtc)

/-! ## Type-level brecOn (brecon.rs:592) -/

/-- Mirrors Rust `build_type_brecon_fvar` (brecon.rs:618).

    Build Type-level `.brecOn.go`, `.brecOn`, and `.brecOn.eq`
    (FVar-based). Generic over any recursor in the flat block: works for
    both original class recursors (`ci < nClasses`) and nested auxiliary
    recursors (`ci >= nClasses`).

    `breconName`: the output name (e.g., `I.brecOn` or `I.brecOn_1`);
    `ci`: the target motive index in the flat block; `_all0`: `all[0]`
    from the first inductive (unused, mirroring Rust's `let _ = all0`). -/
def buildTypeBreconFvar (ci : Nat) (recVal : RecursorVal)
    (breconName : Name) (_all0 : Name) (belowNames : Array Name)
    (nClasses : Nat) (maps : AddrMaps) : KBridgeM (Array BRecOnDef) := do
  -- canon_kenv is populated by `populateCanonKenvWithBelow` between
  -- Phase 2 and Phase 3: PUnit, PProd, parent inductives, canonical
  -- `.below` types.
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices
  let recLevelParams := recVal.cnst.levelParams
  -- Inductive-only level params (rec has [elim_level, ind_levels...]).
  let indLevelParams := recLevelParams.extract 1 recLevelParams.size

  let goName := Name.mkStr breconName "go"
  let eqName := Name.mkStr breconName "eq"

  let elimLevel := Level.mkParam recLevelParams[0]!

  -- below_names for each motive position in the canonical flat block —
  -- supplied by the caller (from `belowConsts`), Lean-source-indexed.
  if belowNames.size != nMotives then
    throw (CompileError.invalidMutualBlock
      s!"build_type_brecon_fvar({breconName.pretty}): {belowNames.size} \
below constants for {nMotives} recursor motives")

  let recUnivs : Array Level := recLevelParams.map Level.mkParam

  -- --- Phase 1: Open rec type into FVars ---
  let (paramFvars, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "tbp" 0

  let mut motiveFvars : Array Expr := #[]
  let mut motiveDecls : Array LocalDecl := #[]
  let mut afterMotives := afterParams
  for mi in [0:nMotives] do
    if let .forallE name dom body _ _ := afterMotives then
      let (fvName, fv) := freshFVar "tbm" mi
      motiveDecls := motiveDecls.push
        { fvarName := fvName, binderName := name, domain := dom,
          info := .implicit }
      motiveFvars := motiveFvars.push fv
      afterMotives := instantiate1 body fv

  -- Open minors (keep FVar-based domains for building modified minors).
  let mut minorDoms : Array Expr := #[]
  let mut afterMinors := afterMotives
  for mi in [0:nMinors] do
    if let .forallE _ dom body _ _ := afterMinors then
      minorDoms := minorDoms.push dom
      let (_, dummy) := freshFVar "tbx" mi
      afterMinors := instantiate1 body dummy

  let (indexFvars, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "tbi" 0
  let (majorFvars, majorDecls, _) :=
    forallTelescope afterIndices 1 "tbj" 0
  let majorFvar := majorFvars[0]!

  -- Per-motive rlvl: each member of the flat block may live in a
  -- different universe. Lean (BRecOn.lean:215-220) computes ilvl via
  -- `inferType (← inferType major)` then `rlvl = mkLevelMax ilvl lvl`.
  -- TcScope::get_level on the major domain from each motive's type
  -- performs the same inferType + ensure_sort sequence. On failure,
  -- propagate — a TC failure here is almost always a missing canon_kenv
  -- dependency (see the Rust comment at brecon.rs:717-737).
  let ilvls : Array Level ← do
    let ilvlCtx : Array LocalDecl := paramDecls ++ motiveDecls
    let mut ilvlTc ← TcScopeSt.new ilvlCtx recLevelParams maps
    let mut out : Array Level := #[]
    for md in motiveDecls do
      -- Peel foralls from the motive type to find the major domain,
      -- then infer its sort level via TC.
      let nMotiveArgs := countForalls md.domain
      let (_ifvs, idcls, _) :=
        forallTelescope md.domain nMotiveArgs "ilvl_m" 0
      -- The major domain is the last binder's domain.
      let majorDom := match idcls.back? with
        | some last => last.domain
        | none => md.domain
      ilvlTc ← ilvlTc.pushLocals idcls
      let ilvlJ ←
        try
          ilvlTc.getLevel majorDom
        catch e =>
          throw (CompileError.unsupportedExpr
            s!"brecOn ilvl inference failed for motive at class {ci}: \
TcScope::get_level on major domain returned {e}. This typically means \
`canon_kenv` is missing a required inductive — check that Phase 2 \
(populate_canon_kenv_with_below) ran before brecOn generation")
      ilvlTc ← ilvlTc.popLocals idcls
      out := out.push ilvlJ
    pure out
  -- Match Lean's BRecOn.lean:220: `mkLevelMax ilvl lvl` — raw Level.max
  -- with only zero elimination.
  let rlvls : Array Level := ilvls.map fun ilvlJ =>
    if ilvlJ matches .zero _ then elimLevel
    else if elimLevel matches .zero _ then ilvlJ
    else Level.mkMax ilvlJ elimLevel
  -- The target's rlvl is used for the rec universe arg and go return type.
  let rlvl := rlvls[ci]!
  let ilvl := ilvls[ci]!

  -- --- Phase 2: Build F binders ---
  -- F_j : ∀ targs, I_j.below params motives targs → motive_j targs
  let mut fFvars : Array Expr := #[]
  let mut fDecls : Array LocalDecl := #[]

  for j in [0:nMotives] do
    let motiveType := motiveDecls[j]!.domain
    let nMotiveArgs := countForalls motiveType
    let (innerFvars, innerDecls, _) :=
      forallTelescope motiveType nMotiveArgs s!"tbfa{j}" 0

    -- below_app: I_j.below params motives inner_fvars
    let belowApp := mkAppN
      (mkAppN (mkAppN (mkConst belowNames[j]! recUnivs) paramFvars)
        motiveFvars)
      innerFvars

    -- motive_app: motiveFvars[j] inner_fvars
    let motiveApp := mkAppN motiveFvars[j]! innerFvars

    -- F type: ∀ inner_args, below_app → motive_app
    let (belowFvName, _) := freshFVar s!"tbfb{j}" 0
    let belowDecl : LocalDecl :=
      { fvarName := belowFvName, binderName := Name.mkStr .mkAnon "f",
        domain := belowApp, info := .default }
    let fTypeBinders : Array LocalDecl := innerDecls.push belowDecl
    let fType := mkForall motiveApp fTypeBinders

    let fName := Name.mkStr .mkAnon s!"F_{j + 1}"
    let (fjFvName, fjFv) := freshFVar "tbf" j
    fDecls := fDecls.push
      { fvarName := fjFvName, binderName := fName, domain := fType,
        info := .default }
    fFvars := fFvars.push fjFv

  -- Collect all outer binder decls / fvars.
  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ indexDecls ++ majorDecls ++ fDecls
  let allFvars : Array Expr :=
    paramFvars ++ motiveFvars ++ indexFvars ++ majorFvars ++ fFvars

  -- --- Phase 3: Build .brecOn.go ---

  -- ONE TcScope for the entire .go construction: start with params +
  -- motives; push/pop indices/major/F-binders as needed (matches Lean's
  -- mkPProd/mkPProdMk which infer levels via getLevel).
  let baseCtx : Array LocalDecl := paramDecls ++ motiveDecls
  let mut rtc ← TcScopeSt.new baseCtx recLevelParams maps

  -- go return type:
  -- PProd (motive_ci indices major) (below_ci params motives indices major)
  rtc ← rtc.pushLocals indexDecls
  rtc ← rtc.pushLocals majorDecls

  let motiveCiApp := mkAppN (mkAppN motiveFvars[ci]! indexFvars)
    #[majorFvar]
  let belowCiApp := mkAppN
    (mkAppN
      (mkAppN (mkAppN (mkConst belowNames[ci]! recUnivs) paramFvars)
        motiveFvars)
      indexFvars)
    #[majorFvar]
  let goRetLvl1 ← rtc.getLevel motiveCiApp
  let goRetLvl2 ← rtc.getLevel belowCiApp
  let goRetType := mkPProd goRetLvl1 goRetLvl2 motiveCiApp belowCiApp

  rtc ← rtc.popLocals majorDecls
  rtc ← rtc.popLocals indexDecls

  -- go value: I.rec.{rlvl, lvls...} params [modified_motives]
  --   [modified_minors] indices major
  let mut goUnivs : Array Level := #[rlvl]
  for lp in indLevelParams do
    goUnivs := goUnivs.push (Level.mkParam lp)
  let mut goVal := mkConst recVal.cnst.name goUnivs

  -- Apply params.
  goVal := mkAppN goVal paramFvars

  -- Modified motives: λ targs => PProd(motive_j targs, below_j params
  -- motives targs).
  for j in [0:nMotives] do
    let mt := motiveDecls[j]!.domain
    let nma := countForalls mt
    let (ifvs, idcls, _) := forallTelescope mt nma s!"tbgm{j}" 0

    rtc ← rtc.pushLocals idcls

    let mApp := mkAppN motiveFvars[j]! ifvs
    let bApp := mkAppN
      (mkAppN (mkAppN (mkConst belowNames[j]! recUnivs) paramFvars)
        motiveFvars)
      ifvs
    let mmLvl1 ← rtc.getLevel mApp
    let mmLvl2 ← rtc.getLevel bApp
    let pprodBody := mkPProd mmLvl1 mmLvl2 mApp bApp

    rtc ← rtc.popLocals idcls

    goVal := Expr.mkApp goVal (mkLambda pprodBody idcls)

  -- Push remaining context (indices, major, F-binders) for minors.
  rtc ← rtc.pushLocals indexDecls
  rtc ← rtc.pushLocals majorDecls
  rtc ← rtc.pushLocals fDecls

  -- Modified minors: PProd-packed, all sharing the single target `rlvl`
  -- (Lean computes rlvl once outside the per-minor loop).
  for minorDom in minorDoms do
    let (minor, rtc') ← buildTypeMinorPremiseFvar minorDom paramFvars
      motiveFvars fFvars belowNames recUnivs rlvl rtc
    rtc := rtc'
    goVal := Expr.mkApp goVal minor

  -- Apply indices and major.
  goVal := mkAppN goVal indexFvars
  goVal := Expr.mkApp goVal majorFvar

  let goType := mkForall goRetType allDecls
  let goValue := mkLambda goVal allDecls

  -- --- Phase 4: Build .brecOn ---
  -- brecOn value: Proj("PProd", 0, brecOn.go all_fvars...)
  let goApp := mkAppN (mkConst goName recUnivs) allFvars
  let breconVal := Expr.mkProj (Name.mkStr .mkAnon "PProd") 0 goApp

  let breconType := mkForall motiveCiApp allDecls
  let breconValue := mkLambda breconVal allDecls

  -- --- Phase 5: Build .brecOn.eq ---
  -- Target inductive name from the major premise domain head: for main
  -- inductives the block member; for nested auxiliaries the external
  -- inductive (e.g., List).
  let targetIndName := Id.run do
    let (head, _) := decomposeApps majorDecls[0]!.domain
    match head with
    | .const name _ _ => return name
    | _ => return Name.mkAnon -- eq generation gracefully degrades
  -- For nested auxiliaries, casesOn needs the ext inductive's own params
  -- (spec_params) applied before the block params.
  let casesOnSpec : Array Expr ←
    if ci >= nClasses then do
      let (_, majorArgs) := decomposeApps majorDecls[0]!.domain
      let extNParams ← match ← lookupConst? targetIndName with
        | some (.inductInfo v) => pure v.numParams
        | _ => pure 0
      pure (majorArgs.extract 0 extNParams)
    else
      pure #[]
  -- Per-index sort levels — Lean's `mkEq` calls `getLevel idx_type` per
  -- index (indexed inductives may have index types at any universe).
  -- Compute while the index decls are pushed into the live `rtc` scope.
  let indexSortLevels : Array Level ← do
    rtc ← rtc.pushLocals indexDecls
    let mut out : Array Level := #[]
    for d in indexDecls do
      out := out.push (← rtc.getLevel d.domain)
    rtc ← rtc.popLocals indexDecls
    pure out
  let eqResult ← buildTypeBreconEqFvar ci targetIndName breconName goName
    recUnivs paramFvars motiveFvars motiveDecls indexFvars indexDecls
    indexSortLevels majorFvars majorDecls fFvars allDecls allFvars
    minorDoms motiveCiApp elimLevel ilvl casesOnSpec recLevelParams maps

  -- `.go` / `.brecOn` / `.eq` all reference the parent inductive's
  -- `.rec`, so Lean's `mkDefinitionValInferringUnsafe` /
  -- `mkThmOrUnsafeDef` consistently propagate the recursor's `is_unsafe`.
  let isUnsafe := recVal.isUnsafe

  let mut results : Array BRecOnDef := #[
    { name := goName, levelParams := recLevelParams, typ := goType,
      value := goValue, isUnsafe, isProp := false },
    { name := breconName, levelParams := recLevelParams,
      typ := breconType, value := breconValue, isUnsafe,
      isProp := false }]

  let (eqTyp, eqVal) := eqResult
  results := results.push
    { name := eqName, levelParams := recLevelParams, typ := eqTyp,
      value := eqVal, isUnsafe, isProp := false }

  return results

/-! ## Prop-level brecOn (brecon.rs:208) -/

/-- Mirrors Rust `build_prop_below_minor_fvar` (brecon.rs:493).

    Build a Prop-level below minor for one constructor (FVar-based).
    Given minor domain `∀ (fields...) (ih_fields...), motive_j
    (ctor_args)` builds `λ (fields_and_ihs) => below_ctor params motives
    args`; for each IH field the binder domain becomes
    `I_{j'}.below params motives args` (forall-wrapped for reflexive IHs)
    and the below-ctor gains (ih, proof) args. -/
def buildPropBelowMinorFvar (minorDom : Expr) (belowCtorName : Name)
    (paramFvars motiveFvars fFvars : Array Expr) (belowNames : Array Name)
    (indUnivs : Array Level) : Expr := Id.run do
  -- Open all minor fields; field domains reference motive FVars directly.
  let nFields := countForalls minorDom
  let (fieldFvars, fieldDecls, _returnType) :=
    forallTelescope minorDom nFields "pbmf" 0

  -- Classify fields and build lambda binders + ctor args.
  let mut lambdaDecls : Array LocalDecl := #[]
  let mut lambdaFvars : Array Expr := #[]
  let mut ctorArgs : Array Expr := #[]

  for (pair, fi) in (fieldDecls.zip fieldFvars).zipIdx do
    let (decl, fvar) := pair
    match findMotiveFVar decl.domain motiveFvars with
    | some jPrime =>
      -- IH field. Non-reflexive: binder is `I_{j'}.below params motives
      -- args`. Reflexive `∀(inner), motive args`: preserve the forall
      -- structure (`ihTypeToBelowType`, IndPredBelow.lean:71-75).
      let nInnerForalls := countForalls decl.domain
      let (innerFvars, innerDecls, leaf) :=
        forallTelescope decl.domain nInnerForalls s!"pbmp{fi}" 0
      let (_, leafArgs) := decomposeApps leaf

      -- Leaf below application: I_{j'}.below params motives leaf_args.
      let mut belowLeaf := mkConst belowNames[jPrime]! indUnivs
      belowLeaf := mkAppN belowLeaf paramFvars
      belowLeaf := mkAppN belowLeaf motiveFvars
      for a in leafArgs do
        belowLeaf := Expr.mkApp belowLeaf a
      -- Re-wrap with the original foralls (empty for non-reflexive).
      let belowDom := mkForall belowLeaf innerDecls

      -- ih FVar with below domain.
      let (ihFvName, ihFv) := freshFVar "pbmi" fi
      lambdaDecls := lambdaDecls.push
        { fvarName := ihFvName, binderName := Name.mkStr .mkAnon "ih",
          domain := belowDom, info := .default }
      lambdaFvars := lambdaFvars.push ihFv

      -- ih arg for below ctor.
      ctorArgs := ctorArgs.push ihFv

      -- proof arg: `F_{j'}` applied to leaf_args and `ih_fv applied to
      -- inner`. Non-reflexive: F_{j'} leaf_args ih_fv; reflexive:
      -- λ inner, F_{j'} leaf_args (ih_fv inner).
      let proof :=
        if nInnerForalls == 0 then Id.run do
          let mut p := fFvars[jPrime]!
          for a in leafArgs do
            p := Expr.mkApp p a
          return Expr.mkApp p ihFv
        else Id.run do
          let mut p := fFvars[jPrime]!
          for a in leafArgs do
            p := Expr.mkApp p a
          let ihApp := mkAppN ihFv innerFvars
          p := Expr.mkApp p ihApp
          return mkLambda p innerDecls
      ctorArgs := ctorArgs.push proof
    | none =>
      -- Non-IH field: pass through.
      lambdaDecls := lambdaDecls.push decl
      lambdaFvars := lambdaFvars.push fvar
      ctorArgs := ctorArgs.push fvar

  -- below ctor application: below_ctor params motives ctor_args.
  let mut app := mkConst belowCtorName indUnivs
  app := mkAppN app paramFvars
  app := mkAppN app motiveFvars
  app := mkAppN app ctorArgs

  return mkLambda app lambdaDecls

/-- Mirrors Rust `build_prop_brecon` (brecon.rs:223).

    Build Prop-level `.brecOn` for class `ci`:

    ```text
    I_i.brecOn : ∀ {params} {motives} (t : I_i params)
      (F_1 : ∀ majors, I_1.below params motives majors → motive_1 majors)
      ...
      → motive_i t
    I_i.brecOn = λ {params} {motives} t F_1..F_n =>
      F_i t (I_i.rec params below_motives below_minors t)
    ```

    (Rust also receives `_lean_env`, unused — dropped here.) -/
def buildPropBrecon (ci : Nat) (recVal0 : RecursorVal) (ind : InductiveVal)
    (nClasses : Nat) (sortedClasses : Array (Array Name))
    (belowConsts : Array BelowConstant) : KBridgeM BRecOnDef := do
  let nParams := recVal0.numParams
  let nMotives := recVal0.numMotives
  let nMinors := recVal0.numMinors
  let nIndices := ind.numIndices
  let indLevelParams := ind.cnst.levelParams

  -- For Prop brecOn with large elimination (drec), substitute
  -- u -> Level::zero(). Invariant: generate_canonical_recursors always
  -- prepends the elimination level as level_params[0] for large
  -- recursors, so [0] is correct.
  let largeElim := recVal0.cnst.levelParams.size > indLevelParams.size
  let recVal :=
    if largeElim && !recVal0.cnst.levelParams.isEmpty then
      let uParam := recVal0.cnst.levelParams[0]!
      { recVal0 with
        cnst := { recVal0.cnst with
          type := substLevelInExpr recVal0.cnst.type uParam Level.mkZero }
        rules := recVal0.rules.map fun r =>
          { r with rhs := substLevelInExpr r.rhs uParam Level.mkZero } }
    else
      recVal0

  let breconName := Name.mkStr ind.cnst.name "brecOn"

  let belowNames : Array Name := (Array.range nClasses).map fun j =>
    Name.mkStr sortedClasses[j]![0]! "below"

  let mut belowCtorNames : Array (Array Name) := #[]
  for j in [0:nClasses] do
    let some bc := belowConsts[j]?
      | throw (CompileError.unsupportedExpr
          s!"prop brecOn: missing below constant for class {j}")
    belowCtorNames := belowCtorNames.push (match bc with
      | .indc bi => bi.ctors.map (·.name)
      | _ => #[])

  -- --- Phase 1: Open rec type into FVars ---
  let (paramFvars, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "pbp" 0

  -- Open motives (make implicit).
  let mut motiveFvars : Array Expr := #[]
  let mut motiveDecls : Array LocalDecl := #[]
  let mut afterMotives := afterParams
  for mi in [0:nMotives] do
    if let .forallE name dom body _ _ := afterMotives then
      let (fvName, fv) := freshFVar "pbm" mi
      motiveDecls := motiveDecls.push
        { fvarName := fvName, binderName := name, domain := dom,
          info := .implicit }
      motiveFvars := motiveFvars.push fv
      afterMotives := instantiate1 body fv

  -- Open minors (keep domains for building below_minors later).
  let mut minorDoms : Array Expr := #[]
  let mut afterMinors := afterMotives
  for mi in [0:nMinors] do
    if let .forallE _ dom body _ _ := afterMinors then
      minorDoms := minorDoms.push dom
      let (_, dummy) := freshFVar "pbx" mi
      afterMinors := instantiate1 body dummy

  -- Open indices and major.
  let (indexFvars, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "pbi" 0
  let (majorFvars, majorDecls, _) :=
    forallTelescope afterIndices 1 "pbj" 0

  -- --- Phase 2: Build F binders ---
  -- F_j : ∀ (motive_args...) (below_proof : I_j.below params motives
  -- args), motive_j args
  let mut fFvars : Array Expr := #[]
  let mut fDecls : Array LocalDecl := #[]
  let indUnivs : Array Level := indLevelParams.map Level.mkParam

  for j in [0:nMotives] do
    -- Open motive_j's type to get inner binders (indices + major).
    let motiveType := motiveDecls[j]!.domain
    let nMotiveArgs := countForalls motiveType
    let (innerFvars, innerDecls, _innerSort) :=
      forallTelescope motiveType nMotiveArgs s!"pbfa{j}" 0

    -- below_app: I_j.below params motives inner_args
    let belowApp := Id.run do
      let mut app := mkConst belowNames[j]! indUnivs
      app := mkAppN app paramFvars
      app := mkAppN app motiveFvars
      app := mkAppN app innerFvars
      return app

    -- motive_app: motive_j inner_args
    let motiveApp := mkAppN motiveFvars[j]! innerFvars

    -- F_j type body: below_app → motive_app.
    let (belowFvName, _belowFv) := freshFVar s!"pbfb{j}" 0
    let belowDecl : LocalDecl :=
      { fvarName := belowFvName, binderName := Name.mkAnon,
        domain := belowApp, info := .default }

    -- F_j type = ∀ inner_args below_proof, motive_app
    let fTypeBinders : Array LocalDecl := innerDecls.push belowDecl
    let fType := mkForall motiveApp fTypeBinders

    let fName := Name.mkStr .mkAnon s!"F_{j + 1}"
    let (fjFvName, fjFv) := freshFVar "pbf" j
    fDecls := fDecls.push
      { fvarName := fjFvName, binderName := fName, domain := fType,
        info := .default }
    fFvars := fFvars.push fjFv

  -- --- Phase 3: Build return type (for type) ---
  -- motive_ci index_fvars major_fvar
  let retType := mkAppN (mkAppN motiveFvars[ci]! indexFvars) majorFvars

  -- --- Phase 4: Build value body ---
  -- F_ci index_fvars major (I_ci.rec params below_motives below_minors
  -- index_fvars major)

  -- Rec application universes: for large elim, [0] specializes to zero.
  let recUnivs : Array Level := recVal.cnst.levelParams.zipIdx.map
    fun (lp, i) =>
      if largeElim && i == 0 then Level.mkZero else Level.mkParam lp
  let mut recApp := mkConst recVal.cnst.name recUnivs

  -- Apply params.
  recApp := mkAppN recApp paramFvars

  -- Apply below_motives: I_j.below params motives (partial application).
  for belowName in belowNames.extract 0 nMotives do
    let belowMotive := mkAppN
      (mkAppN (mkConst belowName indUnivs) paramFvars) motiveFvars
    recApp := Expr.mkApp recApp belowMotive

  -- Apply below_minors: for each ctor, λ (fields) => below_ctor params
  -- motives args.
  let mut globalCtorIdx := 0
  for j in [0:nClasses] do
    let some classCtorNames := belowCtorNames[j]?
      | throw (CompileError.unsupportedExpr
          s!"prop brecOn: missing below ctor names for class {j}")

    for (belowCtorName, cidx) in classCtorNames.zipIdx do
      if globalCtorIdx + cidx >= minorDoms.size then
        break
      let minorDom := minorDoms[globalCtorIdx + cidx]!

      -- Build the below minor using FVars.
      let minor := buildPropBelowMinorFvar minorDom belowCtorName
        paramFvars motiveFvars fFvars belowNames indUnivs
      recApp := Expr.mkApp recApp minor
    globalCtorIdx := globalCtorIdx + classCtorNames.size

  -- Apply indices and major.
  recApp := mkAppN recApp indexFvars
  recApp := mkAppN recApp majorFvars

  -- F_ci index_fvars major rec_app
  let valBody := Expr.mkApp
    (mkAppN (mkAppN fFvars[ci]! indexFvars) majorFvars) recApp

  -- --- Phase 5: Close with mkForall / mkLambda ---
  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ indexDecls ++ majorDecls ++ fDecls

  let typ := mkForall retType allDecls
  let val := mkLambda valBody allDecls

  return {
    name := breconName
    levelParams := indLevelParams
    typ
    value := val
    -- Prop-level `.brecOn` references the parent `.rec` and mentions the
    -- inductive; Lean's `mkThmOrUnsafeDef` flips to `Unsafe`+`Opaque`
    -- when the inductive is unsafe.
    isUnsafe := ind.isUnsafe
    isProp := true
  }

/-! ## Entry point (brecon.rs:56) -/

/-- Mirrors Rust `generate_brecon_constants` (brecon.rs:62).

    Generate all `.brecOn` (and `.brecOn.go`/`.brecOn.eq` for Type-level)
    constants. Called after Phase 2 (`.below` generation), using the
    canonical recursors from Phase 1 and the `.below` constants from
    Phase 2. `isProp` selects Prop-level (single theorem) vs Type-level
    (`.brecOn.go` + `.brecOn` + `.brecOn.eq`) generation. -/
def generateBreconConstants (sortedClasses : Array (Array Name))
    (canonicalRecs : Array (Name × RecursorVal))
    (belowConsts : Array BelowConstant) (isProp : Bool) (maps : AddrMaps)
    : KBridgeM (Array BRecOnDef) := do
  let nClasses := sortedClasses.size
  if nClasses == 0 || canonicalRecs.isEmpty || belowConsts.isEmpty then
    return #[]

  let mut results : Array BRecOnDef := #[]

  -- Rust: `for ci in 0..n_classes.min(canonical_recs.len())
  --   .min(below_consts.len())`.
  let hi := min nClasses (min canonicalRecs.size belowConsts.size)
  for (pair, ci) in (canonicalRecs.extract 0 hi).zipIdx do
    let (_, recVal) := pair
    let classRep := sortedClasses[ci]![0]!
    let ind ←
      match ← lookupConst? classRep with
      | some (.inductInfo v) => pure v
      | _ =>
        -- Rust: MissingConstant { caller: "generate_brecon_constants:
        -- class rep not an inductive" }
        throw (CompileError.missingConstant classRep.pretty)

    -- Only generate brecOn for recursive inductives (Lean's guard:
    -- `unless indVal.isRec do return` in BRecOn.lean:313 and
    -- IndPredBelow.lean:215).
    if !ind.isRec then
      continue

    if !isProp then
      -- Type-level: .brecOn.go + .brecOn + .brecOn.eq (BRecOn.lean path).
      let breconName := Name.mkStr sortedClasses[ci]![0]! "brecOn"
      let all0 := ind.all[0]!
      -- Below names from belowConsts (source-indexed, matching
      -- canon_kenv's content hashes). Positions align with the canonical
      -- flat block: 0..nClasses = primary belows, nClasses.. = aux.
      let belowNames : Array Name := belowConsts.map fun bc =>
        match bc with
        | .defn d => d.name
        | .indc i => i.name
      let defs ← buildTypeBreconFvar ci recVal breconName all0 belowNames
        nClasses maps
      results := results ++ defs
    else
      -- Prop-level: single .brecOn theorem (IndPredBelow.lean path).
      let d ← buildPropBrecon ci recVal ind nClasses sortedClasses
        belowConsts
      results := results.push d

  -- Generate .brecOn_N for nested auxiliary members (Type-level only).
  -- Lean (BRecOn.lean:320-326): for each nested auxiliary recursor
  -- rec_N, generate brecOn_N.go + brecOn_N + brecOn_N.eq using the same
  -- mkBRecOnFromRec function as the main brecOn.
  if !isProp then
    let nAux := canonicalRecs.size - nClasses
    if nAux > 0 then
      -- all[0] from the first class's inductive — Lean hangs _N names
      -- here.
      let firstClassName := sortedClasses[0]![0]!
      let all0 ←
        match ← lookupConst? firstClassName with
        | some (.inductInfo v) => pure v.all[0]!
        | _ => pure firstClassName

      for (pair, j) in
          (canonicalRecs.extract nClasses canonicalRecs.size).zipIdx do
        let (auxRecName, auxRecVal) := pair
        -- Source-indexed suffix from the aux rec's name (aux_gen already
        -- names it `<all0>.rec_{source_j+1}`).
        let some idx := auxRecSuffixIdx auxRecName
          | throw (CompileError.invalidMutualBlock
              s!"brecOn aux recursor '{auxRecName.pretty}' is not \
source-indexed; refusing to synthesize brecOn_{j + 1}")
        let breconName := Name.mkStr all0 s!"brecOn_{idx}"

        -- Only generate if this constant exists in the source
        -- environment. Check lean_env OR stt.env.named (Ixon compile
        -- state — decompilation's work_env won't contain the constant
        -- we're about to generate).
        let cenv ← Ix.CompileM.getCompileEnv
        let existsInEnv := (← lookupConst? breconName).isSome
          || cenv.nameToNamed.contains breconName
        if existsInEnv then
          let ci := nClasses + j -- target motive index in the flat block
          let belowNames : Array Name := belowConsts.map fun bc =>
            match bc with
            | .defn d => d.name
            | .indc i => i.name
          let defs ← buildTypeBreconFvar ci auxRecVal breconName all0
            belowNames nClasses maps
          results := results ++ defs

  return results

end Ix.AuxGen

end
