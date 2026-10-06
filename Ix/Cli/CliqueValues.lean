/-
  The clique value phase of `ix validate-lean` (phase 9; plan M4 (b)).

  Kernel acceptance and decompile do not establish meaning (plan §2,
  evidence standards). For every transported definition clique of the
  validated output this phase evaluates each member on distinguishing inputs
  twice, once from Lean's constant and once from the **compiled** constant,
  and compares the two values.

  * **The compiled side.** The member and the canonical constants it reaches
    (`g._ix._mutual`, `…_proof_k`, `x._ix._f`, …) are decompiled from the
    output's own bytes with `DecompileEnv.compiledTerms`: the Pass 3 record
    `_ix.inline`, which phase 5 replays to Lean's value, is NOT replayed, so
    the term read is the stored (transported) term. Those constants are added
    to Lean's environment (members under a scratch name `m._ix_value`, every
    reference to a member renamed with them) through `addDecl`, i.e. Lean's
    kernel checks them, and the evaluation runs over them. References to
    library constants resolve by name in Lean's environment; that the
    output's addresses for them are Lean's is phases 4–5's claim, and that a
    Lean name holding an image computes as Lean's recursor is phase 7's.
    Lean's kernel and `Meta.reduce` are used as an evaluator of the compiled
    term: what is evaluated is the output's term, not Lean's, so a transport
    that moves a user value changes the compiled value (FIX-pfwf §1).
  * **Evaluation.** Structural members compute (`brecOn` reduces on closed
    data). A well-founded or `partial_fixpoint` member is a fixpoint, which
    does not reduce: it is compared one unfolding deep, as FIX-pfwf's probe
    did. The fixpoint `fix F` is replaced by `F` applied to an oracle that
    answers every recursive call to member `j` with a free variable `o_j`
    (in Lean's packing at position `j`, in the compiled packing at `σ j`,
    `σ` read from the clique's side-car record `_ix.clique`). A free
    variable per member makes any exchange of members, branches or measure
    visible; O16/O15 (`FixPerm.fix_iso`, `WellFounded.fix_eq`) are what make
    one unfolding enough for a correct transport.
  * **Inputs** (`inputTuples`), from the member's type: `Nat` takes
    0, 1, 2, 3, 5, 17 (the fixtures' values; 2, 3, 5 cross both members'
    branches of an alternating recursion), `Bool` both values, a
    non-indexed inductive type its constructors over such samples (depth 2),
    a proposition a `decide` proof when one evaluates, an instance its
    synthesised instance, a type `Nat` (`True` for `Prop`); any other
    argument (functions, strings, structures over them, user data of the
    packing type, unsynthesisable instances) is a free variable, i.e. the
    member is evaluated symbolically in it. Structural members need closed
    data (a `brecOn` on a free variable does not compute), so a structural
    member with no closed input tuple is not value-checkable.
  * **Not value-checkable**, with the reason, counted, never skipped:
    theorems and members whose type is a proposition (proofs are irrelevant;
    the statement is checked by phases 3–5), opaque members, a structural
    member without closed inputs, an evaluation of Lean's own constant that
    the evaluator cannot perform, the resource limit (heartbeats), a compiled
    clique that references compiled inductive-block constants. An evaluation
    failure on the compiled side where Lean's side evaluated is a failure.

  Coverage is asserted: every member of every transported clique has a
  verdict, and a clique with no value-checked member must have a reason for
  each member.
-/
module
public import Lean.Meta
public import Ix.DecompileM
public import Ix.CanonM
public import Ix.Compile.Pass

public section

namespace IxCliqueValues

open Lean Meta

/-- `Ix.Name ↦ Lean.Name`. -/
def toLeanName : Ix.Name → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (toLeanName p) s
  | .num p n _ => .num (toLeanName p) n

/-- A name with a reserved (`_ix…`) component. -/
def isReservedName (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s.startsWith Ix.Compile.Pass.ixComponent
    | _ => false

/-- Lean's encoding constants of a clique (`all₀._mutual…`, `all₀.mutual…`,
`m._f`), on Lean names (`Ix.Compile.Pass.isEncodingName`). -/
def isLeanEncoding (all : Array Name) (n : Name) : Bool :=
  match all[0]? with
  | none => false
  | some a0 =>
    (a0 ++ `_mutual).isPrefixOf n || (a0 ++ `mutual).isPrefixOf n ||
      (match n with
        | .str p "_f" => all.contains p
        | _ => false)

/-! ## Evaluation -/

/-- Unfold every application of a constant satisfying `p` (its definition,
β-reduced), repeatedly (the probe's `deltaNames`). -/
def deltaWhere (p : Name → Bool) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let step (e : Expr) : Expr := e.replace fun x =>
    match x.getAppFn with
    | .const c us =>
      if p c then
        match env.find? c with
        | some ci => match ci.value? (allowOpaque := true) with
          | some v => some ((v.instantiateLevelParams ci.levelParams us).beta x.getAppArgs)
          | none => none
        | none => none
      else none
    | _ => none
  let mut e := e
  for _ in [0:8] do
    let e' := step e
    if e' == e then break
    e := e'
  return e

def isFixApp (x : Expr) : Bool :=
  x.isAppOfArity ``Lean.Order.fix 4 || x.isAppOfArity ``Lean.Order.lfp_monotone 4 ||
    x.isAppOfArity ``WellFounded.fix 6 ||
    x.isAppOfArity ``WellFounded.Nat.fix 5

/-- The `n` components of a right-nested binary type former `k` (`PSum`,
`PProd`). -/
def splitNested (k : Name) (n : Nat) (ty : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  let mut t := ty
  for _ in [0:n - 1] do
    let t' ← whnfR t
    unless t'.isAppOfArity k 2 do throwError "not a {k} packing of {n}: {ty}"
    out := out.push t'.appFn!.appArg!
    t := t'.appArg!
  return out.push t

/-- The tuple `⟨c₀, …⟩` of a right-nested `PProd` packing. -/
partial def mkTupleOf (comps : List Expr) : MetaM Expr := do
  match comps with
  | [] => throwError "empty packing"
  | [c] => pure c
  | c :: rest => mkAppM ``PProd.mk #[c, ← mkTupleOf rest]

/-- `λ y. PSum.casesOn y f₀ f₁ …` over the right-nested packing `α`,
motive `C` (the probe's `mkCases`). -/
partial def mkCases (α C : Expr) (fs : List Expr) (y : Expr) : MetaM Expr := do
  match fs with
  | [] => throwError "empty packing"
  | [f] => pure (mkApp f y)
  | f :: rest =>
    let α ← whnfR α
    unless α.isAppOfArity ``PSum 2 do throwError "not a PSum: {α}"
    let a := α.appFn!.appArg!
    let b := α.appArg!
    let mot ← withLocalDeclD `t α fun t => mkLambdaFVars #[t] (mkApp C t)
    let Cb ← withLocalDeclD `z b fun z => do
      mkLambdaFVars #[z] (mkApp C (← mkAppOptM ``PSum.inr #[a, b, z]))
    let inrFn ← withLocalDeclD `r b fun r => do mkLambdaFVars #[r] (← mkCases b Cb rest r)
    mkAppOptM ``PSum.casesOn #[a, b, mot, y, f, inrFn]

/-- One unfolding of the fixpoint `fx` in `e`: `fix F` ↦ `F ⟨comps⟩`
(`Lean.Order.fix`), `fix F x` ↦ `F x (λ y _. O y)` (`WellFounded.fix`,
`WellFounded.Nat.fix`), component `p` of the packing answered by
`comps[p]`. -/
def unfoldFixAt (fx : Expr) (comps : Array Expr) (e : Expr) : MetaM Expr := do
  let args := fx.getAppArgs
  let repl ← if fx.isAppOf ``Lean.Order.fix || fx.isAppOf ``Lean.Order.lfp_monotone then do
      pure (mkApp args[2]! (← mkTupleOf comps.toList))
    else do
      let α := args[0]!
      let C := args[1]!
      let F := args[args.size - 2]!
      let x := args[args.size - 1]!
      let O ← withLocalDeclD `y α fun y => do mkLambdaFVars #[y] (← mkCases α C comps.toList y)
      let Fty ← whnf (← inferType F)
      let .forallE _ _ body _ := Fty | throwError "functional type {Fty}"
      let Aty ← whnf (body.instantiate1 x)
      let .forallE _ A _ _ := Aty | throwError "recursion binder type {Aty}"
      let a ← forallBoundedTelescope A (some 2) fun ys _ => mkLambdaFVars ys (mkApp O ys[0]!)
      pure (mkAppN F #[x, a])
  return e.replace fun z => if z == fx then some repl else none

/-- The oracle types of the fixpoint `fx` with `n` members: per packing
position, the component type (`Lean.Order.fix`), or `∀ y : A_p, C (inj_p y)`
(well-founded). -/
def oracleTypes (fx : Expr) (n : Nat) : MetaM (Array Expr) := do
  let args := fx.getAppArgs
  if fx.isAppOf ``Lean.Order.fix || fx.isAppOf ``Lean.Order.lfp_monotone then
    splitNested ``PProd n args[0]!
  else
    let α := args[0]!
    let C := args[1]!
    let summands ← splitNested ``PSum n α
    -- the injection of position `p` into the right-nested `α`
    let inj (p : Nat) (y : Expr) : MetaM Expr := do
      let mut tys : Array Expr := #[]
      let mut t := α
      for _ in [0:p] do
        let t' ← whnfR t
        tys := tys.push t'
        t := t'.appArg!
      let t' ← whnfR t
      let mut v ← if p + 1 < n then mkAppOptM ``PSum.inl #[t'.appFn!.appArg!, t'.appArg!, y] else pure y
      for q in (List.range p).reverse do
        let tq := tys[q]!
        v ← mkAppOptM ``PSum.inr #[tq.appFn!.appArg!, tq.appArg!, v]
      return v
    (List.range n).toArray.mapM fun p => do
      withLocalDeclD `y summands[p]! fun y => do
        mkForallFVars #[y] (← headBeta (mkApp C (← inj p y)))
where
  headBeta (e : Expr) : MetaM Expr := pure e.headBeta

/-! ## Inputs -/

def natSamples : Array Nat := #[0, 1, 2, 3, 5, 17]

/-- A proof of `p` by `decide`, when the decision evaluates to `true`. -/
def decideProof? (p : Expr) : MetaM (Option Expr) := do
  try
    let d ← mkDecide p
    let r ← withTransparency .all (whnf d)
    if r.isConstOf ``Bool.true then return some (← mkDecideProof p) else return none
  catch _ => return none

/-- Closed sample values of `ty` (empty: none known). -/
partial def samples (ty : Expr) (depth : Nat) : MetaM (Array Expr) := do
  let ty ← whnf ty
  if ty.isConstOf ``Nat then
    return (if depth ≥ 2 then natSamples else #[0, 1, 17]).map mkNatLit
  if (← isProp ty) then
    return (← decideProof? ty).toArray
  if depth == 0 then return #[]
  let .const I us := ty.getAppFn | return #[]
  -- strings, characters and machine integers: symbolic (their literals do
  -- not evaluate cheaply in the kernel's representation)
  if [``String, ``Char, ``String.Pos.Raw, ``Substring.Raw].contains I then return #[]
  let some (.inductInfo iv) := (← getEnv).find? I | return #[]
  if iv.numIndices != 0 || iv.isUnsafe || iv.levelParams.length != us.length then return #[]
  let params := ty.getAppArgs.extract 0 iv.numParams
  if params.size != iv.numParams then return #[]
  let mut out : Array Expr := #[]
  for c in iv.ctors do
    let some ci := (← getEnv).find? c | continue
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
    if let some ts ← fieldTuples cty (depth - 1) then
      for t in ts do out := out.push (mkAppN (mkAppN (mkConst c us) params) t)
    if out.size ≥ 4 then break
  return out.extract 0 4
where
  fieldTuples (cty : Expr) (depth : Nat) : MetaM (Option (Array (Array Expr))) := do
    let cty ← whnf cty
    match cty with
    | .forallE _ F b _ =>
      let choices ← samples F depth
      if choices.isEmpty then return none
      let mut out : Array (Array Expr) := #[]
      for c in choices.extract 0 2 do
        match ← fieldTuples (b.instantiate1 c) depth with
        | some ts => out := out ++ ts.map (#[c] ++ ·)
        | none => return none
      return some (out.extract 0 4)
    | _ => return some #[#[]]

/-- The argument choices of one binder: closed values, or `none` (a free
variable). -/
def binderChoices (bi : BinderInfo) (F : Expr) : MetaM (Option (Array Expr)) := do
  if bi.isInstImplicit then
    return (← try synthInstance? F catch _ => pure none).map (#[·])
  match ← whnf F with
  | .sort l =>
    if (← isLevelDefEq l Level.zero) then return some #[mkConst ``True]
    return some #[mkConst ``Nat]
  | _ =>
    let s ← samples F 2
    return if s.isEmpty then none else some s

/-- At most this many input tuples per member. -/
def maxTuples : Nat := 24

/-- Run `k` on every input tuple of the telescope `ty` (closed choices, else
a free variable in scope), at most `maxTuples` of them; `k` gets the tuple
and whether a free variable is in it. -/
partial def forInputs (ty : Expr) (k : Array Expr → Bool → MetaM Unit) : MetaM Unit := do
  let budget ← IO.mkRef maxTuples
  let rec go (ty : Expr) (acc : Array Expr) (symb : Bool) : MetaM Unit := do
    if (← budget.get) == 0 then return
    match ← whnf ty with
    | .forallE n F b bi =>
      match ← binderChoices bi F with
      | some cs =>
        for c in cs do
          if (← budget.get) == 0 then return
          go (b.instantiate1 c) (acc.push c) symb
      | none =>
        withLocalDecl n bi F fun x => go (b.instantiate1 x) (acc.push x) true
    | _ =>
      budget.modify (· - 1)
      k acc symb
  go ty #[] false

/-! ## The phase -/

/-- A member's verdict. -/
inductive Verdict where
  /-- value-checked: inputs (closed, symbolic), and tuples declined (resource limit, …) -/
  | checked (closed symbolic declined : Nat)
  /-- not value-checkable, with the reason -/
  | notCheckable (reason : String)
  /-- a mismatch or a compiled-side failure -/
  | failed (lines : Array String)

structure CliqueRow where
  all : Array Name
  encoding : String
  sigma : Array Nat
  members : Array (Name × Verdict)
  /-- a clique-level failure (kernel rejection of the compiled constants, …) -/
  failure : Option String := none
  /-- a clique-level reason none of its members is value-checkable -/
  reason : Option String := none

structure Report where
  cliques : Array CliqueRow := #[]

/-- The side-car record `_ix.clique` of the compiled canonical constants:
the encoding tag and `σ`. -/
def sideCar? (cs : Array ConstantInfo) : Option (String × Array Nat) := Id.run do
  for c in cs do
    let some v := c.value? (allowOpaque := true) | continue
    let isRecord (x : Expr) : Bool := match x with
      | .mdata d _ => (d.find `_ix.clique).isSome
      | _ => false
    let some md := v.find? isRecord | continue
    let .mdata d _ := md | continue
    let some (.ofString r) := d.find `_ix.clique | continue
    let enc := (r.splitOn ";").headD ""
    let some rest := (r.splitOn "sigma #[")[1]? | continue
    let body := (rest.splitOn "]").headD ""
    let sigma := (body.splitOn ",").filterMap fun s => s.trimAscii.toString.toNat?
    return some (enc.trimAscii.toString, sigma.toArray)
  return none

/-- Decompile `n` from the output's bytes, reading compiled terms. -/
def decompileCompiled (ixonEnv : Ixon.Env) (n : Ix.Name) : Except String ConstantInfo := do
  let some nd := ixonEnv.named.get? n | throw s!"{n.pretty}: not in the output"
  let xs ← Ix.DecompileM.decompileOne { ixonEnv, compiledTerms := true } ixonEnv n
    { nd with original := none }
  let some (_, ci) := xs.find? (·.1 == n) | throw s!"{n.pretty}: does not decompile on its own"
  return (Ix.CanonM.uncanonConst ci).run' {}

def renameConsts (m : NameMap Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us => (m.find? n).map (.const · us)
    | _ => none

def kernelAdd (decl : Declaration) : CoreM (Option String) := do
  try
    withOptions (fun o => o.setBool `Elab.async false) do addDecl decl
    return none
  catch e => return some (← e.toMessageData.toString)

/-- The compiled constants of a clique (members and the reserved constants
they reach), decompiled with compiled terms. -/
def compiledClosure (ixonEnv : Ixon.Env) (all : Array Name) :
    Except String (Array ConstantInfo) := do
  let mut out : Array ConstantInfo := #[]
  let mut seen : NameSet := {}
  let mut todo : Array Name := all
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let ci ← decompileCompiled ixonEnv (Ix.Name.fromLeanName n)
    out := out.push ci
    let refs := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for r in refs do
      if isReservedName r && !seen.contains r then todo := todo.push r
  return out

def scratchName (m : Name) : Name := m.str "_ix_value"

def kindName : ConstantInfo → String
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quotient constant"
  | _ => "constant"

/-- Add the compiled constants (members renamed) in dependency order;
`none` when all are accepted, else the first problem. -/
def addCompiled (all : Array Name) (cs : Array ConstantInfo) : CoreM (Option String) := do
  let ren : NameMap Name := all.foldl (fun m a => m.insert a (scratchName a)) {}
  let names : NameSet := cs.foldl (fun s c => s.insert c.name) {}
  let mut pending := cs.toList
  let mut added : NameSet := {}
  let mut progress := true
  while progress && !pending.isEmpty do
    progress := false
    let mut rest := []
    for c in pending do
      let refs := c.type.getUsedConstants ++ ((c.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      unless refs.all fun r => !names.contains r || added.contains r || r == c.name do
        rest := rest ++ [c]
        continue
      let n := (ren.find? c.name).getD c.name
      let ty := renameConsts ren c.type
      let decl? : Except String Declaration := match c with
        | .defnInfo v =>
          let v' : DefinitionVal := { v with name := n, type := ty, value := renameConsts ren v.value, all := [n] }
          .ok (.defnDecl v')
        | .thmInfo v =>
          let v' : TheoremVal := { v with name := n, type := ty, value := renameConsts ren v.value, all := [n] }
          .ok (.thmDecl v')
        | .opaqueInfo v =>
          let v' : OpaqueVal := { v with name := n, type := ty, value := renameConsts ren v.value, all := [n] }
          .ok (.opaqueDecl v')
        | _ => .error s!"{c.name}: a compiled {kindName c} (compiled inductive-block constants are not added to Lean's environment here)"
      match decl? with
      | .error e => return some s!"NOTCHECKABLE {e}"
      | .ok decl =>
        if let some e ← kernelAdd decl then return some s!"Lean's kernel rejects the compiled {c.name}: {e.take 300}"
      added := added.insert c.name
      progress := true
    pending := rest
  if !pending.isEmpty then return some s!"dependency cycle among {pending.map (·.name)}"
  return none

/-- One side, unfolded (its encoding, one fixpoint step) but not reduced. -/
def prepSide (p : Name → Bool) (e : Expr) (fix? : Option (Array Expr)) : MetaM Expr := do
  let e ← deltaWhere p e
  let e ← match fix? with
    | some comps =>
      let some fx := e.find? isFixApp | throwError "no fixpoint to unfold"
      unfoldFixAt fx comps e
    | none => pure e
  deltaWhere p e

/-- One side, evaluated: unfolded, then reduced (transparency `all`). -/
def evalSide (p : Name → Bool) (e : Expr) (fix? : Option (Array Expr)) : MetaM Expr := do
  withTransparency .all (reduce (← prepSide p e fix?) (skipTypes := false))

/-- Are the two unfolded sides definitionally equal (lazy unfolding, no
normal form)? Cheaper than reducing both on symbolic inputs; `true` means
equal values for these inputs and every oracle. Any failure or resource
exhaustion of this shortcut is `false` (the full evaluation decides). -/
def quickDefEq (pL pC : Name → Bool) (lhs rhs : Expr) (comps? : Option (Array Expr × Array Expr)) :
    MetaM Bool := do
  let attempt : MetaM Bool := withCurrHeartbeats do
    let v ← prepSide pL lhs (comps?.map (·.1))
    let w ← prepSide pC rhs (comps?.map (·.2))
    withTransparency .all (isDefEq v w)
  tryCatchRuntimeEx (try attempt catch _ => pure false) fun _ => pure false

def showE (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  return if s.length > 160 then (s.take 160).toString ++ "…" else s

/-- The heartbeat limit (in thousands) of one evaluation. -/
def heartbeatLimit : Nat := 20000

/-- The verdict of a member that cannot be evaluated whatever its compiled
form (theorem, opaque, propositional type), else `none`. -/
def staticVerdict? (m : Name) : MetaM (Option Verdict) := do
  let some ci := (← getEnv).find? m | return some (.notCheckable "Lean's constant not found")
  match ci with
  | .thmInfo _ => return some (.notCheckable "a theorem (proofs are irrelevant; its statement is checked by phases 3–5)")
  | .opaqueInfo _ => return some (.notCheckable "opaque (no value to unfold)")
  | .defnInfo _ =>
    let ty := ci.type.instantiateLevelParams ci.levelParams (ci.levelParams.map fun _ => Level.zero)
    if ← isProp ty then
      return some (.notCheckable "its type is a proposition (a proof: irrelevant; the statement is checked by phases 3–5)")
    return none
  | _ => return some (.notCheckable "not a definition")

/-- Check one member of a clique on every input tuple. -/
def checkMember (all : Array Name) (enc : String) (sigma : Array Nat) (m : Name) : MetaM Verdict := do
  let env ← getEnv
  let some ci := env.find? m | return .notCheckable "Lean's constant not found"
  match ci with
  | .thmInfo _ => return .notCheckable "a theorem (proofs are irrelevant; its statement is checked by phases 3–5)"
  | .opaqueInfo _ => return .notCheckable "opaque (no value to unfold)"
  | .defnInfo _ => pure ()
  | _ => return .notCheckable "not a definition"
  let us := ci.levelParams.map fun _ => Level.zero
  let ty := ci.type.instantiateLevelParams ci.levelParams us
  if ← isProp ty then
    return .notCheckable "its type is a proposition (a proof: irrelevant; the statement is checked by phases 3–5)"
  let n := all.size
  let structural := enc == "structural"
  let inv : Array Nat := Id.run do
    let mut a := Array.replicate n 0
    for j in [0:sigma.size] do
      if sigma[j]! < n then a := a.set! sigma[j]! j
    return a
  let pL : Name → Bool := fun c => all.contains c || isLeanEncoding all c
  let pC : Name → Bool := fun c => isReservedName c
  let closed ← IO.mkRef 0
  let symbolic ← IO.mkRef 0
  let fails ← IO.mkRef (#[] : Array String)
  let declines ← IO.mkRef (#[] : Array String)
  forInputs ty fun args symb => do
    if structural && symb then
      declines.modify (·.push "structural member: no input tuple with closed data (a `brecOn` on a free variable does not compute)")
      return
    let shown := (← args.mapM showE).toList
    let lhs := mkAppN (mkConst m us) args
    let rhs := mkAppN (mkConst (scratchName m) us) args
    -- compare the two sides with the oracles `comps?` (Lean's, compiled)
    let body (comps? : Option (Array Expr × Array Expr)) : MetaM Unit := do
      if ← quickDefEq pL pC lhs rhs comps? then
        if symb then symbolic.modify (· + 1) else closed.modify (· + 1)
        return
      let v? ← try some <$> evalSide pL lhs (comps?.map (·.1)) catch e => do
        declines.modify (·.push s!"Lean's own constant does not evaluate on {shown}: {(← e.toMessageData.toString).take 160}")
        pure none
      let some v := v? | return
      let w? ← try some <$> evalSide pC rhs (comps?.map (·.2)) catch e => do
        fails.modify (·.push s!"{m} {shown}: Lean's value {← showE v}, but the compiled constant does not evaluate: {(← e.toMessageData.toString).take 200}")
        pure none
      let some w := w? | return
      if v == w || (← withTransparency .all (isDefEq v w)) then
        if symb then symbolic.modify (· + 1) else closed.modify (· + 1)
      else
        fails.modify (·.push s!"WRONG MEANING: {m} {shown} is {← showE v} in Lean, {← showE w} compiled")
    let run : MetaM Unit := withCurrHeartbeats do
      if structural then body none
      else
        let e ← deltaWhere pL lhs
        let some fx := e.find? isFixApp
          | declines.modify (·.push "Lean's constant shows no fixpoint after unfolding its encoding")
        let tys? ← try some <$> oracleTypes fx n catch e => do
          declines.modify (·.push s!"Lean's packing: {(← e.toMessageData.toString).take 160}")
          pure none
        let some tys := tys? | return
        if sigma.size != n then
          fails.modify (·.push s!"{m}: the side-car σ {sigma} does not have {n} entries")
          return
        let rec withOracles (i : Nat) (acc : Array Expr) : MetaM Unit := do
          if h : i < tys.size then
            withLocalDeclD (Name.mkSimple s!"o{i}") tys[i] fun o => withOracles (i + 1) (acc.push o)
          else
            -- Lean's packing: position `p` answers for member `p`; the
            -- compiled packing: position `p` for member `σ⁻¹ p`
            let compiled := (List.range n).toArray.map fun p => acc[inv[p]!]!
            body (some (acc, compiled))
        withOracles 0 #[]
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeatLimit * 1000 }) run)
      fun e => do
        if e.isRuntime then
          declines.modify (·.push s!"resource limit on {shown}: {(← e.toMessageData.toString).take 120}")
        else
          fails.modify (·.push s!"{m} {shown}: {(← e.toMessageData.toString).take 200}")
  let fs ← fails.get
  if !fs.isEmpty then return .failed fs
  let c ← closed.get
  let s ← symbolic.get
  if c + s > 0 then return .checked c s (← declines.get).size
  let ds ← declines.get
  return .notCheckable ((ds[0]?).getD "no input tuple")

/-- A clique row without member verdicts. -/
def bareRow (all : Array Name) (enc : String) (sigma : Array Nat) (failure reason : Option String) : CliqueRow :=
  { all := all, encoding := enc, sigma := sigma, members := #[], failure := failure, reason := reason }

/-- The phase over the transported cliques `cliques` (Lean's `all` each). -/
def run (leanEnv : Environment) (ixonEnv : Ixon.Env) (cliques : Array (Array Name)) : IO Report := do
  let mut rep : Report := {}
  for all in cliques do
    let t0 ← IO.monoMsNow
    let ctx : Core.Context := { fileName := "<validate-lean clique values>", fileMap := default, maxHeartbeats := 0 }
    match compiledClosure ixonEnv all with
    | .error e =>
      rep := { rep with cliques := rep.cliques.push (bareRow all "?" #[] (some s!"compiled constants: {e}") none) }
    | .ok cs =>
      let (enc, sigma) := (sideCar? cs).getD ("?", #[])
      let body : MetaM CliqueRow := do
        -- a clique with no definition of non-propositional type has nothing to
        -- evaluate: its verdicts need no compiled constant in Lean's environment
        -- (theorem cliques' proofs can be large to kernel-check)
        let mut pre : Array (Name × Verdict) := #[]
        for m in all do
          if let some v ← staticVerdict? m then pre := pre.push (m, v)
        if pre.size == all.size then
          return { all := all, encoding := enc, sigma := sigma, members := pre }
        match ← addCompiled all cs with
        | some p =>
          if p.startsWith "NOTCHECKABLE " then return bareRow all enc sigma none (some (p.drop 13).toString)
          return bareRow all enc sigma (some p) none
        | none =>
          if enc == "?" then
            return bareRow all enc sigma (some "no side-car record `_ix.clique` on the compiled canonical constants") none
          let mut ms : Array (Name × Verdict) := #[]
          for m in all do ms := ms.push (m, ← checkMember all enc sigma m)
          return { all := all, encoding := enc, sigma := sigma, members := ms }
      let row ← try
          let (r, _) ← (body.run' {} : CoreM CliqueRow).toIO ctx { env := leanEnv }
          pure r
        catch e => pure (bareRow all enc sigma (some s!"evaluation: {e}") none)
      rep := { rep with cliques := rep.cliques.push row }
      IO.println s!"[validate-lean] phase 9: clique {rep.cliques.size}/{cliques.size} {all.toList.take 1}… ({(← IO.monoMsNow) - t0} ms)"
      (← IO.getStdout).flush
  return rep

/-- The phase verdict: `(failed?, detail, lines)`. -/
def summarize (rep : Report) : Bool × String × Array String := Id.run do
  let mut lines : Array String := #[]
  let mut failures := 0
  let mut nMembers := 0
  let mut nChecked := 0
  let mut nClosed := 0
  let mut nSymb := 0
  let mut nNot := 0
  let mut cliquesChecked := 0
  let mut cliquesNot := 0
  let mut cliquesFailed := 0
  for c in rep.cliques do
    let head := s!"clique {c.all.toList} ({c.encoding}, sigma {c.sigma.toList})"
    if let some f := c.failure then
      failures := failures + 1
      cliquesFailed := cliquesFailed + 1
      lines := lines.push s!"✗ {head}: {f}"
      continue
    if let some r := c.reason then
      cliquesNot := cliquesNot + 1
      nMembers := nMembers + c.all.size
      nNot := nNot + c.all.size
      lines := lines.push s!"{head}: not value-checkable: {r}"
      continue
    let mut any := false
    let mut failed := false
    let mut parts : Array String := #[]
    for (m, v) in c.members do
      nMembers := nMembers + 1
      match v with
      | .checked a b d =>
        any := true
        nChecked := nChecked + 1
        nClosed := nClosed + a
        nSymb := nSymb + b
        parts := parts.push s!"{m}: {a + b} input(s) equal ({a} closed, {b} symbolic{if d > 0 then s!", {d} tuple(s) declined" else ""})"
      | .notCheckable r =>
        nNot := nNot + 1
        parts := parts.push s!"{m}: not value-checkable: {r}"
      | .failed ls =>
        failed := true
        failures := failures + ls.size
        for l in ls.extract 0 6 do lines := lines.push s!"✗ {l}"
        parts := parts.push s!"{m}: {ls.size} failure(s)"
    -- coverage: every member has a verdict
    if c.members.size != c.all.size then
      failed := true
      failures := failures + 1
      lines := lines.push s!"✗ {head}: {c.members.size} verdict(s) for {c.all.size} member(s)"
    if failed then cliquesFailed := cliquesFailed + 1
    else if any then cliquesChecked := cliquesChecked + 1
    else cliquesNot := cliquesNot + 1
    lines := lines.push s!"{head}: {"; ".intercalate parts.toList}"
  let detail := s!"{rep.cliques.size} transported clique(s) ({cliquesChecked} value-checked, \
{cliquesNot} with no value-checkable member, each with a reason, {cliquesFailed} failing), {nMembers} \
member(s): {nChecked} value-checked on {nClosed + nSymb} input tuple(s) ({nClosed} closed, {nSymb} \
symbolic), {nNot} not value-checkable; {failures} failure(s)"
  return (failures > 0, detail, lines)

end IxCliqueValues

end
