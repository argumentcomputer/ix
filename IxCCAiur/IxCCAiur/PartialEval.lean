import IxCCAiur.InlineFuse

/-! # Certified Compile-Time Partial Evaluation & Constant Folding (`IxCCAiur.PartialEval`)

Fuel-bounded, strictly total compile-time partial evaluator and residualizer
operating on lowered `Prog` functions (`Aiur.Generic.Function Nat`):

1. **Static / Partially-Static Value Domain (`SVal`)**:
   - Canonical field literals `n < 2^56` (`.lit n`),
   - Known nonzero literal differences `(a : F) - (b : F)` for `a < b < 2^56` (`.subLit a b`),
   - Residual runtime variables (`.var y`),
   - Tuples (`.tuple svs`) and arrays (`.array svs`),
   - Constructors `.ctor enumTy nm svs` (supporting partially-static records/lists
     holding dynamic variables alongside static structure),
   - Static heap pointers `.ptr sv` representing deferred `.store` allocations so
     recursive ADTs (`NodeList`, `FList`, `LookupList`, `Context`, `GroupSummaryResult`)
     dereference at compile time (`*(store(v)) → v`) with zero runtime ROM allocations!

2. **Sound Compile-Time Constant Folding**:
   - Canonical field arithmetic (`+`, `-`, `*`, `neg 0`),
   - Static `matchValue` on literals, nonzero literal differences, tuples, arrays,
     constructors, wildcards, and binders,
   - Static `project` and `index` on tuples/arrays,
   - Static `load` dereference on `.ptr sv`,
   - Static `assertEq` elimination on equal literals,
   - Constant folding of `TypedLower`'s 56-bit arithmetic helpers (`check_u8`,
     `check_u16`, `check_u24`, `check_u56`, `sub_borrow_56`, `split_32_24`,
     `mul_56`, `divmod_56`) and `Fields::is_zero`.

3. **Bounded Recursive Specialization (Let-Insertion Call-Site Residualization)**:
   - Unfolds eligible `Prog` callees invoked with static/partially-static arguments
     (or explicitly listed in `PEConfig.staticFns`, e.g., `@[circuit_static]`),
     subject to `maxSpecDepth`, `maxSpecSteps`, `maxCalleeNodes`, and a dynamic-match
     recursion guard (`dynFns`) preventing runaway unrolling of dynamic loops.
   - Emits strictly alpha-fresh ANF bindings `_p<id>` so unfolded callees compose
     without variable capture or shadowing, collapsing static VK DAG evaluators
     (`nodeListGet`, `fListGet`, `evalAt`, `foldRoots`, `lookupFingerprint`,
     `groupSummary`, `foldLookupsFuel`, `expPower2`, `power2Mod`, `polynomial`)
     into flat straight-line arithmetic with zero residual ROM rows.
   - Optionally prunes unreachable functions via `InlineFuse.pruneUnreachable`.

4. **Plainness Preservation**:
   - Proves `isPlainExpr` preservation for `reifySVal`, `wrapLets`, `wrapLetsTail`,
     `peExpr`, `peFn`, `partialEvalFns`, and `partialEvalProg`.

Strictly total (zero `partial`), zero `sorry`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.PartialEval

open IxCC.AiurBackend.Lower
  (Expr Pat Fn Ty natLimit qualifyName isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.InlineFuse (exprNodes pruneUnreachable)

/-! ## Configuration & Fresh Variable Naming -/

/-- Default arithmetic helper functions kept as dedicated chips (constant-folded
when all arguments are static literals `< 2^56`, never unfolded on dynamic inputs). -/
def defaultNoSpecFns : List String :=
  ["check_u8", "check_u16", "check_u24", "check_u56",
   "sub_borrow_56", "split_32_24", "mul_56", "divmod_56",
   "pow_56_loop", "pow_56", "gcd_56", "shl_56", "shr_56",
   "u32_mul", "u32_complement", "u32_div", "u32_mod",
   "u32_shl", "u32_shr", "u32_of_field", "u64_shl", "u64_shr"]

/-- Configuration for compile-time partial evaluation and specialization. -/
structure PEConfig where
  /-- Maximum recursive call-unfolding depth (`fuel`). -/
  maxSpecDepth : Nat := 64
  /-- Maximum total call unfoldings performed per top-level function body. -/
  maxSpecSteps : Nat := 4096
  /-- Maximum AST node count of a callee body eligible for auto-unfolding. -/
  maxCalleeNodes : Nat := 1024
  /-- Explicit allowlist of functions to specialize (e.g. `@[circuit_static]`).
  When empty (default), auto-specializes any eligible `Prog` function called with
  at least one static or partially-static argument. -/
  staticFns : List String := []
  /-- Functions whose bodies are preserved verbatim and never unfolded on dynamic inputs. -/
  noSpecFns : List String := defaultNoSpecFns
  /-- Whether `partialEvalProg` / `partialEvalFnsPruned` prunes unreachable functions. -/
  prune : Bool := true
  deriving Repr, Inhabited

/-- Computable prefix test for residual variables `_p<id>`. -/
def hasPEPrefix (s : String) : Bool :=
  s.toList.take 2 == ['_', 'p']

/-- Strictly injective residual ANF binder name `_p<id>`. -/
def peVarName (id : Nat) : String :=
  String.ofList ('_' :: 'p' :: Lower.natDigits id)

/-- Partial evaluator state: strictly monotonic fresh binder counter and
remaining call-unfolding budget. -/
structure PEState where
  nextId : Nat := 0
  specSteps : Nat := 4096
  deriving Repr, Inhabited

/-- Allocate a strictly fresh residual binder name `_p<id>`. -/
def allocFresh (st : PEState) : String × PEState :=
  (peVarName st.nextId, { st with nextId := st.nextId + 1 })

/-! ## Static / Partially-Static Value Domain (`SVal`) -/

/-- Compile-time partial-evaluation value domain. Every residual dynamic leaf is a
variable `.var y` already bound in the emitted ANF prefix, making `reifySVal` total. -/
inductive SVal where
  /-- Canonical field literal `n < 2^56`. -/
  | lit (n : Nat)
  /-- Exact field difference `(a : F) - (b : F)` with `a < b < 2^56` (guaranteed nonzero
  and distinct from every canonical `< 2^56` literal under `FieldCompatible64 F`). -/
  | subLit (a b : Nat)
  /-- Residual runtime variable in the current ANF scope. -/
  | var (name : String)
  /-- Tuple of static/partially-static components. -/
  | tuple (items : List SVal)
  /-- Array of static/partially-static components (kept distinct from `.tuple` to
  preserve Formal Aiur's array vs tuple typing during reification). -/
  | array (items : List SVal)
  /-- Nominal enum constructor with static/partially-static fields. -/
  | ctor (enumTy : String) (ctor : String) (args : List SVal)
  /-- Deferred heap allocation `&(inner)` enabling zero-cost compile-time `.load`
  dereference without emitting runtime ROM `.store`s. -/
  | ptr (inner : SVal)
  deriving Repr, Inhabited

/-- Whether an `SVal` carries any compile-time static structure (i.e. is not merely
an opaque runtime `.var`). -/
def SVal.hasStatic : SVal → Bool
  | .var _ => false
  | _ => true

/-- Static environment mapping original local variable names to `SVal`s. -/
abbrev SEnv := List (String × SVal)

/-- Emitted ANF residual binding list. -/
abbrev LetBinds := List (Pat × Expr)

mutual

/-- Materialize any `SVal` back into a plain Formal Aiur expression. -/
def reifySVal : SVal → Expr
  | .lit n => .literal n
  | .subLit a b => .binary .sub (.literal a) (.literal b)
  | .var y => .var y
  | .tuple svs => .tuple (reifySValList svs)
  | .array svs => .array (reifySValList svs)
  | .ctor en c svs => .construct en (some []) c (reifySValList svs)
  | .ptr sv => .store (reifySVal sv)

def reifySValList : List SVal → List Expr
  | [] => []
  | sv :: svs => reifySVal sv :: reifySValList svs

end

/-- Wrap ANF bindings around `tail`. -/
def wrapLets : LetBinds → Expr → Expr
  | [], tail => tail
  | (p, rhs) :: rest, tail => .letValue p rhs (wrapLets rest tail)

/-- Wrap ANF bindings around `tail`, eta-collapsing a final `let y = rhs; y` → `rhs`. -/
def wrapLetsTail (binds : LetBinds) (tail : Expr) : Expr :=
  match binds.reverse, tail with
  | (.bind y, rhs) :: revRest, .var w =>
    if y == w then wrapLets revRest.reverse rhs else wrapLets binds tail
  | _, _ => wrapLets binds tail

/-! ## Fresh Pattern Alpha-Renaming -/

mutual

/-- Replace every `.bind x` in a pattern with a fresh residual binder `_p<id>`,
returning the renamed pattern, the `SEnv` extension mapping each `x` to `.var _p<id>`,
and the updated state. -/
def freshPat : Pat → PEState → (Pat × SEnv) × PEState
  | .bind x, st =>
    let (nm, st') := allocFresh st
    ((.bind nm, [(x, .var nm)]), st')
  | .literal n, st => ((.literal n, []), st)
  | .wildcard, st => ((.wildcard, []), st)
  | .tuple ps, st =>
    let ((ps', bs), st') := freshPatList ps st
    ((.tuple ps', bs), st')
  | .array ps, st =>
    let ((ps', bs), st') := freshPatList ps st
    ((.array ps', bs), st')
  | .construct ty c ps, st =>
    let ((ps', bs), st') := freshPatList ps st
    ((.construct ty c ps', bs), st')
  | p, st => ((p, []), st)

def freshPatList : List Pat → PEState → (List Pat × SEnv) × PEState
  | [], st => (([], []), st)
  | p :: ps, st =>
    let ((p', b1), st1) := freshPat p st
    let ((ps', b2), st2) := freshPatList ps st1
    ((p' :: ps', b1 ++ b2), st2)

end

/-! ## Static Pattern Matching & Arm Selection -/

/-- Three-valued result of matching a pattern against an `SVal` at compile time. -/
inductive MatchDec where
  /-- Pattern definitely matches, producing static environment bindings. -/
  | matched (binds : SEnv)
  /-- Pattern definitely fails to match (sound under `FieldCompatible64 F`). -/
  | noMatch
  /-- Scrutinee is too dynamic to decide statically. -/
  | unknown
  deriving Repr, Inhabited

mutual

/-- Compile-time pattern matching against `SVal`. Every `.matched` and `.noMatch`
verdict is unconditionally sound over `Aiur.Generic.SourceSemantics` under
`FieldCompatible64 F`. -/
def matchPatSVal : Pat → SVal → MatchDec
  | .wildcard, _ => .matched []
  | .bind x, sv => .matched [(x, sv)]
  | .literal n, .lit m =>
    if n < natLimit && m < natLimit then
      if n == m then .matched [] else .noMatch
    else .unknown
  | .literal n, .subLit a b =>
    if n < natLimit && a < b && b < natLimit then .noMatch
    else .unknown
  | .literal _, .tuple _ | .literal _, .array _
  | .literal _, .ctor _ _ _ | .literal _, .ptr _ => .noMatch
  | .tuple ps, .tuple svs | .tuple ps, .array svs
  | .array ps, .tuple svs | .array ps, .array svs =>
    if ps.length == svs.length then matchPatListSVal ps svs else .noMatch
  | .tuple _, .lit _ | .tuple _, .subLit _ _ | .tuple _, .ctor _ _ _ | .tuple _, .ptr _
  | .array _, .lit _ | .array _, .subLit _ _ | .array _, .ctor _ _ _ | .array _, .ptr _ =>
    .noMatch
  | .construct (.named ty []) c ps, .ctor ty' c' svs =>
    if qualifyName ty == qualifyName ty' && c == c' && ps.length == svs.length then
      matchPatListSVal ps svs
    else .noMatch
  | .construct (.named _ []) _ _, .lit _
  | .construct (.named _ []) _ _, .subLit _ _
  | .construct (.named _ []) _ _, .tuple _
  | .construct (.named _ []) _ _, .array _
  | .construct (.named _ []) _ _, .ptr _ => .noMatch
  | _, _ => .unknown

def matchPatListSVal : List Pat → List SVal → MatchDec
  | [], [] => .matched []
  | p :: ps, sv :: svs =>
    match matchPatSVal p sv with
    | .noMatch => .noMatch
    | .unknown => .unknown
    | .matched b1 =>
      match matchPatListSVal ps svs with
      | .noMatch => .noMatch
      | .unknown => .unknown
      | .matched b2 => .matched (b1 ++ b2)
  | _, _ => .noMatch

end

/-- Statically select the first matching arm of a `matchValue` if all preceding arms
definitely fail (`.noMatch`) and the selected arm definitely matches (`.matched`). -/
def selectArmSVal (sv : SVal) : List (Pat × Expr) → Option (SEnv × Expr)
  | [] => none
  | (p, body) :: rest =>
    match matchPatSVal p sv with
    | .matched binds => some (binds, body)
    | .noMatch => selectArmSVal sv rest
    | .unknown => none

theorem selectArmSVal_mem {sv : SVal} {arms : List (Pat × Expr)} {binds : SEnv} {body : Expr}
    (h : selectArmSVal sv arms = some (binds, body)) :
    ∃ p, (p, body) ∈ arms := by
  induction arms with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    unfold selectArmSVal at h
    cases hm : matchPatSVal p sv with
    | matched bs =>
      rw [hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p, h.2 ▸ List.mem_cons_self⟩
    | noMatch =>
      rw [hm] at h
      obtain ⟨p', hmem⟩ := ih h
      exact ⟨p', List.mem_cons_of_mem _ hmem⟩
    | unknown => rw [hm] at h; cases h

theorem selectArmSVal_sizeOf {sv : SVal} {arms : List (Pat × Expr)} {binds : SEnv} {body : Expr}
    (h : selectArmSVal sv arms = some (binds, body)) :
    sizeOf body < sizeOf arms := by
  obtain ⟨p, hmem⟩ := selectArmSVal_mem h
  have h1 := List.sizeOf_lt_of_mem hmem
  simp only [Prod.mk.sizeOf_spec] at h1
  omega

/-! ## Constant Folding of Pure 56-bit Arithmetic Helpers -/

/-- Exact compile-time constant folding for `TypedLower`'s 56-bit arithmetic gadgets
and `Fields::is_zero` when all arguments are canonical `< 2^56` literals. -/
def tryFoldHelperCall (nm : String) (svArgs : List SVal) : Option SVal :=
  match nm, svArgs with
  | "check_u8", [.lit k] => if k < 256 then some (.tuple []) else none
  | "check_u16", [.lit k] => if k < 65536 then some (.tuple []) else none
  | "check_u24", [.lit k] => if k < 16777216 then some (.tuple []) else none
  | "check_u56", [.lit k] => if k < natLimit then some (.tuple []) else none
  | "sub_borrow_56", [.lit a, .lit b] =>
    if a < natLimit && b < natLimit then
      some (.tuple [.lit (a - b), .lit (if b ≤ a then 1 else 0)])
    else none
  | "split_32_24", [.lit k] =>
    if k < natLimit then
      some (.tuple [.lit (k % 4294967296), .lit (k / 4294967296)])
    else none
  | "mul_56", [.lit a, .lit b] =>
    if a < natLimit && b < natLimit && a * b < natLimit then
      some (.lit (a * b))
    else none
  | "divmod_56", [.lit a, .lit b] =>
    if a < natLimit && 0 < b && b < natLimit then
      some (.tuple [.lit (a / b), .lit (a % b)])
    else none
  | "Fields::is_zero", [.lit k] =>
    if k < natLimit then
      some (.lit (if k == 0 then 1 else 0))
    else none
  | _, _ => none

/-! ## Core Let-Insertion Partial Evaluator (`peExpr`) -/

/-- Emit a fresh residual `let _p<id> = rhs` binding and return `.var _p<id>`. -/
def emitResidual (binds : LetBinds) (rhs : Expr) (st : PEState) :
    (LetBinds × SVal) × PEState :=
  let (v, st') := allocFresh st
  ((binds ++ [(.bind v, rhs)], .var v), st')

/-- Decide whether a call `nm(svArgs)` should be specialized/unfolded at the call site. -/
def lookupEligibleCallee (cfg : PEConfig) (fnMap : List (String × Fn))
    (dynFns : List String) (nm : String) (svArgs : List SVal) (remSteps : Nat) : Option Fn :=
  if remSteps == 0 || cfg.noSpecFns.contains nm then none
  else
    let allowed :=
      if cfg.staticFns.isEmpty then
        !dynFns.contains nm && svArgs.any SVal.hasStatic
      else
        cfg.staticFns.contains nm
    if !allowed then none
    else
      match fnMap.lookup nm with
      | some callee =>
        if callee.typeParams.isEmpty && callee.params.length == svArgs.length &&
            exprNodes callee.body ≤ cfg.maxCalleeNodes then
          some callee
        else none
      | none => none

mutual

/-- Strictly total, fuel-bounded let-insertion partial evaluator.
Returns `((binds, sv), st')` where `binds` are strictly fresh ANF residual bindings and
`sv` is the static/partially-static result value in the extended scope.
Terminates lexicographically on `(fuel, sizeOf e)` with zero `partial`. -/
def peExpr (cfg : PEConfig) (fnMap : List (String × Fn))
    (fuel : Nat) (curFn : Option String) (dynFns : List String)
    (senv : SEnv) : Expr → PEState → (LetBinds × SVal) × PEState
  | .literal n, st =>
    if n < natLimit then (([], .lit n), st)
    else emitResidual [] (.literal n) st
  | .var x, st =>
    match senv.lookup x with
    | some sv => (([], sv), st)
    | none => (([], .var x), st)
  | .global nm targs, st => emitResidual [] (.global nm targs) st
  | .control k b, st => emitResidual [] (.control k b) st
  | .tuple xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    ((bs, .tuple svs), st1)
  | .array xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    ((bs, .array svs), st1)
  | .construct en targs c xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    match targs with
    | some [] => ((bs, .ctor en c svs), st1)
    | _ => emitResidual bs (.construct en targs c (reifySValList svs)) st1
  | .constructAs ps ty c xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    emitResidual bs (.constructAs ps ty c (reifySValList svs)) st1
  | .record hd xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    emitResidual bs (.record hd (reifySValList svs)) st1
  | .update ps xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    emitResidual bs (.update ps (reifySValList svs)) st1
  | .repeat x n, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    emitResidual bs (.repeat (reifySVal sv) n) st1
  | .slice x s t, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    emitResidual bs (.slice (reifySVal sv) s t) st1
  | .member x f, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    emitResidual bs (.member (reifySVal sv) f) st1
  | .store x, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    ((bs, .ptr sv), st1)
  | .load x, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    match sv with
    | .ptr inner => ((bs, inner), st1)
    | _ => emitResidual bs (.load (reifySVal sv)) st1
  | .project x i, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    match sv with
    | .tuple svs | .array svs =>
      match svs[i]? with
      | some svi => ((bs, svi), st1)
      | none => emitResidual bs (.project (reifySVal sv) i) st1
    | _ => emitResidual bs (.project (reifySVal sv) i) st1
  | .index x i, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    match sv with
    | .tuple svs | .array svs =>
      match svs[i]? with
      | some svi => ((bs, svi), st1)
      | none => emitResidual bs (.index (reifySVal sv) i) st1
    | _ => emitResidual bs (.index (reifySVal sv) i) st1
  | .hint ty k ch, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv k st
    emitResidual bs (.hint ty (reifySVal sv) ch) st1
  | .neg x, st =>
    let ((bs, sv), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    match sv with
    | .lit 0 => ((bs, .lit 0), st1)
    | _ => emitResidual bs (.neg (reifySVal sv)) st1
  | .binary op l r, st =>
    let ((b1, sv1), st1) := peExpr cfg fnMap fuel curFn dynFns senv l st
    let ((b2, sv2), st2) := peExpr cfg fnMap fuel curFn dynFns senv r st1
    let bs := b1 ++ b2
    match op, sv1, sv2 with
    | .add, .lit a, .lit b =>
      if a < natLimit && b < natLimit && a + b < natLimit then
        ((bs, .lit (a + b)), st2)
      else
        emitResidual bs (.binary op (reifySVal sv1) (reifySVal sv2)) st2
    | .sub, .lit a, .lit b =>
      if a < natLimit && b < natLimit then
        if b ≤ a then ((bs, .lit (a - b)), st2)
        else ((bs, .subLit a b), st2)
      else
        emitResidual bs (.binary op (reifySVal sv1) (reifySVal sv2)) st2
    | .mul, .lit a, .lit b =>
      if a < natLimit && b < natLimit && a * b < natLimit then
        ((bs, .lit (a * b)), st2)
      else
        emitResidual bs (.binary op (reifySVal sv1) (reifySVal sv2)) st2
    | _, _, _ =>
      emitResidual bs (.binary op (reifySVal sv1) (reifySVal sv2)) st2
  | .builtin op xs, st =>
    let ((bs, svs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    match op, svs with
    | .assertEq _, [.lit a, .lit b] =>
      if a == b && a < natLimit then ((bs, .tuple []), st1)
      else emitResidual bs (.builtin op (reifySValList svs)) st1
    | _, _ => emitResidual bs (.builtin op (reifySValList svs)) st1
  | .letValue p rhs body, st =>
    let ((bRhs, svRhs), st1) := peExpr cfg fnMap fuel curFn dynFns senv rhs st
    match matchPatSVal p svRhs with
    | .matched sbinds =>
      let ((bBody, svBody), st2) :=
        peExpr cfg fnMap fuel curFn dynFns (sbinds ++ senv) body st1
      ((bRhs ++ bBody, svBody), st2)
    | _ =>
      let ((p', pBinds), st2) := freshPat p st1
      let ((bBody, svBody), st3) :=
        peExpr cfg fnMap fuel curFn dynFns (pBinds ++ senv) body st2
      ((bRhs ++ [(p', reifySVal svRhs)] ++ bBody, svBody), st3)
  | .matchValue scrut arms, st =>
    let ((bScrut, svScrut), st1) := peExpr cfg fnMap fuel curFn dynFns senv scrut st
    match hsel : selectArmSVal svScrut arms with
    | some (sbinds, armBody) =>
      have _ : sizeOf armBody < sizeOf arms := selectArmSVal_sizeOf hsel
      let ((bArm, svArm), st2) :=
        peExpr cfg fnMap fuel curFn dynFns (sbinds ++ senv) armBody st1
      ((bScrut ++ bArm, svArm), st2)
    | none =>
      let dynFns' := match curFn with
        | some nm => if dynFns.contains nm then dynFns else nm :: dynFns
        | none => dynFns
      let (arms', st2) := peArms cfg fnMap fuel curFn dynFns' senv arms st1
      emitResidual bScrut (.matchValue (reifySVal svScrut) arms') st2
  | .call nm targs xs, st =>
    let ((bArgs, svArgs), st1) := peExprList cfg fnMap fuel curFn dynFns senv xs st
    match targs with
    | some [] =>
      match tryFoldHelperCall nm svArgs with
      | some svRes => ((bArgs, svRes), st1)
      | none =>
        match fuel with
        | 0 => emitResidual bArgs (.call nm (some []) (reifySValList svArgs)) st1
        | fuel' + 1 =>
          match lookupEligibleCallee cfg fnMap dynFns nm svArgs st1.specSteps with
          | some callee =>
            let st2 := { st1 with specSteps := st1.specSteps - 1 }
            let calleeSEnv := (callee.params.map Prod.fst).zip svArgs
            let ((bCallee, svRes), st3) :=
              peExpr cfg fnMap fuel' (some nm) dynFns calleeSEnv callee.body st2
            ((bArgs ++ bCallee, svRes), st3)
          | none =>
            emitResidual bArgs (.call nm (some []) (reifySValList svArgs)) st1
    | _ =>
      emitResidual bArgs (.call nm targs (reifySValList svArgs)) st1
termination_by e _ => (fuel, sizeOf e)

def peExprList (cfg : PEConfig) (fnMap : List (String × Fn))
    (fuel : Nat) (curFn : Option String) (dynFns : List String)
    (senv : SEnv) : List Expr → PEState → (LetBinds × List SVal) × PEState
  | [], st => (([], []), st)
  | x :: xs, st =>
    let ((b1, sv1), st1) := peExpr cfg fnMap fuel curFn dynFns senv x st
    let ((b2, svs), st2) := peExprList cfg fnMap fuel curFn dynFns senv xs st1
    ((b1 ++ b2, sv1 :: svs), st2)
termination_by xs _ => (fuel, sizeOf xs)

def peArms (cfg : PEConfig) (fnMap : List (String × Fn))
    (fuel : Nat) (curFn : Option String) (dynFns : List String)
    (senv : SEnv) : List (Pat × Expr) → PEState → List (Pat × Expr) × PEState
  | [], st => ([], st)
  | (p, b) :: rest, st =>
    let ((p', pBinds), st1) := freshPat p st
    let ((bArm, svArm), st2) := peExpr cfg fnMap fuel curFn dynFns (pBinds ++ senv) b st1
    let (rest', st3) := peArms cfg fnMap fuel curFn dynFns senv rest st2
    ((p', wrapLetsTail bArm (reifySVal svArm)) :: rest', st3)
termination_by arms _ => (fuel, sizeOf arms)

end

/-! ## Function-Level & Program-Level Entrypoints -/

/-- Partially evaluate a single `Prog` function `f` against `fnMap`.
Fixed helpers (`cfg.noSpecFns`), polymorphic functions, and functions with any
`_p`-prefixed parameter are preserved verbatim. -/
def peFn (cfg : PEConfig) (fnMap : List (String × Fn)) (f : Fn) : Fn :=
  if !f.typeParams.isEmpty || cfg.noSpecFns.contains f.name ||
      (f.params.map Prod.fst).any hasPEPrefix then
    f
  else
    let initSEnv : SEnv := f.params.map fun (p, _) => (p, SVal.var p)
    let ((binds, sv), _) :=
      peExpr cfg fnMap cfg.maxSpecDepth (some f.name) [] initSEnv f.body
        { nextId := 0, specSteps := cfg.maxSpecSteps }
    { f with body := wrapLetsTail binds (reifySVal sv) }

/-- Partially evaluate all functions in `fns` (preserving exact order, names,
signatures, and fixed helpers). -/
def partialEvalFns (cfg : PEConfig := {}) (fns : List Fn) : List Fn :=
  let fnMap := fns.map fun f => (f.name, f)
  fns.map (peFn cfg fnMap)

/-- Partially evaluate `fns` and (when `cfg.prune = true`) prune functions no longer
reachable from `roots`. -/
def partialEvalFnsPruned (cfg : PEConfig := {}) (roots : List String) (fns : List Fn) : List Fn :=
  let opt := partialEvalFns cfg fns
  if cfg.prune then pruneUnreachable roots opt else opt

/-- Partially evaluate a lowered `Prog` program and optionally prune unreachable functions. -/
def partialEvalProg (cfg : PEConfig := {}) (roots : List String)
    (prog : Aiur.Generic.Program Nat) : Aiur.Generic.Program Nat :=
  { prog with functions := partialEvalFnsPruned cfg roots prog.functions }

/-! ## Plainness Preservation Proofs (Zero `sorry`) -/

mutual

theorem isPlainExpr_reifySVal : ∀ sv : SVal, isPlainExpr (reifySVal sv) = true
  | .lit _ => rfl
  | .subLit _ _ => rfl
  | .var _ => rfl
  | .tuple svs => isPlainList_reifySValList svs
  | .array svs => isPlainList_reifySValList svs
  | .ctor _ _ svs => isPlainList_reifySValList svs
  | .ptr sv => isPlainExpr_reifySVal sv

theorem isPlainList_reifySValList : ∀ svs : List SVal, isPlainList (reifySValList svs) = true
  | [] => rfl
  | sv :: svs => by
    simp only [reifySValList, isPlainList, isPlainExpr_reifySVal sv,
      isPlainList_reifySValList svs, Bool.and_self]

end

theorem isPlainExpr_wrapLets (binds : LetBinds) (tail : Expr)
    (hb : ∀ p ∈ binds, isPlainExpr p.2 = true) (ht : isPlainExpr tail = true) :
    isPlainExpr (wrapLets binds tail) = true := by
  induction binds with
  | nil => exact ht
  | cons hd tl ih =>
    rcases hd with ⟨p, rhs⟩
    simp only [wrapLets, isPlainExpr, Bool.and_eq_true]
    exact ⟨hb (p, rhs) List.mem_cons_self,
      ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))⟩

theorem isPlainExpr_wrapLetsTail (binds : LetBinds) (tail : Expr)
    (hb : ∀ p ∈ binds, isPlainExpr p.2 = true) (ht : isPlainExpr tail = true) :
    isPlainExpr (wrapLetsTail binds tail) = true := by
  unfold wrapLetsTail
  cases hrev : binds.reverse with
  | nil => exact isPlainExpr_wrapLets binds tail hb ht
  | cons hd revRest =>
    rcases hd with ⟨p, rhs⟩
    cases p with
    | bind y =>
      cases tail with
      | var w =>
        dsimp only
        by_cases hyw : (y == w) = true
        · simp only [hyw, ↓reduceIte]
          apply isPlainExpr_wrapLets
          · intro q hq
            apply hb q
            exact List.mem_reverse.mp (by rw [hrev]; exact List.mem_cons_of_mem _ (List.mem_reverse.mp hq))
          · exact hb (.bind y, rhs) (List.mem_reverse.mp (by rw [hrev]; exact List.mem_cons_self))
        · simp only [hyw, Bool.false_eq_true, ↓reduceIte]
          exact isPlainExpr_wrapLets binds (.var w) hb ht
      | _ => exact isPlainExpr_wrapLets binds _ hb ht
    | _ => exact isPlainExpr_wrapLets binds tail hb ht

private theorem emitResidual_plain (binds : LetBinds) (rhs : Expr) (st : PEState)
    (hb : ∀ p ∈ binds, isPlainExpr p.2 = true) (hr : isPlainExpr rhs = true) :
    ∀ p ∈ (emitResidual binds rhs st).1.1, isPlainExpr p.2 = true := by
  intro q hq
  simp only [emitResidual, allocFresh] at hq
  rcases List.mem_append.mp hq with h1 | h2
  · exact hb q h1
  · simp only [List.mem_singleton] at h2
    subst h2
    exact hr

private theorem mem_append_plain {b1 b2 : LetBinds}
    (h1 : ∀ p ∈ b1, isPlainExpr p.2 = true) (h2 : ∀ p ∈ b2, isPlainExpr p.2 = true) :
    ∀ p ∈ b1 ++ b2, isPlainExpr p.2 = true := by
  intro q hq
  rcases List.mem_append.mp hq with ha | hb
  · exact h1 q ha
  · exact h2 q hb

theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β} :
    ∀ {xs : List (α × β)}, xs.lookup k = some v → (k, v) ∈ xs
  | [], h => by cases h
  | (a, b) :: tl, h => by
    simp only [List.lookup] at h
    by_cases hka : k = a
    · subst hka
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [beq_false_of_ne hka] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem lookupEligibleCallee_spec {cfg : PEConfig} {fnMap : List (String × Fn)}
    {dynFns : List String} {nm : String} {svArgs : List SVal} {rem : Nat} {callee : Fn}
    (h : lookupEligibleCallee cfg fnMap dynFns nm svArgs rem = some callee) :
    (nm, callee) ∈ fnMap ∧ callee.typeParams = [] ∧ callee.params.length = svArgs.length := by
  unfold lookupEligibleCallee at h
  by_cases h1 : (rem == 0 || cfg.noSpecFns.contains nm) = true
  · simp only [h1, ↓reduceIte] at h; cases h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    generalize hall : (if cfg.staticFns.isEmpty = true then !dynFns.contains nm && svArgs.any SVal.hasStatic
        else cfg.staticFns.contains nm) = allowed at h
    by_cases h2 : (!allowed) = true
    · simp only [h2, ↓reduceIte] at h; cases h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      cases hl : fnMap.lookup nm with
      | none => rw [hl] at h; cases h
      | some f =>
        rw [hl] at h
        dsimp only at h
        by_cases h3 : (f.typeParams.isEmpty && f.params.length == svArgs.length &&
            decide (exprNodes f.body ≤ cfg.maxCalleeNodes)) = true
        · simp only [h3, ↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h3
          exact ⟨mem_of_lookup_eq_some hl, h3.1.1, h3.1.2⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h; cases h

mutual

theorem peExpr_binds_plain (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnPlain : ∀ p ∈ fnMap, isPlainExpr p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (e : Expr) (st : PEState),
      isPlainExpr e = true →
      ∀ q ∈ (peExpr cfg fnMap fuel curFn dynFns senv e st).1.1,
        isPlainExpr q.2 = true
  | _, _, _, _, .global _ _, _, h => by simp [isPlainExpr] at h
  | _, _, _, _, .control _ _, _, h => by simp [isPlainExpr] at h
  | _, _, _, _, .literal n, st, _ => by
    rw [peExpr]
    by_cases hlt : n < natLimit
    · simp only [hlt, ↓reduceIte]; intro _ hq; cases hq
    · simp only [hlt, ↓reduceIte]
      exact emitResidual_plain [] (.literal n) st (fun _ h => by cases h) rfl
  | _, _, _, senv, .var x, st, _ => by
    rw [peExpr]
    cases senv.lookup x <;> intro _ hq <;> cases hq
  | fuel, cur, dyn, senv, .tuple xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢; exact hxs
  | fuel, cur, dyn, senv, .array xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢; exact hxs
  | fuel, cur, dyn, senv, .construct en targs c xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢
    cases targs with
    | none => exact emitResidual_plain bs _ st1 hxs (isPlainList_reifySValList svs)
    | some ts =>
      cases ts with
      | nil => exact hxs
      | cons _ _ => exact emitResidual_plain bs _ st1 hxs (isPlainList_reifySValList svs)
  | fuel, cur, dyn, senv, .constructAs ps ty c xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢
    exact emitResidual_plain bs _ st1 hxs (isPlainList_reifySValList svs)
  | fuel, cur, dyn, senv, .record hd xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢
    exact emitResidual_plain bs _ st1 hxs (isPlainList_reifySValList svs)
  | fuel, cur, dyn, senv, .update ps xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢
    exact emitResidual_plain bs _ st1 hxs (isPlainList_reifySValList svs)
  | fuel, cur, dyn, senv, .repeat x n, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal sv)
  | fuel, cur, dyn, senv, .slice x s t, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal sv)
  | fuel, cur, dyn, senv, .member x f, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal sv)
  | fuel, cur, dyn, senv, .store x, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢; exact hx
  | fuel, cur, dyn, senv, .load x, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    cases sv with
    | ptr _ => exact hx
    | _ => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
  | fuel, cur, dyn, senv, .project x i, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only
      cases svs[i]? with
      | some _ => exact hx
      | none => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
    | _ => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
  | fuel, cur, dyn, senv, .index x i, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only
      cases svs[i]? with
      | some _ => exact hx
      | none => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
    | _ => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
  | fuel, cur, dyn, senv, .hint ty k ch, st, h => by
    rw [peExpr]
    have hk := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv k st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv k st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hk; dsimp only at hk ⊢
    exact emitResidual_plain bs _ st1 hk (isPlainExpr_reifySVal sv)
  | fuel, cur, dyn, senv, .neg x, st, h => by
    rw [peExpr]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h
    rcases hres : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [hres] at hx; dsimp only at hx ⊢
    cases sv with
    | lit n =>
      cases n with
      | zero => exact hx
      | succ _ => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
    | _ => exact emitResidual_plain bs _ st1 hx (isPlainExpr_reifySVal _)
  | fuel, cur, dyn, senv, .binary op l r, st, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    rw [peExpr]
    have hl := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv l st h.1
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv l st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hl; dsimp only at hl ⊢
    have hr := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv r st1 h.2
    rcases h2 : peExpr cfg fnMap fuel cur dyn senv r st1 with ⟨⟨b2, sv2⟩, st2⟩
    rw [h2] at hr; dsimp only at hr ⊢
    have hboth := mem_append_plain hl hr
    have hbin : isPlainExpr (.binary op (reifySVal sv1) (reifySVal sv2)) = true := by
      simp [isPlainExpr, isPlainExpr_reifySVal]
    split
    · split
      · exact hboth
      · exact emitResidual_plain _ _ st2 hboth hbin
    · split
      · split
        · exact hboth
        · exact hboth
      · exact emitResidual_plain _ _ st2 hboth hbin
    · split
      · exact hboth
      · exact emitResidual_plain _ _ st2 hboth hbin
    · exact emitResidual_plain _ _ st2 hboth hbin
  | fuel, cur, dyn, senv, .builtin op xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases hres : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [hres] at hxs; dsimp only at hxs ⊢
    have hbu : isPlainExpr (.builtin op (reifySValList svs)) = true :=
      isPlainList_reifySValList svs
    split
    · split
      · exact hxs
      · exact emitResidual_plain _ _ st1 hxs hbu
    · exact emitResidual_plain _ _ st1 hxs hbu
  | fuel, cur, dyn, senv, .letValue p rhs body, st, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    rw [peExpr]
    have hrhs := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv rhs st h.1
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv rhs st with ⟨⟨bRhs, svRhs⟩, st1⟩
    rw [h1] at hrhs; dsimp only at hrhs ⊢
    cases matchPatSVal p svRhs with
    | matched sbinds =>
      dsimp only
      have hbody := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn (sbinds ++ senv) body st1 h.2
      rcases h2 : peExpr cfg fnMap fuel cur dyn (sbinds ++ senv) body st1 with ⟨⟨bBody, svBody⟩, st2⟩
      rw [h2] at hbody; dsimp only at hbody ⊢
      exact mem_append_plain hrhs hbody
    | noMatch | unknown =>
      dsimp only
      rcases _ : freshPat p st1 with ⟨⟨p', pBinds⟩, st2⟩
      dsimp only
      have hbody := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn (pBinds ++ senv) body st2 h.2
      rcases h2 : peExpr cfg fnMap fuel cur dyn (pBinds ++ senv) body st2 with ⟨⟨bBody, svBody⟩, st3⟩
      rw [h2] at hbody; dsimp only at hbody ⊢
      refine mem_append_plain (mem_append_plain hrhs ?_) hbody
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact isPlainExpr_reifySVal svRhs
  | fuel, cur, dyn, senv, .matchValue scrut arms, st, h => by
    simp only [isPlainExpr, Bool.and_eq_true] at h
    rw [peExpr.eq_def]
    dsimp only
    have hsc := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv scrut st h.1
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv scrut st with ⟨⟨bScrut, svScrut⟩, st1⟩
    rw [h1] at hsc; dsimp only at hsc ⊢
    cases hsel : selectArmSVal svScrut arms with
    | some sb =>
      rcases sb with ⟨sbinds, armBody⟩
      dsimp only
      have hsz : sizeOf armBody < sizeOf arms := selectArmSVal_sizeOf hsel
      have harmPlain : isPlainExpr armBody = true := by
        obtain ⟨p, hmem⟩ := selectArmSVal_mem hsel
        clear hsel hsz hsc h1
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases hd with ⟨p0, b0⟩
          simp only [isPlainArms, Bool.and_eq_true] at h
          rcases List.mem_cons.mp hmem with heq | htl
          · obtain ⟨_, rfl⟩ := Prod.mk.inj heq; exact h.2.1
          · exact ih ⟨h.1, h.2.2⟩ htl
      have harm := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn (sbinds ++ senv) armBody st1 harmPlain
      rcases h2 : peExpr cfg fnMap fuel cur dyn (sbinds ++ senv) armBody st1 with ⟨⟨bArm, svArm⟩, st2⟩
      rw [h2] at harm; dsimp only at harm ⊢
      exact mem_append_plain hsc harm
    | none =>
      dsimp only
      let dyn' := match cur with | some nm => if dyn.contains nm then dyn else nm :: dyn | none => dyn
      have harms := peArms_plain cfg fnMap hfnPlain fuel cur dyn' senv arms st1 h.2
      rcases h2 : peArms cfg fnMap fuel cur dyn' senv arms st1 with ⟨arms', st2⟩
      rw [h2] at harms; dsimp only at harms ⊢
      exact emitResidual_plain bScrut _ st2 hsc (by simp [isPlainExpr, isPlainExpr_reifySVal, harms])
  | fuel, cur, dyn, senv, .call nm targs xs, st, h => by
    rw [peExpr]
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st h
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bArgs, svArgs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    have hcall : ∀ ts, isPlainExpr (.call nm ts (reifySValList svArgs)) = true :=
      fun _ => isPlainList_reifySValList svArgs
    cases targs with
    | none => exact emitResidual_plain bArgs _ st1 hxs (hcall none)
    | some ts =>
      cases ts with
      | cons _ _ => exact emitResidual_plain bArgs _ st1 hxs (hcall _)
      | nil =>
        dsimp only
        cases tryFoldHelperCall nm svArgs with
        | some _ => exact hxs
        | none =>
          dsimp only
          cases fuel with
          | zero => exact emitResidual_plain bArgs _ st1 hxs (hcall (some []))
          | succ fuel' =>
            dsimp only
            cases hcal : lookupEligibleCallee cfg fnMap dyn nm svArgs st1.specSteps with
            | none => exact emitResidual_plain bArgs _ st1 hxs (hcall (some []))
            | some callee =>
              dsimp only
              have hcp := hfnPlain (nm, callee) (lookupEligibleCallee_spec hcal).1
              have hbody := peExpr_binds_plain cfg fnMap hfnPlain fuel' (some nm) dyn
                ((callee.params.map Prod.fst).zip svArgs) callee.body
                { st1 with specSteps := st1.specSteps - 1 } hcp
              rcases h2 : peExpr cfg fnMap fuel' (some nm) dyn
                  ((callee.params.map Prod.fst).zip svArgs) callee.body
                  { st1 with specSteps := st1.specSteps - 1 } with ⟨⟨bCal, svRes⟩, st3⟩
              rw [h2] at hbody; dsimp only at hbody ⊢
              exact mem_append_plain hxs hbody
termination_by fuel _ _ _ e _ _ => (fuel, sizeOf e)

theorem peExprList_binds_plain (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnPlain : ∀ p ∈ fnMap, isPlainExpr p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (xs : List Expr) (st : PEState),
      isPlainList xs = true →
      ∀ q ∈ (peExprList cfg fnMap fuel curFn dynFns senv xs st).1.1,
        isPlainExpr q.2 = true
  | _, _, _, _, [], _, _ => fun _ hq => by rw [peExprList] at hq; cases hq
  | fuel, cur, dyn, senv, x :: xs, st, h => by
    simp only [isPlainList, Bool.and_eq_true] at h
    rw [peExprList]
    have hx := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn senv x st h.1
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    have hxs := peExprList_binds_plain cfg fnMap hfnPlain fuel cur dyn senv xs st1 h.2
    rcases h2 : peExprList cfg fnMap fuel cur dyn senv xs st1 with ⟨⟨b2, svs⟩, st2⟩
    rw [h2] at hxs; dsimp only at hxs ⊢
    exact mem_append_plain hx hxs
termination_by fuel _ _ _ xs _ _ => (fuel, sizeOf xs)

theorem peArms_plain (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnPlain : ∀ p ∈ fnMap, isPlainExpr p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (arms : List (Pat × Expr)) (st : PEState),
      isPlainArms arms = true →
      isPlainArms (peArms cfg fnMap fuel curFn dynFns senv arms st).1 = true
  | _, _, _, _, [], _, _ => by rw [peArms]; rfl
  | fuel, cur, dyn, senv, (p, b) :: rest, st, h => by
    simp only [isPlainArms, Bool.and_eq_true] at h
    rw [peArms]
    rcases _ : freshPat p st with ⟨⟨p', pBinds⟩, st1⟩
    dsimp only
    have hb := peExpr_binds_plain cfg fnMap hfnPlain fuel cur dyn (pBinds ++ senv) b st1 h.1
    rcases h1 : peExpr cfg fnMap fuel cur dyn (pBinds ++ senv) b st1 with ⟨⟨bArm, svArm⟩, st2⟩
    rw [h1] at hb; dsimp only at hb ⊢
    have hrest := peArms_plain cfg fnMap hfnPlain fuel cur dyn senv rest st2 h.2
    rcases h2 : peArms cfg fnMap fuel cur dyn senv rest st2 with ⟨rest', st3⟩
    rw [h2] at hrest; dsimp only at hrest ⊢
    simp only [isPlainArms, Bool.and_eq_true]
    exact ⟨isPlainExpr_wrapLetsTail bArm (reifySVal svArm) hb (isPlainExpr_reifySVal _), hrest⟩
termination_by fuel _ _ _ arms _ _ => (fuel, sizeOf arms)

end

theorem isPlainExpr_peFn (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnPlain : ∀ p ∈ fnMap, isPlainExpr p.2.body = true)
    {f : Fn} (hf : isPlainExpr f.body = true) :
    isPlainExpr (peFn cfg fnMap f).body = true := by
  unfold peFn
  split
  · exact hf
  · exact isPlainExpr_wrapLetsTail _ _
      (peExpr_binds_plain cfg fnMap hfnPlain cfg.maxSpecDepth (some f.name) [] _ f.body _ hf)
      (isPlainExpr_reifySVal _)

theorem isPlainExpr_partialEvalFns (cfg : PEConfig) {fns : List Fn}
    (hplain : ∀ f ∈ fns, isPlainExpr f.body = true) :
    ∀ f' ∈ partialEvalFns cfg fns, isPlainExpr f'.body = true := by
  intro f' hf'
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
  apply isPlainExpr_peFn cfg (fns.map fun g => (g.name, g))
  · intro p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    exact hplain g hg
  · exact hplain f hf

theorem isPlainExpr_partialEvalFnsPruned (cfg : PEConfig) (roots : List String) {fns : List Fn}
    (hplain : ∀ f ∈ fns, isPlainExpr f.body = true) :
    ∀ f' ∈ partialEvalFnsPruned cfg roots fns, isPlainExpr f'.body = true := by
  intro f' hf'
  unfold partialEvalFnsPruned at hf'
  split at hf'
  · unfold pruneUnreachable at hf'
    exact isPlainExpr_partialEvalFns cfg hplain f' (List.mem_filter.mp hf').1
  · exact isPlainExpr_partialEvalFns cfg hplain f' hf'

theorem isPlainExpr_partialEvalProg (cfg : PEConfig) (roots : List String)
    {prog : Aiur.Generic.Program Nat}
    (hplain : ∀ f ∈ prog.functions, isPlainExpr f.body = true) :
    ∀ f' ∈ (partialEvalProg cfg roots prog).functions, isPlainExpr f'.body = true :=
  isPlainExpr_partialEvalFnsPruned cfg roots hplain

end IxCC.AiurBackend.PartialEval
