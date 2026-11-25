import IxCCAiur.Peephole

/-! # Pre-Peephole Inlining & Known-Constructor Folding (`IxCCAiur.InlineFuse`)

Runs between `TypedLower` emission and `Peephole.rewriteFn` on lowered `Prog`
functions:

1. **Alpha-safe inlining of small non-recursive `isInline = true` functions**
   (such as `rotr16`/`rotr12`/`rotr8`/`rotr7`, `g`, `permute`, and
   defunctionalized typeclass closures `HAdd`/`HXor` + their `apply`
   dispatcher!).
2. **Copy propagation + known-constructor `matchValue` folding + dead-let
   elimination**: collapses `apply(K4, a, b)` directly to `UInt32::add(a, b)`,
   `apply(K6, a, b)` directly to `UInt32::xor(a, b)`, and struct projections
   on locally constructed tuples/records (`GOut`, `St16`, `Msg16`) directly
   to the underlying variables with zero residual `match` arms.
3. **Peephole fusion (`Peephole.rewriteExpr`)**: with inlined `rotr12`/`rotr7`
   and unfolded `UInt32::add`/`UInt32::xor` now adjacent in the same ANF body,
   `Peephole` fuses `add3`, `rotr16`, `rotr8`, `xor_rotr12`, `xor_rotr7`, and
   constant byte shifts across function boundaries!

Strictly total (zero `partial`), zero `sorry`, zero `native_decide`, preserves
`Lower.isPlainExpr = true` on every expression. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.InlineFuse

open IxCC.AiurBackend.Lower (Expr Pat Fn isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.Peephole (rewriteExpr)

/-! ## Structural Utilities (`exprNodes`, `callsFn`, `patBoundVars`, `freeVars`, `prefixLocals`) -/

mutual

def exprNodes : Expr → Nat
  | .literal _ | .var _ | .global _ _ => 1
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs =>
    1 + exprListNodes xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => 1 + exprNodes x
  | .letValue _ x b | .binary _ x b => 1 + exprNodes x + exprNodes b
  | .matchValue x arms => 1 + exprNodes x + armListNodes arms
  | .control _ _ => 1

def exprListNodes : List Expr → Nat
  | [] => 0
  | x :: xs => exprNodes x + exprListNodes xs

def armListNodes : List (Pat × Expr) → Nat
  | [] => 0
  | (_, b) :: rest => exprNodes b + armListNodes rest

end

mutual

def callsAny (names : List String) : Expr → Bool
  | .call nm _ xs => names.contains nm || callsAnyList names xs
  | .literal _ | .var _ | .global _ _ | .control _ _ => false
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => callsAnyList names xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => callsAny names x
  | .letValue _ x b | .binary _ x b => callsAny names x || callsAny names b
  | .matchValue x arms => callsAny names x || callsAnyArms names arms

def callsAnyList (names : List String) : List Expr → Bool
  | [] => false
  | x :: xs => callsAny names x || callsAnyList names xs

def callsAnyArms (names : List String) : List (Pat × Expr) → Bool
  | [] => false
  | (_, b) :: rest => callsAny names b || callsAnyArms names rest

end

mutual

def patBoundVars : Pat → List String
  | .bind x => [x]
  | .tuple ps | .array ps | .construct _ _ ps | .constructAs _ _ _ ps | .record _ ps =>
    patListBoundVars ps
  | _ => []

def patListBoundVars : List Pat → List String
  | [] => []
  | p :: ps => patBoundVars p ++ patListBoundVars ps

end

mutual

def hasFreeVar (v : String) : Expr → Bool
  | .var x => x == v
  | .literal _ | .global _ _ | .control _ _ => false
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => hasFreeVarList v xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => hasFreeVar v x
  | .binary _ x y => hasFreeVar v x || hasFreeVar v y
  | .letValue p x b => hasFreeVar v x || (!(patBoundVars p).contains v && hasFreeVar v b)
  | .matchValue x arms => hasFreeVar v x || hasFreeVarArms v arms

def hasFreeVarList (v : String) : List Expr → Bool
  | [] => false
  | x :: xs => hasFreeVar v x || hasFreeVarList v xs

def hasFreeVarArms (v : String) : List (Pat × Expr) → Bool
  | [] => false
  | (p, b) :: rest =>
    (!(patBoundVars p).contains v && hasFreeVar v b) || hasFreeVarArms v rest

end

/-! ## Alpha-Safe Variable Prefixing for Inlined Callees -/

mutual

def prefixPat (pfx : String) : Pat → Pat
  | .bind x => .bind (pfx ++ x)
  | .tuple ps => .tuple (prefixPatList pfx ps)
  | .array ps => .array (prefixPatList pfx ps)
  | .construct ty nm ps => .construct ty nm (prefixPatList pfx ps)
  | .constructAs ty targs nm ps => .constructAs ty targs nm (prefixPatList pfx ps)
  | .record ty ps => .record ty (prefixPatList pfx ps)
  | p => p

def prefixPatList (pfx : String) : List Pat → List Pat
  | [] => []
  | p :: ps => prefixPat pfx p :: prefixPatList pfx ps

end

mutual

def prefixExpr (pfx : String) (scope : List String) : Expr → Expr
  | .var x => if scope.contains x then .var (pfx ++ x) else .var x
  | .literal n => .literal n
  | .global nm targs => .global nm targs
  | .control c e => .control c e
  | .tuple xs => .tuple (prefixExprList pfx scope xs)
  | .array xs => .array (prefixExprList pfx scope xs)
  | .construct ty targs nm xs => .construct ty targs nm (prefixExprList pfx scope xs)
  | .constructAs ty targs nm xs => .constructAs ty targs nm (prefixExprList pfx scope xs)
  | .record ty fs => .record ty (prefixExprList pfx scope fs)
  | .update ty fs => .update ty (prefixExprList pfx scope fs)
  | .builtin op xs => .builtin op (prefixExprList pfx scope xs)
  | .call nm targs xs => .call nm targs (prefixExprList pfx scope xs)
  | .repeat x n => .repeat (prefixExpr pfx scope x) n
  | .index x i => .index (prefixExpr pfx scope x) i
  | .slice x a b => .slice (prefixExpr pfx scope x) a b
  | .member x f => .member (prefixExpr pfx scope x) f
  | .project x i => .project (prefixExpr pfx scope x) i
  | .store x => .store (prefixExpr pfx scope x)
  | .load x => .load (prefixExpr pfx scope x)
  | .hint ty x ch => .hint ty (prefixExpr pfx scope x) ch
  | .neg x => .neg (prefixExpr pfx scope x)
  | .binary op x y => .binary op (prefixExpr pfx scope x) (prefixExpr pfx scope y)
  | .letValue p x b =>
    let x' := prefixExpr pfx scope x
    let scope' := patBoundVars p ++ scope
    .letValue (prefixPat pfx p) x' (prefixExpr pfx scope' b)
  | .matchValue x arms =>
    .matchValue (prefixExpr pfx scope x) (prefixArms pfx scope arms)

def prefixExprList (pfx : String) (scope : List String) : List Expr → List Expr
  | [] => []
  | x :: xs => prefixExpr pfx scope x :: prefixExprList pfx scope xs

def prefixArms (pfx : String) (scope : List String) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest =>
    (prefixPat pfx p, prefixExpr pfx (patBoundVars p ++ scope) b) :: prefixArms pfx scope rest

end

/-! ## Step 1: Inline Small Non-Recursive `isInline = true` Functions -/

/-- Wrap `body` in `let (pfx ++ p_i) := arg_i` bindings for all parameters. -/
private def bindParams (pfx : String) : List (String × Expr) → Expr → Expr
  | [], body => body
  | (p, arg) :: rest, body => .letValue (.bind (pfx ++ p)) arg (bindParams pfx rest body)

mutual

private def inlineCallsM (imap : List (String × Fn)) : Expr → StateM Nat Expr
  | .call nm targs xs => do
    let xs' ← inlineCallsListM imap xs
    match targs, imap.lookup nm with
    | some [], some callee =>
      if callee.params.length == xs'.length then
        let id ← get
        set (id + 1)
        let pfx := s!"_i{id}_"
        let pNames := callee.params.map Prod.fst
        let renamed := prefixExpr pfx pNames callee.body
        return bindParams pfx (pNames.zip xs') renamed
      else
        return .call nm targs xs'
    | _, _ => return .call nm targs xs'
  | .literal n => pure (.literal n)
  | .var x => pure (.var x)
  | .global nm targs => pure (.global nm targs)
  | .control c e => pure (.control c e)
  | .tuple xs => return .tuple (← inlineCallsListM imap xs)
  | .array xs => return .array (← inlineCallsListM imap xs)
  | .construct ty targs nm xs => return .construct ty targs nm (← inlineCallsListM imap xs)
  | .constructAs ty targs nm xs => return .constructAs ty targs nm (← inlineCallsListM imap xs)
  | .record ty fs => return .record ty (← inlineCallsListM imap fs)
  | .update ty fs => return .update ty (← inlineCallsListM imap fs)
  | .builtin op xs => return .builtin op (← inlineCallsListM imap xs)
  | .repeat x n => return .repeat (← inlineCallsM imap x) n
  | .index x i => return .index (← inlineCallsM imap x) i
  | .slice x a b => return .slice (← inlineCallsM imap x) a b
  | .member x f => return .member (← inlineCallsM imap x) f
  | .project x i => return .project (← inlineCallsM imap x) i
  | .store x => return .store (← inlineCallsM imap x)
  | .load x => return .load (← inlineCallsM imap x)
  | .hint ty x ch => return .hint ty (← inlineCallsM imap x) ch
  | .neg x => return .neg (← inlineCallsM imap x)
  | .binary op x y => return .binary op (← inlineCallsM imap x) (← inlineCallsM imap y)
  | .letValue p x b =>
    return .letValue p (← inlineCallsM imap x) (← inlineCallsM imap b)
  | .matchValue x arms =>
    return .matchValue (← inlineCallsM imap x) (← inlineCallsArmsM imap arms)

private def inlineCallsListM (imap : List (String × Fn)) : List Expr → StateM Nat (List Expr)
  | [] => pure []
  | x :: xs => return (← inlineCallsM imap x) :: (← inlineCallsListM imap xs)

private def inlineCallsArmsM (imap : List (String × Fn)) :
    List (Pat × Expr) → StateM Nat (List (Pat × Expr))
  | [] => pure []
  | (p, b) :: rest => return (p, ← inlineCallsM imap b) :: (← inlineCallsArmsM imap rest)

end

/-! ## Step 2: Copy Propagation & Known-Constructor `matchValue` Folding -/

abbrev AliasMap := List (String × String)
abbrev CtorMap := List (String × (String × List String))

private def resolveAlias (aliases : AliasMap) (x : String) : String :=
  (aliases.lookup x).getD x

private def allVarNames : List Expr → Option (List String)
  | [] => some []
  | .var v :: rest => (allVarNames rest).map (v :: ·)
  | _ => none

private def matchCtorPats : List Pat → List String → Option AliasMap
  | [], [] => some []
  | .bind v :: ps, fv :: fvs => (matchCtorPats ps fvs).map ((v, fv) :: ·)
  | .wildcard :: ps, _ :: fvs => matchCtorPats ps fvs
  | _, _ => none

private def pickCtorArm (nm : String) (fvs : List String) :
    List (Pat × Expr) → Option (AliasMap × Expr)
  | [] => none
  | (.construct _ nm' pats, body) :: rest =>
    if nm' == nm then
      match matchCtorPats pats fvs with
      | some binds => some (binds, body)
      | none => pickCtorArm nm fvs rest
    else pickCtorArm nm fvs rest
  | (.wildcard, body) :: _ => some ([], body)
  | (.bind _, _) :: _ => none
  | _ :: rest => pickCtorArm nm fvs rest

private def shadowMaps (bs : List String) (aliases : AliasMap) (ctors : CtorMap) :
    AliasMap × CtorMap :=
  (aliases.filter fun p => !bs.contains p.1, ctors.filter fun p => !bs.contains p.1)

/-- Whether an expression is pure (has no `assertEq`, `hint`, `call`, or `store`),
so a dead `let` binding of it can be eliminated without changing semantics! -/
private def isPureCtorOrVar : Expr → Bool
  | .var _ | .literal _ => true
  | .construct _ _ _ xs => xs.all fun e => match e with | .var _ | .literal _ => true | _ => false
  | _ => false

mutual

/-- Bounded-fuel known-constructor folding + copy propagation.
Fuel decreases only when a `matchValue` unfolds an arm body (at most the number
of `matchValue` nodes in the expression), guaranteeing total termination! -/
def simpExpr (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) : Expr → Expr
  | .var x => .var (resolveAlias aliases x)
  | .literal n => .literal n
  | .global nm targs => .global nm targs
  | .control c e => .control c e
  | .tuple xs => .tuple (simpExprList fuel aliases ctors xs)
  | .array xs => .array (simpExprList fuel aliases ctors xs)
  | .construct ty targs nm xs => .construct ty targs nm (simpExprList fuel aliases ctors xs)
  | .constructAs ty targs nm xs => .constructAs ty targs nm (simpExprList fuel aliases ctors xs)
  | .record ty fs => .record ty (simpExprList fuel aliases ctors fs)
  | .update ty fs => .update ty (simpExprList fuel aliases ctors fs)
  | .builtin op xs => .builtin op (simpExprList fuel aliases ctors xs)
  | .call nm targs xs => .call nm targs (simpExprList fuel aliases ctors xs)
  | .repeat x n => .repeat (simpExpr fuel aliases ctors x) n
  | .index x i => .index (simpExpr fuel aliases ctors x) i
  | .slice x a b => .slice (simpExpr fuel aliases ctors x) a b
  | .member x f => .member (simpExpr fuel aliases ctors x) f
  | .project x i => .project (simpExpr fuel aliases ctors x) i
  | .store x => .store (simpExpr fuel aliases ctors x)
  | .load x => .load (simpExpr fuel aliases ctors x)
  | .hint ty x ch => .hint ty (simpExpr fuel aliases ctors x) ch
  | .neg x => .neg (simpExpr fuel aliases ctors x)
  | .binary op x y => .binary op (simpExpr fuel aliases ctors x) (simpExpr fuel aliases ctors y)
  | .letValue p x b =>
    let x' := simpExpr fuel aliases ctors x
    let bs := patBoundVars p
    let (aliases0, ctors0) := shadowMaps bs aliases ctors
    match p, x' with
    | .bind v, .var y =>
      -- Copy propagation: replace all free occurrences of `v` with `y` and drop the copy!
      let aliases1 := (v, y) :: aliases0
      let ctors1 := match ctors0.lookup y with
        | some info => (v, info) :: ctors0
        | none => ctors0
      simpExpr fuel aliases1 ctors1 b
    | .bind v, .construct _ _ nm args =>
      let ctors1 := match allVarNames args with
        | some fvs => (v, (nm, fvs)) :: ctors0
        | none => ctors0
      let b' := simpExpr fuel aliases0 ctors1 b
      if isPureCtorOrVar x' && !hasFreeVar v b' then b'
      else match b' with
        | .var w => if w == v then x' else .letValue p x' b'
        | _ => .letValue p x' b'
    | .bind v, _ =>
      let b' := simpExpr fuel aliases0 ctors0 b
      match b' with
      | .var w => if w == v then x' else .letValue p x' b'
      | _ =>
        if isPureCtorOrVar x' && !hasFreeVar v b' then b'
        else .letValue p x' b'
    | _, _ =>
      .letValue p x' (simpExpr fuel aliases0 ctors0 b)
  | .matchValue scrut arms =>
    let scrut' := simpExpr fuel aliases ctors scrut
    let known? : Option (String × List String) := match scrut' with
      | .var v => ctors.lookup v
      | .construct _ _ nm args => (allVarNames args).map (nm, ·)
      | _ => none
    match fuel with
    | 0 => .matchValue scrut' (simpArms 0 aliases ctors arms)
    | fuel' + 1 =>
      match known? with
      | some (nm, fvs) =>
        match pickCtorArm nm fvs arms with
        | some (binds, armBody) =>
          let (aliases0, ctors0) := shadowMaps (binds.map Prod.fst) aliases ctors
          let aliases1 := binds ++ aliases0
          let ctors1 := binds.foldl (init := ctors0) fun acc (v, fv) =>
            match ctors0.lookup fv with
            | some info => (v, info) :: acc
            | none => acc
          simpExpr fuel' aliases1 ctors1 armBody
        | none => .matchValue scrut' (simpArms (fuel' + 1) aliases ctors arms)
      | none => .matchValue scrut' (simpArms (fuel' + 1) aliases ctors arms)
termination_by e => (fuel, sizeOf e)

def simpExprList (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) : List Expr → List Expr
  | [] => []
  | x :: xs => simpExpr fuel aliases ctors x :: simpExprList fuel aliases ctors xs
termination_by xs => (fuel, sizeOf xs)

def simpArms (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) :
    List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest =>
    let (aliases0, ctors0) := shadowMaps (patBoundVars p) aliases ctors
    (p, simpExpr fuel aliases0 ctors0 b) :: simpArms fuel aliases ctors rest
termination_by arms => (fuel, sizeOf arms)

end

/-! ## Combined Program Pass: Inline Small `isInline` Functions + Fold Ctors + Peephole -/

/-- Build the table of small non-recursive `isInline = true` functions eligible for
pre-peephole inlining (excluding self-recursive functions and functions larger than
`maxInlineNodes`). -/
def buildInlineMap (fns : List Fn) (maxInlineNodes : Nat := 256) : List (String × Fn) :=
  fns.filterMap fun f =>
    -- Only inline lowered user functions (`f*`, `jp*`), never arithmetic helpers like
    -- `u32_of_field` (whose constant calls are matched directly by `Peephole.rewriteExpr`).
    if f.isInline && (f.name.startsWith "f" || f.name.startsWith "jp") &&
        !callsAny [f.name] f.body && exprNodes f.body ≤ maxInlineNodes then
      some (f.name, f)
    else none

/-- One round of inlining + known-constructor folding across `fns`. -/
def inlineAndFoldOnce (fns : List Fn) (counter : Nat) : List Fn × Nat :=
  let imap := buildInlineMap fns
  if imap.isEmpty then
    (fns.map fun f => { f with body := simpExpr 16 [] [] f.body }, counter)
  else
    let (fns', counter') := fns.foldl (init := ([], counter)) fun (acc, c) f =>
      -- Avoid mutually recursive expansion by excluding `f.name` from its own inline map.
      let imapHere := imap.filter fun p => p.1 != f.name
      let (inlined, c') := (inlineCallsM imapHere f.body).run c
      let folded := simpExpr 32 [] [] inlined
      (acc ++ [{ f with body := folded }], c')
    (fns', counter')

mutual

/-- Flatten nested `let p := (let p1 := rhs1; body1); body` into flat ANF
`let p1 := rhs1; let p := body1; body` (when `p1` is alpha-fresh wrt `body`),
exposing cross-callee ANF chains like `let x := UInt32::xor b c; let s1 := u32_shr x 12; ...`
to `Peephole.rewriteExpr`! -/
def flattenLets (fuel : Nat) : Expr → Expr
  | .letValue p (.letValue p1 rhs1 body1) body =>
    match fuel with
    | 0 => .letValue p (flattenLets 0 (.letValue p1 rhs1 body1)) (flattenLets 0 body)
    | fuel' + 1 =>
      let bs1 := patBoundVars p1
      if bs1.all fun v => !hasFreeVar v body then
        flattenLets fuel' (.letValue p1 rhs1 (.letValue p body1 body))
      else
        .letValue p (flattenLets (fuel' + 1) (.letValue p1 rhs1 body1)) (flattenLets (fuel' + 1) body)
  | .letValue p x b => .letValue p (flattenLets fuel x) (flattenLets fuel b)
  | .matchValue x arms => .matchValue (flattenLets fuel x) (flattenLetsArms fuel arms)
  | .tuple xs => .tuple (flattenLetsList fuel xs)
  | .array xs => .array (flattenLetsList fuel xs)
  | .construct ty targs nm xs => .construct ty targs nm (flattenLetsList fuel xs)
  | .constructAs ty targs nm xs => .constructAs ty targs nm (flattenLetsList fuel xs)
  | .record ty fs => .record ty (flattenLetsList fuel fs)
  | .update ty fs => .update ty (flattenLetsList fuel fs)
  | .builtin op xs => .builtin op (flattenLetsList fuel xs)
  | .call nm targs xs => .call nm targs (flattenLetsList fuel xs)
  | .repeat x n => .repeat (flattenLets fuel x) n
  | .index x i => .index (flattenLets fuel x) i
  | .slice x a b => .slice (flattenLets fuel x) a b
  | .member x f => .member (flattenLets fuel x) f
  | .project x i => .project (flattenLets fuel x) i
  | .store x => .store (flattenLets fuel x)
  | .load x => .load (flattenLets fuel x)
  | .hint ty x ch => .hint ty (flattenLets fuel x) ch
  | .neg x => .neg (flattenLets fuel x)
  | .binary op x y => .binary op (flattenLets fuel x) (flattenLets fuel y)
  | e => e
termination_by e => (fuel, sizeOf e)

def flattenLetsList (fuel : Nat) : List Expr → List Expr
  | [] => []
  | x :: xs => flattenLets fuel x :: flattenLetsList fuel xs
termination_by xs => (fuel, sizeOf xs)

def flattenLetsArms (fuel : Nat) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest => (p, flattenLets fuel b) :: flattenLetsArms fuel rest
termination_by arms => (fuel, sizeOf arms)

end

mutual

/-- Post-peephole constant folding: replaces `u32_of_field(lit n)` (`n < 2^32`) with direct
`UInt32::from_fields [n%256, (n/256)%256, (n/65536)%256, (n/16777216)%256]`, eliminating
`bytes_le` hints, top-byte assertions, and recomposition constraints on constant `UInt32`s
(e.g. BLAKE3 IV words and zero-padded block words). -/
def foldConstU32OfField : Expr → Expr
  | .call nm targs xs =>
    match nm, targs, xs with
    | "u32_of_field", some [], [.literal n] =>
      let m := n % 4294967296
      .call "UInt32::from_fields" (some [])
        [.array [.literal (m % 256), .literal ((m / 256) % 256),
                 .literal ((m / 65536) % 256), .literal ((m / 16777216) % 256)]]
    | _, _, _ => .call nm targs (foldConstU32OfFieldList xs)
  | .tuple xs => .tuple (foldConstU32OfFieldList xs)
  | .array xs => .array (foldConstU32OfFieldList xs)
  | .construct ty targs nm xs => .construct ty targs nm (foldConstU32OfFieldList xs)
  | .constructAs ty targs nm xs => .constructAs ty targs nm (foldConstU32OfFieldList xs)
  | .record ty fs => .record ty (foldConstU32OfFieldList fs)
  | .update ty fs => .update ty (foldConstU32OfFieldList fs)
  | .builtin op xs => .builtin op (foldConstU32OfFieldList xs)
  | .repeat x n => .repeat (foldConstU32OfField x) n
  | .index x i => .index (foldConstU32OfField x) i
  | .slice x a b => .slice (foldConstU32OfField x) a b
  | .member x f => .member (foldConstU32OfField x) f
  | .project x i => .project (foldConstU32OfField x) i
  | .store x => .store (foldConstU32OfField x)
  | .load x => .load (foldConstU32OfField x)
  | .hint ty x ch => .hint ty (foldConstU32OfField x) ch
  | .neg x => .neg (foldConstU32OfField x)
  | .binary op x y => .binary op (foldConstU32OfField x) (foldConstU32OfField y)
  | .letValue p x b => .letValue p (foldConstU32OfField x) (foldConstU32OfField b)
  | .matchValue x arms => .matchValue (foldConstU32OfField x) (foldConstU32OfFieldArms arms)
  | e => e

def foldConstU32OfFieldList : List Expr → List Expr
  | [] => []
  | x :: xs => foldConstU32OfField x :: foldConstU32OfFieldList xs

def foldConstU32OfFieldArms : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest => (p, foldConstU32OfField b) :: foldConstU32OfFieldArms rest

end

/-- Full pre-peephole inline + known-constructor fold + ANF let-flatten + `Peephole.rewriteExpr`
+ post-peephole constant `u32_of_field` fold pass. -/
def optimizeFns (fns : List Fn) : List Fn :=
  let (r1, c1) := inlineAndFoldOnce fns 0
  let (r2, c2) := inlineAndFoldOnce r1 c1
  let (r3, _) := inlineAndFoldOnce r2 c2
  r3.map fun f =>
    let flat := flattenLets 256 (simpExpr 32 [] [] f.body)
    { f with body := foldConstU32OfField (rewriteExpr (simpExpr 32 [] [] flat)) }

/-- Keep only functions transitively reachable from `roots` (plus `roots` themselves).
Eliminates dead inlined helpers (`f2`..`f8`, `u32_shr`, `u32_shl`, `divmod_56`, etc.)
after `InlineFuse` + `Peephole` have fused them away! -/
def pruneUnreachable (roots : List String) (fns : List Fn) : List Fn :=
  let rec go (fuel : Nat) (visited : List String) (work : List String) : List String :=
    match fuel, work with
    | 0, _ | _, [] => visited
    | fuel' + 1, nm :: rest =>
      match fns.find? (·.name == nm) with
      | none => go fuel' visited rest
      | some f =>
        let callees := fns.filterMap fun g =>
          if !visited.contains g.name && callsAny [g.name] f.body then some g.name else none
        go fuel' (visited ++ callees) (rest ++ callees)
  let reachable := go (fns.length * 2 + 4) roots roots
  fns.filter fun f => reachable.contains f.name

/-! ## Plainness Preservation Proofs (Zero `sorry`) -/

private theorem isPlainExpr_bindParams (pfx : String) (args : List (String × Expr)) (body : Expr)
    (hargs : ∀ p ∈ args, isPlainExpr p.2 = true) (hbody : isPlainExpr body = true) :
    isPlainExpr (bindParams pfx args body) = true := by
  induction args with
  | nil => exact hbody
  | cons hd tl ih =>
    simp only [bindParams, isPlainExpr, Bool.and_eq_true]
    exact ⟨hargs hd List.mem_cons_self, ih fun p hp => hargs p (List.mem_cons_of_mem _ hp)⟩

mutual

theorem isPlainExpr_prefixExpr (pfx : String) (scope : List String) :
    ∀ e, isPlainExpr (prefixExpr pfx scope e) = isPlainExpr e
  | .var x => by simp [prefixExpr]; split <;> rfl
  | .literal _ | .global _ _ | .control _ _ => rfl
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs =>
    isPlainList_prefixExprList pfx scope xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x =>
    isPlainExpr_prefixExpr pfx scope x
  | .binary _ x y => by
    simp only [prefixExpr, isPlainExpr,
      isPlainExpr_prefixExpr pfx scope x, isPlainExpr_prefixExpr pfx scope y]
  | .letValue p x b => by
    simp only [prefixExpr, isPlainExpr,
      isPlainExpr_prefixExpr pfx scope x, isPlainExpr_prefixExpr pfx (patBoundVars p ++ scope) b]
  | .matchValue x arms => by
    simp only [prefixExpr, isPlainExpr,
      isPlainExpr_prefixExpr pfx scope x, isPlainArms_prefixArms pfx scope arms]

theorem isPlainList_prefixExprList (pfx : String) (scope : List String) :
    ∀ xs, isPlainList (prefixExprList pfx scope xs) = isPlainList xs
  | [] => rfl
  | x :: xs => by
    simp only [prefixExprList, isPlainList,
      isPlainExpr_prefixExpr pfx scope x, isPlainList_prefixExprList pfx scope xs]

theorem isPlainArms_prefixArms (pfx : String) (scope : List String) :
    ∀ arms, isPlainArms (prefixArms pfx scope arms) = isPlainArms arms
  | [] => rfl
  | (p, b) :: rest => by
    simp only [prefixArms, isPlainArms,
      isPlainExpr_prefixExpr pfx (patBoundVars p ++ scope) b,
      isPlainArms_prefixArms pfx scope rest]

end

mutual

theorem isPlainExpr_foldConstU32OfField :
    ∀ e, isPlainExpr (foldConstU32OfField e) = isPlainExpr e
  | .call nm targs xs => by
    simp only [foldConstU32OfField]
    split
    · rfl
    · exact isPlainList_foldConstU32OfFieldList xs
  | .literal _ | .var _ | .global _ _ | .control _ _ => rfl
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs =>
    isPlainList_foldConstU32OfFieldList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x =>
    isPlainExpr_foldConstU32OfField x
  | .binary _ x y => by
    simp only [foldConstU32OfField, isPlainExpr,
      isPlainExpr_foldConstU32OfField x, isPlainExpr_foldConstU32OfField y]
  | .letValue p x b => by
    simp only [foldConstU32OfField, isPlainExpr,
      isPlainExpr_foldConstU32OfField x, isPlainExpr_foldConstU32OfField b]
  | .matchValue x arms => by
    simp only [foldConstU32OfField, isPlainExpr,
      isPlainExpr_foldConstU32OfField x, isPlainArms_foldConstU32OfFieldArms arms]

theorem isPlainList_foldConstU32OfFieldList :
    ∀ xs, isPlainList (foldConstU32OfFieldList xs) = isPlainList xs
  | [] => rfl
  | x :: xs => by
    simp only [foldConstU32OfFieldList, isPlainList,
      isPlainExpr_foldConstU32OfField x, isPlainList_foldConstU32OfFieldList xs]

theorem isPlainArms_foldConstU32OfFieldArms :
    ∀ arms, isPlainArms (foldConstU32OfFieldArms arms) = isPlainArms arms
  | [] => rfl
  | (_, b) :: rest => by
    simp only [foldConstU32OfFieldArms, isPlainArms,
      isPlainExpr_foldConstU32OfField b, isPlainArms_foldConstU32OfFieldArms rest]

end

end IxCC.AiurBackend.InlineFuse
