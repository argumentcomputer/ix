module

public import Ix.Tc.Ingress

/-!
Mirror: crates/compile/src/kernel_egress.rs (the kernel → Ixon half,
restricted to anon mode — Rust's `ixon_egress` is Meta-only and leans on
`Env.named`; the anon variant here works purely from kernel data).

Egress converts a loaded `KConst .anon` (or a whole Muts block) back into an
`Ixon.Constant`. It emits **share-free** expressions with fresh first-use
`refs`/`univs` tables; sibling references that hit the block `mutCtx` become
`Expr.recur`, everything else becomes `Expr.ref` (inverse of
`ingressExpr`'s resolution). Literals re-derive their blob addresses from the
kernel-held values (`natBlob`/`strBlob`) and fail loudly on mismatch, closing
the decode/encode loop on blob fidelity.

The roundtrip comparison is **structural, not byte-exact** (matching the Rust
`kernel-ixon-roundtrip`, which compares post-decompile content hashes and is
insensitive to sharing choices and table order): both the original constant
and the egressed one are passed through `canonConstant`, which

- expands `share` nodes transparently (the kernel provably never sees them),
- renumbers `refs`/`univs` by first use in a fixed per-kind expression order
  (typ, value | typ, rules | typ, ctors | member order for Muts), and
- reduces universe trees through the kernel's simplifying `mkMax`/`mkIMax`
  constructors (ingress stores *reduced* levels; the reduction rules are
  independently certified by the P1 level-algebra tests and the bit-exact
  `tc-node-addr` harness, so sharing this one step with ingress does not
  let an ingress bug mask itself structurally).

Equality of canonical forms then means: everything the serialized constant
encoded — modulo sharing layout, table numbering, and universe reduction —
survived the trip into the kernel and back.

Projection constants (`IPrj`/`CPrj`/`RPrj`/`DPrj`) carry no expressions and
empty tables, so they are regenerated from kernel data (`block`,
`memberIdx`, `cidx`) and compared **byte-exact** against the stored bytes.

Scope note: the v1 kernel is anon-only, so metadata (names, binder info,
mdata) never enters it and there is nothing metadata-shaped to lose or
roundtrip — the comparison covers exactly the kernel-held, hash-relevant
structure. A meta-mode egress (mirroring Rust's `ixon_egress` + `decompile`
leg) becomes possible once meta-mode ingress lands.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-! ### Universe conversion and reduction -/

/-- Ixon universe → kernel universe via the *simplifying* smart constructors
    (the same reduction ingress applies). Pure: no interning. -/
def ixonUnivToK : Ixon.Univ → KUniv .anon
  | .zero => .mkZero
  | .succ u => .mkSucc (ixonUnivToK u)
  | .max a b => .mkMax (ixonUnivToK a) (ixonUnivToK b)
  | .imax a b => .mkIMax (ixonUnivToK a) (ixonUnivToK b)
  | .var idx => .mkParam idx ()

/-- Kernel universe → Ixon universe, structural (kernel levels are already
    reduced by construction). -/
def kUnivToIxon : KUniv .anon → Ixon.Univ
  | .zero _ => .zero
  | .succ u _ => .succ (kUnivToIxon u)
  | .max a b _ => .max (kUnivToIxon a) (kUnivToIxon b)
  | .imax a b _ => .imax (kUnivToIxon a) (kUnivToIxon b)
  | .param idx _ _ => .var idx

/-- Reduce an Ixon universe tree exactly the way ingress does (round through
    the kernel's simplifying constructors). Used by `canonConstant` so the
    original constant's raw levels compare against the kernel's reduced ones. -/
def reduceIxonUniv (u : Ixon.Univ) : Ixon.Univ :=
  kUnivToIxon (ixonUnivToK u)

/-! ### Expression egress -/

/-- Egress state: first-use `refs`/`univs` tables, the block `mutCtx`
    (projection address → member index) for `recur` discrimination, and a
    conversion memo keyed by kernel content hash (DAG-shared subtrees convert
    once; assignments only grow, so memoized results stay valid). -/
structure EgressSt where
  refs : Array Address := #[]
  refIdx : HashMap Address UInt64 := {}
  univs : Array Ixon.Univ := #[]
  univIdx : HashMap Ixon.Univ UInt64 := {}
  mutCtx : HashMap Address UInt64 := {}
  exprMemo : HashMap Address Ixon.Expr := {}

/-- Egress monad: diagnostics as strings, mirroring ingress. -/
abbrev EgressM := EStateM IngressErr EgressSt

namespace EgressM

@[inline] def internRef (addr : Address) : EgressM UInt64 :=
  modifyGet fun st =>
    match st.refIdx[addr]? with
    | some i => (i, st)
    | none =>
      let i := st.refs.size.toUInt64
      (i, { st with refs := st.refs.push addr
                    refIdx := st.refIdx.insert addr i })

@[inline] def internUniv (u : Ixon.Univ) : EgressM UInt64 :=
  modifyGet fun st =>
    match st.univIdx[u]? with
    | some i => (i, st)
    | none =>
      let i := st.univs.size.toUInt64
      (i, { st with univs := st.univs.push u
                    univIdx := st.univIdx.insert u i })

/-- Intern the (already reduced) kernel universes of a `const` node. -/
def internUnivArgs (us : Array (KUniv .anon)) : EgressM (Array UInt64) := do
  let mut out : Array UInt64 := Array.mkEmpty us.size
  for u in us do
    out := out.push (← internUniv (kUnivToIxon u))
  return out

end EgressM

inductive XFrame where
  | process (e : KExpr .anon)
  | appDone
  | lamDone
  | allDone
  | letDone (nd : Bool)
  | prjDone (refIdx field : UInt64)
  | memoAt (addr : Address)
  deriving Inhabited

/-- Convert one kernel expression to a share-free Ixon expression (explicit
    stack machine — Mathlib-deep terms overflow default stacks under
    structural recursion, same rationale as `ingressExpr`).

    Inverse of `ingressExpr`'s resolution: a `const` whose id is in the
    `mutCtx` becomes `recur idx`, otherwise `ref` on the interned address;
    `nat`/`str` re-derive and verify the blob address from the value. A live
    `fvar` is an error — stored constants are closed. -/
def kexprToIxon (root : KExpr .anon) : EgressM Ixon.Expr := do
  let mut stack : Array XFrame := #[.process root]
  let mut values : Array Ixon.Expr := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process e =>
      if let some cached := (← get).exprMemo[e.addr]? then
        values := values.push cached
        continue
      match e with
      | .var idx _ _ =>
        values := values.push (.var idx)
      | .fvar id _ _ =>
        throw s!"kexprToIxon: unexpected FVar({id}) — stored constants must be closed"
      | .sort u _ =>
        values := values.push (.sort (← EgressM.internUniv (kUnivToIxon u)))
      | .const id us _ =>
        let uidxs ← EgressM.internUnivArgs us
        let node ← match (← get).mutCtx[id.addr]? with
          | some memberIdx => pure (Ixon.Expr.recur memberIdx uidxs)
          | none => pure (Ixon.Expr.ref (← EgressM.internRef id.addr) uidxs)
        modify fun st => { st with exprMemo := st.exprMemo.insert e.addr node }
        values := values.push node
      | .app f a _ =>
        stack := stack.push (.memoAt e.addr) |>.push .appDone
          |>.push (.process a) |>.push (.process f)
      | .lam _ _ ty body _ =>
        stack := stack.push (.memoAt e.addr) |>.push .lamDone
          |>.push (.process body) |>.push (.process ty)
      | .all _ _ ty body _ =>
        stack := stack.push (.memoAt e.addr) |>.push .allDone
          |>.push (.process body) |>.push (.process ty)
      | .letE _ ty val body nd _ =>
        stack := stack.push (.memoAt e.addr) |>.push (.letDone nd)
          |>.push (.process body) |>.push (.process val)
          |>.push (.process ty)
      | .prj id field val _ =>
        let refIdx ← EgressM.internRef id.addr
        stack := stack.push (.memoAt e.addr) |>.push (.prjDone refIdx field)
          |>.push (.process val)
      | .nat val blob _ =>
        if KExpr.natBlob val != blob then
          throw s!"kexprToIxon: Nat literal {val} re-encodes to {KExpr.natBlob val} but kernel holds blob {blob}"
        values := values.push (.nat (← EgressM.internRef blob))
      | .str val blob _ =>
        if KExpr.strBlob val != blob then
          throw s!"kexprToIxon: Str literal re-encodes to {KExpr.strBlob val} but kernel holds blob {blob}"
        values := values.push (.str (← EgressM.internRef blob))
    | .appDone =>
      let a := values.back!; values := values.pop
      let f := values.back!; values := values.pop
      values := values.push (.app f a)
    | .lamDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.lam ty body)
    | .allDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.all ty body)
    | .letDone nd =>
      let body := values.back!; values := values.pop
      let val := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.letE nd ty val body)
    | .prjDone refIdx field =>
      let val := values.back!; values := values.pop
      values := values.push (.prj refIdx field val)
    | .memoAt addr =>
      let v := values.back!
      modify fun st => { st with exprMemo := st.exprMemo.insert addr v }
  match values.back? with
  | some v =>
    if values.size != 1 then
      throw s!"kexprToIxon: unbalanced value stack ({values.size} values)"
    return v
  | none => throw "kexprToIxon: empty result stack"

/-! ### Per-kind payload builders -/

def egressDefn : KConst .anon → EgressM Ixon.Definition
  | .defn (kind := kind) (safety := safety) (lvls := lvls) (ty := ty)
      (val := val) .. => do
    let typ ← kexprToIxon ty
    let value ← kexprToIxon val
    return { kind, safety, lvls, typ, value }
  | kc => throw s!"egressDefn: expected definition, got {kc.kindName}"

def egressRecr : KConst .anon → EgressM Ixon.Recursor
  | .recr (k := k) (isUnsafe := isUnsafe) (lvls := lvls) (params := params)
      (indices := indices) (motives := motives) (minors := minors)
      (ty := ty) (rules := rules) .. => do
    let typ ← kexprToIxon ty
    let mut outRules : Array Ixon.RecursorRule := Array.mkEmpty rules.size
    for rule in rules do
      outRules := outRules.push { fields := rule.fields, rhs := ← kexprToIxon rule.rhs }
    return { k, isUnsafe, lvls, params, indices, motives, minors, typ,
             rules := outRules }
  | kc => throw s!"egressRecr: expected recursor, got {kc.kindName}"

def egressAxio : KConst .anon → EgressM Ixon.Axiom
  | .axio (isUnsafe := isUnsafe) (lvls := lvls) (ty := ty) .. => do
    return { isUnsafe, lvls, typ := ← kexprToIxon ty }
  | kc => throw s!"egressAxio: expected axiom, got {kc.kindName}"

def egressQuot : KConst .anon → EgressM Ixon.Quotient
  | .quot (kind := kind) (lvls := lvls) (ty := ty) .. => do
    return { kind, lvls, typ := ← kexprToIxon ty }
  | kc => throw s!"egressQuot: expected quotient, got {kc.kindName}"

def egressCtorPayload : KConst .anon → EgressM Ixon.Constructor
  | .ctor (isUnsafe := isUnsafe) (lvls := lvls) (cidx := cidx)
      (params := params) (fields := fields) (ty := ty) .. => do
    return { isUnsafe, lvls, cidx, params, fields, typ := ← kexprToIxon ty }
  | kc => throw s!"egressCtorPayload: expected constructor, got {kc.kindName}"

/-- Inductive payload: the member's own type plus every constructor payload
    in cidx order (`ctorKcs` pre-sorted by the caller). -/
def egressIndc (kc : KConst .anon) (ctorKcs : Array (KConst .anon)) :
    EgressM Ixon.Inductive := do
  match kc with
  | .indc (lvls := lvls) (params := params) (indices := indices)
      (isUnsafe := isUnsafe) (ty := ty) .. =>
    let typ ← kexprToIxon ty
    let mut ctors : Array Ixon.Constructor := Array.mkEmpty ctorKcs.size
    for c in ctorKcs do
      ctors := ctors.push (← egressCtorPayload c)
    return { isUnsafe, lvls, params, indices, typ, ctors }
  | _ => throw s!"egressIndc: expected inductive, got {kc.kindName}"

/-! ### Standalone / block egress -/

/-- Egress a standalone (non-mutual) constant back to an `Ixon.Constant`.
    `Defn`/`Recr` get `mutCtx = {selfAddr ↦ 0}` so kernel self-references
    (ingressed from `recur 0`) map back to `recur 0`. -/
def egressStandalone (kc : KConst .anon) (selfAddr : Address) :
    Except IngressErr Ixon.Constant :=
  let run (withSelf : Bool) (m : EgressM Ixon.ConstantInfo) :
      Except IngressErr Ixon.Constant :=
    let st0 : EgressSt :=
      { mutCtx := if withSelf
          then ({} : HashMap Address UInt64).insert selfAddr 0 else {} }
    match m.run st0 with
    | .ok info st => .ok ⟨info, #[], st.refs, st.univs⟩
    | .error e _ => .error e
  match kc with
  | .defn .. => run true (Ixon.ConstantInfo.defn <$> egressDefn kc)
  | .recr .. => run true (Ixon.ConstantInfo.recr <$> egressRecr kc)
  | .axio .. => run false (Ixon.ConstantInfo.axio <$> egressAxio kc)
  | .quot .. => run false (Ixon.ConstantInfo.quot <$> egressQuot kc)
  | _ => throw s!"egressStandalone: {kc.kindName} is not a standalone kind"

/-- Egress an entire Muts block from its flat kernel member list
    (`[m0, m0.ctors…, m1, …]` — exactly what `KEnv.blocks` records) back to
    the Muts `Ixon.Constant`, plus the regenerated projection constant for
    every member and constructor (`(projection address, constant)` rows, in
    flat-list order). The `mutCtx` is the member (non-ctor) sublist, matching
    `ingressAnonBlock`. -/
def egressBlock (flat : Array (KId .anon × KConst .anon)) :
    Except IngressErr (Ixon.Constant × Array (Address × Ixon.Constant)) := do
  if flat.isEmpty then
    throw "egressBlock: empty member list"
  -- Partition: members in order; ctors grouped under their inductive.
  let mut memberIds : Array (KId .anon) := #[]
  let mut memberKcs : Array (KConst .anon) := #[]
  let mut ctorsByInduct : HashMap Address (Array (KId .anon × KConst .anon)) := {}
  for (kid, kc) in flat do
    match kc with
    | .ctor (induct := induct) .. =>
      let cur := ctorsByInduct.getD induct.addr #[]
      ctorsByInduct := ctorsByInduct.insert induct.addr (cur.push (kid, kc))
    | _ =>
      memberIds := memberIds.push kid
      memberKcs := memberKcs.push kc
  -- The block address every member must agree on.
  let some blockAddr := memberKcs[0]?.bind fun kc => match kc with
      | .defn (block := b) .. => some b.addr
      | .recr (block := b) .. => some b.addr
      | .indc (block := b) .. => some b.addr
      | _ => none
    | throw "egressBlock: first member carries no block id"
  let mut st : EgressSt := { mutCtx := Id.run do
    let mut m : HashMap Address UInt64 := {}
    for h : i in [0:memberIds.size] do
      m := m.insert memberIds[i].addr i.toUInt64
    return m }
  let mut members : Array Ixon.MutConst := Array.mkEmpty memberKcs.size
  let mut projs : Array (Address × Ixon.Constant) := #[]
  for h : i in [0:memberKcs.size] do
    let idx := i.toUInt64
    let kid := memberIds[i]!
    let kc := memberKcs[i]
    match kc with
    | .defn (block := b) .. =>
      if b.addr != blockAddr then
        throw s!"egressBlock: member {i} block {b.addr} disagrees with {blockAddr}"
      match (egressDefn kc).run st with
      | .ok d st' => st := st'; members := members.push (.defn d)
      | .error e _ => throw e
      projs := projs.push (kid.addr, ⟨.dPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩)
    | .recr (block := b) .. =>
      if b.addr != blockAddr then
        throw s!"egressBlock: member {i} block {b.addr} disagrees with {blockAddr}"
      -- Anon ingress leaves recursor memberIdx at 0 (Rust parity); the flat
      -- position is authoritative here.
      match (egressRecr kc).run st with
      | .ok r st' => st := st'; members := members.push (.recr r)
      | .error e _ => throw e
      projs := projs.push (kid.addr, ⟨.rPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩)
    | .indc (block := b) (memberIdx := mi) (ctors := ctorIds) .. =>
      if b.addr != blockAddr then
        throw s!"egressBlock: member {i} block {b.addr} disagrees with {blockAddr}"
      if mi != idx then
        throw s!"egressBlock: inductive member {i} records memberIdx {mi}"
      -- Constructor KConsts in cidx order (flat order already is, but sort
      -- defensively like Rust's egress_muts_block).
      let mut ctorKcs : Array (UInt64 × KId .anon × KConst .anon) := #[]
      for (ckid, ckc) in ctorsByInduct.getD kid.addr #[] do
        match ckc with
        | .ctor (cidx := cidx) .. => ctorKcs := ctorKcs.push (cidx, ckid, ckc)
        | _ => throw "egressBlock: non-ctor grouped under inductive"
      let sortedCtors := ctorKcs.qsort fun a b => a.1 < b.1
      if sortedCtors.size != ctorIds.size then
        throw s!"egressBlock: inductive member {i} lists {ctorIds.size} ctors but {sortedCtors.size} present in block"
      match (egressIndc kc (sortedCtors.map (·.2.2))).run st with
      | .ok ind st' => st := st'; members := members.push (.indc ind)
      | .error e _ => throw e
      projs := projs.push (kid.addr, ⟨.iPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩)
      for (cidx, ckid, _) in sortedCtors do
        projs := projs.push (ckid.addr, ⟨.cPrj ⟨idx, cidx, blockAddr⟩, #[], #[], #[]⟩)
    | _ => throw s!"egressBlock: invalid member kind {kc.kindName} in block"
  return (⟨.muts members, #[], st.refs, st.univs⟩, projs)

/-! ### Canonicalization -/

/-- Canonicalizer state: fresh first-use tables plus the memo of rewritten
    `share` expansions (safe to reuse: index assignments only grow, and a
    subtree's rewrite is invariant once its first occurrence assigned them). -/
structure CanonSt where
  refs : Array Address := #[]
  refIdx : HashMap Address UInt64 := {}
  univs : Array Ixon.Univ := #[]
  univIdx : HashMap Ixon.Univ UInt64 := {}
  shareMemo : HashMap UInt64 Ixon.Expr := {}

abbrev CanonM := EStateM IngressErr CanonSt

namespace CanonM

@[inline] def internRef (addr : Address) : CanonM UInt64 :=
  modifyGet fun st =>
    match st.refIdx[addr]? with
    | some i => (i, st)
    | none =>
      let i := st.refs.size.toUInt64
      (i, { st with refs := st.refs.push addr
                    refIdx := st.refIdx.insert addr i })

@[inline] def internUniv (u : Ixon.Univ) : CanonM UInt64 :=
  modifyGet fun st =>
    match st.univIdx[u]? with
    | some i => (i, st)
    | none =>
      let i := st.univs.size.toUInt64
      (i, { st with univs := st.univs.push u
                    univIdx := st.univIdx.insert u i })

end CanonM

inductive CFrame where
  | process (e : Ixon.Expr)
  | appDone
  | lamDone
  | allDone
  | letDone (nd : Bool)
  | prjDone (refIdx field : UInt64)
  | memoShare (idx : UInt64)
  deriving Inhabited

/-- Rewrite one expression of a constant into canonical form: `share`
    expanded against `sharing`, `ref`/`prj`/`nat`/`str` addresses re-interned
    first-use, universe indices resolved through `univs`, reduced, and
    re-interned. `recur` member indices are structural and kept as-is. -/
def canonExpr (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (root : Ixon.Expr) : CanonM Ixon.Expr := do
  let resolveRef (i : UInt64) : CanonM UInt64 := do
    let some addr := refs[i.toNat]?
      | throw s!"canonExpr: ref index {i} out of range (len {refs.size})"
    CanonM.internRef addr
  let resolveUniv (i : UInt64) : CanonM UInt64 := do
    let some u := univs[i.toNat]?
      | throw s!"canonExpr: universe index {i} out of range (len {univs.size})"
    CanonM.internUniv (reduceIxonUniv u)
  let resolveUnivs (idxs : Array UInt64) : CanonM (Array UInt64) := do
    let mut out : Array UInt64 := Array.mkEmpty idxs.size
    for i in idxs do
      out := out.push (← resolveUniv i)
    return out
  let mut stack : Array CFrame := #[.process root]
  let mut values : Array Ixon.Expr := #[]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .process e =>
      match e with
      | .share idx =>
        if let some cached := (← get).shareMemo[idx]? then
          values := values.push cached
        else
          let some expansion := sharing[idx.toNat]?
            | throw s!"canonExpr: share index {idx} out of range (len {sharing.size})"
          stack := stack.push (.memoShare idx) |>.push (.process expansion)
      | .var idx =>
        values := values.push (.var idx)
      | .sort uidx =>
        values := values.push (.sort (← resolveUniv uidx))
      | .ref refIdx uidxs =>
        let r ← resolveRef refIdx
        values := values.push (.ref r (← resolveUnivs uidxs))
      | .recur recIdx uidxs =>
        values := values.push (.recur recIdx (← resolveUnivs uidxs))
      | .nat refIdx =>
        values := values.push (.nat (← resolveRef refIdx))
      | .str refIdx =>
        values := values.push (.str (← resolveRef refIdx))
      | .app f a =>
        stack := stack.push .appDone |>.push (.process a) |>.push (.process f)
      | .lam ty body =>
        stack := stack.push .lamDone |>.push (.process body)
          |>.push (.process ty)
      | .all ty body =>
        stack := stack.push .allDone |>.push (.process body)
          |>.push (.process ty)
      | .letE nd ty val body =>
        stack := stack.push (.letDone nd) |>.push (.process body)
          |>.push (.process val) |>.push (.process ty)
      | .prj typeRefIdx field val =>
        let r ← resolveRef typeRefIdx
        stack := stack.push (.prjDone r field) |>.push (.process val)
    | .appDone =>
      let a := values.back!; values := values.pop
      let f := values.back!; values := values.pop
      values := values.push (.app f a)
    | .lamDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.lam ty body)
    | .allDone =>
      let body := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.all ty body)
    | .letDone nd =>
      let body := values.back!; values := values.pop
      let val := values.back!; values := values.pop
      let ty := values.back!; values := values.pop
      values := values.push (.letE nd ty val body)
    | .prjDone refIdx field =>
      let val := values.back!; values := values.pop
      values := values.push (.prj refIdx field val)
    | .memoShare idx =>
      let v := values.back!
      modify fun st => { st with shareMemo := st.shareMemo.insert idx v }
  match values.back? with
  | some v =>
    if values.size != 1 then
      throw s!"canonExpr: unbalanced value stack ({values.size} values)"
    return v
  | none => throw "canonExpr: empty result stack"

/-- Canonical form of a constant (see module doc). Projections are already
    canonical (no expressions, empty tables) and pass through unchanged. -/
def canonConstant (c : Ixon.Constant) : Except IngressErr Ixon.Constant := do
  let go : CanonM Ixon.ConstantInfo := do
    let ce := canonExpr c.sharing c.refs c.univs
    match c.info with
    | .defn d => do
      let typ ← ce d.typ
      let value ← ce d.value
      return .defn { d with typ, value }
    | .recr r => do
      let typ ← ce r.typ
      let mut rules : Array Ixon.RecursorRule := Array.mkEmpty r.rules.size
      for rule in r.rules do
        rules := rules.push { rule with rhs := ← ce rule.rhs }
      return .recr { r with typ, rules }
    | .axio a => do
      return .axio { a with typ := ← ce a.typ }
    | .quot q => do
      return .quot { q with typ := ← ce q.typ }
    | .muts members => do
      let mut out : Array Ixon.MutConst := Array.mkEmpty members.size
      for member in members do
        match member with
        | .defn d =>
          let typ ← ce d.typ
          let value ← ce d.value
          out := out.push (.defn { d with typ, value })
        | .recr r =>
          let typ ← ce r.typ
          let mut rules : Array Ixon.RecursorRule := Array.mkEmpty r.rules.size
          for rule in r.rules do
            rules := rules.push { rule with rhs := ← ce rule.rhs }
          out := out.push (.recr { r with typ, rules })
        | .indc ind =>
          let typ ← ce ind.typ
          let mut ctors : Array Ixon.Constructor := Array.mkEmpty ind.ctors.size
          for ctor in ind.ctors do
            ctors := ctors.push { ctor with typ := ← ce ctor.typ }
          out := out.push (.indc { ind with typ, ctors })
      return .muts out
    | info@(.iPrj _) | info@(.cPrj _) | info@(.rPrj _) | info@(.dPrj _) =>
      return info
  match go {} with
  | .ok info st => return ⟨info, #[], st.refs, st.univs⟩
  | .error e _ => throw e

/-! ### Structural diff description (diagnostics) -/

def truncRepr [Repr α] (x : α) (n : Nat := 160) : String :=
  let s := reprStr x
  if s.length ≤ n then s else (s.take n).toString ++ "…"

def diffExpr (label : String) (a b : Ixon.Expr) : Option String :=
  if a == b then none
  else some s!"{label}: {truncRepr a} ≠ {truncRepr b}"

def diffMutConst (label : String) : Ixon.MutConst → Ixon.MutConst →
    Option String
  | .defn a, .defn b =>
    if a.kind != b.kind || a.safety != b.safety || a.lvls != b.lvls then
      some s!"{label}: defn header ({repr a.kind}/{repr a.safety}/{a.lvls}) ≠ ({repr b.kind}/{repr b.safety}/{b.lvls})"
    else (diffExpr s!"{label}.typ" a.typ b.typ).orElse fun _ =>
      diffExpr s!"{label}.value" a.value b.value
  | .recr a, .recr b =>
    if a.k != b.k || a.isUnsafe != b.isUnsafe || a.lvls != b.lvls
        || a.params != b.params || a.indices != b.indices
        || a.motives != b.motives || a.minors != b.minors then
      some s!"{label}: recursor header differs"
    else if a.rules.size != b.rules.size then
      some s!"{label}: rule count {a.rules.size} ≠ {b.rules.size}"
    else Id.run do
      for h : i in [0:a.rules.size] do
        let ra := a.rules[i]
        let rb := b.rules[i]!
        if ra.fields != rb.fields then
          return some s!"{label}.rule[{i}].fields {ra.fields} ≠ {rb.fields}"
        if let some d := diffExpr s!"{label}.rule[{i}].rhs" ra.rhs rb.rhs then
          return some d
      (diffExpr s!"{label}.typ" a.typ b.typ)
  | .indc a, .indc b =>
    if a.isUnsafe != b.isUnsafe || a.lvls != b.lvls || a.params != b.params
        || a.indices != b.indices then
      some s!"{label}: inductive header differs"
    else if a.ctors.size != b.ctors.size then
      some s!"{label}: ctor count {a.ctors.size} ≠ {b.ctors.size}"
    else Id.run do
      if let some d := diffExpr s!"{label}.typ" a.typ b.typ then
        return some d
      for h : i in [0:a.ctors.size] do
        let ca := a.ctors[i]
        let cb := b.ctors[i]!
        if ca.isUnsafe != cb.isUnsafe || ca.lvls != cb.lvls
            || ca.cidx != cb.cidx || ca.params != cb.params
            || ca.fields != cb.fields then
          return some s!"{label}.ctor[{i}]: header differs"
        if let some d := diffExpr s!"{label}.ctor[{i}].typ" ca.typ cb.typ then
          return some d
      return none
  | a, b => some s!"{label}: member kind {truncRepr a 40} ≠ {truncRepr b 40}"

/-- First structural difference between two canonical constants (for failure
    messages; `none` when equal). Compare canonical forms only — raw
    constants legitimately differ in sharing/table layout. -/
def describeDiff (a b : Ixon.Constant) : Option String := Id.run do
  if a == b then
    return none
  if a.refs != b.refs then
    let firstDiff : String := Id.run do
      for i in [0:min a.refs.size b.refs.size] do
        if a.refs[i]! != b.refs[i]! then
          return s!"[{i}] {a.refs[i]!} ≠ {b.refs[i]!}"
      return "in length"
    return some s!"refs tables differ: {a.refs.size} vs {b.refs.size} entries; first mismatch {firstDiff}"
  if a.univs != b.univs then
    return some s!"univs tables differ ({a.univs.size} vs {b.univs.size} entries)"
  match a.info, b.info with
  | .defn da, .defn db => return diffMutConst "defn" (.defn da) (.defn db)
  | .recr ra, .recr rb => return diffMutConst "recr" (.recr ra) (.recr rb)
  | .axio aa, .axio ab =>
    if aa.isUnsafe != ab.isUnsafe || aa.lvls != ab.lvls then
      return some "axio header differs"
    return diffExpr "axio.typ" aa.typ ab.typ
  | .quot qa, .quot qb =>
    if qa.kind != qb.kind || qa.lvls != qb.lvls then
      return some "quot header differs"
    return diffExpr "quot.typ" qa.typ qb.typ
  | .muts ma, .muts mb =>
    if ma.size != mb.size then
      return some s!"muts member count {ma.size} ≠ {mb.size}"
    for h : i in [0:ma.size] do
      if let some d := diffMutConst s!"muts[{i}]" ma[i] mb[i]! then
        return some d
    return some "muts: BEq disagrees but no member diff found"
  | ia, ib =>
    return some s!"constant kind differs: {truncRepr ia 60} ≠ {truncRepr ib 60}"

/-- Structural roundtrip comparison: canonicalize both sides and compare.
    `none` = roundtrip preserved structure. -/
def roundtripCompare (original egressed : Ixon.Constant) :
    Except IngressErr (Option String) := do
  let ca ← canonConstant original
  let cb ← canonConstant egressed
  if ca == cb then
    return none
  return some ((describeDiff ca cb).getD "canonical forms differ (no diff located)")

end Ix.Tc

end
end
