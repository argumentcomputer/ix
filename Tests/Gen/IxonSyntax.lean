/-
  SlimCheck generators for the Ixon text-format surface AST.

  Mirror of the Rust quickcheck generators
  (`crates/ixon/src/syntax/props.rs`): the same pools, the same
  validity invariants (nonempty spines, name-or-hash references,
  leading `Str` name components, `partial` only on `def`, `cidx` iff
  `cprj`, mutual members restricted), and the same shrinking shapes
  (subterms + minimal `Prop` replacements; element dropping at the
  decl/file level).

  `Repr` for `Term`/`File` goes through the canonical printer, so
  shrunk counterexamples display as actual `.ixon` text.
-/
module

public import LSpec
public import Tests.Gen.Basic
public import Ix.IxonSyntax

public section

open LSpec SlimCheck Gen Ixon.Syntax

namespace Tests.Gen.IxonSyntax

/-- Counterexamples display as syntax, not structure dumps. -/
instance : Repr Term := ⟨fun t _ => printTerm t⟩

instance : Repr File := ⟨fun f _ => printFile f⟩

/-! ## Generators -/

/-- Component pool: bare identifiers, unicode, primes/`!?`, reserved
    words and digit-strings (which must print `«…»`-escaped), and a
    spaced string (ditto). Identical to the Rust `STR_POOL`. -/
def strPool : Array String :=
  #["x", "y", "foo", "bar'", "h!?", "α", "ℕ", "add_comm", "Nat",
    "Except", "def", "weird name", "123", "max"]

def genStrComponent : Gen NameComponent :=
  .str <$> elements strPool

def genComponent : Gen NameComponent :=
  frequency [
    (1, .num <$> choose Nat 0 999),
    (4, genStrComponent)
  ]

def genSName : Gen SName := do
  let n ← choose Nat 0 2
  let mut parts := #[← genStrComponent]
  for _ in [0:n] do
    parts := parts.push (← genComponent)
  return { parts }

def hexChars : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c',
    'd', 'e', 'f']

def genHex (len : Nat) : Gen String := do
  let mut s := ""
  for _ in [0:len] do
    s := s.push (← elements hexChars)
  return s

def genHash : Gen HashRef := do
  return { hex := ← genHex (4 + (← choose Nat 0 11)) }

/-- Universe variables: `Str` only; includes `"max"` (must print
    escaped in universe positions). -/
def genUvar : Gen NameComponent :=
  .str <$> elements #["u", "v", "w", "max", "weird name"]

def genUniv : Nat → Gen UnivExpr
  | 0 =>
    frequency [
      (1, (.nat · {}) <$> choose Nat 0 3),
      (1, (.var · {}) <$> genUvar)
    ]
  | d + 1 =>
    frequency [
      (1, (.nat · {}) <$> choose Nat 0 3),
      (1, (.var · {}) <$> genUvar),
      (1, do return .add (← genUniv d) (1 + (← choose Nat 0 2)) {}),
      (1, do return .max (← genUniv d) (← genUniv d) {}),
      (1, do return .imax (← genUniv d) (← genUniv d) {})
    ]

def genCref : Gen ConstRef := do
  let name ← frequency [(3, some <$> genSName), (1, pure none)]
  let hash ←
    if name.isNone then some <$> genHash
    else frequency [(1, some <$> genHash), (3, pure none)]
  let levels ← frequency [
    (1, do
      let n ← choose Nat 1 2
      let mut ls := #[]
      for _ in [0:n] do
        ls := ls.push (← genUniv 1)
      pure (some ls)),
    (3, pure none)
  ]
  return { name, hash, levels }

def genBinderName : Gen BinderName :=
  frequency [
    (1, pure (.anon {})),
    (5, (.ident · {}) <$> genStrComponent)
  ]

def genSort : Gen SortKind :=
  frequency [
    (1, pure .prop),
    (1, pure (.type none)),
    (1, .type <$> some <$> genUniv 1),
    (1, .sort <$> genUniv 1)
  ]

/-- Interesting string-literal contents (escape coverage) plus the
    pool. -/
def genLitString : Gen String :=
  frequency [
    (3, elements #["", "hi", "line\nbreak", "q\"uote", "tab\there\\"]),
    (1, do
      let n ← choose Nat 0 12
      let mut s := ""
      for _ in [0:n] do
        let c ← frequency [
          (3, elements #['"', '\\', '\n', '\t', 'a', ' ', '«', '»', '¤']),
          (2, Char.ofNat <$> choose Nat 0x20 0x7e),
          (1, Char.ofNat <$> choose Nat 0xa0 0x2fff)
        ]
        s := s.push c
      pure s)
  ]

mutual

partial def genBinder (depth : Nat) : Gen BinderGroup := do
  let info ← elements #[Lean.BinderInfo.default, .implicit,
    .strictImplicit, .instImplicit]
  let names ←
    if info == Lean.BinderInfo.instImplicit && (← choose Nat 0 1) == 0 then
      pure #[]
    else do
      let n ← choose Nat 1 2
      let mut ns := #[]
      for _ in [0:n] do
        ns := ns.push (← genBinderName)
      pure ns
  return .mk info names (← genTerm depth) {}

partial def genTerm (depth : Nat) : Gen Term := do
  if depth == 0 then
    frequency [
      (1, (.natLit · {}) <$> choose Nat 0 1000000),
      (1, (.strLit · {}) <$> genLitString),
      (1, (.sort · {}) <$> genSort),
      (3, .ref <$> genCref)
    ]
  else
    let d := depth - 1
    frequency [
      (1, (.sort · {}) <$> genSort),
      (2, do
        let n ← choose Nat 1 3
        let mut args := #[]
        for _ in [0:n] do
          args := args.push (← genTerm d)
        return .app (← genTerm d) args {}),
      (2, do
        let n ← choose Nat 1 2
        let mut bs := #[]
        for _ in [0:n] do
          bs := bs.push (← genBinder d)
        return .lam bs (← genTerm d) {}),
      (1, do
        let n ← choose Nat 1 2
        let mut bs := #[]
        for _ in [0:n] do
          bs := bs.push (← genBinder d)
        return .pi bs (← genTerm d) {}),
      (1, do return .arrow (← genTerm d) (← genTerm d) {}),
      (1, do
        return .letE ((← choose Nat 0 1) == 0) (← genBinderName)
          (← genTerm d) (← genTerm d) (← genTerm d) {}),
      (1, do return .proj (← genCref) (← choose Nat 0 7) (← genTerm d) {}),
      (1, .ref <$> genCref)
    ]

end

def genUParams : Gen (Array UParam) := do
  let n ← choose Nat 0 2
  let mut out := #[]
  for _ in [0:n] do
    out := out.push { name := ← genUvar }
  return out

def genName? : Gen (Option SName) :=
  frequency [(3, some <$> genSName), (1, pure none)]

/-- The parser rejects `partial` on non-`def` and unsafe+partial. -/
def genModifiers (kw : DefKw) : Gen Modifiers := do
  match ← choose Nat 0 3 with
  | 0 => return { isUnsafe := true }
  | 1 => if kw == .defn then return { isPartial := true } else return {}
  | _ => return {}

def genDefDecl (depth : Nat) : Gen DefDecl := do
  let kw ← elements #[DefKw.defn, .thm, .opaq]
  return { kw, mods := ← genModifiers kw, name := ← genName?
           uparams := ← genUParams, ty := ← genTerm depth
           value := ← genTerm depth }

def genIndDecl (depth : Nat) : Gen IndDecl := do
  let nCtors ← choose Nat 0 2
  let mut ctors := #[]
  for _ in [0:nCtors] do
    ctors := ctors.push
      { name := ← genName?, params := ← choose Nat 0 3
        fields := ← choose Nat 0 3, ty := ← genTerm depth }
  return { isUnsafe := (← choose Nat 0 1) == 0, name := ← genName?
           uparams := ← genUParams, params := ← choose Nat 0 3
           indices := ← choose Nat 0 3, ty := ← genTerm depth, ctors }

def genRecrDecl (depth : Nat) : Gen RecrDecl := do
  let nRules ← choose Nat 0 2
  let mut rules := #[]
  for _ in [0:nRules] do
    rules := rules.push
      { fields := ← choose Nat 0 3, rhs := ← genTerm depth }
  return { isUnsafe := (← choose Nat 0 1) == 0, name := ← genName?
           uparams := ← genUParams, params := ← choose Nat 0 3
           indices := ← choose Nat 0 3, motives := 1 + (← choose Nat 0 1)
           minors := ← choose Nat 0 3, k := (← choose Nat 0 1) == 0
           ty := ← genTerm depth, rules }

def genDecl (depth : Nat) : Gen Decl := do
  match ← choose Nat 0 7 with
  | 0 | 1 => .defn <$> genDefDecl depth
  | 2 =>
    return .axio { isUnsafe := (← choose Nat 0 1) == 0
                   name := ← genName?, uparams := ← genUParams
                   ty := ← genTerm depth }
  | 3 =>
    return .quot { kind := ← elements #[QuotKindKw.type, .ctor, .lift, .ind]
                   name := ← genName?, uparams := ← genUParams
                   ty := ← genTerm depth }
  | 4 => .indc <$> genIndDecl depth
  | 5 => .recr <$> genRecrDecl depth
  | 6 => do
    let n ← choose Nat 1 2
    let mut members := #[]
    for _ in [0:n] do
      let m ← match ← choose Nat 0 2 with
        | 0 => Decl.indc <$> genIndDecl depth
        | 1 => Decl.recr <$> genRecrDecl depth
        | _ => Decl.defn <$> genDefDecl depth
      members := members.push m
    return .muts members {}
  | _ => do
    let kind ← elements #[PrjKind.dprj, .iprj, .cprj, .rprj]
    let cidx ←
      if kind == .cprj then some <$> choose Nat 0 7 else pure none
    return .prj { kind, name := ← genName?, block := ← genHash
                  idx := ← choose Nat 0 7, cidx }

def genImport : Gen ImportDecl := do
  return { prefixName := ← frequency [(1, some <$> genSName), (1, pure none)]
           hash := { hex := ← genHex 64 } }

def genFile : Gen File := do
  let nImports ← choose Nat 0 2
  let mut imports := #[]
  for _ in [0:nImports] do
    imports := imports.push (← genImport)
  let nDecls ← choose Nat 0 3
  let mut decls := #[]
  for _ in [0:nDecls] do
    decls := decls.push (← genDecl 2)
  let main ←
    if (← choose Nat 0 2) == 0 then
      pure (some { value := ← genTerm 2, ty := ← genTerm 2 : MainExpr })
    else pure none
  return { version := VERSION, imports, decls, main }

/-! ## Shrinking (mirrors `props.rs` shrinkers) -/

def propLeaf : Term := .sort .prop {}

def isPropLeaf : Term → Bool
  | .sort .prop _ => true
  | _ => false

/-- Immediate subterms plus minimal replacements — every candidate is
    strictly smaller or the `Prop` leaf (which shrinks to nothing), so
    shrinking terminates. -/
def shrinkTerm (t : Term) : List Term := Id.run do
  let mut out : List Term := []
  if !isPropLeaf t then out := [propLeaf]
  match t with
  | .app head args _ =>
    out := out ++ [head] ++ args.toList
    if args.size > 1 then
      for i in [0:args.size] do
        out := out ++ [.app head (args.eraseIdxIfInBounds i) {}]
  | .lam bs body _ | .pi bs body _ =>
    out := out ++ [body] ++ (bs.toList.map (·.ty))
  | .arrow d c _ => out := out ++ [d, c]
  | .letE _ _ ty val body _ => out := out ++ [ty, val, body]
  | .proj _ _ v _ => out := out ++ [v]
  | .ref r =>
    if r.levels.isSome then
      out := out ++ [.ref { r with levels := none }]
    if r.name.isSome && r.hash.isSome then
      out := out ++ [.ref { r with hash := none }]
  | .strLit s _ =>
    if !s.isEmpty then out := out ++ [.strLit "" {}]
  | _ => pure ()
  return out

instance : Shrinkable Term := ⟨shrinkTerm⟩

def shrinkDecl (d : Decl) : List Decl := Id.run do
  let mut out : List Decl := []
  match d with
  | .defn x =>
    out := (shrinkTerm x.ty).map (fun ty => .defn { x with ty })
      ++ (shrinkTerm x.value).map (fun value => .defn { x with value })
  | .axio x => out := (shrinkTerm x.ty).map (fun ty => .axio { x with ty })
  | .quot x => out := (shrinkTerm x.ty).map (fun ty => .quot { x with ty })
  | .indc x =>
    for i in [0:x.ctors.size] do
      out := out ++ [.indc { x with ctors := x.ctors.eraseIdxIfInBounds i }]
    out := out ++ (shrinkTerm x.ty).map (fun ty => .indc { x with ty })
  | .recr x =>
    for i in [0:x.rules.size] do
      out := out ++ [.recr { x with rules := x.rules.eraseIdxIfInBounds i }]
    out := out ++ (shrinkTerm x.ty).map (fun ty => .recr { x with ty })
  | .muts members _ =>
    out := members.toList
    if members.size > 1 then
      for i in [0:members.size] do
        out := out ++ [.muts (members.eraseIdxIfInBounds i) {}]
  | .prj _ => pure ()
  return out

instance : Shrinkable Decl := ⟨shrinkDecl⟩

instance : Shrinkable File where
  shrink f := Id.run do
    let mut out : List File := []
    if f.main.isSome then
      out := out ++ [{ f with main := none }]
    if let some m := f.main then
      out := out ++ (shrinkTerm m.value).map
        (fun v => { f with main := some { m with value := v } })
      out := out ++ (shrinkTerm m.ty).map
        (fun t => { f with main := some { m with ty := t } })
    for i in [0:f.imports.size] do
      out := out ++ [{ f with imports := f.imports.eraseIdxIfInBounds i }]
    for i in [0:f.decls.size] do
      out := out ++ [{ f with decls := f.decls.eraseIdxIfInBounds i }]
    for i in [0:f.decls.size] do
      for s in shrinkDecl f.decls[i]! do
        out := out ++ [{ f with decls := f.decls.set! i s }]
    return out

/-! ## SampleableExt instances -/

instance : SampleableExt Term :=
  SampleableExt.mkSelfContained (genTerm 4)

instance : SampleableExt File :=
  SampleableExt.mkSelfContained genFile

/-- Fuzz input: strings biased toward syntax-relevant characters
    (delimiters, escapes, digits, unicode) — a sharper boundary walk
    than uniform random strings. -/
structure Fuzz where
  s : String
  deriving Repr

def fuzzChars : Array Char :=
  #['(', ')', '{', '}', '[', ']', '⦃', '⦄', '#', '«', '»', '"', '\\',
    '.', ',', ':', ';', '=', '>', '→', '|', '+', '_', ' ', '\n', '\t',
    'a', 'x', 'f', '0', '1', '9', 'α', 'd', 'e', 'u', 'n', '-', '/']

def genFuzz : Gen Fuzz := do
  let n ← choose Nat 0 60
  let mut s := ""
  for _ in [0:n] do
    let c ← frequency [
      (6, elements fuzzChars),
      (1, Char.ofNat <$> choose Nat 0x20 0x7e),
      (1, Char.ofNat <$> choose Nat 0xa0 0x2fff)
    ]
    s := s.push c
  return ⟨s⟩

instance : Shrinkable Fuzz where
  shrink f :=
    if f.s.isEmpty then []
    else
      let l := f.s.toList
      [⟨String.ofList (l.take (l.length / 2))⟩,
       ⟨String.ofList (l.drop (l.length / 2))⟩,
       ⟨String.ofList l.tail⟩]

instance : SampleableExt Fuzz := SampleableExt.mkSelfContained genFuzz

/-- A batch of (position, pool-index) char mutations for the
    near-valid fuzz property. -/
structure Muts where
  muts : List (Nat × Nat)
  deriving Repr, Inhabited

def genMuts : Gen Muts := do
  let n ← choose Nat 0 6
  let mut out : List (Nat × Nat) := []
  for _ in [0:n] do
    out := (← choose Nat 0 100000, ← choose Nat 0 1000) :: out
  return ⟨out⟩

instance : Shrinkable Muts where
  shrink m := if m.muts.isEmpty then [] else [⟨m.muts.tail⟩]

instance : SampleableExt Muts := SampleableExt.mkSelfContained genMuts

end Tests.Gen.IxonSyntax
