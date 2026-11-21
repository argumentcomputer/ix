import IxAICommon.Hash
import Std.Data.HashMap
import Lean.Data.Json

/-!
# The Aiur artifact framing a verifier needs

`verify_claim` and `aiur_exec_check` recompile a program's verifying key from an execution
package: `"IXAIURX\0" ‖ nat(2) ‖ package ‖ nats(args) ‖ nats(invalid_args) ‖ list(hint)`, where
`package` is a program package (`"IXAIURP\0" ‖ nat(2) ‖ program ‖ option(trace)`). Neither reads
the arguments or the hints. A verifier therefore wraps the approved program package, and nothing
else, in an execution package with no arguments and no hints, so the key it verifies against is
the approved program's, whatever a prover's packages contain.

`nat` is Ixon's TagN code with no flag bits (`aiur::ixon::Writer::nat`).
-/

namespace IxAIVerify.Ixon

def end1 : Nat := 1 <<< 7
def end2 : Nat := end1 + (1 <<< 14)
def end3 : Nat := end2 + (1 <<< 16)
def end4 : Nat := end3 + (1 <<< 24)
def end5 : Nat := end4 + (1 <<< 32)

/-- The little-endian bytes of `v`, `width` of them. -/
def le (v width : Nat) : List UInt8 :=
  (List.range width).map fun k => ((v >>> (8 * k)) % 256).toUInt8

/-- TagN with no flag bits, for values below `2^64`. -/
def nat (v : Nat) : List UInt8 :=
  if v < end1 then [v.toUInt8]
  else if v < end2 then [(end1 + (v - end1) / 256).toUInt8, ((v - end1) % 256).toUInt8]
  else if v < end3 then (end1 + 64).toUInt8 :: le (v - end2) 2
  else if v < end4 then (end1 + 65).toUInt8 :: le (v - end3) 3
  else if v < end5 then (end1 + 66).toUInt8 :: le (v - end4) 4
  else (end1 + 67).toUInt8 :: le (v - end5) 8

def nats (vs : List Nat) : List UInt8 := nat vs.length ++ vs.flatMap nat

def packageMagic : List UInt8 := "IXAIURP".toUTF8.toList ++ [0]
def executionMagic : List UInt8 := "IXAIURX".toUTF8.toList ++ [0]
def formatVersion : Nat := 2

/-- Does `b` start with a program package header? -/
def isPackage (b : ByteArray) : Bool :=
  b.size > 9 && (b.extract 0 9).toList == packageMagic ++ nat formatVersion

/-- The execution package that carries only `package`: no arguments, no invalid arguments, no
hints. -/
def wrapPackage (package : ByteArray) : ByteArray :=
  ⟨(executionMagic ++ nat formatVersion).toArray⟩ ++ package ++ ⟨(nats [] ++ nats [] ++ nat 0).toArray⟩

def header : Nat := (executionMagic ++ nat formatVersion).length

/-- The program package inside a prover's execution package whose arguments are `args`: the bytes
between the header and the last occurrence of `nats(args)`. Used when assembling a receipt; a
verifier checks the result's digest against the approved one and never trusts this split. -/
def programOf (exec : ByteArray) (args : List Nat) : Option ByteArray := Id.run do
  let tail := (nats args).toArray
  if exec.size < header + tail.size then return none
  unless (exec.extract 0 header).toList == executionMagic ++ nat formatVersion do return none
  let mut k := exec.size - tail.size
  while k ≥ header do
    if exec.get! k == tail[0]! && (exec.extract k (k + tail.size)).data == tail then
      return some (exec.extract header k)
    if k == 0 then break
    k := k - 1
  return none

end IxAIVerify.Ixon

/-!
# Reading Ix environments and claims

A verifier reads what the trainer's compiled environment (`.ixe`) says about the model and the
claims without running Ix: the Ixon records of the claim theorems (their types) and of the model
constant (its value). Every record is authenticated by its address, the BLAKE3 of its bytes, so the
environment file needs no digest of its own: a constant's address commits to its content, and
through its references to every constant it mentions.

Only the parts of the format a verifier needs are read: the environment header (envelope version
4 or 5, role binding), the blob and constant sections, and definitions with their expressions. The
grammar follows `Ix.Ixon`, `IxC.Ixon.Codec` and `Ix.Claim` of the pinned ix build (`docs/Ixon.md` in
the Ix repository). A definition is parsed in full (type, value, sharing, references, universes) and
must end where its framing says it does. Expressions are resolved into `Term`s: shared subterms
expanded, references replaced by addresses, universe and literal indices by their values,
application and binder telescopes made binary.

The same reader serves the package verifier (claims, templates, the model constant) and the reward
harness (`checkGoalType`).

Every record is hashed when the file is read, though only a few are ever looked up: those callers'
verdicts cover the whole file (see `Env`), so a damaged record that is never dereferenced must
still be refused. What the reader avoids is copying: records stay slices of the file until looked
up. Shared subterms are resolved once per sharing entry (`Env.resolve`), with the expansion budget
still charged for every occurrence.
-/

namespace IxAIVerify.Ixon

open IxAI

structure Cursor where
  bytes : ByteArray
  pos : Nat := 0

abbrev Get := StateT Cursor (Except String)

def u8 : Get UInt8 := do
  let c ← get
  if h : c.pos < c.bytes.size then
    set { c with pos := c.pos + 1 }
    return c.bytes[c.pos]
  else throw "unexpected end of input"

def takeBytes (n : Nat) : Get ByteArray := do
  let c ← get
  if c.pos + n > c.bytes.size then throw s!"needs {n} bytes, {c.bytes.size - c.pos} left"
  set { c with pos := c.pos + n }
  return c.bytes.extract c.pos (c.pos + n)

def leNat (bs : ByteArray) : Nat := bs.data.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- `leNat (← takeBytes n)`, with the same bounds check and message, without copying the bytes. -/
def leBytes (n : Nat) : Get Nat := do
  let c ← get
  if c.pos + n > c.bytes.size then throw s!"needs {n} bytes, {c.bytes.size - c.pos} left"
  set { c with pos := c.pos + n }
  let mut v := 0
  for k in [0:n] do v := v + (c.bytes.get! (c.pos + k)).toNat <<< (8 * k)
  return v

def address : Get Digest := return ⟨← takeBytes 32⟩

/-- A TagN integer with an `f`-bit flag: `(flag, value)`. -/
def tagN (f : Nat) : Get (Nat × Nat) := do
  let b := (← u8).toNat
  let w := 8 - f
  let flag := b >>> w
  let p := b % (1 <<< w)
  let lead := 1 <<< (w - 1)
  if p < lead then return (flag, p)
  let mbit := 1 <<< (w - 2)
  let e1 := lead
  if p - lead < mbit then return (flag, e1 + (p - lead) * 256 + (← u8).toNat)
  let e2 := e1 + (1 <<< (w - 2 + 8))
  let e3 := e2 + (1 <<< 16)
  let e4 := e3 + (1 <<< 24)
  let e5 := e4 + (1 <<< 32)
  match p - lead - mbit with
    | 0 => return (flag, e2 + (← leBytes 2))
    | 1 => return (flag, e3 + (← leBytes 3))
    | 2 => return (flag, e4 + (← leBytes 4))
    | 3 =>
      let v := e5 + (← leBytes 8)
      if v < 2 ^ 64 then return (flag, v) else throw "TagN value exceeds UInt64"
    | c => throw s!"invalid TagN code {c}"

def tagN0 : Get Nat := return (← tagN 0).2

def count (minBytes : Nat := 1) : Get Nat := do
  let n ← tagN0
  let c ← get
  if n * minBytes > c.bytes.size - c.pos then throw "count exceeds remaining bytes"
  return n

def times {α : Type} (n : Nat) (g : Get α) : Get (Array α) := do
  let mut out := #[]
  for _ in [0:n] do out := out.push (← g)
  return out

inductive Univ where
  | zero
  | succ (u : Univ)
  | max (a b : Univ)
  | imax (a b : Univ)
  | var (i : Nat)
  deriving BEq, Repr, Inhabited

partial def univ : Get Univ := do
  let (flag, v) ← tagN 2
  match flag with
  | 0 => if v == 0 then return .zero else
      let base ← univ
      return (List.range v).foldl (fun u _ => .succ u) base
  | 1 => return .max (← univ) (← univ)
  | 2 => return .imax (← univ) (← univ)
  | 3 => return .var v
  | f => throw s!"invalid universe flag {f}"

/-- An Ixon expression as stored: indices into its constant's tables. -/
inductive Raw where
  | sort (u : Nat)
  | var (i : Nat)
  | ref (r : Nat) (us : Array Nat)
  | recur (r : Nat) (us : Array Nat)
  | prj (t field : Nat) (e : Raw)
  | str (r : Nat)
  | nat (r : Nat)
  | app (f : Raw) (args : Array Raw)
  | lam (binders : Array (UInt8 × Raw)) (body : Raw)
  | all (binders : Array (UInt8 × Raw)) (body : Raw)
  | letE (flags : Nat) (binder : UInt8) (ty val body : Raw)
  | share (i : Nat)
  deriving Inhabited

/-- Expressions nested deeper than this are refused rather than parsed, so a crafted record cannot
exhaust the stack. -/
def maxExprDepth : Nat := 100000

partial def raw (depth : Nat := 0) : Get Raw := do
  if depth > maxExprDepth then throw "expression too deep"
  let sub := raw (depth + 1)
  let (flag, v) ← tagN 4
  match flag with
  | 0x0 => return .sort v
  | 0x1 => return .var v
  | 0x2 => let r ← tagN0; return .ref r (← times v tagN0)
  | 0x3 => let r ← tagN0; return .recur r (← times v tagN0)
  | 0x4 => let t ← tagN0; return .prj t v (← sub)
  | 0x5 => return .str v
  | 0x6 => return .nat v
  | 0x7 =>
    if v == 0 then throw "empty application"
    let f ← sub
    return .app f (← times v sub)
  | 0x8 =>
    if v == 0 then throw "lambda with no binders"
    let bs ← times v (do let c ← u8; return (c, ← sub))
    return .lam bs (← sub)
  | 0x9 =>
    if v == 0 then throw "forall with no binders"
    let bs ← times v (do let c ← u8; return (c, ← sub))
    return .all bs (← sub)
  | 0xA =>
    -- Bit 0: non-dependent; bit 1: shared borrow. Higher header values are invalid.
    if v > 3 then throw "invalid let header"
    let b ← u8; return .letE v b (← sub) (← sub) (← sub)
  | 0xB => return .share v
  | f => throw s!"invalid expression flag {f}"

/-- A resolved expression: references are addresses, literals are values. -/
inductive Term where
  | sort (u : Univ)
  | var (i : Nat)
  | ref (a : Digest) (us : List Univ)
  | recur (i : Nat) (us : List Univ)
  | prj (t : Digest) (field : Nat) (e : Term)
  | str (hex : String)
  | nat (n : Nat)
  | app (f a : Term)
  | lam (contract : UInt8) (ty body : Term)
  | all (contract : UInt8) (ty body : Term)
  | letE (flags : Nat) (binder : UInt8) (ty val body : Term)
  deriving BEq, Inhabited

/-- `head a₁ … aₙ` as `(head, [a₁, …, aₙ])`. -/
def Term.spine (t : Term) : Term × List Term := go t []
where
  go : Term → List Term → Term × List Term
    | .app f a, args => go f (a :: args)
    | t, args => (t, args)

/-- Does `t` have a free variable when read under `depth` binders? `t.loose 0`: is `t` open? -/
def Term.loose (depth : Nat) : Term → Bool
  | .var i => i ≥ depth
  | .prj _ _ e => e.loose depth
  | .app f a => f.loose depth || a.loose depth
  | .lam _ ty b | .all _ ty b => ty.loose depth || b.loose (depth + 1)
  | .letE _ _ ty v b => ty.loose depth || v.loose depth || b.loose (depth + 1)
  | _ => false

/-- A definition record: kind (`0` def, `1` opaque, `2` theorem), safety (`1` safe), universe
parameters, type and value, with the constant's tables. -/
structure Definition where
  kind : Nat
  safety : Nat
  lvls : Nat
  typ : Raw
  value : Raw
  sharing : Array Raw
  refs : Array Digest
  univs : Array Univ

def definition : Get Definition := do
  let (flag, v) ← tagN 4
  unless flag == 0xD && v == 0 do throw "not a definition record"
  let ks ← u8
  let kind := (ks >>> 2).toNat
  let safety := (ks &&& 3).toNat
  if kind > 2 || safety > 2 then throw "invalid definition kind or safety"
  let lvls ← tagN0
  let typ ← raw
  let value ← raw
  let sharing ← times (← count) raw
  let refs ← times (← count 32) address
  let univs ← times (← count) univ
  return { kind, safety, lvls, typ, value, sharing, refs, univs }

/-- An environment's authenticated records: every blob and constant hashes to its address. Records
are kept as `(offset, length)` in `bytes`, the file they were read from, and copied out only when
looked up (`Env.blob?`, `Env.const?`).

Every record is still hashed when the file is read, not when it is first looked up. A lazy check
would be enough for the lookups themselves, which are by address and would hash a record before
its first use, but the verdicts of this reader's callers say more than that: `verifyClaims`
reports the environment as authenticated record by record, and `checkGoalType` refuses an
environment with any record that does not hash to its address. Both would change for a file whose
damaged records are never dereferenced. -/
structure Env where
  version : Nat
  binding : Option Digest
  bytes : ByteArray
  blobs : Std.HashMap Digest (Nat × Nat)
  consts : Std.HashMap Digest (Nat × Nat)

def Env.slice (e : Env) : Nat × Nat → ByteArray
  | (o, n) => e.bytes.extract o (o + n)

def Env.blob? (e : Env) (a : Digest) : Option ByteArray := (e.blobs.get? a).map e.slice
def Env.const? (e : Env) (a : Digest) : Option ByteArray := (e.consts.get? a).map e.slice

/-- A length-prefixed record at the cursor: its `(offset, length)`, after checking that its bytes
hash to `a` (`what` names it in the error). -/
def record (a : Digest) (what : String) : Get (Nat × Nat) := do
  let n ← tagN0
  let o := (← get).pos
  let bytes ← takeBytes n
  unless blake3 bytes == a do throw s!"{what} {a} does not hash to its address"
  return (o, n)

def env : Get Env := do
  let (flag, version) ← tagN 4
  unless flag == 0xE && (version == 4 || version == 5) do
    throw s!"not an .ixe environment (header flag {flag}, version {version})"
  let _root ← address
  match ← u8 with
  | 0 => pure ()
  | 1 => discard address
  | t => throw s!"invalid main tag {t}"
  discard <| times (← count 32) address
  let binding ← if version == 5 then do
      let a ← address
      let bytes ← takeBytes (← tagN0)
      unless blake3 bytes == a do throw "the role binding does not hash to its address"
      pure (some a)
    else pure none
  let mut blobs : Std.HashMap Digest (Nat × Nat) := {}
  let nBlobs ← count 33
  for _ in [0:nBlobs] do
    let a ← address
    blobs := blobs.insert a (← record a "blob")
  let mut consts : Std.HashMap Digest (Nat × Nat) := {}
  let nConsts ← count 33
  for _ in [0:nConsts] do
    let a ← address
    consts := consts.insert a (← record a "constant")
  return { version, binding, bytes := (← get).bytes, blobs, consts }

def readEnv (bytes : ByteArray) : Except String Env := (env.run { bytes }).map (·.1)

def Env.definition? (e : Env) (a : Digest) : Except String Definition := do
  let some bytes := e.const? a | throw s!"constant {a} is not in the environment"
  let (d, c) ← definition.run { bytes }
  unless c.pos == bytes.size do throw s!"constant {a}: trailing bytes"
  return d

/-- The state of `Env.resolve`: the nodes left in the budget, and each sharing entry already
resolved, with the number of nodes its expansion counts. -/
structure ResolveState where
  budget : Nat
  shared : Std.HashMap Nat (Term × Nat) := {}

/-- Resolve a stored expression of `d`. Shared subterms are expanded under a node budget, so a
record whose sharing would expand beyond it is refused rather than unfolded. The budget counts the
nodes of the expanded term; each sharing entry is resolved once and reused (the resulting `Term`
shares it), and every reuse charges its full expanded size, so the work is linear in the stored
expression while the verdict is the one of expanding every occurrence. -/
partial def Env.resolve (e : Env) (d : Definition) (r : Raw) (budget : Nat := 4000000) :
    Except String Term := do
  let (t, _) ← (go r).run { budget }
  return t
where
  exceeded : String := "expression exceeds the expansion budget"
  tick : StateT ResolveState (Except String) Unit := do
    let s ← get
    if s.budget == 0 then throw exceeded
    set { s with budget := s.budget - 1 }
  refAt (i : Nat) : StateT ResolveState (Except String) Digest := do
    let some a := d.refs[i]? | throw s!"reference index {i} out of range"
    return a
  univAt (i : Nat) : StateT ResolveState (Except String) Univ := do
    let some u := d.univs[i]? | throw s!"universe index {i} out of range"
    return u
  blob (i : Nat) : StateT ResolveState (Except String) ByteArray := do
    let a ← refAt i
    let some b := e.blob? a | throw s!"literal blob {a} is not in the environment"
    return b
  binders (bs : List (UInt8 × Raw)) (body : Raw) (mk : UInt8 → Term → Term → Term) :
      StateT ResolveState (Except String) Term := do
    match bs with
    | [] => go body
    | (c, ty) :: rest => return mk c (← go ty) (← binders rest body mk)
  go (r : Raw) : StateT ResolveState (Except String) Term := do
    tick
    match r with
    | .sort u => return .sort (← univAt u)
    | .var i => return .var i
    | .ref i us => return .ref (← refAt i) (← us.toList.mapM univAt)
    | .recur i us => return .recur i (← us.toList.mapM univAt)
    | .prj t f v => return .prj (← refAt t) f (← go v)
    | .str i => return .str (Digest.hex ⟨← blob i⟩)
    | .nat i => return .nat (leNat (← blob i))
    | .app f args => args.foldlM (fun acc a => do return .app acc (← go a)) (← go f)
    | .lam bs body => binders bs.toList body .lam
    | .all bs body => binders bs.toList body .all
    | .letE fl b ty v body => return .letE fl b (← go ty) (← go v) (← go body)
    | .share i =>
      let some s := d.sharing[i]? | throw s!"share index {i} out of range"
      match (← get).shared.get? i with
      | some (t, cost) =>
        let st ← get
        if st.budget < cost then throw exceeded
        set { st with budget := st.budget - cost }
        return t
      | none =>
        let before := (← get).budget
        let t ← go s
        modify fun st => { st with shared := st.shared.insert i (t, before - st.budget) }
        return t

/-! ## Theorem statements

The reward harness fixes a statement as a constant (`IxAIReward.target`) and needs to know that the
compiled `IxAIReward.goal` is a theorem *of that constant*, from the compiled environment itself,
so that how the source was parsed is not part of what it trusts. `checkGoalType` reads exactly that
from the bytes of an `.ixe`:

1. the environment, every record authenticated by its address (`readEnv`);
2. the record stored under the goal's address, parsed in full (`Env.definition?`): a safe,
   universe-monomorphic theorem;
3. its type expression, through the record's sharing table, which must be a reference without
   universe arguments to an entry of its reference table equal to the target's address. -/

/-- The address a definition's type is, through its sharing table: the type must be a constant
without universe arguments. -/
def Definition.typeRef (d : Definition) : Except String Digest := do
  let mut root := d.typ
  for _ in [0:d.sharing.size + 1] do
    match root with
    | .share i =>
      match d.sharing[i]? with
      | some r => root := r
      | none => throw s!"sharing index {i} out of range"
    | .ref k us =>
      unless us.isEmpty do throw "the type has universe arguments"
      match d.refs[k]? with
      | some a => return a
      | none => throw s!"reference index {k} out of range"
    | _ => throw "the type is not a constant"
  throw "cyclic sharing"

/-- Check, from the `.ixe` bytes alone, that the constant at `goal` is a safe theorem whose
statement is the constant at `target`. -/
def checkGoalType (bytes : ByteArray) (goal target : Digest) : Except String Unit := do
  let env ← readEnv bytes
  let d ← env.definition? goal
  unless d.kind == 2 && d.safety == 1 do throw "not a safe theorem"
  unless d.lvls == 0 do throw "universe-polymorphic"
  let a ← d.typeRef
  unless a == target do throw s!"the goal's type is the constant {a}, not the target {target}"

/-! ## Templates

A claim template is a statement with holes: the value of a `Prop`-valued definition
`fun h₀ … hₖ₋₁ => body`, whose binders are the holes. A theorem instantiates the template when its
type is `body` with each hole replaced by a closed term. -/

/-- Match `t` against the template body `pat` with `holes` holes. Returns the hole values, in
binder order. -/
partial def matchTemplate (holes : Nat) (pat t : Term) : Option (Array Term) := do
  let σ ← go 0 pat t (Array.replicate holes none)
  σ.mapM id
where
  go (depth : Nat) (p t : Term) (σ : Array (Option Term)) : Option (Array (Option Term)) :=
    match p, t with
    | .var i, _ =>
      if i < depth then (if t == .var i then some σ else none)
      else
        let k := i - depth
        if k ≥ holes || t.loose 0 then none
        else
          let slot := holes - 1 - k
          match σ[slot]! with
          | none => some (σ.set! slot (some t))
          | some prev => if prev == t then some σ else none
    | .prj a f e, .prj a' f' e' => if a == a' && f == f' then go depth e e' σ else none
    | .app f a, .app f' a' => do go depth a a' (← go depth f f' σ)
    | .lam c ty b, .lam c' ty' b' =>
      if c == c' then do go (depth + 1) b b' (← go depth ty ty' σ) else none
    | .all c ty b, .all c' ty' b' =>
      if c == c' then do go (depth + 1) b b' (← go depth ty ty' σ) else none
    | .letE f k ty v b, .letE f' k' ty' v' b' =>
      if f == f' && k == k' then do
        let σ ← go depth ty ty' σ
        go (depth + 1) b b' (← go depth v v' σ)
      else none
    | p, t => if p == t then some σ else none

/-- Split `fun h₀ … hₖ₋₁ => body` into its `k` holes and body. -/
def Term.unbind : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, .lam _ _ b => Term.unbind k b
  | _, _ => none

/-! ## Terms as JSON, for templates carried in a job commitment -/

open Lean (Json)

partial def Univ.toJson : Univ → Json
  | .zero => Json.arr #["zero"]
  | .succ u => Json.arr #["succ", u.toJson]
  | .max a b => Json.arr #["max", a.toJson, b.toJson]
  | .imax a b => Json.arr #["imax", a.toJson, b.toJson]
  | .var i => Json.arr #["var", i]

partial def Univ.ofJson (j : Json) : Except String Univ := do
  let a ← j.getArr?
  match ← (a[0]?.getD Json.null).getStr?, a.size with
  | "zero", 1 => return .zero
  | "succ", 2 => return .succ (← Univ.ofJson a[1]!)
  | "max", 3 => return .max (← Univ.ofJson a[1]!) (← Univ.ofJson a[2]!)
  | "imax", 3 => return .imax (← Univ.ofJson a[1]!) (← Univ.ofJson a[2]!)
  | "var", 2 => return .var (← a[1]!.getNat?)
  | k, _ => throw s!"malformed universe {k}"

partial def Term.toJson : Term → Json
  | .sort u => Json.arr #["sort", u.toJson]
  | .var i => Json.arr #["var", i]
  | .ref a us => Json.arr #["ref", a.hex, Json.arr (us.map Univ.toJson).toArray]
  | .recur i us => Json.arr #["rec", i, Json.arr (us.map Univ.toJson).toArray]
  | .prj a f e => Json.arr #["prj", a.hex, f, e.toJson]
  | .str h => Json.arr #["str", h]
  | .nat n => Json.arr #["nat", n]
  | .app f a => Json.arr #["app", f.toJson, a.toJson]
  | .lam c ty b => Json.arr #["lam", c.toNat, ty.toJson, b.toJson]
  | .all c ty b => Json.arr #["all", c.toNat, ty.toJson, b.toJson]
  | .letE fl k ty v b => Json.arr #["let", fl, k.toNat, ty.toJson, v.toJson, b.toJson]

partial def Term.ofJson (j : Json) : Except String Term := do
  let a ← j.getArr?
  let at_ : Nat → Json := fun i => a[i]?.getD Json.null
  let digest : Nat → Except String Digest := fun i => do
    match Digest.ofHex? (← (at_ i).getStr?) with
    | some d => pure d
    | none => throw "malformed address"
  let univs : Nat → Except String (List Univ) := fun i => do (← (at_ i).getArr?).toList.mapM Univ.ofJson
  let byte : Nat → Except String UInt8 := fun i => do
    let n ← (at_ i).getNat?
    if n < 256 then pure n.toUInt8 else throw "malformed contract"
  match ← (at_ 0).getStr?, a.size with
  | "sort", 2 => return .sort (← Univ.ofJson (at_ 1))
  | "var", 2 => return .var (← (at_ 1).getNat?)
  | "ref", 3 => return .ref (← digest 1) (← univs 2)
  | "rec", 3 => return .recur (← (at_ 1).getNat?) (← univs 2)
  | "prj", 4 => return .prj (← digest 1) (← (at_ 2).getNat?) (← Term.ofJson (at_ 3))
  | "str", 2 => return .str (← (at_ 1).getStr?)
  | "nat", 2 => return .nat (← (at_ 1).getNat?)
  | "app", 3 => return .app (← Term.ofJson (at_ 1)) (← Term.ofJson (at_ 2))
  | "lam", 4 => return .lam (← byte 1) (← Term.ofJson (at_ 2)) (← Term.ofJson (at_ 3))
  | "all", 4 => return .all (← byte 1) (← Term.ofJson (at_ 2)) (← Term.ofJson (at_ 3))
  | "let", 6 => do
    let ty ← Term.ofJson (at_ 3)
    let v ← Term.ofJson (at_ 4)
    let b ← Term.ofJson (at_ 5)
    return .letE (← (at_ 1).getNat?) (← byte 2) ty v b
  | k, _ => throw s!"malformed term {k}"

/-! ## Check claims

The bytes of `Check(ctx, const, assumptions)` (`Ix.Claim.ser`): the claim tag `E4`, object format
`4`, the validator (`3`: erased-lean-v2, validating its binding; `4`: assuming it), then the
context's specification digest, binding and optional axiom root, the constant and the optional
assumption root. A stored proof (`Ixon.Proof`) carries the same scope and payload under the proof
tag `F1`, followed by the proof bytes. -/

structure CheckClaim where
  spec : Digest
  binding : Digest
  axioms : Option Digest
  const : Digest
  assumptions : Option Digest
  bindingAssumed : Bool
  deriving DecidableEq

def optAddrBytes : Option Digest → ByteArray
  | none => ⟨#[0]⟩
  | some a => ⟨#[1]⟩ ++ a.bytes

def CheckClaim.ser (c : CheckClaim) : ByteArray :=
  ⟨#[0xE4, 4, if c.bindingAssumed then 4 else 3]⟩ ++ c.spec.bytes ++ c.binding.bytes ++
    optAddrBytes c.axioms ++ c.const.bytes ++ optAddrBytes c.assumptions

def CheckClaim.digest (c : CheckClaim) : Digest := blake3 c.ser

def optAddress : Get (Option Digest) := do
  match ← u8 with
  | 0 => return none
  | 1 => return some (← address)
  | t => throw s!"invalid optional address tag {t}"

/-- The claim of a stored proof, if it is a `Check` proof. -/
def checkProofClaim (bytes : ByteArray) : Except String CheckClaim := do
  let get : Get CheckClaim := do
    let (flag, variant) ← tagN 4
    unless flag == 0xF do throw "not a stored proof"
    unless variant == 1 do throw s!"a proof of claim variant {variant + 3}, not a Check claim"
    let format ← u8
    unless format == 4 do throw s!"object format {format}, expected 4"
    let validator ← u8
    unless validator == 3 || validator == 4 do throw s!"validator {validator} is not a Check validator"
    let spec ← address
    let binding ← address
    let axioms ← optAddress
    let const ← address
    let assumptions ← optAddress
    return { spec, binding, axioms, const, assumptions, bindingAssumed := validator == 4 }
  return (← get.run { bytes }).1

end IxAIVerify.Ixon
