import Ix.Ixon.Authenticated
import Ix.KernelCheck.Run
import Ix.Runtime.Thread
import Tests.Ix.Kernel.DepthRef

/-! # The cases of `kernel-depth`, run one per process (`kernel-depth-case NAME N`)

The records and entry points of each case; the test itself, which runs each
case on a 2 MiB stack in a process of its own, and what each case shows, are in
`Tests.Ix.Kernel.Depth`. A separate small executable, so that a case's process
starts in milliseconds (the test binary's own start-up takes about 20 s). -/

namespace Tests.Ix.Kernel.Depth

open Benchmarks.Kernel.CheckIxeStep

abbrev IE := _root_.Ixon.Expr
abbrev IU := _root_.Ixon.Univ

/-! ## The records -/

/-- `∀ p : Prop, p`, a closed proposition. -/
def P : IE := _root_.Ixon.Expr.leanAll (.sort 0) (.var 0)

/-- `∀ p : Prop, p → p`. -/
def Pid : IE := _root_.Ixon.Expr.leanAll (.sort 0) (_root_.Ixon.Expr.leanAll (.var 0) (.var 1))

/-- `Prop`, `Type`. -/
def univs01 : Array IU := #[.zero, .succ .zero]

def defnR (ty val : IE) (refs : Array Address) : _root_.Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, ty, val⟩, #[], refs, univs01⟩

def record (c : _root_.Ixon.Constant) : Address × ByteArray :=
  let b := _root_.Ixon.serConstant c
  (Address.admissionHash b, b)

/-- `D0 : Type := Prop`, then `n` records `Dj : Type := step D(j-1)`, then
`last D_n` if given. -/
def chain (n : Nat) (step : IE → IE) (last : Option (IE → IE)) : _root_.Ix.Kernel.Admission.Records := Id.run do
  let d0 := record (defnR (.sort 1) (.sort 0) #[])
  let mut rs := #[d0]
  let mut prev := d0.1
  for _ in [0:n] do
    let dj := record (defnR (.sort 1) (step (.ref 0 #[])) #[prev])
    rs := rs.push dj
    prev := dj.1
  if let some f := last then
    rs := rs.push (record (defnR (.ref 0 #[]) (f (.ref 0 #[])) #[prev]))
  return rs.toList

/-- `delta n`: `X : D_n := P` after `Dj : Type := D(j-1)`. -/
def delta (n : Nat) : _root_.Ix.Kernel.Admission.Records := chain n id (some fun _ => P)

/-- `wide n`: `Dj : Type := Prop → D(j-1)`; nothing unfolds. -/
def wide (n : Nat) : _root_.Ix.Kernel.Admission.Records := chain n (_root_.Ixon.Expr.leanAll (.sort 0)) none

/-- A natural number's blob: its little-endian bytes, without trailing zeros
(the reader's `natural`). -/
def natBytes (n : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := .empty
  let mut m := n
  while m > 0 do
    out := out.push (m % 256).toUInt8
    m := m / 256
  return out

/-- `iota n`: `X : Prop := Nat.rec.{1} (fun _ : Nat => Prop) P' (fun n ih => ih) n`
with `P' = ∀ p : Prop, p → p` and `n` a literal (a blob), then `T : X := fun p h => h`.
`Nat.rec` and `Nat` are the prelude's, at the addresses the default table binds. -/
def iota (table : _root_.Ix.Kernel.RoleTable) (n : Nat) :
    Except String (_root_.Ix.Kernel.Admission.Records × _root_.Ix.Kernel.Ingress.Blobs) := do
  let bound (r : _root_.Ix.Kernel.Role) : Except String Address :=
    match table.bound.find? (·.1 == r) with
    | some (_, a) => pure a
    | none => throw s!"the default table binds no {repr r}"
  let natRec ← bound .natRec
  let nat ← bound .nat
  let blob := natBytes n
  let blobAddr := Address.admissionHash blob
  let motive : IE := _root_.Ixon.Expr.leanLam (.ref 1 #[]) (.sort 0)
  let minor : IE := _root_.Ixon.Expr.leanLam (.ref 1 #[]) (_root_.Ixon.Expr.leanLam (.sort 0) (.var 0))
  let value : IE := .app (.app (.app (.app (.ref 0 #[1]) motive) Pid) minor) (.nat 2)
  let x := record (defnR (.sort 0) value #[natRec, nat, blobAddr])
  let t := record (defnR (.ref 0 #[]) (_root_.Ixon.Expr.leanLam (.sort 0) (_root_.Ixon.Expr.leanLam (.var 0) (.var 0))) #[x.1])
  pure ([x, t], [(blobAddr, blob)])

/-- The command line's limits (`ix check-lean`'s `artifactLimits`). -/
def limits : _root_.Ix.Kernel.Admission.Limits :=
  { maxRecords := 1 <<< 22, maxBlobs := 1 <<< 22, maxTotalBytes := 1 <<< 34,
    maxRecordBytes := 1 <<< 28, maxRecordUnivNodes := 1 <<< 26 }

def hint : _root_.Ix.Kernel.ConstRef Address → Option _root_.Ix.Kernel.ReducibilityHint := fun _ => some (.regular 1)

/-! ## The record-by-record check -/

/-- An address that encodes `n` (no hashing: the loop source decodes it). -/
def addrOf (n : Nat) : Address :=
  ⟨⟨(List.range 32).toArray.map fun i => if i < 8 then ((n >>> (8 * i)) % 256).toUInt8 else 0x5a⟩⟩

def indexOf (a : Address) : Nat :=
  (List.range 8).foldr (fun i acc => acc * 256 + (a.hash.data[i]?.getD 0).toNat) 0

/-- `n` declarations `Dj : Type := Prop` and, last, `Dn : Type := Type`
(rejected): the check-lean step's records, read without a codec. -/
def stepSource (n : Nat) : LoopSource Nat .anon :=
  let decl (j : Nat) : _root_.Ix.Kernel.Declaration .anon :=
    .defnDecl ⟨.id (addrOf j), [], .sort (.succ .zero)⟩
      (.sort (if j < n then .zero else .succ .zero)) .opaque
  { view := fun _ => some { kind := "fixture", recs := #[], deps := fun _ => #[] }
    read := fun _ a => pure { decls := #[decl (indexOf a)] }
    commit := fun st _ _ => st + 1
    init := pure 0 }

/-! ## One case, in the child -/

/-- A non-tail recursion `n` deep (the control). -/
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

def timed (act : IO String) : IO String := do
  let t0 ← IO.monoMsNow
  let s ← act
  return s!"{s} in {(← IO.monoMsNow) - t0} ms"

def entryVerdict (r : Except _root_.Ix.Kernel.Admission.Error (_root_.Ix.Kernel.Env .anon)) : String :=
  match r with
  | .ok env => s!"accepted ({env.consts.length} constants)"
  | .error e => s!"{if e.outcome == .declined then "declined" else "rejected"}: {(toString e).take 200}"

/-- KD's chain: `E_0 = L = λy. y`, `E_k = (λx. E_{k-1}) P L` with `P = Sort p`
(binders `pw := .never`, `x` unused). Returns `(λx. E_{n-1}, E_n)`. Every level is
built by the same step, so with a hash of `w` bits the hashes of `E_k` iterate one
function and, at 32 bits, cycle after a few thousand levels (`docs/kernel.md`,
"Running time"). -/
def nestedChain (p n : Nat) : _root_.Ix.Kernel.Expr .anon × _root_.Ix.Kernel.Expr .anon := Id.run do
  let never : _root_.Ix.Kernel.BinderMeta := { pw := .never }
  let pe : _root_.Ix.Kernel.Expr .anon := .sort ((List.range p).foldl (fun u _ => .succ u) .zero)
  let l : _root_.Ix.Kernel.Expr .anon := .lam pe (.bvar 0) never
  let mut lam := l
  let mut e := l
  for _ in [0:n] do
    lam := .lam pe e never
    e := .app (.app lam pe) l
  return (lam, e)

/-- The hashes of the λ heads and of `E_1 … E_n` of `nestedChain p n`. -/
def nestedHashes (p n : Nat) : Array UInt64 × Array UInt64 := Id.run do
  let never : _root_.Ix.Kernel.BinderMeta := { pw := .never }
  let pe : _root_.Ix.Kernel.Expr .anon := .sort ((List.range p).foldl (fun u _ => .succ u) .zero)
  let l : _root_.Ix.Kernel.Expr .anon := .lam pe (.bvar 0) never
  let mut e := l
  let mut lams : Array UInt64 := #[]
  let mut es : Array UInt64 := #[]
  for _ in [0:n] do
    let lam : _root_.Ix.Kernel.Expr .anon := .lam pe e never
    e := .app (.app lam pe) l
    lams := lams.push lam.hash
    es := es.push e.hash
  return (lams, es)

/-! ## The depth limit (`Limits.maxDepth`) -/

/-- `step^n leaf`, written out (`shared = false`) or as a chain of sharing
entries appended to `tbl`, one per level (the codec then reads each level as a
leaf, and only the expanded depth sees the nesting). -/
def nest (shared : Bool) (n : Nat) (leaf : IE) (step : IE → IE) (tbl : Array IE) :
    IE × Array IE := Id.run do
  let mut t := tbl
  let mut cur := leaf
  for _ in [0:n] do
    if shared then
      t := t.push (step cur)
      cur := .share (t.size - 1).toUInt64
    else
      cur := step cur
  return (cur, t)

def defnS (lvls : UInt64) (ty val : IE) (sharing : Array IE) (refs : Array Address)
    (us : Array IU) : _root_.Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, lvls, ty, val⟩, sharing, refs, us⟩

def lamConst (shared : Bool) (n : Nat) : _root_.Ixon.Constant :=
  let (ty, t) := nest shared n (.sort 0) (_root_.Ixon.Expr.leanAll (.sort 0)) #[]
  let (val, t) := nest shared n (.var 0) (_root_.Ixon.Expr.leanLam (.sort 0)) t
  defnS 0 ty val t #[] univs01

/-- The robustness plan's shapes (`P` is `∀ p : Prop, p`), `n` steps each:
`lam` (`def F : ∀ (x : Prop)^n, Prop := λ (x : Prop)^n, x`), `pi`
(`def T : Type := ∀ (x : Prop)^n, Prop`), `appArg` (`g (g (… (g P)))`), `spine`
(`F P … P`), `let` (`let x1 : Prop := P; let x2 : Prop := x1; …`), `usucc`
(`def U : Sort (L+1) := Sort L`, `L = succ^n 0`), `umax` (`L = max u (max u (… u))`). -/
def shape (name : String) (shared : Bool) (n : Nat) : Option (List _root_.Ixon.Constant) :=
  match name with
  | "lam" => some [lamConst shared n]
  | "pi" =>
    let (val, t) := nest shared n (.sort 0) (_root_.Ixon.Expr.leanAll (.sort 0)) #[]
    some [defnS 0 (.sort 1) val t #[] univs01]
  | "appArg" =>
    let g := defnS 0 (_root_.Ixon.Expr.leanAll (.sort 0) (.sort 0))
      (_root_.Ixon.Expr.leanLam (.sort 0) (.var 0)) #[] #[] univs01
    let (val, t) := nest shared n P (fun b => .app (.ref 0 #[]) b) #[]
    some [g, defnS 0 (.sort 0) val t #[(record g).1] univs01]
  | "spine" =>
    let f := lamConst shared n
    let (val, t) := nest shared n (.ref 0 #[]) (fun b => .app b P) #[]
    some [f, defnS 0 (.sort 0) val t #[(record f).1] univs01]
  | "let" =>
    let (body, t) := nest shared (n - 1) (.var 0)
      (fun b => _root_.Ixon.Expr.leanLet false (.sort 0) (.var 0) b) #[]
    some [defnS 0 (.sort 0) (_root_.Ixon.Expr.leanLet false (.sort 0) P body) t #[] univs01]
  | "usucc" => Id.run do
    let mut l : IU := .zero
    for _ in [0:n] do l := .succ l
    return some [defnS 0 (.sort 1) (.sort 0) #[] #[] #[l, .succ l]]
  | "umax" => Id.run do
    let mut l : IU := .var 0
    for _ in [0:n] do l := .max (.var 0) l
    return some [defnS 1 (.sort 1) (.sort 0) #[] #[] #[l, .succ l]]
  | _ => none

/-- A shape of `n` steps is `n + shapeOffset` deep. -/
def shapeOffset : String → Nat
  | "lam" | "pi" | "let" => 1
  | _ => 2

/-- The depth the limit is about, computed independently of the kernel's
scan: the kernel's binary nesting with shares expanded, the root at 1. -/
partial def exprDepth (sharing : Array IE) : IE → Nat
  | .app f a => 1 + max (exprDepth sharing f) (exprDepth sharing a)
  | .lam _ t b | .all _ _ t b => 1 + max (exprDepth sharing t) (exprDepth sharing b)
  | .letE _ t v b => 1 + max (exprDepth sharing t) (max (exprDepth sharing v) (exprDepth sharing b))
  | .prj _ _ v => 1 + exprDepth sharing v
  | .share i => (sharing[i.toNat]?.map (exprDepth sharing)).getD 1
  | _ => 1

def univDepth : IU → Nat
  | .succ u => 1 + univDepth u
  | .max a b | .imax a b => 1 + max (univDepth a) (univDepth b)
  | _ => 1

def constDepth (c : _root_.Ixon.Constant) : Nat :=
  let payload := match c.info with
    | .defn d => max (exprDepth c.sharing d.typ) (exprDepth c.sharing d.value)
    | _ => 0
  max payload (max (c.sharing.foldl (fun m e => max m (exprDepth c.sharing e)) 0)
    (c.univs.foldl (fun m u => max m (univDepth u)) 0))

/-- `limit[MAX]-SHAPE-ENC d`: the shape `d` deep (`ENC` `flat` or `shared`)
through the certified entry under `maxDepth` `MAX` (the default if absent):
the measured depth, then the verdict. -/
def limitCase (binding : _root_.Ix.Kernel.Admission.Binding) (name : String) (d : Nat) :
    IO String := do
  let [pre, sh, enc] := name.splitOn "-" | throw (IO.userError s!"kernel-depth: bad case {name}")
  let maxDepth := ((toString (pre.drop 5)).toNat?).getD limits.maxDepth
  let some cs := shape sh (enc == "shared") (d - shapeOffset sh)
    | throw (IO.userError s!"kernel-depth: unknown shape {sh}")
  let measured := cs.foldl (fun m c => max m (constDepth c)) 0
  let rs := cs.map record
  let lim := { limits with maxDepth }
  timed do
    IO.lazyPure fun _ =>
      s!"depth {measured}, {entryVerdict (_root_.Ixon.Authenticated.checkBytes binding lim rs [] hint)}"

/-- How deep a record nests as stored (shares as leaves), computed independently of the scan. -/
partial def storedExprDepth : IE → Nat
  | .app f a => 1 + max (storedExprDepth f) (storedExprDepth a)
  | .lam _ t b | .all _ _ t b => 1 + max (storedExprDepth t) (storedExprDepth b)
  | .letE _ t v b => 1 + max (storedExprDepth t) (max (storedExprDepth v) (storedExprDepth b))
  | .prj _ _ v => 1 + storedExprDepth v
  | _ => 1

def storedConstDepth (c : _root_.Ixon.Constant) : Nat :=
  let payload := match c.info with
    | .defn d => max (storedExprDepth d.typ) (storedExprDepth d.value)
    | _ => 0
  max payload (max (c.sharing.foldl (fun m e => max m (storedExprDepth e)) 0)
    (c.univs.foldl (fun m u => max m (univDepth u)) 0))

/-- `bounds`: the two bounds the depth stages skip by (`Admission.storedDepthBound`: a record of
`s` bytes and `u` universe nodes nests at most `s + u + 1` deep as stored;
`Admission.expandedDepthBound`: at most `2 s + 2` with its shares expanded), checked against the
shapes that nest most per byte (each shape, written out and shared, at sizes up to 5,000, and a
spine of one-byte arguments). -/
def boundsCase : IO String := do
  let dense (shared : Bool) (n : Nat) : List _root_.Ixon.Constant :=
    let (val, t) := nest shared n (.ref 0 #[]) (fun b => .app b (.sort 0)) #[]
    [defnS 0 (.sort 0) val t #[] univs01]
  let mut checked := 0
  for sh in ["lam", "pi", "appArg", "spine", "let", "usucc", "umax", "dense"] do
    for shared in [false, true] do
      for n in [1, 2, 10, 100, 1000, 5000] do
        let cs := if sh == "dense" then dense shared n else (shape sh shared n).getD []
        for c in cs do
          let s := (_root_.Ixon.serConstant c).size
          let u := c.univs.foldl (fun acc v => acc + v.nodeCount) 0
          let stored := storedConstDepth c
          -- the expanded check measures expressions only (a universe has no shares: the scan's)
          let expanded := match c.info with
            | .defn d => max (max (exprDepth c.sharing d.typ) (exprDepth c.sharing d.value))
                (c.sharing.foldl (fun m e => max m (exprDepth c.sharing e)) 0)
            | _ => 0
          unless stored ≤ s + u + 1 && expanded ≤ 2 * s + 2 do
            return s!"bound broken: {sh} shared {shared} n {n}: stored {stored}, expanded {expanded}, \
              {s} bytes, {u} universe nodes"
          checked := checked + 1
  return s!"bounds hold on {checked} records"

/-! ## The depth stages against their first form and on hostile tables -/

/-- A deterministic generator (a linear congruential state). -/
abbrev G := StateM UInt64

def next : G Nat := modifyGet fun (s : UInt64) =>
  let s' : UInt64 := s * 6364136223846793005 + 1442695040888963407
  ((s' >>> 33).toNat, s')

def below (n : Nat) : G Nat := do
  let x ← next
  return if n == 0 then 0 else x % n

/-- An integer whose header takes one, two, three or more bytes. -/
def genInt : G UInt64 := do
  match ← below 8 with
  | 0 => return (← below 1100).toUInt64
  | 1 => return (← below 70000).toUInt64
  | 2 => return (2 ^ 40 + (← below 7)).toUInt64
  | _ => return (← below 8).toUInt64

def genUniv : Nat → G IU
  | 0 => return .zero
  | d + 1 => do
    match ← below 6 with
    | 0 => return .succ (← genUniv d)
    | 1 => return .max (← genUniv d) (← genUniv d)
    | 2 => return .imax (← genUniv d) (← genUniv d)
    | 3 => return .var (← genInt)
    | _ => return .zero

/-- An expression at most `d` constructors deep whose shares are below `bound` (none if `0`). -/
def genExpr (bound : Nat) : Nat → G IE
  | 0 => return .var (← genInt)
  | d + 1 => do
    match ← below 14 with
    | 0 => return .sort (← genInt)
    | 1 => if bound == 0 then return .var 0 else return .share (← below bound).toUInt64
    | 2 | 3 => do
      let args ← (List.range (1 + (← below 12))).mapM fun _ => genExpr bound d
      return args.foldl .app (← genExpr bound d)
    | 4 => return .lam .many (← genExpr bound d) (← genExpr bound d)
    | 5 => return .all .many .shared (← genExpr bound d) (← genExpr bound d)
    | 6 => return .letE (.lean true) (← genExpr bound d) (← genExpr bound d) (← genExpr bound d)
    | 7 => return .prj (← genInt) (← genInt) (← genExpr bound d)
    | 8 => return .ref (← genInt) #[← genInt, ← genInt]
    | 9 => return .recur (← genInt) #[]
    | 10 => return .str (← genInt)
    | 11 => return .nat (← genInt)
    | _ => return .var (← genInt)

/-- A definition with a sharing table whose entries refer only to earlier entries (half the
records) or to any entry or past the table (forward, self, cyclic, dangling), references and
universes. -/
def genConst : G _root_.Ixon.Constant := do
  let size ← below 7
  let ordered := (← below 2) == 0
  let mut sharing : Array IE := #[]
  for i in [0:size] do
    sharing := sharing.push (← genExpr (if ordered then i else size + 2) (1 + (← below 6)))
  let ty ← genExpr (size + (← below 2)) (← below 7)
  let val ← genExpr (size + (← below 2)) (← below 7)
  let refs := (List.range (← below 3)).toArray.map addrOf
  let us ← (List.range (← below 4)).mapM fun _ => do genUniv (← below 6)
  return defnS 0 ty val sharing refs us.toArray

def sameScan : Except _root_.Ix.Kernel.Admission.Depth.Stop Nat →
    Except _root_.Ix.Kernel.Admission.Depth.Stop Nat → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-- `differential n`: `n` generated records, each scanned by the kernel's scan and by its
first form (`Tests.Ix.Kernel.DepthRef`) at ten limits and, at two, with six bytes of it
mutated six ways (bits of each header field flipped, `0xFF`, plus one, cut short there); and
measured by the expanded check and by the general post-order (`expandedPost`) at the ten
limits. Any difference is a failure. -/
def differential (n : Nat) : String := Id.run do
  let (cs, _) := ((List.range n).mapM fun _ => genConst).run 0x6b692d6b
  let lims := [16384, 300, 64, 16, 8, 4, 3, 2, 1, 0]
  let mut scans := 0
  let mut exps := 0
  let mut muts := 0
  let mut post := 0
  let mut diffs : List String := []
  for c in cs do
    let b := _root_.Ixon.serConstant c
    for lim in lims do
      scans := scans + 1
      unless sameScan (_root_.Ix.Kernel.Admission.Depth.record lim b)
          (Tests.Ix.Kernel.DepthRef.record lim b) do
        diffs := s!"scan at {lim}: {b.size} bytes" :: diffs
      exps := exps + 1
      unless _root_.Ix.Kernel.Admission.Depth.expandedWithin lim (2 ^ 40) c ==
          _root_.Ix.Kernel.Admission.Depth.expandedPost lim (2 ^ 40) c do
        diffs := s!"expanded at {lim}: {b.size} bytes" :: diffs
    if (_root_.Ix.Kernel.Admission.Depth.expandedInOrder 16384 c).isNone then post := post + 1
    for q in [0:6] do
      let p := b.size * q / 6
      let x := b.get! p
      for v in [b.set! p (x ^^^ 0x08), b.set! p (x ^^^ 0x80), b.set! p (x ^^^ 0x20), b.set! p 0xFF,
          b.set! p (x + 1), b.extract 0 p] do
        for lim in [16384, 4] do
          muts := muts + 1
          unless sameScan (_root_.Ix.Kernel.Admission.Depth.record lim v)
              (Tests.Ix.Kernel.DepthRef.record lim v) do
            diffs := s!"mutated scan at {lim}: {v.size} bytes" :: diffs
  if diffs.isEmpty then
    return s!"no differences: {scans} scans, {exps} expanded checks ({post} records by the \
      post-order), {muts} scans of mutated bytes"
  return s!"differences ({diffs.length}): {diffs.take 5}"

/-- A spine of `n` arguments (`n + 1` deep). -/
def spineN (n : Nat) : IE := Id.run do
  let mut e : IE := .var 0
  for _ in [0:n] do e := .app e (.var 0)
  return e

/-- The expanded check alone on `c` under `limit` (the decoded record built directly, so
nothing else recurses): its answer, the path it took, its time. -/
def expandedTimed (c : _root_.Ixon.Constant) (limit : Nat) : IO String := do
  let t0 ← IO.monoNanosNow
  let ok ← IO.lazyPure fun _ => _root_.Ix.Kernel.Admission.Depth.expandedWithin limit (2 ^ 40) c
  let t1 ← IO.monoNanosNow
  let path := if (_root_.Ix.Kernel.Admission.Depth.expandedInOrder limit c).isSome then "in order"
    else "post-order"
  return s!"{if ok then "within" else "past"} ({path}) in {(t1 - t0) / 1000000} ms"

/-- The stage-time cases: `walk-spine n`, a spine of `n` arguments under the limit `n + 1`
(the walk, recursing once per level); `post-spine n`, the same spine behind a forward
reference (sharing entry 0 is `share 1`), measured by the post-order; `post-cycle n`, a
table whose two entries refer to each other, the spine inside one of them. -/
def stageCase (name : String) (n : Nat) : Option (IO String) :=
  let walk := (defnS 0 (.sort 0) (spineN n) #[] #[] univs01, n + 1)
  let post := (defnS 0 (.sort 0) (.share 0) #[.share 1, spineN n] #[] univs01, n + 1)
  let cycle := (defnS 0 (.sort 0) (.share 0) #[.app (spineN n) (.share 1), .share 0] #[] univs01, n + 2)
  -- `old-*`: the same records through the expanded check as it was before KI's change
  let old (c : _root_.Ixon.Constant × Nat) : IO String := do
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => Tests.Ix.Kernel.DepthRef.expandedWithinRef c.2 (2 ^ 40) c.1
    let t1 ← IO.monoNanosNow
    return s!"{if ok then "within" else "past"} (first form) in {(t1 - t0) / 1000000} ms"
  match name with
  | "walk-spine" => some (expandedTimed walk.1 walk.2)
  | "post-spine" => some (expandedTimed post.1 post.2)
  | "post-cycle" => some (expandedTimed cycle.1 cycle.2)
  | "old-walk-spine" => some (old walk)
  | "old-post-spine" => some (old post)
  | "old-post-cycle" => some (old cycle)
  | _ =>
    -- `frame-walk-SHAPE n`, `frame-decode-SHAPE n`: the walk alone, the codec alone, on the shape
    -- written out (to find the native stack each takes per level)
    match name.splitOn "-" with
    | ["frame", "walk", sh] => (shape sh false n).map fun cs => do
      let ok ← IO.lazyPure fun _ =>
        _root_.Ix.Kernel.Admission.Depth.expandedWithin (n + 10) (2 ^ 40) cs.getLast!
      return if ok then "within" else "past"
    | ["frame", "decode", sh] => (shape sh false n).map fun cs => do
      let b := _root_.Ixon.serConstant cs.getLast!
      let r ← IO.lazyPure fun _ => _root_.Ixon.Canonical.deConstant (1 <<< 28) (1 <<< 26) b
      return if r.isOk then "decoded" else "not decoded"
    | _ => none

/-- Run one case; the line it prints starts with the verdict. -/
def runOne (name : String) (n : Nat) : IO String := do
  if let some act := stageCase name n then return ← act
  if name == "differential" then return differential n
  let binding ← IO.ofExcept _root_.Ix.Kernel.Admission.defaultBinding
  match name with
  | "control" => return s!"returned {deep n}"
  | "delta" => timed do
    let rs := delta n
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs [] hint)
  | "delta-tiered" => timed do
    let rs := delta n
    IO.lazyPure fun _ =>
      match _root_.Ixon.Authenticated.checkBytesTiered binding limits rs [] hint with
      | .ok (env, _) => s!"accepted ({env.consts.length} constants)"
      | .error e => s!"refused: {(toString e).take 200}"
  | "iota" => timed do
    let table ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTable
    let (rs, blobs) ← IO.ofExcept (iota table n)
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs blobs hint)
  | "wide" => timed do
    let rs := wide n
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs [] hint)
  | "bounds" => boundsCase
  | "wide-w0" | "wide-w1" | "wide-w4" => timed do
    -- phase B on at most 0 (the calling thread), 1 or 4 tasks: the verdict of `wide`
    let w := ((toString (name.drop 6)).toNat?).getD 0
    let rs := wide n
    IO.lazyPure fun _ =>
      entryVerdict (_root_.Ixon.Authenticated.checkBytes binding { limits with workers := some w } rs [] hint)
  | "step" | "step-pool" => timed do
    let cfg : RunConfig := if name == "step" then {} else { workers := some 1 }
    let report ← runRecords (stepSource n) [] (fun _ => #[])
      ((Array.range (n + 1)).map addrOf) cfg
    let accepts := report.rows.filter (·.outcome == "accept") |>.size
    let last := (report.rows.back?.map (·.outcome)).getD "none"
    return s!"{accepts} accepted, last {last}, {report.rows.size} rows"
  | "nested0" | "nested3" => timed do
    -- KD's chain at `P = Sort 0` / `Sort 3`: head normalisation of `E_n` nests once per level
    let (_, e) := nestedChain (if name == "nested0" then 0 else 3) n
    let core := _root_.Ix.Kernel.Cached.coreKnotI .verified
      (_root_.Ix.Kernel.mkFEnv (⟨[]⟩ : _root_.Ix.Kernel.Env .anon)) _root_.Ix.Kernel.checkFuel
    IO.lazyPure fun _ => match StateT.run (core.whnfCore 0 e) {} with
      | .ok (.lam .., st) => s!"returned the λ, whnfCoreC {st.whnfCoreC.size}"
      | .ok _ => "returned another term"
      | .error err => let (o, reason) := checkOutcome err; s!"error {o}: {reason.take 120}"
  | "hash0" | "hash3" => do
    -- the hashes of `E_1 … E_n` and of their λ heads: the first repeat, if any
    let (lams, es) := nestedHashes (if name == "hash0" then 0 else 3) n
    let firstRepeat (hs : Array UInt64) : Option (Nat × Nat) := Id.run do
      let mut seen : Std.HashMap UInt64 Nat := {}
      for i in [0:hs.size] do
        if let some j := seen[hs[i]!]? then return some (j + 1, i + 1)
        seen := seen.insert hs[i]! i
      return none
    return match firstRepeat es, firstRepeat lams with
      | none, none => s!"no repeat in {n} levels"
      | re, rl => s!"repeat: E_k at {re}, λ heads at {rl}"
  | _ =>
    if name.startsWith "limit" then limitCase binding name n
    else throw (IO.userError s!"kernel-depth: unknown case {name}")

/-- `kernel-depth-case NAME N`: run the case on a dedicated thread of
`LEAN_STACK_SIZE_KB` and print one line, `NAME N: VERDICT`. -/
def runCase (args : List String) : IO UInt32 := do
  let some kb := (← IO.getEnv "LEAN_STACK_SIZE_KB").bind String.toNat?
    | IO.eprintln "kernel-depth-case: LEAN_STACK_SIZE_KB unset"; return 2
  let [name, nStr] := args | IO.eprintln "usage: kernel-depth-case NAME N"; return 2
  let some n := nStr.toNat? | IO.eprintln s!"kernel-depth-case: bad size {nStr}"; return 2
  _root_.Ix.Runtime.setLeanThreadStackSize (USize.ofNat (kb * 1024))
  let line ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) (runOne name n)))
  IO.println s!"{name} {n}: {line}"
  return 0

end Tests.Ix.Kernel.Depth
