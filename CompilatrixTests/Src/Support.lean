import Compilatrix.Src.Load

/-! Shared support for the Src and relevance suites: fixture loading, an
assertion counter, outcome rendering and a builder for synthetic programs. -/

namespace CompilatrixTests.Src

open Compilatrix Compilatrix.Src Compilatrix.Ixon
open Compilatrix.Sem (Result)

def fixtures : System.FilePath := "fixtures/ixon-v3"

/-- The K1 benchmark closures, with their `entry` arity and test arguments
from `benchmarks/fixtures/manifest.json`. -/
def benchNames : List String := ["fib", "sum-loop", "ackermann", "tak", "gcd"]

/-- Assertion counter; a failed assertion throws with its message. -/
abbrev Assert := IO.Ref Nat

def expect (a : Assert) (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)
  a.modify (· + 1)

def expectEq [BEq α] [ToString α] (a : Assert) (got expected : α) (msg : String) : IO Unit :=
  expect a (got == expected) s!"{msg}: got {got}, expected {expected}"

def timed (action : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← action
  return (r, (← IO.monoMsNow) - t0)

def outcome : Result Value → String
  | .ok v => s!"ok {v.shape}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource _ => "resource"

/-- Outcomes compared by observation (`readbackAll`), or by shape when
there is none. -/
def sameOutcome (p : Program) : Result Value → Result Value → Bool
  | .ok a, .ok b =>
    match readbackAll p a, readbackAll p b with
    | some x, some y => x == y
    | none, none => a.shape == b.shape
    | _, _ => false
  | .timeout, .timeout | .stuck, .stuck | .trap, .trap => true
  | .resource r, .resource s => r == s
  | _, _ => false

def natOf : Result Value → Option Nat
  | .ok (.lit n) => some n
  | _ => none

/-- Force the evaluation inside `IO` (so timings measure it). -/
def runRoot (p : Program) (k : Nat) (root : CId) (args : List Nat) : IO (Result Value) :=
  IO.lazyPure fun _ => run p k root (args.map .lit)

/-- Load a fixture pack. Erased typing of every K1 closure is gated by
`tests-ixon-v3`, so it is skipped here unless asked for. -/
def loadPack (ixe eqs : System.FilePath) (cfg : LoadConfig := { typecheck := false })
    (oracle : RelOracle := Relevance.annotate) : IO Loaded := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  match load bytes json cfg oracle with
  | .ok l => pure l
  | .error d => throw (IO.userError s!"{ixe}: {d}")

def loadBench (name : String) (cfg : LoadConfig := { typecheck := false })
    (oracle : RelOracle := Relevance.annotate) : IO Loaded :=
  loadPack (fixtures / "bench-k1" / s!"{name}.ixe") (fixtures / "bench-k1" / s!"{name}.equations.json")
    cfg oracle

def loadK1 (cfg : LoadConfig := { typecheck := false }) (oracle : RelOracle := Relevance.annotate) :
    IO Loaded :=
  loadPack (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json") cfg oracle

/-- Load `k1.ixe` with extra roots (constants run directly by a test must be
roots, so that the annotator and `Admit` reach them). -/
def loadK1Roots (extra : Array Address) (cfg : LoadConfig := { typecheck := false }) :
    IO Loaded := do
  let bytes ← IO.FS.readBinFile (fixtures / "k1/k1.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "k1/equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let hints := { hints with roots := hints.roots ++ extra.map (·, none) }
  match loadEnv cfg env hints with
  | .ok l => pure l
  | .error d => throw (IO.userError s!"k1.ixe with extra roots: {d}")

/-- The root recorded under an untrusted sidecar name. -/
def rootNamed (l : Loaded) (name : String) : IO CId := do
  match l.hints.roots.find? (·.2 == some name) with
  | some (a, _) =>
    match l.program.lookup a with
    | some c => pure c
    | none => throw (IO.userError s!"root {name} is not in the closure")
  | none => throw (IO.userError s!"no root named {name}")

/-! ## Synthetic programs -/

/-- A synthetic program under construction. Addresses are distinct fake
hashes; types are placeholders unless a rule reads them. -/
structure Builder where
  consts : Array ConstEntry := #[]
  resolve : Array (Option Resolve) := #[]
  recKind : Array (Option RecKind) := #[]
  lazy : Array (Option Nat) := #[]
  opaqueByValue : Array Bool := #[]
  known : Known := {}

namespace Builder

def fakeAddr (i : Nat) : Address :=
  Address.ofFn fun j => if j.val < 8 then UInt8.ofNat ((i >>> (8 * j.val)) % 256) else 0xab

def add (b : Builder) (decl : Decl) : Builder × CId :=
  let c := b.consts.size
  ({ b with consts := b.consts.push { ref := .member (fakeAddr c) 0, addr := fakeAddr c, decl }
            resolve := b.resolve.push none, recKind := b.recKind.push none
            lazy := b.lazy.push none, opaqueByValue := b.opaqueByValue.push false }, c)

def setDecl (b : Builder) (c : CId) (decl : Decl) : Builder :=
  { b with consts := b.consts.modify c fun e => { e with decl } }

def program (b : Builder) (roots : Array CId := #[]) : Program :=
  { consts := b.consts
    byAddr := b.consts.zipIdx.foldl (fun m (e, i) => m.insert e.addr i) {}
    table := { resolve := b.resolve, recKind := b.recKind, lazy := b.lazy
               inline := .replicate b.consts.size false, opaqueByValue := b.opaqueByValue }
    roots := roots.map fun c => (fakeAddr c, c)
    known := b.known }

end Builder

/-- Append a constant with a fresh fake address; with `root`, it becomes the
only root. -/
def pushConst (p : Program) (decl : Decl) (salt : Nat) (root : Bool := false) : Program × CId :=
  let c := p.size
  let a := Builder.fakeAddr (c + salt)
  let e : ConstEntry := { ref := .member a 0, addr := a, decl }
  let p := { p with consts := p.consts.push e, byAddr := p.byAddr.insert a c }
  (if root then { p with roots := #[(a, c)] } else p, c)

/-- Placeholder type. -/
def ty : Term := .sort (.succ .zero)

def app (f : Term) (args : List Term) (m : Mode := .strict) : Term :=
  args.foldl (fun t a => .app t a m) f

def appM (f : Term) (args : List (Term × Mode)) : Term :=
  args.foldl (fun t (a, m) => .app t a m) f

def lam (body : Term) (b : Binder := {}) : Term := .lam b ty body

def lams : Nat → Term → Term
  | 0, t => t
  | n + 1, t => lam (lams n t)

def irrArg : Term := .sort .zero

/-- Identifiers of the synthetic base program. -/
structure Base where
  nat : CId
  zero : CId
  succ : CId
  natRec : CId
  natCases : CId
  bool : CId
  btrue : CId
  bfalse : CId
  boolRec : CId
  boolCases : CId
  add : CId
  sub : CId
  beq : CId
  pair : CId
  pairMk : CId
  empty : CId
  emptyRec : CId
  isNat : CId
  isNatMk : CId
  isNatRec : CId
  quot : CId
  quotMk : CId
  quotLift : CId
  quotInd : CId

/-- Nat, Bool, a structure, an empty type, an index-carrying Prop family,
quotients and three primitives, with hand-written recursor rules. -/
def base : Builder × Base := Id.run do
  let mut b : Builder := {}
  let (b1, nat) := b.add (.induct true 0 0 0 ty #[])
  b := b1
  let (b1, zeroC) := b.add (.ctor true 0 nat 0 0 0 (.const nat []))
  b := b1
  let (b1, succ) := b.add (.ctor true 0 nat 1 0 1 (.pi {} {} (.const nat []) (.const nat [])))
  b := b1
  b := b.setDecl nat (.induct true 0 0 0 ty #[zeroC, succ])
  -- Nat.rec: motive, zero minor, succ minor, major.
  let natRecId := b.consts.size
  let rule0 : Rule := { ctor := zeroC, fields := 0, rhs := lams 3 (.var 1) }
  let ih := appM (.const natRecId [.var 0])
    [(.var 3, .irr), (.var 2, .byName), (.var 1, .byName), (.var 0, .strict)]
  let rhs1 := lams 4 (appM (.var 1) [(.var 0, .strict), (ih, .byName)])
  let rule1 : Rule := { ctor := succ, fields := 1, rhs := rhs1 }
  let (b1, natRec) := b.add (.recr true false 1 0 1 2 0 nat #[rule0, rule1] ty)
  b := { b1 with recKind := b1.recKind.set! natRec (some .ordinary) }
  let (b1, natCases) := b.add (.defn .defn .safe 1 ty (lams 4 (.natLit 0)))
  b := { b1 with resolve := b1.resolve.set! natCases (some (.case natRec)) }
  let (b1, bool) := b.add (.induct true 0 0 0 ty #[])
  b := b1
  let (b1, bfalse) := b.add (.ctor true 0 bool 0 0 0 (.const bool []))
  b := b1
  let (b1, btrue) := b.add (.ctor true 0 bool 1 0 0 (.const bool []))
  b := b1
  b := b.setDecl bool (.induct true 0 0 0 ty #[bfalse, btrue])
  let (b1, boolRec) := b.add (.recr true false 1 0 1 2 0 bool
    #[{ ctor := bfalse, fields := 0, rhs := lams 3 (.var 1) },
      { ctor := btrue, fields := 0, rhs := lams 3 (.var 0) }] ty)
  b := { b1 with recKind := b1.recKind.set! boolRec (some .ordinary) }
  let (b1, boolCases) := b.add (.defn .defn .safe 1 ty (lams 4 (.natLit 0)))
  b := { b1 with resolve := b1.resolve.set! boolCases (some (.case boolRec)) }
  let (b1, add) := b.add (.defn .defn .safe 0 ty (lams 2 (.natLit 0)))
  b := { b1 with resolve := b1.resolve.set! add (some (.prim .add)) }
  let (b1, sub) := b.add (.defn .defn .safe 0 ty (lams 2 (.natLit 0)))
  b := { b1 with resolve := b1.resolve.set! sub (some (.prim .sub)) }
  let (b1, beq) := b.add (.defn .defn .safe 0 ty (lams 2 (.natLit 0)))
  b := { b1 with resolve := b1.resolve.set! beq (some (.prim .beq)) }
  let (b1, pair) := b.add (.induct true 0 0 0 ty #[])
  b := b1
  let (b1, pairMk) := b.add (.ctor true 0 pair 0 0 2 ty)
  b := b1
  b := b.setDecl pair (.induct true 0 0 0 ty #[pairMk])
  let (b1, empty) := b.add (.induct true 0 0 0 ty #[])
  b := b1
  let (b1, emptyRec) := b.add (.recr true false 1 0 1 0 0 empty #[] ty)
  b := { b1 with recKind := b1.recKind.set! emptyRec (some .empty) }
  -- IsNat : Nat → Prop with `mk (n : Nat) : IsNat n`: the field is index 0.
  let (b1, isNat) := b.add (.induct true 0 0 1 ty #[])
  b := b1
  let (b1, isNatMk) := b.add (.ctor true 0 isNat 0 0 1 ty)
  b := b1
  b := b.setDecl isNat (.induct true 0 0 1 ty #[isNatMk])
  let (b1, isNatRec) := b.add (.recr true false 1 0 1 1 1 isNat
    #[{ ctor := isNatMk, fields := 1, rhs := lams 3 (appM (.var 1) [(.var 0, .strict)]) }] ty)
  b := { b1 with recKind := b1.recKind.set! isNatRec (some (.subsingleton #[.index 0])) }
  let (b1, quot) := b.add (.quot .type 1 ty)
  b := b1
  let (b1, quotMk) := b.add (.quot .ctor 1 ty)
  b := b1
  let (b1, quotLift) := b.add (.quot .lift 2 ty)
  b := b1
  let (b1, quotInd) := b.add (.quot .ind 1 ty)
  b := b1
  b := { b with known := { nat := some nat, natZero := some zeroC, natSucc := some succ,
                            natRec := some natRec, bool := some bool, boolTrue := some btrue,
                            boolFalse := some bfalse } }
  return (b, { nat, zero := zeroC, succ, natRec, natCases, bool, btrue, bfalse, boolRec, boolCases, add, sub,
               beq, pair, pairMk, empty, emptyRec, isNat, isNatMk, isNatRec, quot, quotMk,
               quotLift, quotInd })

end CompilatrixTests.Src
