/-
  Shared test utilities for kernel tests.
  - Address helpers (mkAddr)
  - Name parsing (parseIxName, leanNameToIx)
  - Env-building helpers (addInductive, addCtor, addAxiom)
  - Expect helpers (expectError, expectOk)
-/
import Ix.Kernel

open Ix.Kernel

namespace Tests.Ix.Kernel.Helpers

/-- Helper: make unique addresses from a seed byte. -/
def mkAddr (seed : UInt8) : Address :=
  Address.blake3 (ByteArray.mk #[seed, 0xAA, 0xBB])

/-- Parse a dotted name string like "Nat.add" into an Ix.Name.
    Handles `«...»` quoted name components (e.g. `Foo.«0».Bar`). -/
partial def parseIxName (s : String) : Ix.Name :=
  let parts := splitParts s.toList []
  parts.foldl (fun acc part =>
    match part with
    | .inl str => Ix.Name.mkStr acc str
    | .inr nat => Ix.Name.mkNat acc nat
  ) Ix.Name.mkAnon
where
  /-- Split a dotted name into parts: .inl for string components, .inr for numeric (guillemet). -/
  splitParts : List Char → List (String ⊕ Nat) → List (String ⊕ Nat)
    | [], acc => acc
    | '.' :: rest, acc => splitParts rest acc
    | '«' :: rest, acc =>
      let (inside, rest') := collectUntilClose rest ""
      let part := match inside.toNat? with
        | some n => .inr n
        | none => .inl inside
      splitParts rest' (acc ++ [part])
    | cs, acc =>
      let (word, rest) := collectUntilDot cs ""
      splitParts rest (if word.isEmpty then acc else acc ++ [.inl word])
  collectUntilClose : List Char → String → String × List Char
    | [], s => (s, [])
    | '»' :: rest, s => (s, rest)
    | c :: rest, s => collectUntilClose rest (s.push c)
  collectUntilDot : List Char → String → String × List Char
    | [], s => (s, [])
    | '.' :: rest, s => (s, '.' :: rest)
    | '«' :: rest, s => (s, '«' :: rest)
    | c :: rest, s => collectUntilDot rest (s.push c)

/-- Convert a Lean.Name to an Ix.Name (reproducing the Blake3 hashing). -/
partial def leanNameToIx : Lean.Name → Ix.Name
  | .anonymous => Ix.Name.mkAnon
  | .str pre s => Ix.Name.mkStr (leanNameToIx pre) s
  | .num pre n => Ix.Name.mkNat (leanNameToIx pre) n

/-- Build an inductive and insert it into the env. -/
def addInductive (env : Env .anon) (addr : Address)
    (type : Expr .anon) (ctors : Array Address)
    (numParams numIndices : Nat := 0) (isRec := false)
    (isUnsafe := false) (numNested := 0)
    (numLevels : Nat := 0) (all : Array Address := #[addr]) : Env .anon :=
  env.insert addr (.inductInfo {
    toConstantVal := { numLevels, type, name := (), levelParams := () },
    numParams, numIndices, all, ctors, numNested,
    isRec, isUnsafe, isReflexive := false
  })

/-- Build a constructor and insert it into the env. -/
def addCtor (env : Env .anon) (addr : Address) (induct : Address)
    (type : Expr .anon) (cidx numParams numFields : Nat)
    (isUnsafe := false) (numLevels : Nat := 0) : Env .anon :=
  env.insert addr (.ctorInfo {
    toConstantVal := { numLevels, type, name := (), levelParams := () },
    induct, cidx, numParams, numFields, isUnsafe
  })

/-- Build an axiom and insert it into the env. -/
def addAxiom (env : Env .anon) (addr : Address)
    (type : Expr .anon) (isUnsafe := false) (numLevels : Nat := 0) : Env .anon :=
  env.insert addr (.axiomInfo {
    toConstantVal := { numLevels, type, name := (), levelParams := () },
    isUnsafe
  })

/-- Build a recursor and insert it into the env. -/
def addRec (env : Env .anon) (addr : Address)
    (numLevels : Nat) (type : Expr .anon) (all : Array Address)
    (numParams numIndices numMotives numMinors : Nat)
    (rules : Array (RecursorRule .anon))
    (k := false) (isUnsafe := false) : Env .anon :=
  env.insert addr (.recInfo {
    toConstantVal := { numLevels, type, name := (), levelParams := () },
    all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe
  })

/-- Assert typecheckConst fails. Returns (passed_delta, failure_msg?). -/
def expectError (env : Env .anon) (prims : Primitives) (addr : Address)
    (label : String) : Bool × Option String :=
  match typecheckConst env prims addr with
  | .error _ => (true, none)
  | .ok () => (false, some s!"{label}: expected error")

/-- Assert typecheckConst succeeds. Returns (passed_delta, failure_msg?). -/
def expectOk (env : Env .anon) (prims : Primitives) (addr : Address)
    (label : String) : Bool × Option String :=
  match typecheckConst env prims addr with
  | .ok () => (true, none)
  | .error e => (false, some s!"{label}: unexpected error: {e}")

end Tests.Ix.Kernel.Helpers
