import Ix.Compiler.IxIR0.Eval

/-!
# Hand-written IxIR₀ environments

The test corpus until real inputs arrive. The standalone ix-importer
is **skipped** (JCB 2026-08-12): Ixon v2 merges into ix directly when
we're ready for real corpora; until then these hand-written
environments — built exactly as the erasure contract in `Basic.lean`
prescribes — exercise the semantics. Everything here is pure (no
FFI), so the tests are elaboration-time `#guard`s and run on every
build.

The encodings mirror what erasure produces from the kernel
declarations: `Nat.rec`/`List.rec` with motives dropped and minors
kept (`numArgs = 2`), constructors carrying kept fields only
(`List.cons` has arity 2 — the `α` param is gone), and rule
right-hand sides in the `RecRule` environment convention.
-/

namespace Ix.Compiler.IxIR0.Examples

open Ix.Compiler.Ixon (Uses Address)

private def addrOf (n : UInt8) : Address :=
  Address.replicate n

/-! ## Addresses (arbitrary — content addressing of IxIR₀ comes later) -/

def natZero := addrOf 0x10
def natSucc := addrOf 0x11
def natRec := addrOf 0x12
def natAddDef := addrOf 0x13
def listNil := addrOf 0x20
def listCons := addrOf 0x21
def listRec := addrOf 0x22
def appendDef := addrOf 0x23
def lengthDef := addrOf 0x24
def pairMk := addrOf 0x30
def natAddExt := addrOf 0x40
def dropFstDef := addrOf 0x50
def dropSndDef := addrOf 0x51

/-! ## Nat: zero/succ constructors, `Nat.rec`, addition -/

/-- Zero rule. Rule env is `[s, z, rec]`: no fields, pre-major args
`[z, s]` reversed, recursor deepest. `⊢ z`. -/
private def natRecZero : RecRule := { fields := 0, rhs := .var 1 }

/-- Succ rule. Rule env is `[n, s, z, rec]`. `⊢ s n (rec z s n)` —
the kernel rule with the motive dropped and `Nat.rec` mapped to the
deepest variable. -/
private def natRecSucc : RecRule where
  fields := 1
  rhs := .app (.app (.var 1) (.var 0))
    (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))

/-- `fun m n => Nat.rec (z := m) (s := fun _ ih => succ ih) n` -/
private def addBody : Expr :=
  .lam .many (.lam .many
    (.app
      (.app (.app (.ref natRec) (.var 1))
        (.lam .many (.lam .many (.app (.ref natSucc) (.var 0)))))
      (.var 0)))

/-! ## List: nil/cons, `List.rec`, append, length -/

/-- Nil rule. Rule env `[c, n, rec]`. `⊢ n`. -/
private def listRecNil : RecRule := { fields := 0, rhs := .var 1 }

/-- Cons rule. Rule env `[t, h, c, n, rec]` (fields `[h, t]`
reversed first). `⊢ c h t (rec n c t)`. -/
private def listRecCons : RecRule where
  fields := 2
  rhs := .app
    (.app (.app (.var 2) (.var 1)) (.var 0))
    (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 0))

/-- `fun xs ys => List.rec (n := ys) (c := fun h _ ih => cons h ih) xs` -/
private def appendBody : Expr :=
  .lam .many (.lam .many
    (.app
      (.app (.app (.ref listRec) (.var 0))
        (.lam .many (.lam .many (.lam .many
          (.app (.app (.ref listCons) (.var 2)) (.var 0))))))
      (.var 1)))

/-- `fun xs => List.rec (n := zero) (c := fun _ _ ih => succ ih) xs` -/
private def lengthBody : Expr :=
  .lam .many
    (.app
      (.app (.app (.ref listRec) (.ref natZero))
        (.lam .many (.lam .many (.lam .many
          (.app (.ref natSucc) (.var 0))))))
      (.var 0))

/-! ## Mixed-mode telescopes: affine and many binders in both orders.
Modes are inert in this IR's semantics; the IxIR₁ lowering reads its
per-parameter worlds off them, so the corpus must not be uniformly
`many` (a reversed mode telescope is invisible on uniform modes). -/

/-- `fun (x :ᵃ _) (y :ω _) => y` — drops its affine first argument. -/
private def dropFstBody : Expr := .lam .affine (.lam .many (.var 0))

/-- `fun (x :ω _) (y :ᵃ _) => x` — drops its affine second argument. -/
private def dropSndBody : Expr := .lam .many (.lam .affine (.var 1))

/-! ## The environment and oracle -/

/-- The declarations as a list — the IxIR₀ → IxIR₁ lowering consumes
this form (an `Env` function can't be enumerated). -/
def declList : List (Address × Decl) := [
  (natZero, .ctor 0 0),
  (natSucc, .ctor 1 1),
  (natRec, .recursor 2 true #[natRecZero, natRecSucc]),
  (natAddDef, .defn .shared addBody),
  (listNil, .ctor 0 0),
  (listCons, .ctor 1 2),
  (listRec, .recursor 2 false #[listRecNil, listRecCons]),
  (appendDef, .defn .shared appendBody),
  (lengthDef, .defn .shared lengthBody),
  (pairMk, .ctor 0 2),
  (dropFstDef, .defn .shared dropFstBody),
  (dropSndDef, .defn .shared dropSndBody),
  (natAddExt, .extern 2)
]

def env : Env := Env.ofList declList

/-- Demo ledger entry: `natAddExt` is `Nat.add` on literals (the
GMP-shaped extern), refusing anything else. -/
def oracle : Oracle := fun a args =>
  if a == natAddExt then
    match args with
    | [.lit (.nat m), .lit (.nat n)] => some (.lit (.nat (m + n)))
    | _ => none
  else none

def ctx : Ctx := { env, oracle }

/-! ## Expression and value helpers -/

/-- Church-style numeral over the `Nat` constructors. -/
def natE : Nat → Expr
  | 0 => .ref natZero
  | n + 1 => .app (.ref natSucc) (natE n)

def listE (f : α → Expr) : List α → Expr
  | [] => .ref listNil
  | x :: xs => .app (.app (.ref listCons) (f x)) (listE f xs)

/-- Read a `Nat` back out of a value, accepting literal tails so
`natLit`-peeled results (`succ (succ (lit 3))`) decode too. Fueled
only to keep the recursion structurally obvious. -/
private def valNatGo : Nat → Value → Option Nat
  | 0, _ => none
  | _, .lit (.nat n) => some n
  | _, .ctor _ 0 [] => some 0
  | fuel + 1, .ctor _ 1 [v] => (valNatGo fuel v).map (· + 1)
  | _, _ => none

def valNat? (v : Value) : Option Nat := valNatGo 1000000 v

private def valNatListGo : Nat → Value → Option (List Nat)
  | 0, _ => none
  | _, .ctor _ 0 [] => some []
  | fuel + 1, .ctor _ 1 [h, t] => do
    let n ← valNat? h
    let rest ← valNatListGo fuel t
    pure (n :: rest)
  | _, _ => none

def valNatList? (v : Value) : Option (List Nat) := valNatListGo 1000000 v

def run (e : Expr) (fuel : Nat := 100000) : Except Err Value :=
  eval ctx fuel [] e

def runNat? (e : Expr) : Option Nat :=
  match run e with
  | .ok v => valNat? v
  | .error _ => none

def runNatList? (e : Expr) : Option (List Nat) :=
  match run e with
  | .ok v => valNatList? v
  | .error _ => none

/-! ## β, let, projection -/

#guard runNat? (.app (.lam .many (.var 0)) (natE 4)) == some 4
#guard runNat? (.letE .many (natE 2) (.app (.ref natSucc) (.var 0))) == some 3
#guard runNat? (.proj 0 (.app (.app (.ref pairMk) (natE 1)) (natE 2))) == some 1
#guard runNat? (.proj 1 (.app (.app (.ref pairMk) (natE 1)) (natE 2))) == some 2

-- Under-applied constructors are first-class partial applications.
#guard
  match run (.app (.ref pairMk) (natE 1)) with
  | .ok (.pap _ [_]) => true
  | _ => false

/-! ## Mixed-mode telescopes evaluate as plain curried functions -/

#guard runNat? (.app (.app (.ref dropFstDef) (natE 1)) (natE 2)) == some 2
#guard runNat? (.app (.app (.ref dropSndDef) (natE 2)) (natE 1)) == some 2

/-! ## Recursor ι: addition via `Nat.rec`, on constructors and on
peeled literals -/

#guard runNat? (.app (.app (.ref natAddDef) (natE 2)) (natE 3)) == some 5
#guard runNat? (.app (.app (.ref natAddDef) (natE 0)) (natE 0)) == some 0
#guard runNat? (.app (.app (.ref natAddDef) (natE 7)) (natE 0)) == some 7
#guard runNat? (.app (.app (.ref natAddDef) (.lit (.nat 2))) (.lit (.nat 3)))
  == some 5
#guard runNat? (.app (.app (.ref natAddDef) (natE 1)) (.lit (.nat 3)))
  == some 4

/-! ## `List.rec`: append and length -/

#guard runNatList?
    (.app (.app (.ref appendDef) (listE natE [1, 2])) (listE natE [3]))
  == some [1, 2, 3]
#guard runNatList? (.app (.app (.ref appendDef) (listE natE [])) (listE natE []))
  == some []
#guard runNat? (.app (.ref lengthDef) (listE natE [5, 6, 7])) == some 3

/-! ## Externs and the oracle boundary -/

#guard runNat? (.app (.app (.ref natAddExt) (.lit (.nat 20))) (.lit (.nat 22)))
  == some 42

-- The oracle refuses constructor-form arguments: the ledger entry is
-- literals-only, and refusal is observable as `oracleMissing`.
#guard
  match run (.app (.app (.ref natAddExt) (natE 1)) (.lit (.nat 1))) with
  | .error (.oracleMissing _) => true
  | _ => false

/-! ## ◻ absorption -/

#guard
  match run (.app .erased (natE 1)) with
  | .ok .erased => true
  | _ => false
#guard
  match run (.proj 0 .erased) with
  | .ok .erased => true
  | _ => false

/-! ## Error taxonomy -/

#guard
  match run (.ref (addrOf 0xFF)) with
  | .error (.unknownRef _) => true
  | _ => false
#guard
  match run (.app (.lit (.nat 1)) (.lit (.nat 2))) with
  | .error (.stuck _) => true
  | _ => false
#guard
  match run (.proj 5 (.app (.app (.ref pairMk) (natE 1)) (natE 2))) with
  | .error (.stuck _) => true
  | _ => false

/-! ## Fuel: divergence and monotonicity -/

private def delta : Expr := .lam .many (.app (.var 0) (.var 0))

-- Ω runs out of any finite fuel — the untyped IR expresses divergence
-- even without fixpoints.
#guard
  match run (.app delta delta) with
  | .error .fuel => true
  | _ => false

-- The same term that succeeds above fails as `.fuel` (not `.stuck`)
-- when starved: fuel exhaustion is the only non-answer.
#guard
  match eval ctx 5 [] (.app (.app (.ref natAddDef) (natE 2)) (natE 3)) with
  | .error .fuel => true
  | _ => false

end Ix.Compiler.IxIR0.Examples
