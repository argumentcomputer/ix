/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.ConLecheAdmission

/-! # Ixon records through con-leche's verified checker (plan v4, L4)

End-to-end fixtures for `Ix.Ixon.ConLecheAdmission.checkBytes`: canonical
record bytes are preflighted, decoded, read by `Ix.Kernel.ConLecheReader`,
prepared with the Ixon prelude (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, the
quotient package, `And`, `Bool`, from the compiled Init's own records) and
checked by `Ix.Kernel.Cached.checkDecls .verified`.

Positive: a definition and a definition over it with a theorem by delta, a
definition block stored out of dependency order with a theorem by delta
through both members, an
inductive with its separately stored recursor and an ι-reduction, a
structure with a projection function and a projection reduction, the
quotient's lift reduction, a Nat literal against its constructors, a String
literal against its `String.ofList` expansion (over test constants pinned as
the string-literal support), a compiled block nested through a container
that is itself nested, whose auxiliary motives Ix's compiler orders with the
container family's instance before its head (cl-m1), and a compiled theorem
whose universe levels Ix's compiler stored in canonical form, which only the
Géran fallback of con-leche's level comparison equates (cl-m1, cl-level, the
`RatFunc.liftOn_def` shape).

Negative: a block of another shape stored under the real `Eq`'s address is
named `Eq` and rejected by con-leche's reserved-name check; a definition
block with an ill-typed member is rejected by the checker; a `partial` block
whose members call each other (the shape of Lean's `_unsafe_rec` companions)
declines with its safety, as a partial singleton does, and the same block
marked safe declines as mutually recursive; a definition of
the wrong shape pinned as `Nat.add` is not accepted under that name (and is
accepted unpinned); a copy of `Nat`'s contents at another address is not
named `Nat`; malformed tables, duplicate records (byte stage and reader)
and unsafe declarations;
`pinMap`'s refusals. -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader
open Ix.Ixon.ConLecheAdmission

namespace Tests.Ix.Kernel.ConLecheReader

/-! ## Fixture builders -/

def address (tag : UInt8) : Address := ⟨⟨Array.replicate 32 tag⟩⟩

abbrev E := Ixon.Expr

def all (t b : E) : E := .leanAll t b
def lam (t b : E) : E := .leanLam t b
def apps (f : E) (as : List E) : E := as.foldl .app f
def ref (i : Nat) (us : List Nat := []) : E := .ref i.toUInt64 (us.toArray.map (·.toUInt64))
def recur (i : Nat) (us : List Nat := []) : E := .recur i.toUInt64 (us.toArray.map (·.toUInt64))
def var (i : Nat) : E := .var i.toUInt64
def sort (i : Nat) : E := .sort i.toUInt64

def one : Ixon.Univ := .succ .zero

def const (info : Ixon.ConstantInfo) (refs : List Address) (univs : List Ixon.Univ) : Ixon.Constant :=
  ⟨info, #[], refs.toArray, univs.toArray⟩

def defn (kind : Ix.DefKind) (typ value : E) (refs : List Address) (univs : List Ixon.Univ := [])
    (lvls : Nat := 0) (safety : Ix.DefinitionSafety := .safe) : Ixon.Constant :=
  const (.defn ⟨kind, safety, lvls.toUInt64, typ, value⟩) refs univs

def iPrj (block : Address) (i : Nat := 0) : Ixon.Constant := const (.iPrj ⟨i.toUInt64, block⟩) [] []
def cPrj (block : Address) (c : Nat) (i : Nat := 0) : Ixon.Constant :=
  const (.cPrj ⟨i.toUInt64, c.toUInt64, block⟩) [] []

def limits : Ix.Ixon.Admission.Limits := ⟨1024, 1024, 1 <<< 24, 1 <<< 20, 1 <<< 16⟩

def encode (cs : List (Address × Ixon.Constant)) : Ix.Ixon.Admission.Records :=
  cs.map fun (a, c) => (a, Ixon.serConstant c)

def builtinPins : Pins := match defaultPins with | .ok p => p | .error _ => {}
def builtinPre : Prelude := match builtinPrelude with | .ok p => p | .error _ => default
def builtinNatPins : List Ix.Kernel.NatOpPinSet := match builtinNatOpPins with | .ok ps => ps | .error _ => []

def run (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (pins : Pins := builtinPins) : Except Error Ix.Kernel.Env :=
  checkBytesWith pins builtinPre builtinNatPins limits (encode cs) blobs

def accepts (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (pins : Pins := builtinPins) : Bool :=
  (run cs blobs pins).isOk

def namesOf (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (pins : Pins := builtinPins) : List String :=
  match run cs blobs pins with
  | .ok env => env.consts.map (toString ·.name)
  | .error _ => []

def keyString (r : ConstRef Address) : String := toString (keyName r)

/-- The prelude record that denotes a pinned name. -/
def pinned (n : String) : Address := Id.run do
  let some (r, _) := builtinPins.names.toList.find? (toString ·.2 == n) | return address 0
  let store := storeOf builtinPre.records
  let some (a, _) := builtinPre.records.find? (fun (a, c) => resolveSource store a c == some r)
    | return address 0
  return a

def eq := pinned "Eq"
def eqRefl := pinned "Eq.refl"
def nat := pinned "Nat"
def natZero := pinned "Nat.zero"
def natSucc := pinned "Nat.succ"
def quotMk := pinned "Quot.mk"
def quotLift := pinned "Quot.lift"

/-! ## The prelude and the tables -/

#guard defaultPins.isOk && builtinPrelude.isOk && builtinNatOpPins.isOk
-- the committed Nat-operation pin variant, generated from Ixon records: one
-- variant, eight operations, the certificate proofs of their pinned statements
#guard builtinNatPins.length == 1 && builtinNatPins.all fun ps =>
  ps.divProofs.length == 3 && ps.modProofs.length == 3 && ps.gcdProofs.length == 2 &&
  ps.landProofs.length == 2 && ps.lorProofs.length == 2 && ps.xorProofs.length == 2 &&
  ps.shiftLeftProofs.length == 2 && ps.shiftRightProofs.length == 2
-- the share-table decoder refuses forward references and unknown nodes
#guard (decodePinTable "A 2 3").isOk == false && (decodePinTable "Q 0").isOk == false
#guard match decodePinTable "n 0 Nat\nn 2 succ\nC 3\nT a%20b" with
  | .ok ns => match (ns[4]? : Option PinNode), (ns[5]? : Option PinNode) with
    | some (.expr (.const n [])), some (.expr (.lit (.strVal s))) => toString n == "Nat.succ" && s == "a b"
    | _, _ => false
  | .error _ => false
#guard builtinPins.names.size == 55
#guard (builtinPre.ix.decls.toList.map (toString ∘ Ix.Kernel.Frontend.preludeKey)) ==
  ["Eq", "Nat", "PUnit", "Empty", "False", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound",
   "And", "Bool"]
#guard [eq, eqRefl, nat, natZero, natSucc, quotMk, quotLift].all (· != address 0)
-- the empty stream: the prelude alone
#guard (namesOf []).length == 27 && (namesOf []).contains "Eq.rec" && (namesOf []).contains "Bool.true"

/-! ## A definition, and one over it -/

def idNat : Ixon.Constant := defn .defn (all (ref 0) (ref 0)) (lam (ref 0) (var 0)) [nat]
def twoDef : Ixon.Constant :=
  defn .defn (ref 0) (.app (ref 1) (.app (ref 2) (.app (ref 2) (ref 3)))) [nat, address 10, natSucc, natZero]
/-- `two = Nat.succ (Nat.succ Nat.zero)`, by delta through `two` and `idNat`. -/
def twoEq : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [ref 1, ref 2, .app (ref 3) (.app (ref 3) (ref 4))])
    (apps (ref 5 [0]) [ref 1, .app (ref 3) (.app (ref 3) (ref 4))])
    [eq, nat, address 11, natSucc, natZero, eqRefl] [one]

def definitions : List (Address × Ixon.Constant) :=
  [(address 10, idNat), (address 11, twoDef), (address 12, twoEq)]

#guard accepts definitions
#guard (namesOf definitions).contains (keyString (.member (address 10) 0))
#guard (namesOf definitions).contains (keyString (.member (address 12) 0))
-- a false equation is not
#guard !accepts [(address 10, idNat), (address 11, twoDef),
  (address 12, defn .thm (apps (ref 0 [0]) [ref 1, ref 2, ref 4]) (apps (ref 5 [0]) [ref 1, ref 4])
    [eq, nat, address 11, natSucc, natZero, eqRefl] [one])]

/-! ## Definition blocks

A definition `muts` block is one `defnDecl` per member, each checked against
the environment that holds what it names, in an order where every member
follows the members it names by `recur`. Here the block stores
`b : Nat := a zero` before `a : Nat → Nat := fun n => n`: the reader puts
`a` first, and `b = zero` checks by delta through both. -/

def dPrj (block : Address) (i : Nat) : Ixon.Constant := const (.dPrj ⟨i.toUInt64, block⟩) [] []

def member (typ value : E) (safety : Ix.DefinitionSafety := .safe) : Ixon.MutConst :=
  .defn ⟨.defn, safety, 0, typ, value⟩

def natToNat : E := all (ref 0) (ref 0)

/-- `[b := a zero, a := fun n => n]`, refs `[Nat, Nat.zero]`. -/
def abBlock (aValue : E := lam (ref 0) (var 0)) : Ixon.Constant :=
  const (.muts #[member (ref 0) (.app (recur 1) (ref 1)), member natToNat aValue]) [nat, natZero] []

/-- `b = Nat.zero`, by delta through `b` and `a`. -/
def bEq : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [ref 1, ref 2, ref 3]) (apps (ref 4 [0]) [ref 1, ref 3])
    [eq, nat, address 101, natZero, eqRefl] [one]

def abFixture (block : Ixon.Constant := abBlock) : List (Address × Ixon.Constant) :=
  [(address 100, block), (address 101, dPrj (address 100) 0), (address 102, dPrj (address 100) 1),
   (address 103, bEq)]

#guard (recurDeps abBlock ⟨.defn, .safe, 0, ref 0, .app (recur 1) (ref 1)⟩).toList == [1]
#guard defOrder #[Std.HashSet.ofList [1], {}] == some #[1, 0]
#guard defOrder #[Std.HashSet.ofList [0], {}] == some #[0, 1]
#guard defOrder #[Std.HashSet.ofList [1], Std.HashSet.ofList [0]] == none
#guard accepts abFixture
#guard (namesOf abFixture).contains (keyString (.member (address 100) 0)) &&
  (namesOf abFixture).contains (keyString (.member (address 100) 1))
-- `b = succ zero` is not
#guard !accepts ((abFixture.take 3) ++ [(address 103,
  defn .thm (apps (ref 0 [0]) [ref 1, ref 2, .app (ref 5) (ref 3)]) (apps (ref 4 [0]) [ref 1, ref 3])
    [eq, nat, address 101, natZero, eqRefl, natSucc] [one])])
-- every member is checked: `a := fun n => Nat` is ill-typed, and the checker rejects it
#guard match run (abFixture (abBlock (lam (ref 0) (ref 0)))) with
  | .error (.kernel _ _) => true
  | _ => false

/-- `f := fun n => g n`, `g := fun n => f n` at a safety: the shape of the
compiler's `_unsafe_rec` companions when `partial`
(`addAndCompilePartialRec` adds one block per mutual group, its members
calling each other). -/
def fgBlock (safety : Ix.DefinitionSafety) : Ixon.Constant :=
  const (.muts #[member natToNat (lam (ref 0) (.app (recur 1) (var 0))) safety,
    member natToNat (lam (ref 0) (.app (recur 0) (var 0))) safety]) [nat] []

def declineReason (cs : List (Address × Ixon.Constant)) : Option String :=
  match run cs with
  | .error (.read _ (.declined r)) => some r
  | _ => none

-- the partial block declines with its safety, as a partial singleton does
#guard declineReason [(address 110, fgBlock .part)] == some "definition with safety 'partial'"
#guard declineReason [(address 110, fgBlock .part)] ==
  declineReason [(address 10, defn .defn natToNat (lam (ref 0) (var 0)) [nat] (safety := .part))]
#guard declineReason [(address 110, fgBlock .unsaf)] == some "definition with safety 'unsafe'"
-- the same block marked safe has no order (Lean's kernel refuses it too)
#guard declineReason [(address 110, fgBlock .safe)] == some "mutually recursive definition block"
-- a member that is not safe declines the block whatever the others are
#guard declineReason [(address 111, const (.muts #[member (ref 0) (ref 1),
  member (ref 0) (ref 1) .part]) [nat, natZero] [])] == some "definition with safety 'partial'"

/-! ## An inductive with its separately stored recursor

`inductive Two | a | b` and `Two.rec.{u}`, as the compiler lays them out: the
block, its projection records, the recursor as its own record. -/

def twoBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0,
    #[⟨false, 0, 0, 0, 0, recur 0⟩, ⟨false, 0, 1, 0, 0, recur 0⟩]⟩]) [] [one]

def twoMotive : E := all (ref 0) (sort 0)
def twoRec : Ixon.Constant :=
  let typ := all twoMotive (all (.app (var 0) (ref 1)) (all (.app (var 1) (ref 2))
    (all (ref 0) (.app (var 3) (var 0)))))
  let pre (body : E) : E := lam twoMotive (lam (.app (var 0) (ref 1)) (lam (.app (var 1) (ref 2)) body))
  const (.recr ⟨false, false, 1, 0, 0, 1, 2, typ, #[⟨0, pre (var 1)⟩, ⟨0, pre (var 0)⟩]⟩)
    [address 21, address 22, address 23] [.var 0]

/-- `Two.rec (motive := fun _ => Nat) zero (succ zero) Two.b = succ zero`, by ι. -/
def twoIota : Ixon.Constant :=
  let sz := Ixon.Expr.app (ref 4) (ref 3)
  defn .thm
    (apps (ref 0 [0]) [ref 1, apps (ref 2 [0]) [lam (ref 6) (ref 1), ref 3, sz, ref 5], sz])
    (apps (ref 7 [0]) [ref 1, sz])
    [eq, nat, address 24, natZero, natSucc, address 23, address 21, eqRefl] [one]

def twoFixture : List (Address × Ixon.Constant) :=
  [(address 20, twoBlock), (address 21, iPrj (address 20)), (address 22, cPrj (address 20) 0),
   (address 23, cPrj (address 20) 1), (address 24, twoRec), (address 25, twoIota)]

#guard accepts twoFixture
#guard (namesOf twoFixture).contains (keyString (.member (address 20) 0) ++ ".rec")
#guard (namesOf twoFixture).contains (keyString (.ctor (address 20) 0 1))
-- the recursor record may come before its block
#guard accepts [(address 24, twoRec), (address 20, twoBlock), (address 21, iPrj (address 20)),
  (address 22, cPrj (address 20) 0), (address 23, cPrj (address 20) 1), (address 25, twoIota)]
-- the wrong branch is not the ι-reduct
#guard !accepts (twoFixture.take 5 ++ [(address 25,
  let sz := Ixon.Expr.app (ref 4) (ref 3)
  defn .thm
    (apps (ref 0 [0]) [ref 1, apps (ref 2 [0]) [lam (ref 6) (ref 1), ref 3, sz, ref 5], ref 3])
    (apps (ref 7 [0]) [ref 1, ref 3])
    [eq, nat, address 24, natZero, natSucc, address 23, address 21, eqRefl] [one])])
-- a block without its recursor declines at the reader
#guard match run (twoFixture.take 4) with
  | .error (.read _ (.declined _)) => true
  | _ => false

/-! ## A structure with a projection function

`structure P where x : Nat; y : Nat`, `P.x := fun self => self.1` (an Ixon
`prj`), and `P.x (P.mk zero (succ zero)) = zero` by the projection's
reduction. -/

def pBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0,
    #[⟨false, 0, 0, 0, 2, all (ref 0) (all (ref 0) (recur 0))⟩]⟩]) [nat] [one]

def pMotive : E := all (ref 0) (sort 0)
def pMinor : E := all (ref 1) (all (ref 1) (.app (var 2) (apps (ref 2) [var 1, var 0])))
def pRec : Ixon.Constant :=
  let typ := all pMotive (all pMinor (all (ref 0) (.app (var 2) (var 0))))
  let rhs := lam pMotive (lam pMinor (lam (ref 1) (lam (ref 1) (apps (var 2) [var 1, var 0]))))
  const (.recr ⟨false, false, 1, 0, 0, 1, 1, typ, #[⟨2, rhs⟩]⟩) [address 31, nat, address 32] [.var 0]

def pX : Ixon.Constant := defn .defn (all (ref 0) (ref 1)) (lam (ref 0) (.prj 0 0 (var 0))) [address 31, nat]

def pIota : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [ref 1, .app (ref 2) (apps (ref 3) [ref 4, .app (ref 5) (ref 4)]), ref 4])
    (apps (ref 6 [0]) [ref 1, ref 4])
    [eq, nat, address 34, address 32, natZero, natSucc, eqRefl] [one]

def pFixture : List (Address × Ixon.Constant) :=
  [(address 30, pBlock), (address 31, iPrj (address 30)), (address 32, cPrj (address 30) 0),
   (address 33, pRec), (address 34, pX), (address 35, pIota)]

#guard accepts pFixture
-- the second field is not the first
#guard !accepts (pFixture.take 5 ++ [(address 35,
  defn .thm (apps (ref 0 [0]) [ref 1, .app (ref 2) (apps (ref 3) [ref 4, .app (ref 5) (ref 4)]),
    .app (ref 5) (ref 4)])
    (apps (ref 6 [0]) [ref 1, .app (ref 5) (ref 4)])
    [eq, nat, address 34, address 32, natZero, natSucc, eqRefl] [one])])

/-! ## The quotient

`∀ h, Quot.lift (fun n => n) h (Quot.mk Eq zero) = zero`, over the prelude's
pinned quotient package. -/

def eqNat : E := .app (ref 0 [0]) (ref 1)
def quotIota : Ixon.Constant :=
  let hTy := all (ref 1) (all (ref 1) (all (apps eqNat [var 1, var 0]) (apps eqNat [var 2, var 1])))
  let lifted := apps (ref 2 [0, 0])
    [ref 1, eqNat, ref 1, lam (ref 1) (var 0), var 0, apps (ref 3 [0]) [ref 1, eqNat, ref 4]]
  defn .thm (all hTy (apps eqNat [lifted, ref 4])) (lam hTy (apps (ref 5 [0]) [ref 1, ref 4]))
    [eq, nat, quotLift, quotMk, natZero, eqRefl] [one]

#guard accepts [(address 40, quotIota)]

/-! ## A Nat literal -/

def litEq : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [ref 1, .nat 2, .app (ref 3) (.app (ref 3) (ref 4))])
    (apps (ref 5 [0]) [ref 1, .nat 2]) [eq, nat, address 41, natSucc, natZero, eqRefl] [one]

#guard accepts [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]
#guard !accepts [(address 42, litEq)] [(address 41, ⟨#[3]⟩)]
-- a literal blob that is not supplied is malformed
#guard match run [(address 42, litEq)] with
  | .error (.read _ (.malformed _)) => true
  | _ => false

/-! ## A String literal

Test constants with the string-literal support's exact types — `List` with
its recursor, `Char` and `String` one-constructor types with theirs,
`Char.ofNat` and `String.ofList` definitions — pinned under those names in
place of the committed table's Init entries. Then `"ab"` is its
`String.ofList [Char.ofNat 97, Char.ofNat 98]` expansion. -/

def listBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 1, 1, 0, all (sort 0) (sort 0),
    #[⟨false, 1, 0, 1, 0, all (sort 0) (.app (recur 0 [1]) (var 0))⟩,
      ⟨false, 1, 1, 1, 2, all (sort 0) (all (var 0) (all (.app (recur 0 [1]) (var 1))
        (.app (recur 0 [1]) (var 2))))⟩]⟩]) [] [.succ (.var 0), .var 0]

/-- `List.rec.{u_1, u}`: universe table `[Type u, u_1, u]`, refs `[List, nil, cons]`. -/
def listMotive : E := all (.app (ref 0 [2]) (var 0)) (sort 1)
def listNil : E := .app (var 0) (.app (ref 1 [2]) (var 1))
def listCons : E := all (var 2) (all (.app (ref 0 [2]) (var 3)) (all (.app (var 3) (var 0))
  (.app (var 4) (apps (ref 2 [2]) [var 5, var 2, var 1]))))
def listRec : Ixon.Constant :=
  let typ := all (sort 0) (all listMotive (all listNil (all listCons
    (all (.app (ref 0 [2]) (var 3)) (.app (var 3) (var 0))))))
  let pre (body : E) : E := lam (sort 0) (lam listMotive (lam listNil (lam listCons body)))
  let consRhs := pre (lam (var 3) (lam (.app (ref 0 [2]) (var 4))
    (apps (var 2) [var 1, var 0, apps (recur 0 [1, 2]) [var 5, var 4, var 3, var 2, var 0]])))
  const (.recr ⟨false, false, 2, 1, 0, 1, 2, typ, #[⟨0, pre (var 1)⟩, ⟨2, consRhs⟩]⟩)
    [address 51, address 52, address 53] [.succ (.var 1), .var 0, .var 1]

def unitBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0, #[⟨false, 0, 0, 0, 0, recur 0⟩]⟩]) [] [one]

/-- The recursor of a one-constructor, no-field type at `refs = [T, mk]`. -/
def unitRec (t mk : Address) : Ixon.Constant :=
  let motive := all (ref 0) (sort 0)
  let typ := all motive (all (.app (var 0) (ref 1)) (all (ref 0) (.app (var 2) (var 0))))
  const (.recr ⟨false, false, 1, 0, 0, 1, 1, typ,
    #[⟨0, lam motive (lam (.app (var 0) (ref 1)) (var 0))⟩]⟩) [t, mk] [.var 0]

def charOfNat : Ixon.Constant :=
  defn .defn (all (ref 0) (ref 1)) (lam (ref 0) (ref 2)) [nat, address 61, address 62]

/-- `String : Type`, `String.mk : List.{0} Char → String`. -/
def stringBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0,
    #[⟨false, 0, 0, 0, 1, all (.app (ref 0 [1]) (ref 1)) (recur 0)⟩]⟩])
    [address 51, address 61] [one, .zero]

def stringRec : Ixon.Constant :=
  let motive := all (ref 0) (sort 0)
  let minor := all (.app (ref 1 [1]) (ref 2)) (.app (var 1) (.app (ref 3) (var 0)))
  let typ := all motive (all minor (all (ref 0) (.app (var 2) (var 0))))
  let rhs := lam motive (lam minor (lam (.app (ref 1 [1]) (ref 2)) (.app (var 1) (var 0))))
  const (.recr ⟨false, false, 1, 0, 0, 1, 1, typ, #[⟨1, rhs⟩]⟩)
    [address 71, address 51, address 61, address 72] [.var 0, .zero]

def stringOfList : Ixon.Constant :=
  defn .defn (all (.app (ref 0 [0]) (ref 1)) (ref 2)) (lam (.app (ref 0 [0]) (ref 1)) (.app (ref 3) (var 0)))
    [address 51, address 61, address 71, address 72] [.zero]

/-- `"ab" = String.ofList [Char.ofNat 97, Char.ofNat 98]`. -/
def strEq : Ixon.Constant :=
  let ch (blob : Nat) : E := .app (ref 6) (.nat blob.toUInt64)
  let list := apps (ref 4 [1]) [ref 5, ch 7, apps (ref 4 [1]) [ref 5, ch 8, .app (ref 9 [1]) (ref 5)]]
  defn .thm (apps (ref 0 [0]) [ref 1, .str 2, .app (ref 3) list]) (apps (ref 10 [0]) [ref 1, .str 2])
    [eq, address 71, address 80, address 74, address 53, address 61, address 64, address 81, address 82,
     address 52, eqRefl] [one, .zero]

def strings : List (Address × Ixon.Constant) :=
  [(address 50, listBlock), (address 51, iPrj (address 50)), (address 52, cPrj (address 50) 0),
   (address 53, cPrj (address 50) 1), (address 54, listRec),
   (address 60, unitBlock), (address 61, iPrj (address 60)), (address 62, cPrj (address 60) 0),
   (address 63, unitRec (address 61) (address 62)), (address 64, charOfNat),
   (address 70, stringBlock), (address 71, iPrj (address 70)), (address 72, cPrj (address 70) 0),
   (address 73, stringRec), (address 74, stringOfList), (address 75, strEq)]

def strBlobs : List (Address × ByteArray) :=
  [(address 80, "ab".toUTF8), (address 81, ⟨#[97]⟩), (address 82, ⟨#[98]⟩)]

def stringNames : List String := ["String", "String.ofList", "List", "List.nil", "List.cons", "Char", "Char.ofNat"]

/-- The committed table with the string-literal support moved to the test constants. -/
def stringPins : Pins :=
  let kept := builtinPins.names.toList.filter fun p => !stringNames.contains (toString p.2)
  let test : List (ConstRef Address × CName) :=
    [(.member (address 70) 0, .str .anonymous "String"),
     (.member (address 74) 0, .str (.str .anonymous "String") "ofList"),
     (.member (address 50) 0, .str .anonymous "List"),
     (.ctor (address 50) 0 0, .str (.str .anonymous "List") "nil"),
     (.ctor (address 50) 0 1, .str (.str .anonymous "List") "cons"),
     (.member (address 60) 0, .str .anonymous "Char"),
     (.member (address 64) 0, .str (.str .anonymous "Char") "ofNat")]
  { builtinPins with names := (kept ++ test).foldl (fun m (r, n) => m.insert r n) {} }

#guard accepts strings strBlobs stringPins
-- a string of another length is not that expansion (the test `Char.ofNat` is
-- constant, so only the length is observable)
#guard !accepts strings [(address 80, "abc".toUTF8), (address 81, ⟨#[97]⟩), (address 82, ⟨#[98]⟩)] stringPins
-- without the support pinned on these constants, the literal does not check
#guard !accepts strings strBlobs

/-! ## The constants a literal references

A record that contains a literal depends on the records of the constants the
literal references (`literalEdges`): the `Nat` block for a `Nat` literal, and
also the string-support records for a string literal. -/

def natBlock : Address := match builtinPins.names.toList.find? (toString ·.2 == "Nat") with
  | some (r, _) => r.block
  | none => address 0

#guard literalKinds strEq == (true, true) && literalKinds litEq == (true, false) &&
  literalKinds charOfNat == (false, false)
#guard (literalEdges stringPins.names strings.toArray)[address 75]? ==
  some #[natBlock, address 70, address 74, address 50, address 60, address 64]
#guard ((literalEdges stringPins.names strings.toArray)[address 74]?).isNone
#guard (literalEdges builtinPins.names #[(address 42, litEq)])[address 42]? == some #[natBlock]

/-! ## A block nested through a container that is itself nested (cl-m1)

The records Ix's compiler produces for `Tests.Ix.Kernel.EntryCaseDefs.LTree`
(`lake exe ix compile Tests/Ix/Kernel/EntryCaseDefs.lean --consts` with
`LTree`, its recursors, `LNode`'s recursors and `List.rec`), in the census
order with the projections last; the same records `kernel-entry-cases`
submits for its `nested-through-nested` case:

    inductive LNode (α : Type) where
      | node : List (LNode α) → LNode α
      | leaf : α → LNode α
    inductive LTree where
      | node : LNode LTree → LTree

The compiler orders `LTree.rec`'s auxiliary motives canonically, as
`[List (LNode LTree), LNode LTree]`: an instance of the container family before
the family's head. The kernel's discovery order, and so every lean4export
stream, has the head first. The in-process modeller formed its container
groups in motive order, so `List`'s singleton group and `LNode`'s family both
claimed motive 1, and the block was rejected with `duplicate declaration
ix.<LTree>.0._model._impl.pack_0`, as `Lean.Elab.InfoTree` was (with `pack_1`)
in the first Mathlib census. The modeller now forms the groups largest family
first (`Ix/Kernel/Frontend/InModel/Nested.lean`, an adapted row). -/

/-- (address, canonical record bytes) -/
def lTreeRecords : List (String × String) := [
  ("6cff906dbfa2bdafe0ec2bf0131e80052cce7e2c653b81495fe5197e53ac67ab",
    "c101000101009117000002000100010091170071b010000101010293170017101771b011" ++
    "71b01201310001000201c0c0"),
  ("8f2c84a1f74bacc1ba80610719e487949eefc2518be0681faff3f6d21f72aef1",
    "c1010000010091170101020000000101921701177121000071b010b10000010101921701" ++
    "1710b102300071b011014fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63" ++
    "f7ec277aaf0102000100"),
  ("697b5ac9c6a84d59c3031db23bdf61fcc97fe6dd9174bd143c9a3107294ce91d",
    "c10100000000000100000000019117712000300030000001b1caa16e96b96d2e28a1c57e" ++
    "c79241fc2c43c99a2e6bd1d04d696a24f64caf86010100"),
  ("a2eaa01e342f9c820f114762edf81a37a2ff6934c44da151fcd8e55522e2bba3",
    "c302000100000305980917b82517b82417b82317b617b80917b81617b81c17b82217b071" ++
    "1808100101880907b82507b82407b82307b607b80907b81607b81c07b82207b171b81778" ++
    "093102011808171615141312111002000100000305980917b82517b82417b82317b617b8" ++
    "0917b81617b81c17b82217b80bb81d0200880807b82507b82407b82307b607b80907b816" ++
    "07b81c07b8221302880a07b82507b82407b82307b607b80907b81607b81c07b82207b107" ++
    "b80b73b80c10780931020118091808171615141312117809310101180918081716151413" ++
    "121002000100000305980917b82517b82417b82317b617b80917b81617b81c17b82217b1" ++
    "7116100201880907b82507b82407b82307b607b80907b81607b81c07b82207b80b721210" ++
    "78093101011808171615141312111001880907b82507b82407b82307b607b80907b81607" ++
    "b81c07b82207b071b2780931000118081716151413121110262003712005b07111107120" ++
    "07117114b39117b2b49117b1b521010071b7b17112b80821020071b80ab1711411711611" ++
    "21060071b80eb171b80f1371b810127117b8119117b80db8129117b80cb8139117b80bb8" ++
    "149117b1b815711510712000b071b818117115b8199117b817b81a9117b80bb81b711710" ++
    "712004b071b81e117116b81f9117b81db8209117b0b8219117b1019117b80b019117b001" ++
    "082dedbc9529f414cf80965bda79c404438c0abc0022f44e0a0162aba67999cbb23994bc" ++
    "51e3686f30a1d483d69d0a835a7b484d892393c084f87a5849de54f3024fb6b41c30532e" ++
    "6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf017054a806e9971efe990263" ++
    "e8c434a35481dd97542f41e4b6d1a16399d2116d16ad1dc96cc152a07f2d28507d5afe39" ++
    "59fa67597f9a01a529dc7411e1c9c293c6b1caa16e96b96d2e28a1c57ec79241fc2c43c9" ++
    "9a2e6bd1d04d696a24f64caf86b3a7d80249fd823100ee03626232d1412a0e8335275d5d" ++
    "f53b92943887b650f7fd903efe0bb38382178634c0d7c1de9bd89d01657d50d3b04044d6" ++
    "ea0d8686340200c0"),
  ("d1ee163ce244c0d4d191cea6ce6271c1f39708ecdb1916db0861a38aa810fa90",
    "c2020001010002049808170117b82417b82317b80917b80d17b81117b81f17b813711610" ++
    "02018808070107b82407b82307b80907b80d07b81107b81f07b814721410780831010217" ++
    "16151413121110018808070107b82407b82307b80907b80d07b81107b81f071671131002" ++
    "0001010002049808170117b82417b82317b80917b80d17b81117b81f17b8147115100200" ++
    "87070107b82407b82307b80907b80d07b81107b81f11028809070107b82407b82307b809" ++
    "07b80d07b81107b81f07b8130771b071b117741211107808310002180817161514131211" ++
    "780831010218081716151413121025210200200471b11271b0b27111107120001471b511" ++
    "7113b69117b4b79117b3b8087120031471b80a107113b80b911713b80c21010071b11471" ++
    "b80eb80f7112b81071b11571b11671b0b81371161121050071b1180971b816b81771b818" ++
    "1371b819127117b81a9117b815b81b9117b815b81c9117b814b81d9117b812b81e71b110" ++
    "71b11171b0b8219117b822029117b82002062dedbc9529f414cf80965bda79c404438c0a" ++
    "bc0022f44e0a0162aba67999cbb23994bc51e3686f30a1d483d69d0a835a7b484d892393" ++
    "c084f87a5849de54f3024fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63" ++
    "f7ec277aaf01ad1dc96cc152a07f2d28507d5afe3959fa67597f9a01a529dc7411e1c9c2" ++
    "93c6b1caa16e96b96d2e28a1c57ec79241fc2c43c99a2e6bd1d04d696a24f64caf86b3a7" ++
    "d80249fd823100ee03626232d1412a0e8335275d5df53b92943887b650f703000100c0"),
  ("efcb43e45afb1a5785f12434d45eb437e4b77f06cf23eb25a73e79a91e58dea8",
    "d100020100010295170017b417b617b80d17b1b2020084070007b407b607b80d11028607" ++
    "0007b407b607b80d07130771b01473121110753200010215141312100e21010271b01371" ++
    "131071b0109117b30171210002117110b5712102021571b71271b808117114b8099117b2" ++
    "b80a9117b1b80b911712b80c033994bc51e3686f30a1d483d69d0a835a7b484d892393c0" ++
    "84f87a5849de54f3024fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7" ++
    "ec277aaf01b3a7d80249fd823100ee03626232d1412a0e8335275d5df53b92943887b650" ++
    "f70301c1c0c1"),
  ("0e935c80d533525d156d40e0b1488a324d9bc9dfa17a55ecb74b468e63eb9a09",
    "d502a2eaa01e342f9c820f114762edf81a37a2ff6934c44da151fcd8e55522e2bba30000" ++
    "00"),
  ("2dedbc9529f414cf80965bda79c404438c0abc0022f44e0a0162aba67999cbb2",
    "d400008f2c84a1f74bacc1ba80610719e487949eefc2518be0681faff3f6d21f72aef100" ++
    "0000"),
  ("3994bc51e3686f30a1d483d69d0a835a7b484d892393c084f87a5849de54f302",
    "d400006cff906dbfa2bdafe0ec2bf0131e80052cce7e2c653b81495fe5197e53ac67ab00" ++
    "0000"),
  ("4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01",
    "d6006cff906dbfa2bdafe0ec2bf0131e80052cce7e2c653b81495fe5197e53ac67ab0000" ++
    "00"),
  ("7054a806e9971efe990263e8c434a35481dd97542f41e4b6d1a16399d2116d16",
    "d600697b5ac9c6a84d59c3031db23bdf61fcc97fe6dd9174bd143c9a3107294ce91d0000" ++
    "00"),
  ("841d72f6b0a13975c32fd724e6c7ab1bbc7cd6becb992f1ac51ec40ff3473f4d",
    "d501d1ee163ce244c0d4d191cea6ce6271c1f39708ecdb1916db0861a38aa810fa900000" ++
    "00"),
  ("ad1dc96cc152a07f2d28507d5afe3959fa67597f9a01a529dc7411e1c9c293c6",
    "d400018f2c84a1f74bacc1ba80610719e487949eefc2518be0681faff3f6d21f72aef100" ++
    "0000"),
  ("b1caa16e96b96d2e28a1c57ec79241fc2c43c99a2e6bd1d04d696a24f64caf86",
    "d6008f2c84a1f74bacc1ba80610719e487949eefc2518be0681faff3f6d21f72aef10000" ++
    "00"),
  ("b3a7d80249fd823100ee03626232d1412a0e8335275d5df53b92943887b650f7",
    "d400016cff906dbfa2bdafe0ec2bf0131e80052cce7e2c653b81495fe5197e53ac67ab00" ++
    "0000"),
  ("b933100634e2fd70929bcb62d1bac8762209fdbee66e4d4afa0e631c4b611d73",
    "d500a2eaa01e342f9c820f114762edf81a37a2ff6934c44da151fcd8e55522e2bba30000" ++
    "00"),
  ("d96c789c997e527c9a09485df2c314adfb4e9182b9c10b796a131deea477e00b",
    "d501a2eaa01e342f9c820f114762edf81a37a2ff6934c44da151fcd8e55522e2bba30000" ++
    "00"),
  ("dc65e7d5f52c3233376da36832382eff62e93606ef392dc467e43ce2aae2c9e8",
    "d500d1ee163ce244c0d4d191cea6ce6271c1f39708ecdb1916db0861a38aa810fa900000" ++
    "00"),
  ("fd903efe0bb38382178634c0d7c1de9bd89d01657d50d3b04044d6ea0d868634",
    "d40000697b5ac9c6a84d59c3031db23bdf61fcc97fe6dd9174bd143c9a3107294ce91d00" ++
    "0000")]

def lTreeStream : Ix.Ixon.Admission.Records :=
  lTreeRecords.filterMap fun (a, b) => do pure (← addressOfHex a, ← bytesOfHex b)

def lTreeBlock : Address := (addressOfHex "697b5ac9c6a84d59c3031db23bdf61fcc97fe6dd9174bd143c9a3107294ce91d").getD (address 0)
def lNodeBlock : Address := (addressOfHex "8f2c84a1f74bacc1ba80610719e487949eefc2518be0681faff3f6d21f72aef1").getD (address 0)

/-- The reader's state and declarations after the stream. -/
def lTreeRead : Option (State × Array Ix.Kernel.Declaration) := do
  let constants ← (Ix.Ixon.Admission.decodeRecords limits lTreeStream).toOption
  let cx := streamContext builtinPins builtinPre constants [] (fun _ => none)
  (readRecords cx builtinPre.state constants.toArray).toOption

/-- The carriers' heads of `LTree.rec`'s motives, in motive order, as the
modeller reads them. -/
def lTreeMotiveHeads : Option (List String) := do
  let (st, _) ← lTreeRead
  let b ← st.indBlocks[keyName (.member lTreeBlock 0)]?
  let t0 ← b.types.head?
  let r0 ← b.recs.find? (·.cv.name == t0.cv.name.str "rec")
  let (_, afterP) ← r0.cv.type.stripPis t0.nP
  let (motives, _) ← afterP.stripPis r0.nM
  let mems ← (Ix.Kernel.Frontend.InModel.readMems t0.cv.levelParams t0.nP b.types
    (motives.map (·.1))).toOption
  pure (mems.map (toString ·.I))

/-- Every name the reader's declarations of the stream introduce. -/
def lTreeNames : List String :=
  match lTreeRead with
  | some (_, decls) => decls.toList.flatMap fun
    | .indDecl block _ => block.map (toString ·.toConstantVal.name)
    | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .axiomDecl cv | .quotDecl _ cv =>
      [toString cv.name]
    | .basisDecl k => k.decls.map (toString ·.toConstantVal.name)
  | none => []

#guard lTreeStream.length == lTreeRecords.length && lTreeRecords.length == 19
-- the order that exercises the grouping: `List (LNode LTree)` before `LNode LTree`
#guard lTreeMotiveHeads ==
  some [keyString (.member lTreeBlock 0), "List", keyString (.member lNodeBlock 0)]
-- the modeller's records introduce every name once (`pack_0` was emitted twice)
#guard !lTreeNames.isEmpty && lTreeNames.eraseDups.length == lTreeNames.length
#guard (lTreeNames.filter (· == keyString (.member lTreeBlock 0) ++ "._model._impl.pack_0")).length == 1
-- and the block, its three recursors and the container's install
#guard match checkBytesWith builtinPins builtinPre builtinNatPins limits lTreeStream [] with
  | .ok env =>
    let names := env.consts.map (toString ·.name)
    let t := keyString (.member lTreeBlock 0)
    names.contains t && names.contains (t ++ ".rec") && names.contains (t ++ ".rec_1") &&
      names.contains (t ++ ".rec_2") && names.contains (keyString (.member lNodeBlock 0))
  | .error _ => false

/-! ## Universe levels in canonical form (cl-m1, cl-level)

The records Ix's compiler produces for
`Tests.Ix.Kernel.EntryCaseDefs.levelCanon` (`--consts levelCanon,Subtype.rec,
True.rec`), in the census order with the projections last:

    theorem levelCanon.{w, x} {a b : {_f : (K : Type w) → (P : Sort x) → P // True}}
        (h : a = b) : a = b := h

Lean elaborates `Subtype.{W}` and `Eq.{max 1 W}`, `W = imax (w+2) (imax (x+1)
x)`. Ixon stores each level as the canonical form of its semantic class
(`Ix/IxonUniv.lean`): `Subtype.{imax (max (w+2) (x+1)) x}` and
`Eq.{max (x+1) (imax (w+2) x)}`. The checker infers the `Subtype`'s type,
`Sort (max (imax (max (w+2) (x+1)) x) 1)`, where the `Eq` expects
`Sort (max (x+1) (imax (w+2) x))`. The two levels are equal at every
valuation. Nanoda's comparison (the official kernel's `leq`, which con-leche
ports) establishes only `≤`: the converse `x+1 ≤ max (imax … x) 1` splits
the `max`, and each branch fails on its own (at `x = 0` and at `x = 1`).
Until cl-level the theorem was refused with `application type mismatch`, as
`RatFunc.liftOn_def` and `RatFunc.liftOn'_def` (unfolding lemmas of
`irreducible_def`) were in the Mathlib census. That case of the comparison
now falls back on Géran's sublevels (`Ix/Kernel/LevelGeran.lean`, a
decision procedure, `Ix.Kernel.Level.Geran.leq_iff`), and the theorem is
accepted. The reader converts levels as stored. -/

/-- (address, canonical record bytes) -/
def levelRecords : List (String × String) := [
  ("cfec05d1d7f2512f6577c2f61a840523804c36d4043c252ab4ba2508ede75171",
    "c1010000000000010000000000300000000100"),
  ("34447f09a3a88dfbf7eba2070430dbab3343de5f3b67b7db2d75d31af390d13d",
    "c1010001020092170217b00101000100020294170217b017111771111072310002131201" ++
    "9117100000030040c00100c0"),
  ("10cebb826088ceb379d85969e9cc3f60ee05aaa02088e7ab36cb7caa3d28b410",
    "d009029317b517b517b80872b612118307b507b507b808100921000291170310911700b1" ++
    "71b0b28107b2200271b3b471210101b571b61171b710036620bf274c4c89870476888d22" ++
    "8d0b43af0ddcc856cfa7b006fb5a979d12eb89c37d6290e00fb865fb5db7bce18fd69e6d" ++
    "1674ad573724b85466ea9f7578a207e35ab17358fae7a81efb3d94a164fd3f85ab8b0c88" ++
    "8aaa071cfe0d60ffbc1cac0401c04001c18002c0c1804002c001c1c1c1"),
  ("17f54217ac922579222cf29e42f1ccaac7cdc1f3b90401881d65a63b51064057",
    "d1000202000101951702179117100017b317b80917722100021312711210010286070207" ++
    "9117100007b307b809071307711310721211100a7121010214712100021171b1109117b2" ++
    "0171b01371b41171b5107112b69117711210b7911712b808026620bf274c4c8987047688" ++
    "8d228d0b43af0ddcc856cfa7b006fb5a979d12eb899e92d21510c29302dae3880e11eb53" ++
    "a149d96c49662a866d86b080c41f8f45510300c0c1"),
  ("4402b03b4b95a01edd5bed60a5851e3d851a2073590236d7ee4935f8b0261e88",
    "d10101000001019317b217b017b171121001008207b207b010037110200120009117b100" ++
    "02e35ab17358fae7a81efb3d94a164fd3f85ab8b0c888aaa071cfe0d60ffbc1cacf4bc2a" ++
    "9e8e268eb352f719657d8806b072a555a29f2eb85e72805fddc9cd019101c0"),
  ("6620bf274c4c89870476888d228d0b43af0ddcc856cfa7b006fb5a979d12eb89",
    "d60034447f09a3a88dfbf7eba2070430dbab3343de5f3b67b7db2d75d31af390d13d0000" ++
    "00"),
  ("9e92d21510c29302dae3880e11eb53a149d96c49662a866d86b080c41f8f4551",
    "d4000034447f09a3a88dfbf7eba2070430dbab3343de5f3b67b7db2d75d31af390d13d00" ++
    "0000"),
  ("e35ab17358fae7a81efb3d94a164fd3f85ab8b0c888aaa071cfe0d60ffbc1cac",
    "d600cfec05d1d7f2512f6577c2f61a840523804c36d4043c252ab4ba2508ede751710000" ++
    "00"),
  ("f4bc2a9e8e268eb352f719657d8806b072a555a29f2eb85e72805fddc9cd0191",
    "d40000cfec05d1d7f2512f6577c2f61a840523804c36d4043c252ab4ba2508ede7517100" ++
    "0000")]

/-- The theorem's record. -/
def levelTheorem : String := "10cebb826088ceb379d85969e9cc3f60ee05aaa02088e7ab36cb7caa3d28b410"

def levelStream : Ix.Ixon.Admission.Records :=
  levelRecords.filterMap fun (a, b) => do pure (← addressOfHex a, ← bytesOfHex b)

/-- The theorem's level parameters as the reader names them. -/
def lw : Ix.Kernel.Level := .param (levelName 0)
def lx : Ix.Kernel.Level := .param (levelName 1)
def lsucc (l : Ix.Kernel.Level) : Nat → Ix.Kernel.Level
  | 0 => l
  | k + 1 => .succ (lsucc l k)

/-- The `Subtype`'s inferred type level and the `Eq`'s domain level. -/
def subtypeLevel : Ix.Kernel.Level :=
  .max (.imax (.max (lsucc lw 2) (lsucc lx 1)) lx) (lsucc .zero 1)
def eqLevel : Ix.Kernel.Level := .max (lsucc lx 1) (.imax (lsucc lw 2) lx)

#guard levelStream.length == levelRecords.length && levelRecords.length == 9
-- equal at every valuation of `w, x` in `0‥5` (both are `1` at `x = 0`, and
-- `max (w+2) (x+1)` otherwise)
#guard (List.range 6).all fun i => (List.range 6).all fun j =>
  let φ : Ix.Kernel.Name → Nat := fun n => if n == levelName 0 then i else if n == levelName 1 then j else 0
  Ix.Kernel.Level.eval φ subtypeLevel == Ix.Kernel.Level.eval φ eqLevel
-- the comparison establishes both directions, and so the equivalence
#guard Ix.Kernel.Level.leq subtypeLevel eqLevel == some true
#guard Ix.Kernel.Level.leq eqLevel subtypeLevel == some true
#guard Ix.Kernel.Level.isEquiv subtypeLevel eqLevel == some true
-- the case nanoda's split misses, `x + 1 ≤ max (imax … x) 1`, by sublevels:
-- `x + 1` is dominated by the `imax`'s `x + 1` where `x` is nonzero and by
-- the `1` where it is zero
#guard Ix.Kernel.Level.Geran.leq lx (subtypeLevel) (-1)
-- and the theorem is accepted
#guard match checkBytesWith builtinPins builtinPre builtinNatPins limits levelStream [] with
  | .ok env => (env.consts.map (toString ·.name)).contains
      (keyString (.member ((addressOfHex levelTheorem).getD (address 0)) 0))
  | .error _ => false

/-! ## Negative: pinned names on constants of another shape -/

/-- A one-constructor `Type` stored under the real `Eq` block's address, with
its recursor over the real `Eq`/`Eq.refl` projection records: the reader
names it `Eq` (by address), and con-leche rejects the reserved name. -/
def eqBlock : Address := match builtinPins.names.toList.find? (toString ·.2 == "Eq") with
  | some (r, _) => r.block
  | none => address 0

def fakeEq : List (Address × Ixon.Constant) :=
  [(eqBlock, unitBlock), (address 90, unitRec eq eqRefl)]

#guard match run fakeEq with
  | .error (.kernel (.invalid msg) _) => msg.startsWith "reserved basis name"
  | _ => false

/-- `fun n m => n` pinned as `Nat.add` is not certified, so not accepted under
that name; unpinned, it is an ordinary definition. -/
def fakeAdd : Ixon.Constant :=
  defn .defn (all (ref 0) (all (ref 0) (ref 0))) (lam (ref 0) (lam (ref 0) (var 1))) [nat]

def addPins : Pins :=
  let kept := builtinPins.names.toList.filter (toString ·.2 != "Nat.add")
  let test : List (ConstRef Address × CName) := [(.member (address 91) 0, .str (.str .anonymous "Nat") "add")]
  { builtinPins with names := (kept ++ test).foldl (fun m (r, n) => m.insert r n) {} }

#guard !accepts [(address 91, fakeAdd)] (pins := addPins)
#guard accepts [(address 91, fakeAdd)]

/-- Names attach to addresses, not to contents: `Nat`'s block stored at
another address is not named `Nat`. -/
def natBlockRecord : Ixon.Constant := Id.run do
  let some (r, _) := builtinPins.names.toList.find? (toString ·.2 == "Nat") | return default
  let some (_, c) := builtinPre.records.find? (·.1 == r.block) | return default
  return c

#guard
  let cx := contextOf builtinPins #[(address 92, natBlockRecord)] [] builtinPre.records
  toString (cx.nameOf (.member (address 92) 0)) == keyString (.member (address 92) 0) &&
    toString (cx.nameOf (.member (address 92) 0)) != "Nat"

-- The address encodings are computed ahead (`Ctx.keys`, T1): an unpinned
-- record's reference is in the table, under `keyName`'s spelling, and a
-- pinned one is not.
#guard
  let cx := contextOf builtinPins #[(address 93, idNat)] [] builtinPre.records
  let natRef := (builtinPins.names.toList.find? (toString ·.2 == "Nat")).map (·.1)
  cx.keys.map.contains (.member (address 93) 0) &&
    toString (cx.nameOf (.member (address 93) 0)) == keyString (.member (address 93) 0) &&
    natRef.isSome && natRef.all (!cx.keys.map.contains ·)

/-! ## Negative: malformed and unsupported records -/

-- the same address twice: the byte stage rejects it (`uniqueKeys`, L6b),
-- and the reader rejects it in decoded records (`readRecords_nodup`)
#guard match run [(address 10, idNat), (address 10, idNat)] with
  | .error (.duplicate .records 1 a) => a == address 10
  | _ => false
#guard match checkConstantsWith builtinPins builtinPre builtinNatPins
    [(address 10, idNat), (address 10, idNat)] [] with
  | .error (.read 1 (.malformed _)) => true
  | _ => false
-- a projection to a block that is not there
#guard match run [(address 21, iPrj (address 99))] with
  | .error (.read 0 (.malformed _)) => true
  | _ => false
-- a reference to a record that is not there
#guard match run [(address 11, twoDef)] with
  | .error (.read 0 (.malformed _)) => true
  | _ => false
-- unsafe and partial definitions decline
#guard match run [(address 10, defn .defn (all (ref 0) (ref 0)) (lam (ref 0) (var 0)) [nat] (safety := .unsaf))] with
  | .error (.read 0 (.declined _)) => true
  | _ => false
#guard match run [(address 10, defn .defn (all (ref 0) (ref 0)) (lam (ref 0) (var 0)) [nat] (safety := .part))] with
  | .error (.read 0 (.declined _)) => true
  | _ => false
-- a non-canonical byte string fails at decoding
#guard match checkBytesWith builtinPins builtinPre builtinNatPins limits [(address 10, ⟨#[0xff]⟩)] [] with
  | .error (.decode 0 _ _) => true
  | _ => false

/-! ## The table's own refusals -/

#guard (pinMap #[⟨.member (address 1) 0, .str .anonymous "A"⟩, ⟨.member (address 2) 0, .str .anonymous "A"⟩]).isOk == false
#guard (pinMap #[⟨.member (address 1) 0, .str .anonymous "A"⟩, ⟨.member (address 1) 0, .str .anonymous "B"⟩]).isOk == false
#guard (pinMap #[⟨.member (address 1) 0, .str (.str .anonymous "ix") "A"⟩]).isOk == false
#guard (pinMap #[⟨.member (address 1) 0, .str (.str .anonymous "A") "rec"⟩]).isOk == false
#guard (pinMap #[⟨.member (address 1) 0, .str (.str .anonymous "A") "B"⟩]).isOk

/-! ## The key encoding is injective -/

example {r s : ConstRef Address} (h : keyName r = keyName s) : r = s := keyName_injective h

/-- info: 'Ix.Kernel.ConLecheReader.keyName_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keyName_injective

/-! ## Model existence -/

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : run strings strBlobs stringPins = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytesWith_has_model V h

end Tests.Ix.Kernel.ConLecheReader
