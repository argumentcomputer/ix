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
checked by `ConLeche.Cached.checkDecls .verified`.

Positive: a definition and a definition over it with a theorem by delta, an
inductive with its separately stored recursor and an ι-reduction, a
structure with a projection function and a projection reduction, the
quotient's lift reduction, a Nat literal against its constructors, a String
literal against its `String.ofList` expansion (over test constants pinned as
the string-literal support).

Negative: a block of another shape stored under the real `Eq`'s address is
named `Eq` and rejected by con-leche's reserved-name check; a definition of
the wrong shape pinned as `Nat.add` is not accepted under that name (and is
accepted unpinned); a copy of `Nat`'s contents at another address is not
named `Nat`; malformed tables, duplicate records and unsafe declarations;
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
def builtinNatPins : List ConLeche.NatOpPinSet := match builtinNatOpPins with | .ok ps => ps | .error _ => []

def run (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (pins : Pins := builtinPins) : Except Error ConLeche.Env :=
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
#guard (builtinPre.ix.decls.toList.map (toString ∘ ConLeche.Frontend.preludeKey)) ==
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

/-! ## Negative: malformed and unsupported records -/

-- the same address twice
#guard match run [(address 10, idNat), (address 10, idNat)] with
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

example (V : Type) [ConLeche.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : ConLeche.Env}
    (h : checkBytes limits records blobs = .ok env) : Nonempty (ConLeche.Model V env) :=
  checkBytes_has_model V h

example (V : Type) [ConLeche.SetTheory V] {env : ConLeche.Env}
    (h : run strings strBlobs stringPins = .ok env) : Nonempty (ConLeche.Model V env) :=
  checkBytesWith_has_model V h

end Tests.Ix.Kernel.ConLecheReader
