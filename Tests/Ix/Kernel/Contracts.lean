import IxC.Kernel.Admission.Theorems
import Ix.Ixon.Authenticated.Theorems
import Tests.Ix.Kernel.Reader

/-! # Ixon binder contracts in the checker

Ixon's binder contracts (`IxC/Ixon/Types/Contract.lean`) are identity data
in the checker's `BinderMeta`, and typing does not read them:

* **The reader keeps them.** A definition whose `all` and `lam` carry
  non-default contracts, read through the certified entry at BLAKE3
  (`Ixon.Authenticated.checkBytes`), is installed with those contracts in
  its type's and value's `BinderMeta`; a `let` contract is erased.
* **Verdicts do not depend on them.** Pairs of fixtures that differ only in
  binder contracts get the same verdict: definitions, a conversion between
  λs and between ∀s whose contracts differ, and a false equation. That
  includes a value whose binder contract disagrees with its type's,
  `f : ∀[erased] (x : Nat), Nat := fun[many] x => x`, which is accepted:
  typing is contract-blind (the binder congruences compare `pw` only),
  and a result contract is never compared.
* **Pinned shapes compare them.** The basis blocks are matched up to
  `canon` and the standard pins by `matchesPin`, and both compare
  contracts: the prelude's `Eq` block with a non-default contract on a
  binder is not the basis `Eq` (the fold rejects the reserved name), and
  a `propext` whose binder carries one does not match its pin. Both still
  forgive the `pw` datum. -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader (keyName)
open Tests.Ix.Kernel.Reader

namespace Tests.Ix.Kernel.Contracts

/-! ## Fixtures -/

/-- The certified entry at BLAKE3 on a fixture under its BLAKE3 keys. -/
def check (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Except Ix.Kernel.Admission.Error Ix.Kernel.Env :=
  let r := rekeyed cs blobs
  Ixon.Authenticated.checkBytes limits r.encoded r.blobs

def outcomeOf (cs : List (Address × Ixon.Constant)) : Option Ix.Kernel.Admission.Outcome :=
  match check cs with
  | .ok _ => none
  | .error e => some e.outcome

/-- The installed constant of the stand-in record `a`'s member `0`. -/
def installed (cs : List (Address × Ixon.Constant)) (a : Address) : Option Ix.Kernel.ConstantInfo :=
  match check cs with
  | .ok env => env.find? (keyName (.member ((rekeyed cs).rename a) 0))
  | .error _ => none

/-- `∀[c, r] (n : Nat), Nat := fun[c'] n => n`, over the prelude's `Nat`. -/
def idNatWith (c : Ixon.BinderContract) (r : Ixon.ValueContract) (c' : Ixon.BinderContract) :
    Ixon.Constant :=
  defn .defn (.all c r (ref 0) (ref 0)) (.lam c' (ref 0) (var 0)) [nat]

/-- The contracts of a term's binders, in preorder. -/
def contracts : Ix.Kernel.Expr → List (Ixon.BinderContract × Ixon.ValueContract)
  | .lam t b m | .forallE t b m => (m.contract, m.result) :: (contracts t ++ contracts b)
  | .app f a => contracts f ++ contracts a
  | .letE t v b => contracts t ++ contracts v ++ contracts b
  | .proj _ _ e | .fvar _ e => contracts e
  | _ => []

/-- An installed definition's type and value contracts. -/
def defnContracts : Option Ix.Kernel.ConstantInfo →
    Option (List (Ixon.BinderContract × Ixon.ValueContract) ×
      List (Ixon.BinderContract × Ixon.ValueContract))
  | some (.defnInfo cv value _) => some (contracts cv.type, contracts value)
  | _ => none

/-! ## The reader keeps binder contracts -/

def linearUnique : Ixon.Constant := idNatWith .linear .unique .affine

#guard defnContracts (installed [(address 10, linearUnique)] (address 10)) ==
  some ([(.linear, .unique)], [(.affine, .shared)])
-- Lean-fragment binders carry the defaults
#guard defnContracts (installed [(address 10, idNat)] (address 10)) ==
  some ([(.many, .shared)], [(.many, .shared)])
-- every input contract and every result contract reaches `BinderMeta`
def binderContracts : List Ixon.BinderContract :=
  (List.range 16).filterMap fun bits => Ixon.BinderContract.ofBits? bits.toUInt8
def valueContracts : List Ixon.ValueContract :=
  (List.range 4).filterMap fun bits => Ixon.ValueContract.ofBits? bits.toUInt8
#guard binderContracts.length == 16 && valueContracts.length == 4
#guard binderContracts.all fun c => valueContracts.all fun r =>
  defnContracts (installed [(address 10, idNatWith c r c)] (address 10)) ==
    some ([(c, r)], [(c, .shared)])
-- a `let` contract is erased (the checker's `letE` has no field for it), and
-- the annotation pass ζ-reduces the `let`
def borrowLet : Ixon.Constant :=
  defn .defn (all (ref 0) (ref 0))
    (lam (ref 0) (.letE (.borrow false .linear) (ref 0) (var 0) (var 0))) [nat]
#guard defnContracts (installed [(address 10, borrowLet)] (address 10)) ==
  some ([(.many, .shared)], [(.many, .shared)])

/-! ## Verdicts do not depend on binder contracts -/

/-- Both fixtures get the verdict `v`. -/
def sameVerdict (a b : List (Address × Ixon.Constant)) (v : Option Ix.Kernel.Admission.Outcome) :
    Bool :=
  outcomeOf a == v && outcomeOf b == v

-- definitions
#guard sameVerdict [(address 10, idNat)] [(address 10, linearUnique)] none
#guard binderContracts.all fun c => valueContracts.all fun r =>
  outcomeOf [(address 10, idNatWith c r .many)] == none
-- a value whose binder contract is not its type's: contract-blind typing
-- accepts `f : ∀[erased] (x : Nat), Nat := fun[many] x => x`, whose type and
-- value keep their own contracts
def erasedType : Ixon.Constant := idNatWith .erased .shared .many
#guard sameVerdict [(address 10, idNat)] [(address 10, erasedType)] none
#guard defnContracts (installed [(address 10, erasedType)] (address 10)) ==
  some ([(.erased, .shared)], [(.many, .shared)])
-- a result contract is never compared: `∀[linear] (x : Nat), unique Nat`
-- holds `fun[linear] x => x`, whose type is inferred with the default result
#guard sameVerdict [(address 10, idNat)] [(address 10, idNatWith .linear .unique .linear)] none

/-- `@Eq.{1} (Nat → Nat) l r := @Eq.refl.{1} (Nat → Nat) v`, refs
`[Eq, Eq.refl, Nat]`. -/
def lamEq (l r v : E) : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [all (ref 2) (ref 2), l, r]) (apps (ref 1 [0]) [all (ref 2) (ref 2), v])
    [eq, eqRefl, nat] [one]

def idLam (c : Ixon.BinderContract) : E := .lam c (ref 2) (var 0)

-- conversion between λs that differ only in contracts
#guard sameVerdict [(address 10, lamEq (idLam .many) (idLam .many) (idLam .many))]
  [(address 10, lamEq (idLam .linear) (idLam .erased) (idLam .affine))] none
-- and a false equation, whatever the contracts
def zeroLam (c : Ixon.BinderContract) : E := .lam c (ref 2) (ref 3)
def falseLamEq (c : Ixon.BinderContract) : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [all (ref 2) (ref 2), idLam c, zeroLam c])
    (apps (ref 1 [0]) [all (ref 2) (ref 2), idLam c]) [eq, eqRefl, nat, natZero] [one]
#guard sameVerdict [(address 10, falseLamEq .many)] [(address 10, falseLamEq .linear)] (some .declined)

/-- `@Eq.{2} Type l r := @Eq.refl.{2} Type v`, refs `[Eq, Eq.refl, Nat]`,
universes `[2, 1]`. -/
def piEq (l r v : E) : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [sort 1, l, r]) (apps (ref 1 [0]) [sort 1, v])
    [eq, eqRefl, nat] [.succ one, one]

def natPi (c : Ixon.BinderContract) (r : Ixon.ValueContract) : E := .all c r (ref 2) (ref 2)

-- conversion between ∀s that differ only in input and result contracts
#guard sameVerdict [(address 10, piEq (natPi .many .shared) (natPi .many .shared) (natPi .many .shared))]
  [(address 10, piEq (natPi .erased .unique) (natPi .many .shared) (natPi .linear .localShared))] none

/-! ## Pinned shapes compare binder contracts -/

/-- The first binder of a term with input contract `c`. -/
def withFirstContract (c : Ixon.BinderContract) : Ix.Kernel.Expr → Ix.Kernel.Expr
  | .forallE t b m => .forallE t b { m with contract := c }
  | .lam t b m => .lam t b { m with contract := c }
  | e => e

/-- The first binder of a term with the datum `pw`. -/
def withFirstPw (pw : Ix.Kernel.PropWhen) : Ix.Kernel.Expr → Ix.Kernel.Expr
  | .forallE t b m => .forallE t b { m with pw }
  | .lam t b m => .lam t b { m with pw }
  | e => e

/-- The prelude's declarations with the type of the basis `Eq`'s type
former rewritten by `f`. -/
def preludeWithEq (f : Ix.Kernel.Expr → Ix.Kernel.Expr) : Array Ix.Kernel.Declaration :=
  builtinPre.ix.decls.map fun
    | .indDecl (.indInfo cv caps :: rest) nP =>
      if toString cv.name == "Eq" then .indDecl (.indInfo { cv with type := f cv.type } caps :: rest) nP
      else .indDecl (.indInfo cv caps :: rest) nP
    | d => d

def foldOutcome (ds : Array Ix.Kernel.Declaration) : Option String :=
  match Ix.Kernel.Cached.checkDecls .verified [] ds with
  | .ok _ => none
  | .error (.invalid msg, _) => some msg
  | .error _ => some "other"

-- the prelude as it is installs every basis block
#guard foldOutcome (preludeWithEq id) == none
-- an `Eq` whose `{α : Sort u}` is `erased` is not the basis `Eq`
#guard foldOutcome (preludeWithEq (withFirstContract .erased)) == some "reserved basis name Eq"
-- an `Eq` whose result contract differs is not either
#guard foldOutcome (preludeWithEq fun
    | .forallE t b m => .forallE t b { m with result := .unique }
    | e => e) == some "reserved basis name Eq"
-- the `pw` datum is still forgiven
#guard foldOutcome (preludeWithEq (withFirstPw (.ifAllZero []))) == none

-- `matchesPin` compares contracts and forgives `pw`
#guard Ix.Kernel.ConstantVal.matchesPin Ix.Kernel.propextA Ix.Kernel.propextA
#guard !Ix.Kernel.ConstantVal.matchesPin
  { Ix.Kernel.propextA with type := withFirstContract .linear Ix.Kernel.propextA.type } Ix.Kernel.propextA
#guard Ix.Kernel.ConstantVal.matchesPin
  { Ix.Kernel.propextA with type := withFirstPw (.ifAllZero []) Ix.Kernel.propextA.type } Ix.Kernel.propextA

end Tests.Ix.Kernel.Contracts
