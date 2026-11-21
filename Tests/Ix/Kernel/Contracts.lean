import IxC.Kernel.Admission.Theorems
import Ix.Ixon.Authenticated.Theorems
import Tests.Ix.Kernel.Reader

/-! # Binder modes in the checker

An Ixon record keeps its binders' modes in its binder-data section and a
`let`'s mode in the `let`'s header (`IxC/Ixon/Types/Modes.lean`). The checker
is mode-blind:

* **The reader does not read modes.** A definition whose section gives
  its `all` and `lam` binders non-default modes, read through the certified
  entry at BLAKE3 (`Ixon.Authenticated.checkBytes`), is installed with the same
  type and value as one without a section (kernel terms carry no modes), as is one whose
  section carries the defaults; a `let` with a mode in its header is read
  like an ordinary one.
* **Modes do not change a verdict.** A record gets the verdict it gets with
  default modes, whatever its section's modes, including modes that differ
  between a definition's type and its value: an identity is accepted, a
  false equation declined.
* **Pinned shapes forgive the `pw` datum.** The basis blocks are matched up
  to `canon` and the standard pins by `matchesPin`, and both forgive the
  `pw` datum. -/

open Ix.Kernel (ConstRef)
open Tests.Ix.Kernel.Reader

namespace Tests.Ix.Kernel.Contracts

/-! ## Fixtures -/

/-- The certified entry at BLAKE3 on a fixture under its BLAKE3 keys. -/
def check (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Except Ix.Kernel.Admission.Error (Ix.Kernel.Env .anon) :=
  let r := rekeyed cs blobs
  Ixon.Authenticated.checkBytes builtinBinding limits r.encoded r.blobs

def outcomeOf (cs : List (Address × Ixon.Constant)) : Option Ix.Kernel.Admission.Outcome :=
  match check cs with
  | .ok _ => none
  | .error e => some e.outcome

/-- The installed constant of the stand-in record `a`'s member `0`. -/
def installed (cs : List (Address × Ixon.Constant)) (a : Address) : Option (Ix.Kernel.ConstantInfo .anon) :=
  match check cs with
  | .ok env => env.find? (.id ((rekeyed cs).rename a))
  | .error _ => none

/-- `c` with a binder-data section of one root block per entry of `roots`,
in root order, each binder's node `never` at its mode. -/
def withModes (c : Ixon.Constant) (roots : List (List Ixon.AllMode)) : Ixon.Constant :=
  { c with binders := roots.toArray.mapIdx fun i modes =>
      { shared := false, index := i.toUInt64, variant := 0
        nodes := modes.toArray.map Ixon.BinderNode.never } }

/-- `∀ (n : Nat), Nat := fun n => n` over the prelude's `Nat`, its type's
binder at mode `type` and its value's at `value`. -/
def idNatWith (type value : Ixon.AllMode) : Ixon.Constant :=
  withModes idNat [[type], [value]]

/-- Every binder mode. -/
def allModes : List Ixon.AllMode :=
  [Ixon.BinderMode.many, .borrowed, .unique, .uniqueBorrowed, .once, .onceBorrowed, .erased].flatMap
    fun input => [Ixon.ResultMode.shared, .borrowed, .unique, .uniqueBorrowed].map
      fun result => { input, result }

/-- An installed definition's type and value. -/
def defnTerms : Option (Ix.Kernel.ConstantInfo .anon) →
    Option (Ix.Kernel.Expr .anon × Ix.Kernel.Expr .anon)
  | some (.defnInfo cv value _) => some (cv.type, value)
  | _ => none

/-- The identity's type and value, read without a section. -/
def plainTerms : Option (Ix.Kernel.Expr .anon × Ix.Kernel.Expr .anon) :=
  defnTerms (installed [(address 10, idNat)] (address 10))

/-! ## The reader does not read modes -/

#guard allModes.length == 28
#guard plainTerms.isSome
-- with the default modes in the section
#guard defnTerms (installed [(address 10, idNatWith {} {})] (address 10)) == plainTerms
-- every mode in the section, on the type and on the value
#guard allModes.all fun m =>
  defnTerms (installed [(address 10, idNatWith m m)] (address 10)) == plainTerms
-- a `let` with a mode in its header (`borrow`) is read like an ordinary one
def borrowLet : Ixon.Constant :=
  defn .defn (all (ref 0) (ref 0))
    (lam (ref 0) (.letE false .borrow (ref 0) (var 0) (var 0))) [nat]
def valueLet : Ixon.Constant :=
  defn .defn (all (ref 0) (ref 0))
    (lam (ref 0) (.letE false (.value .many) (ref 0) (var 0) (var 0))) [nat]
#guard outcomeOf [(address 10, borrowLet)] == none
#guard (defnTerms (installed [(address 10, valueLet)] (address 10))).isSome
#guard defnTerms (installed [(address 10, borrowLet)] (address 10))
  == defnTerms (installed [(address 10, valueLet)] (address 10))

/-! ## Modes do not change a verdict -/

-- the identity is accepted at every mode, and with its type's and value's
-- modes apart
#guard allModes.all fun m => outcomeOf [(address 10, idNatWith m m)] == none
#guard allModes.all fun m =>
  outcomeOf [(address 10, idNatWith m {})] == none && outcomeOf [(address 10, idNatWith {} m)] == none

def natPi : E := all (ref 2) (ref 2)
def idLam : E := lam (ref 2) (var 0)
def zeroLam : E := lam (ref 2) (ref 3)

/-- `@Eq.{1} (∀ (n : Nat), Nat) (fun n => n) (fun n => Nat.zero) :=
@Eq.refl.{1} _ (fun n => n)`, refs `[Eq, Eq.refl, Nat, Nat.zero]`: false. -/
def falseLamEq : Ixon.Constant :=
  defn .thm (apps (ref 0 [0]) [natPi, idLam, zeroLam])
    (apps (ref 1 [0]) [natPi, idLam]) [eq, eqRefl, nat, natZero] [one]

-- a false equation is declined, whatever the modes of its binders
#guard outcomeOf [(address 10, falseLamEq)] == some .declined
#guard [({} : Ixon.AllMode), ⟨.erased, .unique⟩, ⟨.once, .borrowed⟩].all fun m =>
  outcomeOf [(address 10, withModes falseLamEq [[m, m, m], [m, m]])] == some .declined

/-! ## Pinned shapes forgive the `pw` datum -/

/-- The first binder of a term with the datum `pw`. -/
def withFirstPw (pw : Ix.Kernel.PropWhen) : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon
  | .forallE t b m => .forallE t b { m with pw }
  | .lam t b m => .lam t b { m with pw }
  | e => e

/-- The prelude's declarations with the type of the basis `Eq`'s type
former rewritten by `f`. -/
def preludeWithEq (f : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon) : Array (Ix.Kernel.Declaration .anon) :=
  builtinPre.ix.decls.map fun
    | .indDecl (.indInfo cv caps :: rest) nP =>
      if toString cv.name == "Eq" then .indDecl (.indInfo { cv with type := f cv.type } caps :: rest) nP
      else .indDecl (.indInfo cv caps :: rest) nP
    | d => d

def foldOutcome (ds : Array (Ix.Kernel.Declaration .anon)) : Option String :=
  match Ix.Kernel.Cached.checkDecls .verified [] ds with
  | .ok _ => none
  | .error (.invalid msg, _) => some (Ix.Kernel.Msg.render toString msg)
  | .error _ => some "other"

-- the prelude as it is installs every basis block, and the `pw` datum is forgiven
#guard foldOutcome (preludeWithEq id) == none
#guard foldOutcome (preludeWithEq (withFirstPw (.ifAllZero []))) == none
#guard Ix.Kernel.ConstantVal.matchesPin (md := .anon) Ix.Kernel.propextA Ix.Kernel.propextA
#guard Ix.Kernel.ConstantVal.matchesPin
  { Ix.Kernel.propextA with type := withFirstPw (.ifAllZero []) Ix.Kernel.propextA.type } Ix.Kernel.propextA

end Tests.Ix.Kernel.Contracts
