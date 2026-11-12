import IxC.Kernel.Admission.Theorems
import IxC.Fixtures.Authentic
import Ix.Address.Admission

/-! # Ixon records through the verified checker

End-to-end fixtures for `Ix.Kernel.Admission.checkBytes` at the admission
hash (BLAKE3): the fixtures are written with stand-in keys and re-keyed to
their BLAKE3 addresses before admission (`Tests.Ix.Kernel.Authentic.rekey`),
with role tables renamed and installed names spelled back in the stand-in
keys, so the expectations below are stated in the stand-ins. Canonical
record bytes are preflighted, authenticated, decoded, read by `Ix.Kernel.Reader`,
prepared with the Ixon prelude (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, the
quotient package, `And`, `Bool`, from the compiled Init's own records) and
checked by `Ix.Kernel.Cached.checkDecls .verified`.

Positive: a definition and a definition over it with a theorem by delta, a
definition block stored out of dependency order with a theorem by delta
through both members, an
inductive with its separately stored recursor and an ι-reduction, a
structure with a projection function and a projection reduction, the
quotient's lift reduction, a Nat literal against its constructors, a String
literal against its `String.ofList` expansion (over test constants bound as
the string-literal support), a compiled block nested through a container
that is itself nested, whose auxiliary motives come with the container
family's instance before its head, and a compiled theorem
whose universe levels Ix's compiler stored in canonical form, which only the
Géran fallback of the level comparison equates (the `RatFunc.liftOn_def`
shape).

Negative: a block of another shape stored under the real `Eq`'s address is
refused, because the address is not its hash; a definition
block with an ill-typed member is rejected by the checker; a `partial` block
whose members call each other (the shape of Lean's `_unsafe_rec` companions)
declines with its safety, as a partial singleton does, and the same block
marked safe declines as mutually recursive; a definition of
the wrong shape bound to `Nat.add` is not accepted under that name (and is
accepted unbound); a copy of `Nat`'s contents at another address is not
named `Nat`; malformed tables, duplicate records (byte stage and reader)
and unsafe declarations; the role table's refusals (`RoleTable.check`, the
binding section's decoder, the admission of an unauthentic section). -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.Kernel.Admission
open Tests.Ix.Kernel.Authentic (rekey Rekeyed)

namespace Tests.Ix.Kernel.Reader

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
  ⟨info, #[], refs.toArray, univs.toArray, #[]⟩

def defn (kind : Ix.DefKind) (typ value : E) (refs : List Address) (univs : List Ixon.Univ := [])
    (lvls : Nat := 0) (safety : Ix.DefinitionSafety := .safe) : Ixon.Constant :=
  const (.defn ⟨kind, safety, lvls.toUInt64, typ, value⟩) refs univs

def iPrj (block : Address) (i : Nat := 0) : Ixon.Constant := const (.iPrj ⟨i.toUInt64, block⟩) [] []
def cPrj (block : Address) (c : Nat) (i : Nat := 0) : Ixon.Constant :=
  const (.cPrj ⟨i.toUInt64, c.toUInt64, block⟩) [] []

def limits : Ix.Kernel.Admission.Limits := ⟨1024, 1024, 1 <<< 24, 1 <<< 20, 1 <<< 16⟩

def encode (cs : List (Address × Ixon.Constant)) : Ix.Kernel.Admission.Records :=
  cs.map fun (a, c) => (a, Ixon.serConstant c)

def builtinTable : Ix.Kernel.RoleTable := match defaultTable with | .ok t => t | .error _ => default
def builtinPre : Prelude .anon := match builtinPrelude with | .ok p => p | .error _ => default

/-- The admission hash: BLAKE3 (the Rust backend executes it). -/
def hash : ByteArray → Address := Address.admissionHash

/-- A fixture under its BLAKE3 keys. -/
def rekeyed (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Rekeyed :=
  rekey hash cs blobs

/-- A table's section, authenticated under the admission hash. -/
def bindingOf (t : Ix.Kernel.RoleTable) : Binding := ⟨hash t.toBytes, t.toBytes⟩

def builtinBinding : Binding := bindingOf builtinTable

/-- A role table over a fixture's stand-in keys, on its BLAKE3 keys. -/
def renameTable (r : Rekeyed) (t : Ix.Kernel.RoleTable) : Ix.Kernel.RoleTable :=
  { t with bound := t.bound.map fun (role, a) => (role, r.rename a) }

/-- The default table with some roles bound to other addresses. -/
def rebind (pairs : List (Ix.Kernel.Role × Address)) : Ix.Kernel.RoleTable :=
  { builtinTable with bound := builtinTable.bound.map fun (role, a) =>
      match pairs.find? (·.1 == role) with
      | some (_, a') => (role, a')
      | none => (role, a) }

/-- A key with a fixture's stand-in keys in place of its BLAKE3 keys. -/
def unrename (r : Rekeyed) : CName .anon → CName .anon
  | .id a => .id (r.original a)
  | .role ro => .role ro
  | .aux k d => .aux (unrename r k) d

def run (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (table : Ix.Kernel.RoleTable := builtinTable) : Except Error (Ix.Kernel.Env .anon) :=
  let r := rekeyed cs blobs
  checkBytesWith hash (bindingOf (renameTable r table)) builtinPre limits r.encoded r.blobs

def accepts (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (table : Ix.Kernel.RoleTable := builtinTable) : Bool :=
  (run cs blobs table).isOk

def namesOf (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := [])
    (table : Ix.Kernel.RoleTable := builtinTable) : List String :=
  match run cs blobs table with
  | .ok env => env.consts.map fun c => toString (unrename (rekeyed cs blobs) c.name)
  | .error _ => []

/-- How the input key of the record at `a` prints. -/
def idString (a : Address) : String := toString (Ix.Kernel.Key.id (md := .anon) a)

/-- The address the default table binds a role to (a prelude record). -/
def bound (r : Ix.Kernel.Role) : Address := (builtinTable.addressOf? r).getD (address 0)

/-- The reference a role's bound address denotes. -/
def boundRef (r : Ix.Kernel.Role) : Option (ConstRef Address) :=
  resolve (storeOf builtinPre.records) (bound r)

def eq := bound .eq
def eqRefl := bound .eqRefl
def nat := bound .nat
def natZero := bound .natZero
def natSucc := bound .natSucc
def quotMk := bound .quotMk
def quotLift := bound .quotLift

/-! ## The prelude and the tables -/

#guard defaultTable.isOk && (builtinPrelude (md := .anon)).isOk && defaultBinding.isOk
-- the default table: every role bound, well formed, its section canonical and
-- committed under its BLAKE3 hash
#guard builtinTable.bound.size == 108 && builtinTable.check.isOk
#guard (Ix.Kernel.RoleTable.ofBytes builtinTable.toBytes).isSome
#guard match defaultBinding with
  | .ok b => hash b.bytes == b.address && b.bytes == builtinTable.toBytes
  | .error _ => false
-- Every equation has evidence of an allowed kind: the original fifteen Nat
-- operations retain their fixed kinds; twenty-nine definitions add equations
-- whose unconditional entries may be definitional or checked proofs.
#guard builtinTable.evidence.size == 44 && builtinTable.evidence.all fun (r, es) =>
  let allowed := (Ix.Kernel.Role.spec (md := .anon) r).evidenceAllowed
  es.size == allowed.length &&
    (es.toList.zip allowed).all fun (e, kind) => kind.all e.isDefeqKind
#guard
  let operations := builtinTable.evidence.filter fun (r, _) =>
    r.spec (md := .anon) matches .ops ..
  operations.size == 15 && operations.all fun (r, es) =>
    let kinds := (r.spec (md := .anon)).evidenceKinds
    es.size == kinds.length && (es.toList.zip kinds).all fun (e, kind) => e.isDefeqKind kind
-- Over the prelude alone, rows containing only definitional evidence resolve.
-- A proof needs records supplied by the stream; one unresolved proof declines
-- its entire row, including any definitional entries beside it.
#guard
  let ev := evidenceOf (contextOf builtinTable #[] [] (builtinPre.records ++ builtinPre.evidence) builtinPre.blobs)
    builtinPre.state builtinTable
  ev.length == 44 && ev.all fun (r, es) =>
    let declared := ((builtinTable.evidence.find? (·.1 == r)).map (·.2)).getD #[]
    let onlyDefinitional := declared.all fun | .defeq => true | .proof _ => false
    es.length == (if onlyDefinitional then declared.size else 0) &&
      es.all fun | .defeq => true | .proof _ => false
#guard (builtinPre.ix.decls.toList.map (fun d => toString <$> Ix.Kernel.Frontend.preludeKey d)) ==
  ["Eq", "Nat", "PUnit", "Empty", "False", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound",
   "And", "Bool"].map some
#guard [eq, eqRefl, nat, natZero, natSucc, quotMk, quotLift].all (· != address 0)
-- the stream's copies of the prelude's records read to what the prelude read
-- (`State.keepsPrelude`): the prelude's own records as a stream pass; under a prelude
-- whose state differs at `Nat`'s key (the declared type, or the parsed block's index
-- count), they are refused
#guard match readStream hash builtinTable builtinPre builtinPre.records.toList [] with
  | .ok _ => true
  | .error _ => false
#guard
  let tampered : Prelude .anon := { builtinPre with state := { builtinPre.state with
    constTypes := builtinPre.state.constTypes.insert (.role .nat) ([], .sort .zero) } }
  match readStream hash builtinTable tampered builtinPre.records.toList [] with
  | .error .preludeCopy => true
  | _ => false
#guard
  let natKey : Ix.Kernel.Key .anon := .role .nat
  let tampered : Prelude .anon := { builtinPre with state := { builtinPre.state with
    indBlocks := match builtinPre.state.indBlocks[natKey]? with
      | some b => builtinPre.state.indBlocks.insert natKey
          { b with types := b.types.map fun t => { t with nIdx := t.nIdx + 1 } }
      | none => builtinPre.state.indBlocks } }
  match readStream hash builtinTable tampered builtinPre.records.toList [] with
  | .error .preludeCopy => true
  | _ => false
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
#guard (namesOf definitions).contains (idString (address 10))
#guard (namesOf definitions).contains (idString (address 12))
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
-- the members are keyed by their projection records
#guard (namesOf abFixture).contains (idString (address 101)) &&
  (namesOf abFixture).contains (idString (address 102))
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

`inductive Two : Type 1 | a | b` and `Two.rec.{u}`, as the compiler lays
them out: the block, its projection records, the recursor as its own record.
(In `Type` its block would be `Bool`'s, byte for byte, and so would be the
prelude's `Bool` under its content address.) -/

def twoBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0,
    #[⟨false, 0, 0, 0, 0, recur 0⟩, ⟨false, 0, 1, 0, 0, recur 0⟩]⟩]) [] [.succ one]

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
-- the recursor is keyed by its own record, a constructor by its projection record
#guard (namesOf twoFixture).contains (idString (address 24))
#guard (namesOf twoFixture).contains (idString (address 23))
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
def stringTable : Ix.Kernel.RoleTable :=
  rebind [(.string, address 71), (.stringOfList, address 74), (.list, address 51),
    (.listNil, address 52), (.listCons, address 53), (.char, address 61), (.charOfNat, address 64)]

/-- The role keys a table binds over fixture records backed by the prelude. -/
def namesUnder (t : Ix.Kernel.RoleTable) (cs : List (Address × Ixon.Constant)) :
    Std.HashMap (ConstRef Address) (CName .anon) :=
  (bindingsOf (storeOf cs.toArray (storeOf builtinPre.records)) t).names

#guard accepts strings strBlobs stringTable
-- a string of another length is not that expansion (the test `Char.ofNat` is
-- constant, so only the length is observable)
#guard !accepts strings [(address 80, "abc".toUTF8), (address 81, ⟨#[97]⟩), (address 82, ⟨#[98]⟩)] stringTable
-- without the support pinned on these constants, the literal does not check
#guard !accepts strings strBlobs

/-! ## The constants a literal references

A record that contains a literal depends on the records of the constants the
literal references (`literalEdges`): the `Nat` block for a `Nat` literal, and
also the string-support records for a string literal. -/

def natBlock : Address := match boundRef .nat with
  | some r => r.block
  | none => address 0

#guard literalKinds strEq == (true, true) && literalKinds litEq == (true, false) &&
  literalKinds charOfNat == (false, false)
#guard (literalEdges (namesUnder stringTable strings) strings.toArray)[address 75]? ==
  some #[natBlock, address 70, address 74, address 50, address 60, address 64]
#guard ((literalEdges (namesUnder stringTable strings) strings.toArray)[address 74]?).isNone
#guard (literalEdges (namesUnder builtinTable []) #[(address 42, litEq)])[address 42]? == some #[natBlock]

/-! ## A block nested through a container that is itself nested

The records Ix's compiler produces for `Tests.Ix.Kernel.EntryCaseDefs.LTree`
(with `LTree`, its recursors, `LNode`'s recursors and `List.rec`), in the
environment check order with the projections last: the records
`kernel-entry-cases` submits for its `nested-through-nested` case, as
`lake exe kernel-entry-cases --records nested-through-nested` prints them
(Ixon v5):

    inductive LNode (α : Type) where
      | node : List (LNode α) → LNode α
      | leaf : α → LNode α
    inductive LTree where
      | node : List (LNode LTree) → LTree

`LTree.rec`'s auxiliary motives are `[List (LNode LTree), LNode LTree]`: an
instance of the container family before the family's head. The compiler keeps
Lean's recursor, so this is the order in which Lean's kernel discovers the
nested occurrences (`LTree.node`'s field, then that auxiliary's `cons`), and it
does not depend on addresses; a block nested through the head itself
(`node : LNode LTree → LTree`) has the head first. Container groups formed in motive order would
both claim motive 1 here (`List`'s singleton group and `LNode`'s family), and
the block would be rejected with `duplicate declaration
ix.<LTree>.0._model._impl.pack_0`, as Mathlib's `Lean.Elab.InfoTree` would
be (with `pack_1`). The modeller forms the groups largest family first
(`IxC/Kernel/Frontend/InModel/Nested.lean`, an adapted file). -/

/-- (address, canonical record bytes) -/
def lTreeRecords : List (String × String) := [
  ("5942ca5af2aa7e4e7501daa87fad2e57b9d836b9e256637bb0a9265319ac366a",
    "c101000101009117000002000100010091170071b010000101010293170017101771b011" ++
    "71b01201310001000201c0c0030000000100000100010000020003000000"),
  ("4edf6a66d815ac61e976c01600baa2f1ef5ade43bd1dcbf8cbe9b92b97bac65a",
    "c1010000010091170101020000000101921701177121000071300010b000000101019217" ++
    "011710b0017130001101e4c9a8e4fb921be9d9b7ad0cdaaa4195ac2d0942141f2bfbea47" ++
    "e804f97591ff02000100030000000100000100020000000200020000"),
  ("ba1ebe6443c07e7ecb6666bfd572c9c6c24aab2163d7d7b5fe4b8ca47c431a20",
    "c2020001010002049800170117b117b517b617b317b217b80317b7711610020188000701" ++
    "07b107b507b607b307b207b80307b8007214107800b80117161514131211100188000701" ++
    "07b107b507b607b307b207b8030716711310020001010002049800170117b117b517b617" ++
    "b317b217b80317b800711510020087070107b107b507b607b307b207b803110288010701" ++
    "07b107b507b607b307b207b80307b70771b471b017741211107800310002180017161514" ++
    "1312117800b8011800171615141312100c2000911771b0100271127121020071b0149117" ++
    "1371137220031410210500911771b471b01102921771b471b01217711110711372200414" ++
    "1171b01671b4b7310102711611941771b01517b80017b80217b80271177321010071b018" ++
    "011312066fbf19ae76baef7b12bc687dd5b38b4cf7941168bec8dc5bfd9602fb5ecb8908" ++
    "80c5ba913d234543c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2892f3d35" ++
    "a4788c60b18e722f14215603a59fad868b0b8bdad68954fc312fabfbbb8e7fe8ea186448" ++
    "4d31377be8a08275b15ab01779ed5884b92a5a66d25d503bcd0b1953f6c05a79058d027d" ++
    "e92613356fa31eb633aeeba6eda511238e3da387e4c9a8e4fb921be9d9b7ad0cdaaa4195" ++
    "ac2d0942141f2bfbea47e804f97591ff03000100c00b0000000d02010002010003000201" ++
    "0003000201000300020100030002010002010003000201000001000d0201000201000300" ++
    "02010003000201000300020100030002010002010003000201000002000d020100020100" ++
    "030002010003000201000300020100030002010002010003000201000003000d02010002" ++
    "0100030002010003000201000300020100030002010002010003000201000004000c0201" ++
    "00020100030002010003000201000300020100030002010002010003000005000e020100" ++
    "020100030002010003000201000300020100030002010002010003000201000201000101" ++
    "00010001030001020100010500010001060002020100020100010b000402010002010002" ++
    "0100020100"),
  ("d723978ed00a313bc30a9fc3b85bcddb1e3ca56e1f91f9f044e9297efee1dd66",
    "c10100000000010100000000019117712101007120003000300000026fbf19ae76baef7b" ++
    "12bc687dd5b38b4cf7941168bec8dc5bfd9602fb5ecb8908e4c9a8e4fb921be9d9b7ad0c" ++
    "daaa4195ac2d0942141f2bfbea47e804f97591ff02000100010001000100"),
  ("9b78c391adde6b480db7c886edbfef653234713b0bf2fa86692a2aaaf9410dad",
    "c302000100000305980117b017b617b417b717b517b80117b80017b11720077118001001" ++
    "01880107b007b607b407b707b507b80107b80007b107b3721510b8020200010000030598" ++
    "0117b017b617b417b717b517b80117b80017b117b37117100200880007b007b607b407b7" ++
    "07b507b80107b80007b11302880207b007b607b407b707b507b80107b80007b107b207b3" ++
    "741411107801310201180118001716151413121178013101011801180017161514131210" ++
    "02000100000305980117b017b617b417b717b517b80117b80017b117b271161002018801" ++
    "07b007b607b407b707b507b80107b80007b107b3721210b80201880107b007b607b407b7" ++
    "07b507b80107b80007b10720077211107801310001180017161514131211100b91172007" ++
    "0192172007177117107116722004200711712000200771210600b29117b2017112712102" ++
    "00b29117b3019217b3177112107114712003119217b31771151071157220052007119417" ++
    "b217b31771141117711611711773210100b2131278013101011800171615141312111008" ++
    "6fbf19ae76baef7b12bc687dd5b38b4cf7941168bec8dc5bfd9602fb5ecb890880c5ba91" ++
    "3d234543c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2892f3d35a4788c60" ++
    "b18e722f14215603a59fad868b0b8bdad68954fc312fabfb9853c008aab7393da3dd8ddb" ++
    "2342eb3a79d9ee2cffddd8246dcfd19f26f83e53bb8e7fe8ea1864484d31377be8a08275" ++
    "b15ab01779ed5884b92a5a66d25d503bcd0b1953f6c05a79058d027de92613356fa31eb6" ++
    "33aeeba6eda511238e3da387e4c9a8e4fb921be9d9b7ad0cdaaa4195ac2d0942141f2bfb" ++
    "ea47e804f97591ffe904a2772ee41e025dece6585d087b50144b4481cc1e261c7ca829af" ++
    "aed112fc0200c00f00000010020100030002010003000201000300020100030002010002" ++
    "010003000201000300020100030002010000010010020100030002010003000201000300" ++
    "020100030002010002010003000201000300020100030002010000020010020100030002" ++
    "010003000201000300020100030002010002010003000201000300020100030002010000" ++
    "03000f020100030002010003000201000300020100030002010002010003000201000300" ++
    "020100030000040011020100030002010003000201000300020100030002010002010003" ++
    "000201000300020100030002010002010000050010020100030002010003000201000300" ++
    "020100030002010002010003000201000300020100030002010000060010020100030002" ++
    "010003000201000300020100030002010002010003000201000300020100030002010000" ++
    "070010020100030002010003000201000300020100030002010002010003000201000300" ++
    "020100030002010001000001000101000202010002010001040001000106000100010700" ++
    "020201000201000108000202010002010001090004020100020100020100020100"),
  ("dbb8e83be90a8d9aab31f4fe8d601d60d855b4935b97244039515a8d454607be",
    "d100020100010295170017b217b117b517b4b3020084070007b207b107b5110286070007" ++
    "b207b107b507130771b01473121110753200010215141312100621020271107121010211" ++
    "911771b0100171131071b01393171217b417b37114732100021512110380c5ba913d2345" ++
    "43c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2892f3d35a4788c60b18e72" ++
    "2f14215603a59fad868b0b8bdad68954fc312fabfbe4c9a8e4fb921be9d9b7ad0cdaaa41" ++
    "95ac2d0942141f2bfbea47e804f97591ff0301c1c0c10500000007020100020100030002" ++
    "010002010003000201000001000602010002010003000201000201000300000200080201" ++
    "000201000300020100020100030002010002010001020001000105000302010002010002" ++
    "0100"),
  ("6d03b57234448a78d48883f5e005837a88dcade307a3696e10605e25e5ab2871",
    "d500ba1ebe6443c07e7ecb6666bfd572c9c6c24aab2163d7d7b5fe4b8ca47c431a200000" ++
    "0000"),
  ("6fbf19ae76baef7b12bc687dd5b38b4cf7941168bec8dc5bfd9602fb5ecb8908",
    "d6004edf6a66d815ac61e976c01600baa2f1ef5ade43bd1dcbf8cbe9b92b97bac65a0000" ++
    "0000"),
  ("719f3e390e25d58716c7847143a1614d15f6e49e45d7afafbe6ab395eb7a2ea4",
    "d501ba1ebe6443c07e7ecb6666bfd572c9c6c24aab2163d7d7b5fe4b8ca47c431a200000" ++
    "0000"),
  ("80c5ba913d234543c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2",
    "d400015942ca5af2aa7e4e7501daa87fad2e57b9d836b9e256637bb0a9265319ac366a00" ++
    "000000"),
  ("850f859e37d74234b7465722b8eeec99d58b1181b1643dd5e8285418e20935e8",
    "d5029b78c391adde6b480db7c886edbfef653234713b0bf2fa86692a2aaaf9410dad0000" ++
    "0000"),
  ("892f3d35a4788c60b18e722f14215603a59fad868b0b8bdad68954fc312fabfb",
    "d400005942ca5af2aa7e4e7501daa87fad2e57b9d836b9e256637bb0a9265319ac366a00" ++
    "000000"),
  ("9853c008aab7393da3dd8ddb2342eb3a79d9ee2cffddd8246dcfd19f26f83e53",
    "d40000d723978ed00a313bc30a9fc3b85bcddb1e3ca56e1f91f9f044e9297efee1dd6600" ++
    "000000"),
  ("bb8e7fe8ea1864484d31377be8a08275b15ab01779ed5884b92a5a66d25d503b",
    "d400014edf6a66d815ac61e976c01600baa2f1ef5ade43bd1dcbf8cbe9b92b97bac65a00" ++
    "000000"),
  ("c19eaeeb50391f7b17442277a781275f5de88a38ed9e2c9cf795a75f4c294d6e",
    "d5019b78c391adde6b480db7c886edbfef653234713b0bf2fa86692a2aaaf9410dad0000" ++
    "0000"),
  ("cd0b1953f6c05a79058d027de92613356fa31eb633aeeba6eda511238e3da387",
    "d400004edf6a66d815ac61e976c01600baa2f1ef5ade43bd1dcbf8cbe9b92b97bac65a00" ++
    "000000"),
  ("ce4ca767f8134aaa2eaac43a65eaa461070740059829308e4ede7370b7b58c51",
    "d5009b78c391adde6b480db7c886edbfef653234713b0bf2fa86692a2aaaf9410dad0000" ++
    "0000"),
  ("e4c9a8e4fb921be9d9b7ad0cdaaa4195ac2d0942141f2bfbea47e804f97591ff",
    "d6005942ca5af2aa7e4e7501daa87fad2e57b9d836b9e256637bb0a9265319ac366a0000" ++
    "0000"),
  ("e904a2772ee41e025dece6585d087b50144b4481cc1e261c7ca829afaed112fc",
    "d600d723978ed00a313bc30a9fc3b85bcddb1e3ca56e1f91f9f044e9297efee1dd660000" ++
    "0000")]

def lTreeStream : Ix.Kernel.Admission.Records :=
  lTreeRecords.filterMap fun (a, b) => do pure (← addressOfHex a, ← bytesOfHex b)

def lTreeBlock : Address := (addressOfHex "d723978ed00a313bc30a9fc3b85bcddb1e3ca56e1f91f9f044e9297efee1dd66").getD (address 0)
def lNodeBlock : Address := (addressOfHex "4edf6a66d815ac61e976c01600baa2f1ef5ade43bd1dcbf8cbe9b92b97bac65a").getD (address 0)

/-- The stream's records and its reading context, as the entry builds them. -/
def lTreeContext : Option (List (Address × Ixon.Constant) × Ctx .anon) := do
  let constants ← (Ix.Kernel.Admission.decodeRecords limits lTreeStream).toOption
  pure (constants, streamContext hash builtinTable builtinPre constants [] (fun _ => none))

/-- The key the stream's reading gives the constant at `r`. -/
def lTreeKey (r : ConstRef Address) : Option (CName .anon) := do
  let (_, cx) ← lTreeContext
  (cx.memberKey r).toOption

/-- The keys of the recursors that eliminate `LTree`'s block, in motive order. -/
def lTreeRecKeys : List (CName .anon) := Id.run do
  let some (_, cx) := lTreeContext | return []
  let some shape := cx.index.blocks[lTreeBlock]? | return []
  return shape.recs.toList.filterMap fun r => (cx.memberKey r).toOption

/-- The reader's state and declarations after the stream. -/
def lTreeRead : Option (State .anon × Array (Ix.Kernel.Declaration .anon)) := do
  let (constants, cx) ← lTreeContext
  (readRecords cx builtinPre.state constants.toArray).toOption

/-- The carriers' heads of `LTree.rec`'s motives, in motive order, as the
modeller reads them. -/
def lTreeMotiveHeads : Option (List String) := do
  let (st, _) ← lTreeRead
  let b ← st.indBlocks[← lTreeKey (.member lTreeBlock 0)]?
  let t0 ← b.types.head?
  -- the recursor of the first motive
  let r0 ← b.recs.head?
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
    | .basisDecl k => (k.decls (md := .anon)).map (toString ·.toConstantVal.name)
  | none => []

#guard lTreeStream.length == lTreeRecords.length && lTreeRecords.length == 19
-- the order that exercises the grouping: `List (LNode LTree)` before `LNode LTree`
#guard lTreeMotiveHeads ==
  some [toString (lTreeKey (.member lTreeBlock 0)).get!, "List",
    toString (lTreeKey (.member lNodeBlock 0)).get!]
-- the modeller's records introduce every name once (`pack_0` was emitted twice)
#guard !lTreeNames.isEmpty && lTreeNames.eraseDups.length == lTreeNames.length
#guard (lTreeNames.filter
  (· == toString (lTreeKey (.member lTreeBlock 0)).get! ++ "._model._impl.pack_0")).length == 1
-- and the block, its three recursors and the container's install
#guard match checkBytesWith hash builtinBinding builtinPre limits lTreeStream [] with
  | .ok env =>
    let names := env.consts.map (·.name)
    (lTreeKey (.member lTreeBlock 0)).any names.contains && lTreeRecKeys.length == 3 &&
      lTreeRecKeys.all names.contains && (lTreeKey (.member lNodeBlock 0)).any names.contains
  | .error _ => false

/-! ## Universe levels in canonical form

The records Ix's compiler produces for
`Tests.Ix.Kernel.EntryCaseDefs.levelCanon` (with `Subtype.rec` and `True.rec`),
in the check order with the projections last, without the prelude's `Eq`
records: `lake exe kernel-entry-cases --records level-comparison` (Ixon v5):

    theorem levelCanon.{w, x} {a b : {_f : (K : Type w) → (P : Sort x) → P // True}}
        (h : a = b) : a = b := h

Lean elaborates `Subtype.{W}` and `Eq.{max 1 W}`, `W = imax (w+2) (imax (x+1)
x)`. Ixon stores each level as the canonical form of its semantic class
(`Ix/IxonUniv.lean`): `Subtype.{imax (max (w+2) (x+1)) x}` and
`Eq.{max (x+1) (imax (w+2) x)}`. The checker infers the `Subtype`'s type,
`Sort (max (imax (max (w+2) (x+1)) x) 1)`, where the `Eq` expects
`Sort (max (x+1) (imax (w+2) x))`. The two levels are equal at every
valuation. Nanoda's comparison (the official kernel's `leq`, which the
kernel's `Level.leqCore` implements) establishes only `≤`: the converse
`x+1 ≤ max (imax … x) 1` splits the `max`, and each branch fails on its own
(at `x = 0` and at `x = 1`); without a fallback the theorem is refused with
`application type mismatch`, as Mathlib's `RatFunc.liftOn_def` and
`RatFunc.liftOn'_def` (unfolding lemmas of `irreducible_def`) would be.
That case of the comparison falls back on Géran's sublevels
(`IxC/Kernel/LevelGeran.lean`, a decision procedure,
`Ix.Kernel.Level.Geran.leq_iff`), and the theorem is accepted. The reader
converts levels as stored. -/

/-- (address, canonical record bytes) -/
def levelRecords : List (String × String) := [
  ("09f6413b8ec5c2472bba0c0994e5299bdcc5e88d5ab76a7c7c762251cfbcac49",
    "c101000000000001000000000030000000010000"),
  ("ec2e08f795359cba63506d935faf0f2f64ab38a5366d70e6ff7534097a4d610b",
    "c1010001020092170217b00101000100020294170217b017111771111072310002131201" ++
    "9117100000030040c00100c0030000000300000300000100050000030000000100000100"),
  ("2fad885906165c6f02cfc5b8be7abb7128e7c09e83ff868b8d59baa21be2ce4f",
    "d10101000001019317b117b017200071121001008207b107b01002711020019117200000" ++
    "02251883bf2eea40cd0b067b2e897533e149dfb82f82cb0cc45990157226cb8cda99329f" ++
    "6422ed47ec7c6fa53674e43b2d439367baf8dbff1a8e98a3243dc3ce4801c00300000004" ++
    "02010003000201000201000001000302010003000201000101000100"),
  ("4f0148e40f2b086ed87e0b6d07a33ce70af67870210121c6ef9b008576c310df",
    "d100020200010195170217b217b317b41772b01312b1010286070207b207b307b4071307" ++
    "711310721211100521000271121091171000911772b011100192171217b1711274210102" ++
    "14131110021c1d53c72556073d2ad3f45656213cedb0e2b9fa21d936a5046df80cd457c7" ++
    "347f7339d7a96dedc0d65cd672c7d2dcece5344bdcace6edc5baa522efd458d0460300c0" ++
    "c10500000008020100020100030002010003000201000300020100000100090201000201" ++
    "000300020100030002010003000201000201000102000100010300010001040002020100" ++
    "020100"),
  ("e00709dc90d79800344bc9d85bf181b27e0da7c9523ba1c5a5b2a3379f9c5fae",
    "d009029317b117b117b372b212118307b107b107b3100492170017031072210002b08107" ++
    "b0200171210201b172b21110031c1d53c72556073d2ad3f45656213cedb0e2b9fa21d936" ++
    "a5046df80cd457c734251883bf2eea40cd0b067b2e897533e149dfb82f82cb0cc4599015" ++
    "7226cb8cda8283e2ba6471c8318a8637d7346b54fef85c5e7eae35df4b2d482915e02c41" ++
    "5d0401c04001c18002c0c1804002c001c1c1c10600000007010300010300010300030000" ++
    "010006010300010300010300010000020201010201010101000303000003000102000103" ++
    "00010300010300"),
  ("1c1d53c72556073d2ad3f45656213cedb0e2b9fa21d936a5046df80cd457c734",
    "d600ec2e08f795359cba63506d935faf0f2f64ab38a5366d70e6ff7534097a4d610b0000" ++
    "0000"),
  ("251883bf2eea40cd0b067b2e897533e149dfb82f82cb0cc45990157226cb8cda",
    "d60009f6413b8ec5c2472bba0c0994e5299bdcc5e88d5ab76a7c7c762251cfbcac490000" ++
    "0000"),
  ("7f7339d7a96dedc0d65cd672c7d2dcece5344bdcace6edc5baa522efd458d046",
    "d40000ec2e08f795359cba63506d935faf0f2f64ab38a5366d70e6ff7534097a4d610b00" ++
    "000000"),
  ("99329f6422ed47ec7c6fa53674e43b2d439367baf8dbff1a8e98a3243dc3ce48",
    "d4000009f6413b8ec5c2472bba0c0994e5299bdcc5e88d5ab76a7c7c762251cfbcac4900" ++
    "000000")]

/-- The theorem's record. -/
def levelTheorem : String := "e00709dc90d79800344bc9d85bf181b27e0da7c9523ba1c5a5b2a3379f9c5fae"

def levelStream : Ix.Kernel.Admission.Records :=
  levelRecords.filterMap fun (a, b) => do pure (← addressOfHex a, ← bytesOfHex b)

/-- The theorem's level parameters as the reader numbers them. -/
def lw : Ix.Kernel.Level := .param 0
def lx : Ix.Kernel.Level := .param 1
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
  let φ : Ix.Kernel.LevelParam → Nat := fun n => if n == 0 then i else if n == 1 then j else 0
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
#guard match checkBytesWith hash builtinBinding builtinPre limits levelStream [] with
  | .ok env => (env.consts.map (toString ·.name)).contains
      (idString ((addressOfHex levelTheorem).getD (address 0)))
  | .error _ => false

/-! ## Negative: pinned names on constants of another shape -/

/-- A one-constructor `Type` stored under the real `Eq` block's address, with
its recursor over the real `Eq`/`Eq.refl` projection records: the address is
not the block's hash, so the entry refuses it before the reader names it
`Eq` (by address). -/
def eqBlock : Address := match boundRef .eq with
  | some r => r.block
  | none => address 0

def fakeEq : List (Address × Ixon.Constant) :=
  [(eqBlock, unitBlock), (address 90, unitRec eq eqRefl)]

#guard match checkBytesWith hash builtinBinding builtinPre limits (encode fakeEq) [] with
  | .error e@(.mismatch .records 0 a) => a == eqBlock && e.outcome == .rejected
  | _ => false

/-- The same block under its own address, with its projection records and
recursor, and a pin table that names it `Eq` in place of Init's: its reading
changes the prelude's entries at `Eq`, so the prelude-copy check declines it
before the kernel's reserved-name check. -/
def ownEq : List (Address × Ixon.Constant) :=
  [(address 89, unitBlock), (address 88, iPrj (address 89)), (address 87, cPrj (address 89) 0),
   (address 90, unitRec (address 88) (address 87))]

def eqTable : Ix.Kernel.RoleTable :=
  rebind [(.eq, address 88), (.eqRefl, address 87), (.eqRec, address 90)]

#guard match run ownEq (table := eqTable) with
  | .error e@.preludeCopy => e.outcome == .declined
  | _ => false

/-- `fun n m => n` pinned as `Nat.add` is not certified, so not accepted under
that name; unpinned, it is an ordinary definition. -/
def fakeAdd : Ixon.Constant :=
  defn .defn (all (ref 0) (all (ref 0) (ref 0))) (lam (ref 0) (lam (ref 0) (var 1))) [nat]

def addTable : Ix.Kernel.RoleTable := rebind [(.natAdd, address 91)]

#guard !accepts [(address 91, fakeAdd)] (table := addTable)
#guard accepts [(address 91, fakeAdd)]

/-- Keys attach to addresses, not to contents: `Nat`'s block stored at another
address is not keyed as `Nat`. -/
def natBlockRecord : Ixon.Constant := Id.run do
  let some r := boundRef .nat | return default
  let some (_, c) := builtinPre.records.find? (·.1 == r.block) | return default
  return c

-- its member is keyed by the address its projection record would have (none is
-- in the input), under the entry's hash; without the hash it has no key
#guard
  let cx := contextOf (md := .anon) builtinTable #[(address 92, natBlockRecord)] [] builtinPre.records
    (reconstruct := Ix.Kernel.Admission.projectionAddress hash)
  let projection := Ix.Kernel.Admission.projectionAddress hash cx.store (.member (address 92) 0)
  match cx.memberKey (.member (address 92) 0) with
  | .ok (.id a) => projection == some a && a != address 92
  | _ => false
#guard
  let cx := contextOf (md := .anon) builtinTable #[(address 92, natBlockRecord)] [] builtinPre.records
  match cx.memberKey (.member (address 92) 0) with
  | .error (.declined _) => true
  | _ => false

/-- The prelude's record at `a`, if it has one. -/
def preludeRecord (a : Address) : List (Address × Ixon.Constant) :=
  (builtinPre.records.find? (·.1 == a)).toList

/-- `Nat`'s family copied from the prelude byte for byte, at the prelude's own addresses: its
block, its projection records and, `withRec`, its recursor. -/
def natCopy (withRec : Bool) : List (Address × Ixon.Constant) :=
  match boundRef .nat with
  | some r => ([r.block, nat, natZero, natSucc] ++ (if withRec then [bound .natRec] else [])).flatMap preludeRecord
  | none => []

#guard (natCopy true).length == 5 && (natCopy false).length == 4
-- a stream copying the family reads with its own recursor
#guard match readStream hash builtinTable builtinPre (natCopy true) [] with
  | .ok _ => true
  | .error _ => false
-- without it, the prelude's recursor, which the analysis files under the copied block, is left out of
-- the index (`fallbackIndexed`): the copied block declines instead of reading with the prelude's
-- recursor
#guard
  let cx := contextOf (md := .anon) builtinTable (natCopy false).toArray [] builtinPre.records
  match boundRef .nat with
  | some r => (buildIndex cx.store builtinPre.records).blocks.contains r.block && !cx.index.blocks.contains r.block
  | none => false
#guard match readStream hash builtinTable builtinPre (natCopy false) [] with
  | .error (.read _ (.declined _)) => true
  | _ => false

/-! ## A recursor of a block only the fallback supplies

A recursor record is read with its block. A record the analysis files under a block the input
does not supply is read by nothing, so it is admitted only as the fallback's own record at its
address; any other declines, whatever its rules say. -/

/-- The prelude's `Nat.rec` record. -/
def natRecRecord : Option Ixon.Constant := (preludeRecord (bound .natRec)).head?.map (·.2)

/-- `Nat.rec`'s record with the right-hand sides of its two rules swapped: its type, and so its
analysis, is the prelude's, and its rules are ill-typed. -/
def swappedNatRec : Option Ixon.Constant := do
  let c ← natRecRecord
  let .recr r := c.info | none
  let (some r0, some r1) := (r.rules[0]?, r.rules[1]?) | none
  pure { c with info := .recr { r with rules := #[{ r0 with rhs := r1.rhs }, { r1 with rhs := r0.rhs }] } }

#guard natRecRecord.isSome && swappedNatRec.isSome && swappedNatRec != natRecRecord
-- the prelude's own record, alone, is accepted
#guard natRecRecord.any fun c => accepts [(address 71, c)]
-- the swapped record declines, alone and as a block of recursors
#guard swappedNatRec.any fun c =>
  declineReason [(address 71, c)] == some "recursor whose inductive block is not in the input"
#guard swappedNatRec.any fun c => match c.info with
  | .recr r => declineReason [(address 71, { c with info := .muts #[.recr r] })] ==
      some "recursor whose inductive block is not in the input"
  | _ => false
-- beside a copy of its block, the swapped record is read, and its rules fail
#guard swappedNatRec.any fun c =>
  match boundRef .nat with
  | some r =>
    let cs := ([r.block, nat, natZero, natSucc].flatMap preludeRecord) ++ [(address 71, c)]
    !accepts cs && (declineReason cs).isNone
  | none => false

-- The keys are computed ahead (`Ctx.keys`): every record address has its key,
-- an unbound singleton its own address and a bound reference its role's, and
-- every reference its address
#guard
  let cx := contextOf (md := .anon) builtinTable #[(address 93, idNat)] [] builtinPre.records
  let natRef := boundRef .nat
  cx.keys.byAddress[address 93]? == some (.id (address 93)) &&
    cx.keys.address[ConstRef.member (address 93) 0]? == some (address 93) &&
    (cx.memberKey (.member (address 93) 0)).toOption == some (.id (address 93)) &&
    natRef.isSome && natRef.all fun r => (cx.memberKey r).toOption == some (.role .nat)

/-! ## Negative: malformed and unsupported records -/

-- the same address twice: the byte stage rejects it (`uniqueKeys`),
-- and the reader rejects it in decoded records (`readRecords_nodup`)
#guard match run [(address 10, idNat), (address 10, idNat)] with
  | .error (.duplicate .records 1 a) => a == (rekeyed [(address 10, idNat)]).rename (address 10)
  | _ => false
#guard match checkConstantsWith hash builtinTable builtinPre
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
-- a non-canonical byte string under its own hash fails at decoding; under
-- any other key it fails at authentication, before decoding
#guard match checkBytesWith hash builtinBinding builtinPre limits [(hash ⟨#[0xff]⟩, ⟨#[0xff]⟩)] [] with
  | .error (.decode 0 _ _) => true
  | _ => false
#guard match checkBytesWith hash builtinBinding builtinPre limits [(address 10, ⟨#[0xff]⟩)] [] with
  | .error (.mismatch .records 0 a) => a == address 10
  | _ => false

/-! ## The role table's own refusals

`RoleTable.check`: the version, injectivity in both directions, closure
under blocks and dependencies, and evidence exactly the bound operations',
of the kinds their equations fix. -/

def drop (t : Ix.Kernel.RoleTable) (rs : List Ix.Kernel.Role) : Ix.Kernel.RoleTable :=
  { t with bound := t.bound.filter (!rs.contains ·.1),
           evidence := t.evidence.filter (!rs.contains ·.1) }

def refuses (t : Ix.Kernel.RoleTable) (why : String) : Bool :=
  match t.check with
  | .error e => (e.splitOn why).length > 1
  | .ok () => false

#guard refuses { builtinTable with version := 6 } "version 6"
#guard refuses { builtinTable with bound := builtinTable.bound.push (.nat, address 1) } "bound twice"
#guard refuses (rebind [(.natAdd, bound .natSub)]) "bound to two roles"
#guard refuses (drop builtinTable [.eqRefl]) "its block's"
#guard refuses (drop builtinTable [.natPred]) "a dependency"
#guard refuses { builtinTable with evidence := builtinTable.evidence.filter (·.1 != .natDiv) }
  "without evidence"
#guard refuses { builtinTable with evidence := builtinTable.evidence.push (.nat, #[]) }
  "has no equations"
#guard refuses { builtinTable with evidence := builtinTable.evidence.map fun (r, es) =>
    (r, if r == .natDiv then es.map fun _ => .defeq else es) } "does not match"
#guard refuses { builtinTable with evidence := builtinTable.evidence.map fun (r, es) =>
    (r, if r == .natAdd then es.pop else es) } "does not match"
-- String operations need their literal support. Removing that support alone
-- fails; removing the operations with it leaves a well-formed partial table.
#guard refuses (drop builtinTable [.string, .stringOfList]) "a dependency"
#guard (drop builtinTable [.string, .stringOfList, .stringDecEq,
  .stringToByteArray, .stringAppend, .stringUtf8ByteSize, .stringBack]).check.isOk

/-! ## The binding section

Canonical decoding (`RoleTable.ofBytes_eq_some_iff`): the encoder's output
decodes back; trailing bytes, another tag, roles out of order are refused. The
entry admits a section only under the hash of its bytes, decoded and well
formed (`admitBinding`), before it reads any record. -/

#guard (Ix.Kernel.RoleTable.ofBytes (builtinTable.toBytes.push 0)).isNone
#guard (Ix.Kernel.RoleTable.ofBytes ⟨builtinTable.toBytes.data.set! 1 0x02⟩).isNone
#guard (Ix.Kernel.RoleTable.ofBytes
  { builtinTable with bound := builtinTable.bound.reverse }.toBytes).isNone
#guard match checkBytesWith hash ⟨address 1, builtinTable.toBytes⟩ builtinPre limits [] [] with
  | .error (.binding (.mismatch a)) => a == address 1
  | _ => false
#guard match checkBytesWith hash (bindingOf { builtinTable with version := Ix.Kernel.specVersion + 1 })
    builtinPre limits [] [] with
  | .error (.binding (.malformed _)) => true
  | _ => false
#guard match checkBytesWith hash ⟨hash ⟨#[0xe8]⟩, ⟨#[0xe8]⟩⟩ builtinPre limits [] [] with
  | .error (.binding .decode) => true
  | _ => false

/-! ## The keys a reading gives -/

example {cx : Ctx .anon} {a : Address} {k : CName .anon} (h : cx.keyAt a = .ok k) :
    keyOfAddress cx.store cx.roles a = some k :=
  Ctx.keyAt_eq_ok.mp h

/-- info: 'Ix.Kernel.Reader.Ctx.keyAt_eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ctx.keyAt_eq_ok

/-! ## Model existence -/

example (V : Type) [Ix.Kernel.SetTheory V] {binding : Binding} {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (h : run strings strBlobs stringTable = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytesWith_has_model V h

end Tests.Ix.Kernel.Reader
