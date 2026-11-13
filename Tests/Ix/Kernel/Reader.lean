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
  const (.defn ⟨kind, safety, {}, lvls.toUInt64, typ, value⟩) refs univs

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
  .defn ⟨.defn, safety, {}, 0, typ, value⟩

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

#guard (recurDeps abBlock ⟨.defn, .safe, {}, 0, ref 0, .app (recur 1) (ref 1)⟩).toList == [1]
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
    #[⟨false, 0, 0, 0, 0, .inherited, recur 0⟩, ⟨false, 0, 1, 0, 0, .inherited, recur 0⟩]⟩]) [] [.succ one]

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
-- a one-type block without its recursor reads, and the checker declines it
-- (no route of the executable checker installs a block without a recursor)
#guard match run (twoFixture.take 4) with
  | .error (.kernel _ _) => true
  | _ => false

/-! ## A structure with a projection function

`structure P where x : Nat; y : Nat`, `P.x := fun self => self.1` (an Ixon
`prj`), and `P.x (P.mk zero (succ zero)) = zero` by the projection's
reduction. -/

def pBlock : Ixon.Constant :=
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0,
    #[⟨false, 0, 0, 0, 2, .inherited, all (ref 0) (all (ref 0) (recur 0))⟩]⟩]) [nat] [one]

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
    #[⟨false, 1, 0, 1, 0, .inherited, all (sort 0) (.app (recur 0 [1]) (var 0))⟩,
      ⟨false, 1, 1, 1, 2, .inherited, all (sort 0) (all (var 0) (all (.app (recur 0 [1]) (var 1))
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
  const (.muts #[.indc ⟨false, 0, 0, 0, sort 0, #[⟨false, 0, 0, 0, 0, .inherited, recur 0⟩]⟩]) [] [one]

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
    #[⟨false, 0, 0, 0, 1, .inherited, all (.app (ref 0 [1]) (ref 1)) (recur 0)⟩]⟩])
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
  ("0bdb5fabb1be6c48976ff4d61f3bc58625d243679ae47426caef366b853a246e",
    "c10100010100910000020001000100910071b010000101010293001071b01171b0120131" ++
    "0001000201c0c0030000000100000100010000020003000000"),
  ("596eb9e8fc4ad54152e94895873e08302eee617e4b90a1187bfd3eb25d10dc3b",
    "c1010000010091010102000000010192017121000071300010b00000010101920110b001" ++
    "7130001101487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b025b1dcdbf5d" ++
    "e002000100030000000100000100020000000200020000"),
  ("79b4065e8b2074d44d012ace5d98db9928a7393e8290ed9bd1d492e5c295e0e6",
    "c10100000000010100000000019171210000712001300030000002487a90b33c7dcd5f34" ++
    "34aa04338e1a5b290552cbe922eeb59b025b1dcdbf5de049be024a6d47ba31711fe2b696" ++
    "63238912874a1372fdac57efa1cada7196368902000100010001000100"),
  ("2891eaf9458f3e1886691768cf583cc3a917d32aa947ec4ea5643127db118533",
    "c3020001000003059801b0b6b4b7b5b801b800b120007118001001018801b0b6b4b7b5b8" ++
    "01b800b1b3721510b802020001000003059801b0b6b4b7b5b801b800b1b3711710020088" ++
    "00b0b6b4b7b5b801b800b113028802b0b6b4b7b5b801b800b1b2b3741411107801310201" ++
    "180118001716151413121178013101011801180017161514131210020001000003059801" ++
    "b0b6b4b7b5b801b800b1b271161002018801b0b6b4b7b5b801b800b1b3721210b8020188" ++
    "01b0b6b4b7b5b801b800b120007211107801310001180017161514131211100b91200001" ++
    "9220007117107116722006200011712002200071210100b291b201711271210500b291b3" ++
    "0192b371121071147120031192b3711510711572200720001194b2b37114117116117117" ++
    "73210400b2131278013101011800171615141312111008414f5c25fa6fb91079fecf8a54" ++
    "f670e1d6344ac838c0d8c7f73707c911ff4761487a90b33c7dcd5f3434aa04338e1a5b29" ++
    "0552cbe922eeb59b025b1dcdbf5de049be024a6d47ba31711fe2b69663238912874a1372" ++
    "fdac57efa1cada7196368957bf90f1f654269bf21ff68568ed3f5cbef1780891ea489b93" ++
    "e2de6b866a41d963cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd007" ++
    "3e01abacc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818faea" ++
    "8b1112eb84cd2b6249f4a27f10f654649c7d645cdb9bbc7ef1e59ae2924c34fd9d7d381e" ++
    "9c4e7865b0580b7ed09851e19d983d8a80d896f3bb360d373b6b4e0200c00f0000001002" ++
    "010003000201000300020100030002010003000201000201000300020100030002010003" ++
    "000201000001001002010003000201000300020100030002010003000201000201000300" ++
    "020100030002010003000201000002001002010003000201000300020100030002010003" ++
    "000201000201000300020100030002010003000201000003000f02010003000201000300" ++
    "020100030002010003000201000201000300020100030002010003000004001102010003" ++
    "000201000300020100030002010003000201000201000300020100030002010003000201" ++
    "000201000005001002010003000201000300020100030002010003000201000201000300" ++
    "020100030002010003000201000006001002010003000201000300020100030002010003" ++
    "000201000201000300020100030002010003000201000007001002010003000201000300" ++
    "020100030002010003000201000201000300020100030002010003000201000100000100" ++
    "010100020201000201000104000100010600010001070002020100020100010800020201" ++
    "0002010001090004020100020100020100020100"),
  ("39a6c6927ab95fb25de0100f88b1dea2f8291f2169968638f720e3da52197c0e",
    "d10002010001029500b2b1b5b4b302008400b2b1b511028600b2b1b51371b01473121110" ++
    "7532000102151413121006210002711071210202119171b0100171131071b0139312b4b3" ++
    "71147321010215121103487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b02" ++
    "5b1dcdbf5de063cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd0073e" ++
    "01abacc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818fa0301" ++
    "c1c0c1050000000702010002010003000201000201000300020100000100060201000201" ++
    "000300020100020100030000020008020100020100030002010002010003000201000201" ++
    "00010200010001050003020100020100020100"),
  ("bfb31e00437a03eb08616348710e586b68e0df38309d224781a3b542d5627737",
    "c202000101000204980001b1b5b6b3b2b803b77116100201880001b1b5b6b3b2b803b800" ++
    "7214107800b801171615141312111001880001b1b5b6b3b2b80316711310020001010002" ++
    "04980001b1b5b6b3b2b803b80071151002008701b1b5b6b3b2b8031102880101b1b5b6b3" ++
    "b2b803b771b471b0177412111078003100021800171615141312117800b8011800171615" ++
    "141312100c20019171b0100271127121030071b0149113711372200414102100009171b4" ++
    "71b011029271b471b0127111107113722005141171b01671b4b73101027116119471b015" ++
    "b800b802b80271177321020071b01801131206487a90b33c7dcd5f3434aa04338e1a5b29" ++
    "0552cbe922eeb59b025b1dcdbf5de049be024a6d47ba31711fe2b69663238912874a1372" ++
    "fdac57efa1cada7196368963cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bf" ++
    "ca4fd0073e01abacc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a971178" ++
    "6818faea8b1112eb84cd2b6249f4a27f10f654649c7d645cdb9bbc7ef1e59ae2924c34fd" ++
    "9d7d381e9c4e7865b0580b7ed09851e19d983d8a80d896f3bb360d373b6b4e03000100c0" ++
    "0b0000000d02010002010003000201000300020100030002010003000201000201000300" ++
    "0201000001000d0201000201000300020100030002010003000201000300020100020100" ++
    "03000201000002000d020100020100030002010003000201000300020100030002010002" ++
    "010003000201000003000d02010002010003000201000300020100030002010003000201" ++
    "0002010003000201000004000c0201000201000300020100030002010003000201000300" ++
    "02010002010003000005000e020100020100030002010003000201000300020100030002" ++
    "010002010003000201000201000101000100010300010201000105000100010600020201" ++
    "00020100010b0004020100020100020100020100"),
  ("15b637b3ace8c59237c26f1db0aa5e48bac097b8bd0220f875ffe1932bbabc22",
    "d5012891eaf9458f3e1886691768cf583cc3a917d32aa947ec4ea5643127db1185330000" ++
    "0000"),
  ("29d8b49e0eeac51da491b43c7766020444e64da585208a27c30db03840aed069",
    "d5022891eaf9458f3e1886691768cf583cc3a917d32aa947ec4ea5643127db1185330000" ++
    "0000"),
  ("414f5c25fa6fb91079fecf8a54f670e1d6344ac838c0d8c7f73707c911ff4761",
    "d60079b4065e8b2074d44d012ace5d98db9928a7393e8290ed9bd1d492e5c295e0e60000" ++
    "0000"),
  ("487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b025b1dcdbf5de0",
    "d6000bdb5fabb1be6c48976ff4d61f3bc58625d243679ae47426caef366b853a246e0000" ++
    "0000"),
  ("49be024a6d47ba31711fe2b69663238912874a1372fdac57efa1cada71963689",
    "d600596eb9e8fc4ad54152e94895873e08302eee617e4b90a1187bfd3eb25d10dc3b0000" ++
    "0000"),
  ("57bf90f1f654269bf21ff68568ed3f5cbef1780891ea489b93e2de6b866a41d9",
    "d4000079b4065e8b2074d44d012ace5d98db9928a7393e8290ed9bd1d492e5c295e0e600" ++
    "000000"),
  ("5f8684a7536dc6b8412e27da2364ed74f00e4c3e276f5f31e3274adc5002b699",
    "d5002891eaf9458f3e1886691768cf583cc3a917d32aa947ec4ea5643127db1185330000" ++
    "0000"),
  ("63cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd0073e01ab",
    "d400010bdb5fabb1be6c48976ff4d61f3bc58625d243679ae47426caef366b853a246e00" ++
    "000000"),
  ("70a0538d9954719a509dfd5171d70813b3e258f46439775503a8809c38e04c19",
    "d501bfb31e00437a03eb08616348710e586b68e0df38309d224781a3b542d56277370000" ++
    "0000"),
  ("acc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818fa",
    "d400000bdb5fabb1be6c48976ff4d61f3bc58625d243679ae47426caef366b853a246e00" ++
    "000000"),
  ("ea8b1112eb84cd2b6249f4a27f10f654649c7d645cdb9bbc7ef1e59ae2924c34",
    "d40001596eb9e8fc4ad54152e94895873e08302eee617e4b90a1187bfd3eb25d10dc3b00" ++
    "000000"),
  ("f77412ab1008e2db606af0861e63b97e825215809f7f95cdd2ce60f06523cbfe",
    "d500bfb31e00437a03eb08616348710e586b68e0df38309d224781a3b542d56277370000" ++
    "0000"),
  ("fd9d7d381e9c4e7865b0580b7ed09851e19d983d8a80d896f3bb360d373b6b4e",
    "d40000596eb9e8fc4ad54152e94895873e08302eee617e4b90a1187bfd3eb25d10dc3b00" ++
    "000000")]

def lTreeStream : Ix.Kernel.Admission.Records :=
  lTreeRecords.filterMap fun (a, b) => do pure (← addressOfHex a, ← bytesOfHex b)

def lTreeBlock : Address := (addressOfHex "79b4065e8b2074d44d012ace5d98db9928a7393e8290ed9bd1d492e5c295e0e6").getD (address 0)
def lNodeBlock : Address := (addressOfHex "596eb9e8fc4ad54152e94895873e08302eee617e4b90a1187bfd3eb25d10dc3b").getD (address 0)

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
  ("8aa2daf017aa6ec909bf429e62d95082ad09ad64646d02fea36ea66aa85522a9",
    "c101000102009202b0010100010002029402b01171111072310002131201911000000300" ++
    "40c00100c0030000000300000300000100050000030000000100000100"),
  ("1780b7e5408ad328b414d3c74059c84310a820b99155e515dcda5a49d1d76ab1",
    "d0090293b1b1b372b2121183b1b1b310049200031072210102b081b0200071210201b172" ++
    "b2111003251883bf2eea40cd0b067b2e897533e149dfb82f82cb0cc45990157226cb8cda" ++
    "6920881fa6260902eda1fad260df22a267b39817ba9e3426254984c5bfa587e29d3c7bcf" ++
    "cc8f1f1661bce87d371a5da0d5188c1bc05def21d4aa176138c91b100401c04001c18002" ++
    "c0c1804002c001c1c1c10600000007010300010300010300030000010006010300010300" ++
    "01030001000002020101020101010100030300000300010200010300010300010300"),
  ("78f7145fbf5cdfed9b00cc64af0548ef0406093ae7358e744f27906da42041ce",
    "d10002020001019502b2b3b472b01312b101028602b2b3b4137113107212111005210002" ++
    "7112109110009172b01110019212b171127421010214131110026920881fa6260902eda1" ++
    "fad260df22a267b39817ba9e3426254984c5bfa587e2a71ae4b11356c10cab01e7115363" ++
    "a7a03c41da063313cf7353e54a0579dabe470300c0c10500000008020100020100030002" ++
    "010003000201000300020100000100090201000201000300020100030002010003000201" ++
    "000201000102000100010300010001040002020100020100"),
  ("b01e04997b6e892e62d98ec1ea03d9563a1fddd04f8389fddb9a8a7d23228f79",
    "d101010000010193b1b02000711210010082b1b01002711020019120000002251883bf2e" ++
    "ea40cd0b067b2e897533e149dfb82f82cb0cc45990157226cb8cda99329f6422ed47ec7c" ++
    "6fa53674e43b2d439367baf8dbff1a8e98a3243dc3ce4801c00300000004020100030002" ++
    "01000201000001000302010003000201000101000100"),
  ("251883bf2eea40cd0b067b2e897533e149dfb82f82cb0cc45990157226cb8cda",
    "d60009f6413b8ec5c2472bba0c0994e5299bdcc5e88d5ab76a7c7c762251cfbcac490000" ++
    "0000"),
  ("6920881fa6260902eda1fad260df22a267b39817ba9e3426254984c5bfa587e2",
    "d6008aa2daf017aa6ec909bf429e62d95082ad09ad64646d02fea36ea66aa85522a90000" ++
    "0000"),
  ("99329f6422ed47ec7c6fa53674e43b2d439367baf8dbff1a8e98a3243dc3ce48",
    "d4000009f6413b8ec5c2472bba0c0994e5299bdcc5e88d5ab76a7c7c762251cfbcac4900" ++
    "000000"),
  ("a71ae4b11356c10cab01e7115363a7a03c41da063313cf7353e54a0579dabe47",
    "d400008aa2daf017aa6ec909bf429e62d95082ad09ad64646d02fea36ea66aa85522a900" ++
    "000000")]

/-- The theorem's record. -/
def levelTheorem : String := "1780b7e5408ad328b414d3c74059c84310a820b99155e515dcda5a49d1d76ab1"

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
-- the index (`fallbackIndexed`): the copied block does not read with the prelude's recursor; it
-- reads without one (`unindexedShape`), which is not what the prelude read, so the copy declines
-- (`preludeCopy`)
#guard
  let cx := contextOf (md := .anon) builtinTable (natCopy false).toArray [] builtinPre.records
  match boundRef .nat with
  | some r => (buildIndex cx.store builtinPre.records).blocks.contains r.block && !cx.index.blocks.contains r.block
  | none => false
#guard match readStream hash builtinTable builtinPre (natCopy false) [] with
  | .error .preludeCopy => true
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

#guard refuses { builtinTable with version := Ix.Kernel.specVersion + 1 }
  s!"version {Ix.Kernel.specVersion + 1}"
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
