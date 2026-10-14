import IxC.Kernel.Admission.Theorems
import Ix.Ixon.Authenticated.Theorems
import Tests.Ix.Kernel.Reader

/-! # The certified Ixon API

The public entries — `Ixon.Authenticated.checkBytes`, the certified entry
`Ix.Kernel.Admission.checkBytes` at the admission hash (BLAKE3), and its
projection-reconstructing and block-ordering variants
`Ixon.Authenticated.checkBytesProjection` and
`Ixon.Authenticated.checkBytesBlockOrder` — run the verified checker behind
the Ixon reader. These fixtures are the reader fixtures
(`Tests.Ix.Kernel.Reader`, re-keyed to their BLAKE3 addresses) through the
public names, the failure classification at the Ix API (`e.outcome`), a
theorem of the pinned `False` that is not accepted, and the public theorems
applied. The byte stage and the shared Ixon record fixtures are tested in
`Tests.Ix.Kernel.ByteAdmission`, projection reconstruction in
`Tests.Ix.Kernel.Projection`, authentication in
`Tests.Ix.Kernel.Authentication`. -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader (isSingleton SingletonRead keyName keyName_injective)
open Tests.Ix.Kernel.Reader

namespace Tests.Ix.Kernel.CertifiedEntry

def check (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Except Ix.Kernel.Admission.Error Ix.Kernel.Env :=
  let r := rekeyed cs blobs
  Ixon.Authenticated.checkBytes builtinBinding limits r.encoded r.blobs

def accepted (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Bool :=
  (check cs blobs).isOk

def outcomeOf (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Option Ix.Kernel.Admission.Outcome :=
  match check cs blobs with
  | .ok _ => none
  | .error e => some (e.outcome)

/-- A payload under its BLAKE3 address. -/
def authentic (bytes : ByteArray) : Address × ByteArray := (hash bytes, bytes)

/-! ## The certified entry is the kernel entry -/

#guard accepted definitions
#guard accepted twoFixture
#guard accepted pFixture
#guard accepted [(address 40, quotIota)]
#guard accepted [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]
-- a theorem in Ixon's canonical universe levels, which only the Géran
-- fallback of the level comparison equates (`RatFunc.liftOn_def`'s shape)
#guard (Ixon.Authenticated.checkBytes builtinBinding limits levelStream []).isOk
-- the empty stream installs the prelude
#guard match check [] with
  | .ok env => env.consts.length == 27
  | .error _ => false

/-! ## The Ix taxonomy of failures

A record the reader finds malformed, non-canonical bytes and a key that is
not the hash of its bytes reject; every checker verdict declines (a false
equation is `invalid` to the checker, a failed conversion search, which is
not independent evidence of a wrong input); a block whose recursor is
missing declines at the reader; batch limits decline. -/

-- a false equation
#guard outcomeOf [(address 10, idNat), (address 11, twoDef),
  (address 12, defn .thm (apps (ref 0 [0]) [ref 1, ref 2, ref 4]) (apps (ref 5 [0]) [ref 1, ref 4])
    [eq, nat, address 11, natSucc, natZero, eqRefl] [one])] == some .declined
-- a block without its recursor
#guard outcomeOf (twoFixture.take 4) == some .declined
-- a literal blob that is not supplied
#guard outcomeOf [(address 42, litEq)] == some .rejected
-- a non-canonical record
#guard match Ixon.Authenticated.checkBytes builtinBinding limits [authentic ⟨#[0xff]⟩] [] with
  | .error e => e.outcome == .rejected
  | .ok _ => false
-- a record or a blob whose key is not its hash
#guard match Ixon.Authenticated.checkBytes builtinBinding limits (encode definitions) [] with
  | .error e@(.mismatch .records 0 a) => a == address 10 && e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytes builtinBinding limits (rekeyed [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]).encoded
    [(address 41, ⟨#[2]⟩)] with
  | .error e@(.mismatch .blobs 0 a) => a == address 41 && e.outcome == .rejected
  | _ => false
-- batch limits
#guard match Ixon.Authenticated.checkBytes builtinBinding { limits with maxRecords := 0 } (rekeyed definitions).encoded [] with
  | .error e => e.outcome == .declined
  | .ok _ => false

/-! ## Duplicate keys

Two records, or two blobs, under one address are malformed input: the byte
stage rejects them (`Ix.Kernel.Admission.uniqueKeys`) at the second
occurrence, before authentication and decoding, in all three byte entries,
and the API classifies that as a reject. Two different payloads under one
authentic key are refused as duplicates, before the second is hashed. The
controls are the same inputs with distinct keys. -/

def two : Address × ByteArray := authentic ⟨#[2]⟩
def litRecords : Ix.Kernel.Admission.Records := (rekeyed [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]).encoded

-- a duplicate blob that a literal uses, the copies disagreeing
#guard match Ixon.Authenticated.checkBytes builtinBinding limits litRecords [two, (two.1, ⟨#[3]⟩)] with
  | .error (.duplicate .blobs 1 a) => a == two.1
  | _ => false
#guard outcomeOf [(address 42, litEq)] [(address 41, ⟨#[2]⟩), (address 41, ⟨#[2]⟩)] == some .rejected
-- a duplicate blob that nothing uses
#guard match check definitions [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error (.duplicate .blobs 1 a) => a == two.1
  | _ => false
-- a duplicate constant: the same record again, or another record under its key
#guard match check (definitions ++ [(address 10, idNat)]) with
  | .error (.duplicate .records 3 a) => a == (rekeyed definitions).rename (address 10)
  | _ => false
#guard match Ixon.Authenticated.checkBytes builtinBinding limits
    ((rekeyed [(address 10, idNat)]).encoded ++ [((rekeyed [(address 10, idNat)]).rename (address 10),
      Ixon.serConstant twoDef)]) [] with
  | .error e@(.duplicate .records 1 _) => e.outcome == .rejected
  | _ => false
-- controls
#guard accepted [(address 42, litEq)] [(address 41, ⟨#[2]⟩), (address 43, ⟨#[3]⟩)]
#guard accepted definitions [(address 43, ⟨#[2]⟩)]
#guard accepted [(address 10, idNat)] [(address 10, Ixon.serConstant idNat)]

/-! ## No theorem of `False`

`theorem bad : False := bad'` for any value: the record's type is a bare
reference to the prelude's `False`, which the default table binds to
`False`'s role and the reader names by its role key `False`
(`checkBytes_no_False_theorem`'s syntactic case,
`checkBytesWith_no_False_reference`). It is never accepted, whatever the
value. -/

def false_ := bound Ix.Kernel.Role.false

#guard false_ != address 0
#guard !accepted [(address 50, defn .thm (ref 0) (ref 0) [false_])]
#guard !accepted [(address 50, defn .thm (ref 0) (lam (ref 0) (var 0)) [false_])]

/-! ## Projection reconstruction

The `Two` fixture with its projection records omitted: the recursor and the
ι theorem name the projections by their BLAKE3 addresses, which are the
addresses reconstruction derives. -/

def omitted : Ix.Kernel.Admission.Records :=
  encode ((rekeyed twoFixture).records.filter fun (_, c) => !Ix.Kernel.Ingress.isProjection c.info)

def twoKey : Address := (rekeyed twoFixture).rename (address 20)
def twoAgain : Ix.Kernel.Admission.Records := omitted ++ (omitted.filter (·.1 == twoKey))

#guard omitted.length == 3 && twoAgain.length == 4
#guard (Ixon.Authenticated.checkBytesProjection builtinBinding 16 limits omitted []).isOk
-- without reconstruction the projections are missing
#guard !(Ixon.Authenticated.checkBytes builtinBinding limits omitted []).isOk
-- the projection request bound applies
#guard match Ixon.Authenticated.checkBytesProjection builtinBinding 0 limits omitted [] with
  | .error e@(.reconstruction .limit) => e.outcome == .declined
  | _ => false

-- duplicate keys reject before reconstruction
#guard match Ixon.Authenticated.checkBytesProjection builtinBinding 16 limits omitted
    [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error e@(.reconstruction (.admission (.duplicate .blobs 1 _))) => e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesProjection builtinBinding 16 limits twoAgain [] with
  | .error (.reconstruction (.admission (.duplicate .records 3 _))) => true
  | _ => false

/-! ## Block order -/

#guard (Ixon.Authenticated.checkBytesBlockOrder builtinBinding 16 limits {} omitted []).isOk
#guard match Ixon.Authenticated.checkBytesBlockOrder builtinBinding 16 limits {} omitted
    [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error e@(.order (.admission (.duplicate .blobs 1 _))) => e.outcome == .rejected
  | _ => false
#guard match Ixon.Authenticated.checkBytesBlockOrder builtinBinding 16 limits {} twoAgain [] with
  | .error (.order (.admission (.duplicate .records 3 _))) => true
  | _ => false
#guard match Ixon.Authenticated.checkBytesBlockOrder builtinBinding 16 limits ⟨0, 0⟩ omitted [] with
  | .error (.order _) => true
  | _ => false

/-! ## The public theorems, applied -/

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes builtinBinding limits (rekeyed definitions).encoded [] = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ixon.Authenticated.checkBytes_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes builtinBinding limits records blobs = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  Ixon.Authenticated.checkBytes_no_proof_of_False V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes builtinBinding limits records blobs = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint, Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) :=
  Ix.Kernel.Admission.checkBytes_has_model_values V h

/-- Authentication at the API: every record and blob of accepted bytes is
stored under the BLAKE3 hash of its bytes, and so is the role table's
binding section. -/
example {binding : Ix.Kernel.Admission.Binding} {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes binding limits records blobs = .ok env) :
    ((∀ entry ∈ records, entry.1 = Address.blake3Pure entry.2) ∧
      ∀ entry ∈ blobs, entry.1 = Address.blake3Pure entry.2) ∧
      Address.blake3Pure binding.bytes = binding.address :=
  Ixon.Authenticated.checkBytes_authentic h

/-- Fidelity at a record: each accepted singleton record's declaration is
installed under its name with its kind. -/
example {binding : Ix.Kernel.Admission.Binding} {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes binding limits records blobs = .ok env) :
    ∃ t pre constants, Ix.Kernel.Admission.RecordsRead limits records constants ∧
      ∀ owner c, (owner, c) ∈ constants → isSingleton c.info = true →
        ∃ st decl, SingletonRead (Ix.Kernel.Admission.streamContext t pre constants blobs
          (fun _ => none)) st owner c decl ∧
          ∀ s, Ix.Kernel.Cached.declSkel decl = some s →
            ∃ ci ∈ env.consts, Ix.Kernel.Cached.ciSkel ci = s := by
  obtain ⟨t, pre, _, _, _, _, _, constants, _, reading, _, installed⟩ :=
    Ixon.Authenticated.checkBytes_reading h
  refine ⟨t, pre, constants, reading, fun owner c hmem hs => ?_⟩
  obtain ⟨st, decl, _, _, hread, _, _, hinst⟩ := installed.singleton hmem hs
  exact ⟨st, decl, hread, hinst⟩

/-- Key uniqueness at the API: no two records and no two blobs of accepted
bytes share an address, and no two of the decoded records the reader read
(`Installed.keys`), each of which is stored under the BLAKE3 hash of its
canonical encoding. -/
example {binding : Ix.Kernel.Admission.Binding} {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytes binding limits records blobs = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup ∧
      ∃ t pre constants, Ix.Kernel.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Admission.Installed t pre constants blobs (fun _ => none) env ∧
        (constants.map Prod.fst).Nodup ∧
        ∀ entry ∈ constants, entry.1 = Address.blake3Pure (Ixon.serConstant entry.2) := by
  obtain ⟨t, pre, _, _, _, keys, _, constants, _, reading, hashed, installed⟩ :=
    Ixon.Authenticated.checkBytes_reading h
  exact ⟨keys.1, keys.2, t, pre, constants, reading, installed, installed.keys, hashed⟩

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytesProjection builtinBinding 16 limits records blobs = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ixon.Authenticated.checkBytesProjection_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Kernel.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ixon.Authenticated.checkBytesBlockOrder builtinBinding 16 limits {} records blobs = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ixon.Authenticated.checkBytesBlockOrder_has_model V h

example : Function.Injective keyName := fun _ _ h => keyName_injective h

end Tests.Ix.Kernel.CertifiedEntry
