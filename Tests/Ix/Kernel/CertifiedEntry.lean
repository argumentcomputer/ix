import Ix.Kernel.Admission.Theorems
import Ix.Ixon.BlockOrder.Theorems
import Tests.Ix.Kernel.Reader

/-! # The certified Ixon API

The public entries — `Ix.Ixon.Admission.checkBytes`, and its
projection-reconstructing and block-ordering variants
`Ix.Ixon.Projection.checkBytes` and `Ix.Ixon.BlockOrder.checkBytes` — run
the verified checker behind the Ixon reader. These fixtures are the
reader fixtures (`Tests.Ix.Kernel.Reader`) through the public
names, the failure classification at the Ix API (`Admission.outcome`), a
theorem of the pinned `False` that is not accepted, and the public theorems
applied. The byte stage and the shared Ixon record fixtures are tested in
`Tests.Ix.Kernel.ByteAdmission`, projection reconstruction in
`Tests.Ix.Kernel.Projection`. -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader (isSingleton SingletonRead keyName keyName_injective)
open Tests.Ix.Kernel.Reader

namespace Tests.Ix.Kernel.CertifiedEntry

def check (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Except Ix.Ixon.Admission.Error Ix.Kernel.Env :=
  Ix.Ixon.Admission.checkBytes limits (encode cs) blobs

def accepted (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) : Bool :=
  (check cs blobs).isOk

def outcomeOf (cs : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray) := []) :
    Option Ix.Ixon.Admission.Outcome :=
  match check cs blobs with
  | .ok _ => none
  | .error e => some (e.outcome)

/-! ## The certified entry is the kernel entry -/

#guard accepted definitions
#guard accepted twoFixture
#guard accepted pFixture
#guard accepted [(address 40, quotIota)]
#guard accepted [(address 42, litEq)] [(address 41, ⟨#[2]⟩)]
-- a theorem in Ixon's canonical universe levels, which only the Géran
-- fallback of the level comparison equates (`RatFunc.liftOn_def`'s shape)
#guard (Ix.Ixon.Admission.checkBytes limits levelStream []).isOk
-- the empty stream installs the prelude
#guard match check [] with
  | .ok env => env.consts.length == 27
  | .error _ => false

/-! ## The Ix taxonomy of failures

A record the reader finds malformed and non-canonical bytes reject; every
checker verdict declines (a false equation is `invalid` to the checker, a
failed conversion search, which is not independent evidence of a wrong
input); a block whose recursor is missing declines at the reader; batch
limits decline. -/

-- a false equation
#guard outcomeOf [(address 10, idNat), (address 11, twoDef),
  (address 12, defn .thm (apps (ref 0 [0]) [ref 1, ref 2, ref 4]) (apps (ref 5 [0]) [ref 1, ref 4])
    [eq, nat, address 11, natSucc, natZero, eqRefl] [one])] == some .declined
-- a block without its recursor
#guard outcomeOf (twoFixture.take 4) == some .declined
-- a literal blob that is not supplied
#guard outcomeOf [(address 42, litEq)] == some .rejected
-- a non-canonical record
#guard match Ix.Ixon.Admission.checkBytes limits [(address 10, ⟨#[0xff]⟩)] [] with
  | .error e => e.outcome == .rejected
  | .ok _ => false
-- batch limits
#guard match Ix.Ixon.Admission.checkBytes { limits with maxRecords := 0 } (encode definitions) [] with
  | .error e => e.outcome == .declined
  | .ok _ => false

/-! ## Duplicate keys

Two records, or two blobs, under one address are malformed input: the byte
stage rejects them (`Ix.Ixon.Admission.uniqueKeys`) at the second
occurrence, before decoding, in all three byte entries, and the API
classifies that as a reject. The controls are the same inputs with distinct
keys. -/

-- a duplicate blob that a literal uses, the copies disagreeing
#guard match check [(address 42, litEq)] [(address 41, ⟨#[2]⟩), (address 41, ⟨#[3]⟩)] with
  | .error (.duplicate .blobs 1 a) => a == address 41
  | _ => false
#guard outcomeOf [(address 42, litEq)] [(address 41, ⟨#[2]⟩), (address 41, ⟨#[2]⟩)] == some .rejected
-- a duplicate blob that nothing uses
#guard match check definitions [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error (.duplicate .blobs 1 a) => a == address 43
  | _ => false
-- a duplicate constant: the same record again, or another record under its key
#guard match check (definitions ++ [(address 10, idNat)]) with
  | .error (.duplicate .records 3 a) => a == address 10
  | _ => false
#guard outcomeOf [(address 10, idNat), (address 10, twoDef)] == some .rejected
-- controls
#guard accepted [(address 42, litEq)] [(address 41, ⟨#[2]⟩), (address 43, ⟨#[3]⟩)]
#guard accepted definitions [(address 43, ⟨#[2]⟩)]
#guard accepted [(address 10, idNat)] [(address 10, ⟨#[2]⟩)]

/-! ## No theorem of the pinned `False`

`theorem bad : False := bad'` for any value: the record's type is a bare
reference to the prelude's `False`, which the reader names `False`
(`checkBytes_no_False_theorem`'s syntactic case,
`checkBytesWith_no_False_reference`). It is never accepted, whatever the
value. -/

def false_ := pinned "False"

#guard false_ != address 0
#guard !accepted [(address 50, defn .thm (ref 0) (ref 0) [false_])]
#guard !accepted [(address 50, defn .thm (ref 0) (lam (ref 0) (var 0)) [false_])]

/-! ## Projection reconstruction

The `Two` fixture with its projection records omitted: the recursor and the
ι theorem name the projections by their reconstructed addresses (the pure
BLAKE3 of their canonical encodings). -/

def twoI : Address := Ix.Ixon.Projection.address (iPrj (address 20))
def twoA : Address := Ix.Ixon.Projection.address (cPrj (address 20) 0)
def twoB : Address := Ix.Ixon.Projection.address (cPrj (address 20) 1)

def twoRecR : Ixon.Constant := { twoRec with refs := #[twoI, twoA, twoB] }
def twoIotaR : Ixon.Constant :=
  { twoIota with refs := #[eq, nat, address 24, natZero, natSucc, twoB, twoI, eqRefl] }

def omitted : List (Address × Ixon.Constant) :=
  [(address 20, twoBlock), (address 24, twoRecR), (address 25, twoIotaR)]

#guard (Ix.Ixon.Projection.checkBytes 16 limits (encode omitted) []).isOk
-- without reconstruction the projections are missing
#guard !accepted omitted
-- the projection request bound applies
#guard match Ix.Ixon.Projection.checkBytes 0 limits (encode omitted) [] with
  | .error (.reconstruction .limit) => true
  | _ => false

-- duplicate keys reject before reconstruction
#guard match Ix.Ixon.Projection.checkBytes 16 limits (encode omitted)
    [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error (.reconstruction (.admission (.duplicate .blobs 1 _))) => true
  | _ => false
#guard match Ix.Ixon.Projection.checkBytes 16 limits (encode (omitted ++ [(address 20, twoBlock)])) [] with
  | .error (.reconstruction (.admission (.duplicate .records 3 _))) => true
  | _ => false

/-! ## Block order -/

#guard (Ix.Ixon.BlockOrder.checkBytes 16 limits {} (encode omitted) []).isOk
#guard match Ix.Ixon.BlockOrder.checkBytes 16 limits {} (encode omitted)
    [(address 43, ⟨#[2]⟩), (address 43, ⟨#[2]⟩)] with
  | .error (.order (.admission (.duplicate .blobs 1 _))) => true
  | _ => false
#guard match Ix.Ixon.BlockOrder.checkBytes 16 limits {} (encode (omitted ++ [(address 20, twoBlock)])) [] with
  | .error (.order (.admission (.duplicate .records 3 _))) => true
  | _ => false
#guard match Ix.Ixon.BlockOrder.checkBytes 16 limits ⟨0, 0⟩ (encode omitted) [] with
  | .error (.order _) => true
  | _ => false

/-! ## The public theorems, applied -/

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Admission.checkBytes limits (encode definitions) [] = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ix.Ixon.Admission.checkBytes_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Admission.checkBytes limits records blobs = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  Ix.Ixon.Admission.checkBytes_no_proof_of_False V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Admission.checkBytes limits records blobs = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint, Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) :=
  Ix.Ixon.Admission.checkBytes_has_model_values V h

/-- Fidelity at a record: each accepted singleton record's declaration is
installed under its name with its kind. -/
example {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Admission.checkBytes limits records blobs = .ok env) :
    ∃ pins pre constants, Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
      ∀ owner c, (owner, c) ∈ constants → isSingleton c.info = true →
        ∃ st decl, SingletonRead (Ix.Ixon.Admission.streamContext pins pre constants blobs
          (fun _ => none)) st owner c decl ∧
          ∀ s, Ix.Kernel.IxonFold.declSkel decl = some s →
            ∃ ci ∈ env.consts, Ix.Kernel.Cached.ciSkel ci = s := by
  obtain ⟨pins, pre, _, _, _, _, _, _, constants, reading, installed⟩ :=
    Ix.Ixon.Admission.checkBytes_reading h
  refine ⟨pins, pre, constants, reading, fun owner c hmem hs => ?_⟩
  obtain ⟨st, decl, _, hread, _, _, hinst⟩ := installed.singleton hmem hs
  exact ⟨st, decl, hread, hinst⟩

/-- Key uniqueness at the API: no two records and no two blobs of accepted
bytes share an address, and no two of the decoded records the reader read
(`Installed.keys`). -/
example {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Admission.checkBytes limits records blobs = .ok env) :
    (records.map Prod.fst).Nodup ∧ (blobs.map Prod.fst).Nodup ∧
      ∃ pins pre natPins constants, Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Ixon.Admission.Installed pins pre natPins constants blobs (fun _ => none) env ∧
        (constants.map Prod.fst).Nodup := by
  obtain ⟨pins, pre, natPins, _, _, _, _, keys, constants, reading, installed⟩ :=
    Ix.Ixon.Admission.checkBytes_reading h
  exact ⟨keys.1, keys.2, pins, pre, natPins, constants, reading, installed, installed.keys⟩

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.Projection.checkBytes 16 limits records blobs = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ix.Ixon.Projection.checkBytes_has_model V h

example (V : Type) [Ix.Kernel.SetTheory V] {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)} {env : Ix.Kernel.Env}
    (h : Ix.Ixon.BlockOrder.checkBytes 16 limits {} records blobs = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Ix.Ixon.BlockOrder.checkBytes_has_model V h

example : Function.Injective keyName := fun _ _ h => keyName_injective h

end Tests.Ix.Kernel.CertifiedEntry
