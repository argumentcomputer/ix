module

public import Ix.Ixon

@[expose] public section

namespace Ix.HostAdmission

/-- The logical part uses the standard-three theory. A tier additionally has
opaque typing, including its permitted unsafe axioms, with no model for them. -/
inductive Kind where
  | logical
  | tiered (logicalRoot tierRoot : Option Address)
  deriving BEq, DecidableEq, Repr

/-- No external artifact assumptions. This does not assert a model for tier
axioms, and does not adopt resource-v1's uncertified assumption policy. -/
inductive Policy where
  | noExternalArtifactAssumptions
  deriving BEq, DecidableEq, Repr

structure Statement where
  kind : Kind
  hostSpecDigest : Address
  bindingHash : Address
  contentRoot : Address
  main : Option Address
  policy : Policy := .noExternalArtifactAssumptions
  deriving BEq, DecidableEq, Repr

namespace Statement

open Ixon

def magic : ByteArray := "IXHC".toUTF8
def version : UInt8 := 1

def putOption : Option Address → PutM Unit
  | none => putU8 0
  | some a => do putU8 1; Serialize.put a

def getOption : GetM (Option Address) := do
  match ← getU8 with
  | 0 => return none
  | 1 => return some (← Serialize.get)
  | _ => throw "host statement: invalid optional-root tag"

def check (s : Statement) : Except String Unit := do
  let parts := match s.kind with | .logical => #[] | .tiered l t => l.toArray ++ t.toArray
  for a in #[s.hostSpecDigest, s.bindingHash, s.contentRoot] ++ s.main.toArray ++ parts do
    unless a.hash.size == 32 do throw "host statement: address width is not 32 bytes"

/-- IXHC,version1,object4,kind,policy,digests,content root,main,then tier roots.
Fixed widths and option tags preserve the distinction between none and zero. -/
def bytes (s : Statement) : Except String ByteArray := do
  s.check
  return runPut do
    putBytes magic; putU8 version; putU8 Env.OBJECT_FORMAT
    putU8 (match s.kind with | .logical => 0 | .tiered .. => 1)
    putU8 (match s.policy with | .noExternalArtifactAssumptions => 0)
    Serialize.put s.hostSpecDigest; Serialize.put s.bindingHash; Serialize.put s.contentRoot
    putOption s.main
    match s.kind with | .logical => pure () | .tiered l t => putOption l *> putOption t

def get : GetM Statement := do
  unless (← getBytes 4) == magic do throw "host statement: expected IXHC"
  unless (← getU8) == version do throw "host statement: unsupported version"
  unless (← getU8) == Env.OBJECT_FORMAT do throw "host statement: unsupported checked object format"
  let kind ← getU8
  unless kind == 0 || kind == 1 do throw "host statement: unknown admission kind"
  unless (← getU8) == 0 do throw "host statement: unsupported external-assumption policy"
  let hostSpecDigest ← Serialize.get
  let bindingHash ← Serialize.get
  let contentRoot ← Serialize.get
  let main ← getOption
  let kind ← if kind == 0 then pure Kind.logical else do pure (Kind.tiered (← getOption) (← getOption))
  return { kind, hostSpecDigest, bindingHash, contentRoot, main }

def decode (raw : ByteArray) : Except String Statement := do
  let statement ← runGetExact get raw
  unless (← statement.bytes) == raw do throw "host statement: noncanonical bytes"
  return statement

def address (s : Statement) : Except String Address := Address.admissionHash <$> s.bytes

end Statement
end Ix.HostAdmission
