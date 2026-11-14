module

public import Ix.SpecDigest

@[expose] public section

/-! # Reading the specification digest's bytes back

`specBytes` (`Ix/SpecDigest.lean`) encodes what the digest commits to
(`Committed`). This module reads those bytes back into a `Committed`, so that
`IxVM.RoleSpecGen` can render the circuit's role specifications from the bytes
alone: every value the rendered file holds then comes from the bytes the
digest is the hash of, and `ix codegen --check` fails when the file and the
digest drift apart.

A role key decodes to `Role.all[i]`, the role at the index the bytes give.
The reader is strict: tags and role indices outside their
ranges are refused, a count larger than the bytes left is refused, and
`Committed.ofBytes` accepts the bytes only when the data read re-encode to
exactly those bytes (`encode`), so the reader and the encoder agree on every
input the reader accepts. -/

namespace Ix.SpecDigest

open Ix.Kernel

def getNat : Ixon.GetM Nat := do
  return (← Ixon.getTagN 0).value.toNat

def getBool : Ixon.GetM Bool := do
  match ← Ixon.getU8 with
  | 0 => pure false
  | 1 => pure true
  | b => throw s!"spec bytes: boolean byte {b}"

/-- A counted list. Every item takes at least one byte, so a count beyond
the bytes left is refused before anything is read. -/
def getList {α : Type} (item : Ixon.GetM α) : Ixon.GetM (List α) := do
  let n ← getNat
  let st ← get
  if n > st.bytes.size - st.idx then
    throw s!"spec bytes: a list of {n} items runs past the input"
  let mut out : Array α := #[]
  for _ in [0:n] do
    out := out.push (← item)
  return out.toList

def getStr : Ixon.GetM String := do
  let bytes ← getList Ixon.getU8
  match String.fromUTF8? ⟨bytes.toArray⟩ with
  | some s => pure s
  | none => throw "spec bytes: a string that is not UTF-8"

/-- A role, by its index in `Role.all`. -/
def getRole : Ixon.GetM Role := do
  let i ← getNat
  match Role.all[i]? with
  | some r => pure r
  | none => throw s!"spec bytes: role index {i} is not a role"

def getKey : Ixon.GetM (Key .anon) := do return .role (← getRole)

partial def getLevel : Ixon.GetM Level := do
  match ← Ixon.getU8 with
  | 0 => return .zero
  | 1 => return .succ (← getLevel)
  | 2 => let u ← getLevel; return .max u (← getLevel)
  | 3 => let u ← getLevel; return .imax u (← getLevel)
  | 4 => return .param (← getNat)
  | b => throw s!"spec bytes: level tag {b}"

def getPropWhen : Ixon.GetM PropWhen := do
  match ← Ixon.getU8 with
  | 0 => return .never
  | 1 => return .ifAllZero (← getList getNat)
  | b => throw s!"spec bytes: datum tag {b}"

def getBinder : Ixon.GetM BinderMeta := do
  return { pw := ← getPropWhen }

partial def getExpr : Ixon.GetM (Expr .anon) := do
  match ← Ixon.getU8 with
  | 0 => return .bvar (← getNat)
  | 1 => let i ← getNat; return .fvar i (← getExpr)
  | 2 => return .sort (← getLevel)
  | 3 => let k ← getKey; return .const k (← getList getLevel)
  | 4 => let f ← getExpr; return .app f (← getExpr)
  | 5 => let t ← getExpr; let b ← getExpr; return .lam t b (← getBinder)
  | 6 => let t ← getExpr; let b ← getExpr; return .forallE t b (← getBinder)
  | 7 =>
    let t ← getExpr; let v ← getExpr; let b ← getExpr
    let nonDep ← getBool
    return .letE t v b { nonDep }
  | 8 => return .lit (.natVal (← getNat))
  | 9 => return .lit (.strVal (← getStr))
  | 10 => let k ← getKey; let i ← getNat; return .proj k i (← getExpr)
  | b => throw s!"spec bytes: expression tag {b}"

def getVal : Ixon.GetM (ConstantVal .anon) := do
  let name ← getKey
  let levelParams ← getList getNat
  let type ← getExpr
  return { name, levelParams, type }

def getHint : Ixon.GetM ReducibilityHint := do
  match ← Ixon.getU8 with
  | 0 => return .opaque
  | 1 => return .abbrev
  | 2 => return .regular (← getNat)
  | b => throw s!"spec bytes: hint tag {b}"

def getCaps : Ixon.GetM (IndCaps .anon) := do
  let eta ← getBool
  let etaTag ← Ixon.getU8
  let etaCtor ← match etaTag with
    | 0 => pure none
    | 1 => some <$> getKey
    | b => throw s!"spec bytes: option tag {b}"
  let etaParams ← getNat
  let etaFields ← getNat
  let unitlike ← getBool
  let unitParams ← getNat
  let ruleK ← getBool
  let sortZ ← getPropWhen
  return { eta, etaCtor, etaParams, etaFields, unitlike, unitParams, ruleK, sortZ }

def getFire : Ixon.GetM (RecRuleFire .anon) := do
  match ← Ixon.getU8 with
  | 0 => return .inert
  | 1 => return .plain
  | 2 => let lvls ← getList getLevel; return .nested lvls (← getList getExpr)
  | b => throw s!"spec bytes: rule fire tag {b}"

def getRule : Ixon.GetM (RecRule .anon) := do
  let ctor ← getKey
  let nfields ← getNat
  let ctorParams ← getNat
  let fire ← getFire
  let rhs ← getExpr
  let k ← getBool
  let eta ← getBool
  let paramsBlind ← getBool
  return { ctor, nfields, ctorParams, fire, rhs, k, eta, paramsBlind }

def getInfo : Ixon.GetM (ConstantInfo .anon) := do
  match ← Ixon.getU8 with
  | 0 => return .axiomInfo (← getVal)
  | 1 => let cv ← getVal; let v ← getExpr; return .defnInfo cv v (← getHint)
  | 2 => let cv ← getVal; return .thmInfo cv (← getExpr)
  | 3 => let cv ← getVal; return .indInfo cv (← getCaps)
  | 4 => let cv ← getVal; let nP ← getNat; return .ctorInfo cv nP (← getNat)
  | 5 =>
    let cv ← getVal; let m ← getNat; let p ← getNat
    return .recInfo cv m p (← getList getRule)
  | b => throw s!"spec bytes: declaration tag {b}"

def getEquation : Ixon.GetM (Equation .anon) := do
  let vars ← getList getExpr
  let hyps ← getList getExpr
  let level ← getLevel
  let carrier ← getExpr
  let lhs ← getExpr
  let rhs ← getExpr
  return { vars, hyps, level, carrier, lhs, rhs }

def getSpec : Ixon.GetM (Spec .anon) := do
  match ← Ixon.getU8 with
  | 0 => return .block (← getList getInfo)
  | 1 => let n ← getNat; return .anchor n (← getExpr)
  | 2 =>
    let type ← getExpr
    let eqs ← getList do
      let hyps ← getList getExpr
      let l ← getExpr
      let r ← getExpr
      pure (hyps, l, r)
    return .ops type eqs
  | 3 =>
    let n ← getNat
    match ← Ixon.getU8 with
    | 0 => return .axiom n none
    | 1 => return .axiom n (some (← getExpr))
    | b => throw s!"spec bytes: option tag {b}"
  | 4 =>
    let n ← getNat; let type ← getExpr
    return .eqns n type (← getList getEquation)
  | b => throw s!"spec bytes: specification tag {b}"

/-- Role `i`'s row: its index must be `i`. -/
def getRow (i : Nat) : Ixon.GetM Row := do
  let j ← getNat
  unless j == i do throw s!"spec bytes: row {i} carries index {j}"
  let name ← getList getStr
  let spec ← getSpec
  let block ← getList getRole
  let deps ← getList getRole
  let implicit ← getBool
  let inert ← getBool
  let quotKind ← getNat
  let family ← getNat
  let op ← getNat
  return { name, spec, block, deps, implicit, inert, quotKind, native := (family, op) }

def getCommitted : Ixon.GetM Committed := do
  let specVersion ← getNat
  let encodingVersion ← getNat
  let n ← getNat
  let st ← get
  if n > st.bytes.size - st.idx then throw s!"spec bytes: {n} rows run past the input"
  let mut rows : Array Row := #[]
  for i in [0:n] do
    rows := rows.push (← getRow i)
  let groups ← getList (getList getRole)
  let firstWellFounded ← getNat
  let firstEquation ← getNat
  return { specVersion, encodingVersion, rows := rows.toList,
           schedule := { groups, firstWellFounded, firstEquation } }

/-- **The committed data, read back from `bytes`**: refused unless `bytes` is
exactly one encoding and the data read re-encode to `bytes` (`encode`). -/
def Committed.ofBytes (bytes : ByteArray) : Except String Committed := do
  let c ← Ixon.runGetExact getCommitted bytes
  unless (← encode c) == bytes do
    throw "spec bytes: the data read do not re-encode to the bytes"
  pure c

end Ix.SpecDigest

end
