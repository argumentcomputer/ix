/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import LSpec
import Ix.Kernel.Verify.Consistency.Quotient

/-!
Regressions for the canonical quotient bundle: the four constants installed
by Lean's `Environment.addQuot`, built directly in a kernel environment at the
reserved primitive addresses as in `Tests.Kernel.CheckTests`, pass
`TcM.checkConst`; a non-canonical type or a wrong universe count is rejected;
and the canonical kernel types read as the certified quotient description
under the reference map that the admission theorems derive. This file is not
a `module` because the proof library it exercises is not one.
-/

namespace Tests.Kernel.Quotient

open LSpec Ix.Kernel Ix.Theory Ix.Kernel.Consistency

private def prims : Primitives .anon := .ofAnonAddrs

/-- The canonical `Eq`/`Eq.refl`/quotient bundle at the reserved addresses. -/
private def canonicalQuotEnv : KEnv .anon := Id.run do
  let p := prims
  let mut env : KEnv .anon := {}
  env := env.insert p.eq
    (.indc () () 1 2 1 false p.eq 0 (RecM.canonicalEqType (m := .anon)) #[p.eqRefl] ())
  env := env.insert p.eqRefl (.ctor () () false 1 p.eq 0 2 0 (RecM.canonicalEqReflType p))
  env := env.insert p.quotType (.quot () () .type 1 (RecM.canonicalQuotType p .type))
  env := env.insert p.quotCtor (.quot () () .ctor 1 (RecM.canonicalQuotType p .ctor))
  env := env.insert p.quotLift (.quot () () .lift 2 (RecM.canonicalQuotType p .lift))
  env := env.insert p.quotInd (.quot () () .ind 1 (RecM.canonicalQuotType p .ind))
  return env

private def checkOn (env : KEnv .anon) (id : KId .anon) : Except (TcError .anon) Unit :=
  match (TcM.checkConst id).run (.ofEnvAnon env) with
  | .ok () _ => .ok ()
  | .error e _ => .error e

private def failsContaining (env : KEnv .anon) (id : KId .anon) (fragment : String) : Bool :=
  match checkOn env id with
  | .error e => ((toString e).splitOn fragment).length > 1
  | .ok () => false

private def replaceQuot (env : KEnv .anon) (id : KId .anon) (kind : Ix.QuotKind) (lvls : UInt64)
    (ty : KExpr .anon) : KEnv .anon :=
  env.insert id (.quot () () kind lvls ty)

/-- A well-typed type of the right binder depth carrying no quotient semantics. -/
private def forgedForallType (n : Nat) : KExpr .anon :=
  (List.range n).foldl (fun body _ => KExpr.mkAll () () (.mkSort .mkZero) body) (.mkSort .mkZero)

private instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

private instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

private instance : DecidableEq Address := fun left right =>
  decidable_of_iff ((left == right) = true) ⟨eq_of_beq, fun same => same ▸ beq_self_eq_true left⟩

/-- The canonical standalone coordinates of the reserved addresses. -/
private def refs : QuotientRefs Address :=
  { type := .member prims.quotType.addr 0, ctor := .member prims.quotCtor.addr 0,
    lift := .member prims.quotLift.addr 0, ind := .member prims.quotInd.addr 0,
    eq := .member prims.eq.addr 0, eqRefl := .member prims.eqRefl.addr 0,
    eqRec := .member prims.eq.addr 1 }

/-- The reference map on the reserved addresses. -/
private def resolve (addr : Address) : Option (ConstRef Address) :=
  if addr == prims.quotType.addr || addr == prims.quotCtor.addr || addr == prims.quotLift.addr ||
      addr == prims.quotInd.addr || addr == prims.eq.addr || addr == prims.eqRefl.addr then
    some (.member addr 0)
  else none

private def readsCanonically (kind : Ix.QuotKind) : Bool :=
  decide (readExpr? resolve (RecM.canonicalQuotType prims kind) = some (refs.entryType kind).erase)

private def cases : TestSeq :=
  test "quotient: the canonical bundle passes checkConst"
    ((checkOn canonicalQuotEnv prims.quotType).isOk &&
      (checkOn canonicalQuotEnv prims.quotCtor).isOk &&
      (checkOn canonicalQuotEnv prims.quotLift).isOk &&
      (checkOn canonicalQuotEnv prims.quotInd).isOk)
  ++ test "quotient: a non-canonical type is rejected"
    (failsContaining (replaceQuot canonicalQuotEnv prims.quotType .type 1 (forgedForallType 2))
        prims.quotType "type is not canonical" &&
      failsContaining (replaceQuot canonicalQuotEnv prims.quotLift .lift 2 (forgedForallType 6))
        prims.quotLift "type is not canonical")
  ++ test "quotient: a wrong universe count is rejected"
    (failsContaining (replaceQuot canonicalQuotEnv prims.quotLift .lift 3
        (RecM.canonicalQuotType prims .lift)) prims.quotLift "expects 2 universe params" &&
      failsContaining (replaceQuot canonicalQuotEnv prims.quotInd .ind 2
        (RecM.canonicalQuotType prims .ind)) prims.quotInd "expects 1 universe params")
  ++ test "quotient: a kind at another reserved address is rejected"
    (failsContaining (replaceQuot canonicalQuotEnv prims.quotType .ctor 1
      (RecM.canonicalQuotType prims .ctor)) prims.quotType "kind mismatch")
  ++ test "quotient: the canonical kernel types read as the certified quotient description"
    (readsCanonically .type && readsCanonically .ctor && readsCanonically .lift &&
      readsCanonically .ind)

def suite : List TestSeq := [cases]

end Tests.Kernel.Quotient
