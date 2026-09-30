/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress.Reading
import Ix.Kernel.Search

/-! # A proof-carrying Ixon expression reader

The fuel bounds expansion depth, including sharing edges. A forward/cyclic
sharing edge is malformed independently of fuel. Unsupported syntax and a
missing literal-family configuration decline. Successful output carries its
exact structural reading; the proof is erased during execution.
-/

namespace Ix.Kernel.Ingress

private def requireSome (value : Option α) (failure : SearchFailure) :
    Search { result : α // value = some result } :=
  match value with
  | none => .error failure
  | some result => .ok ⟨result, rfl⟩

/-- Read one expression with a decreasing bound on reachable sharing entries.
The usual initial bound is the source sharing table's size. -/
def readExprC (ctx : Context) : (fuel limit : Nat) → (input : Ixon.Expr) →
    Search { output : VExpr Address // ExprReads ctx limit input output }
  | 0, _, _ => .error .exhausted
  | fuel + 1, limit, input =>
    match input with
    | .var i => .ok ⟨.bvar i.toNat, .var⟩
    | .sort i => do
      let level ← requireSome (ctx.level i) (.malformed "universe table index is out of bounds")
      return ⟨.sort level.val, .sort level.property⟩
    | .ref i us => do
      let ref ← requireSome (ctx.external i) (.malformed "reference is missing or has invalid ownership")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .ref ref.property levels.property⟩
    | .recur i us => do
      let ref ← requireSome (ctx.recursive i) (.malformed "recursive reference is outside this block")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .recur ref.property levels.property⟩
    | .nat i => do
      let bytes ← requireSome (ctx.blob i) (.malformed "natural literal blob is missing")
      let family ← requireSome ctx.natFamily (.unsupported "natural literal family is not configured")
      return ⟨.natLit family.val (natural bytes.val), .nat bytes.property family.property⟩
    | .str i => do
      let refs ← requireSome ctx.strings (.unsupported "string literal constants are not configured")
      let bytes ← requireSome (ctx.blob i) (.malformed "string literal blob is missing")
      let text ← requireSome (String.fromUTF8? bytes.val) (.malformed "string literal is not valid UTF-8")
      return ⟨refs.val.stringLiteral text.val, .str bytes.property refs.property text.property⟩
    | .app f a => do
      let f' ← readExprC ctx fuel limit f
      let a' ← readExprC ctx fuel limit a
      return ⟨.app f'.val a'.val, .app f'.property a'.property⟩
    | .lam _ type body => do
      let type' ← readExprC ctx fuel limit type
      let body' ← readExprC ctx fuel limit body
      return ⟨.lam type'.val body'.val, .lam type'.property body'.property⟩
    | .all _ _ type body => do
      let type' ← readExprC ctx fuel limit type
      let body' ← readExprC ctx fuel limit body
      return ⟨.forallE type'.val body'.val, .all type'.property body'.property⟩
    | .letE _ type value body => do
      let type' ← readExprC ctx fuel limit type
      let value' ← readExprC ctx fuel limit value
      let body' ← readExprC ctx fuel limit body
      return ⟨.letE type'.val value'.val body'.val,
        .letE type'.property value'.property body'.property⟩
    | .prj i field value => do
      let ref ← requireSome (ctx.external i) (.malformed "projection family is missing or has invalid ownership")
      let value' ← readExprC ctx fuel limit value
      return ⟨.proj ref.val field.toNat value'.val, .prj ref.property value'.property⟩
    | .share i => do
      if earlier : i.toNat < limit then
        let value ← requireSome ctx.source.sharing[i.toNat]? (.malformed "sharing index is out of bounds")
        let value' ← readExprC ctx fuel i.toNat value.val
        return ⟨value'.val, .share earlier value.property value'.property⟩
      else throw (.malformed "sharing reference is not to an earlier entry")

/-! ## Reading with a shared table

`readExprC` re-reads a sharing entry at every occurrence, which is exponential
in the depth of nested sharing. `buildShared` reads each entry once, in order,
against the entries before it, and `readExprT` resolves `.share i` to entry
`i`'s result, so a record's shared subterms become one object each. Each
successful entry carries its exact reading (`SharedReads`), and the relation
read, `ExprReads`, is unchanged. -/

/-- Every successful entry `j` of a read sharing table is the exact reading of
`sharing[j]` at limit `j`. -/
def SharedReads (ctx : Context) (table : Array (Search (VExpr Address))) : Prop :=
  ∀ j (h : j < table.size) output, table[j] = .ok output →
    ∃ value, ctx.source.sharing[j]? = some value ∧ ExprReads ctx j value output

theorem SharedReads.empty (ctx : Context) : SharedReads ctx #[] := fun _ h => by simp at h

theorem SharedReads.push {ctx : Context} {table : Array (Search (VExpr Address))}
    (h : SharedReads ctx table) (entry : Search (VExpr Address))
    (hentry : ∀ output, entry = .ok output →
      ∃ value, ctx.source.sharing[table.size]? = some value ∧ ExprReads ctx table.size value output) :
    SharedReads ctx (table.push entry) := by
  intro k hk output hout
  by_cases hlt : k < table.size
  · rw [Array.getElem_push_lt hlt] at hout
    exact h k hlt output hout
  · have hk' : k = table.size := by simp at hk; omega
    subst hk'
    rw [Array.getElem_push_eq] at hout
    exact hentry output hout

/-- Read one expression, resolving each sharing reference by its table entry. -/
def readExprT (ctx : Context) (table : Array (Search (VExpr Address)))
    (htable : SharedReads ctx table) : (fuel limit : Nat) → limit ≤ table.size →
    (input : Ixon.Expr) → Search { output : VExpr Address // ExprReads ctx limit input output }
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, limit, hl, input =>
    match input with
    | .var i => .ok ⟨.bvar i.toNat, .var⟩
    | .sort i => do
      let level ← requireSome (ctx.level i) (.malformed "universe table index is out of bounds")
      return ⟨.sort level.val, .sort level.property⟩
    | .ref i us => do
      let ref ← requireSome (ctx.external i) (.malformed "reference is missing or has invalid ownership")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .ref ref.property levels.property⟩
    | .recur i us => do
      let ref ← requireSome (ctx.recursive i) (.malformed "recursive reference is outside this block")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .recur ref.property levels.property⟩
    | .nat i => do
      let bytes ← requireSome (ctx.blob i) (.malformed "natural literal blob is missing")
      let family ← requireSome ctx.natFamily (.unsupported "natural literal family is not configured")
      return ⟨.natLit family.val (natural bytes.val), .nat bytes.property family.property⟩
    | .str i => do
      let refs ← requireSome ctx.strings (.unsupported "string literal constants are not configured")
      let bytes ← requireSome (ctx.blob i) (.malformed "string literal blob is missing")
      let text ← requireSome (String.fromUTF8? bytes.val) (.malformed "string literal is not valid UTF-8")
      return ⟨refs.val.stringLiteral text.val, .str bytes.property refs.property text.property⟩
    | .app f a => do
      let f' ← readExprT ctx table htable fuel limit hl f
      let a' ← readExprT ctx table htable fuel limit hl a
      return ⟨.app f'.val a'.val, .app f'.property a'.property⟩
    | .lam _ type body => do
      let type' ← readExprT ctx table htable fuel limit hl type
      let body' ← readExprT ctx table htable fuel limit hl body
      return ⟨.lam type'.val body'.val, .lam type'.property body'.property⟩
    | .all _ _ type body => do
      let type' ← readExprT ctx table htable fuel limit hl type
      let body' ← readExprT ctx table htable fuel limit hl body
      return ⟨.forallE type'.val body'.val, .all type'.property body'.property⟩
    | .letE _ type value body => do
      let type' ← readExprT ctx table htable fuel limit hl type
      let value' ← readExprT ctx table htable fuel limit hl value
      let body' ← readExprT ctx table htable fuel limit hl body
      return ⟨.letE type'.val value'.val body'.val,
        .letE type'.property value'.property body'.property⟩
    | .prj i field value => do
      let ref ← requireSome (ctx.external i) (.malformed "projection family is missing or has invalid ownership")
      let value' ← readExprT ctx table htable fuel limit hl value
      return ⟨.proj ref.val field.toNat value'.val, .prj ref.property value'.property⟩
    | .share i =>
      if earlier : i.toNat < limit then
        match hc : table[i.toNat]'(Nat.lt_of_lt_of_le earlier hl) with
        | .ok output => .ok ⟨output, by
            obtain ⟨value, hv, hr⟩ := htable i.toNat _ output hc
            exact .share earlier hv hr⟩
        | .error failure => .error failure
      else throw (.malformed "sharing reference is not to an earlier entry")

/-- Read a record's sharing entries in order, each against the ones before it. -/
def buildShared (ctx : Context) (fuel : Nat) : { table : Array (Search (VExpr Address)) //
    SharedReads ctx table ∧ table.size = ctx.source.sharing.size } :=
  go #[] (.empty ctx) (Nat.zero_le _)
where
  go (table : Array (Search (VExpr Address))) (htable : SharedReads ctx table)
      (hle : table.size ≤ ctx.source.sharing.size) :
      { table : Array (Search (VExpr Address)) //
        SharedReads ctx table ∧ table.size = ctx.source.sharing.size } :=
    if hj : table.size < ctx.source.sharing.size then
      let value := ctx.source.sharing[table.size]
      have hv : ctx.source.sharing[table.size]? = some value := Array.getElem?_eq_getElem hj
      match readExprT ctx table htable fuel table.size (Nat.le_refl _) value with
      | .ok result =>
        go (table.push (.ok result.val))
          (htable.push _ fun output h => by cases h; exact ⟨value, hv, result.property⟩)
          (by simp; omega)
      | .error failure =>
        go (table.push (.error failure)) (htable.push _ fun _ h => by cases h)
          (by simp; omega)
    else ⟨table, htable, by omega⟩
  termination_by ctx.source.sharing.size - table.size
  decreasing_by all_goals simp; omega

/-- The expression reader of one record: its sharing table is read once. -/
abbrev Reader (ctx : Context) :=
  (input : Ixon.Expr) → Search { output : VExpr Address // ExprReads ctx ctx.source.sharing.size input output }

def Context.reader (ctx : Context) (fuel : Nat) : Reader ctx :=
  let table := buildShared ctx fuel
  readExprT ctx table.val table.property.1 fuel ctx.source.sharing.size
    (Nat.le_of_eq table.property.2.symm)

/-- Erase the reading evidence at the public expression boundary. -/
def readExpr (ctx : Context) (fuel : Nat) (input : Ixon.Expr) : Search (VExpr Address) :=
  (readExprC ctx fuel ctx.source.sharing.size input).map Subtype.val

theorem readExpr_reading {ctx : Context} {fuel : Nat} {input : Ixon.Expr}
    {output : VExpr Address} (h : readExpr ctx fuel input = .ok output) :
    ExprReads ctx ctx.source.sharing.size input output := by
  unfold readExpr at h
  cases hc : readExprC ctx fuel ctx.source.sharing.size input with
  | error failure => simp [hc, Except.map] at h
  | ok result =>
    simp [hc, Except.map] at h
    exact h ▸ result.property

/-- Successful reads at different fuel budgets describe the same expression. -/
theorem readExpr_agree {ctx : Context} {fuel₁ fuel₂ : Nat} {input : Ixon.Expr}
    {left right : VExpr Address}
    (h₁ : readExpr ctx fuel₁ input = .ok left) (h₂ : readExpr ctx fuel₂ input = .ok right) :
    left = right := (readExpr_reading h₁).deterministic (readExpr_reading h₂)

end Ix.Kernel.Ingress
