module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.EnvPreds

public section

/-!
# The pinned basis constants' direct valuations

`pinnedStructT` — what a reserved basis constant denotes to in the
declarative layer, where it denotes to a bare `BConst` built-in.

Relocated verbatim from `ConLeche/TTVerify/EnvTT.lean` (task #148, T1):
the definition is `V`-free — it is a table from the checker's reserved
names to `ConLeche/Term/Const.lean`'s built-ins — so it belongs where both
verification lanes can import it.  The level-parameter names it reads
are `ConLeche/Verify/EnvPreds.lean`'s `uN`/`vN`/`u1N` (the `uN`/`vN`/
`u1N` restatements that stood beside it were the same relocation's
fourth item).
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- What a reserved basis constant denotes to, where it denotes to a
bare built-in.  `none` for the four the layer derives rather than
carries (see the section note).

**Three entries were wrong until the basis install elaborated them**
(task #119, `DESIGN.md` §8.2's defect, in its "unproved definition"
form).  `Empty` is stored *level-monomorphically* (`levelParams = []`),
so its valuation may not read the assignment at all — its level is
fixed by its pinned type, `Sort 1`.  `Empty.rec` binds **one** level
where the layer's `emptyRec` takes two, the first being `Empty`'s own.
And `PUnit.rec` binds `u_1, u` — motive level *second* in the layer's
order and named `u_1`, not `v`.

`False` (task #181) is `Empty.{0}` in the layer's currency: the
built-in `empty` at level `0` is `Sort 0`-valued (`BConst.type`), and
`False.rec` is `emptyRec` at `[0, u]`.  No new built-in.

Each would have been caught only here, because `val_params` is what
they violate and nothing before the install asserts it for a basis
constant.  That is the house rule's point exactly (`ConLeche/Term/DESIGN.md`
§3.1): a definition is a conjecture until a consumer elaborates it. -/
@[expose] def pinnedStructT (n : Name) (ψ : Name → Nat) : Option Term :=
  if n = natName then some (.const .nat [])
  else if n = natZeroName then some (.const .natZero [])
  else if n = natSuccName then some (.const .natSucc [])
  else if n = natName.str "rec" then some (.const .natRec [ψ uN])
  else if n = punitName then some (.const .punit [ψ uN])
  else if n = punitUnitName then some (.const .punitUnit [ψ uN])
  else if n = punitName.str "rec" then
    some (.const .punitRec [ψ uN, ψ u1N])
  else if n = emptyName then some (.const .empty [1])
  else if n = emptyName.str "rec" then
    some (.const .emptyRec [1, ψ uN])
  else if n = falseName then some (.const .empty [0])
  else if n = falseName.str "rec" then
    some (.const .emptyRec [0, ψ uN])
  else if n = quotName then some (.const .quot [ψ uN])
  else if n = quotMkName then some (.const .quotMk [ψ uN])
  else if n = quotLiftName then some (.const .quotLift [ψ uN, ψ vN])
  else if n = quotIndName then some (.const .quotInd [ψ uN])
  else if n = quotSoundName then some (.const .quotSound [ψ uN])
  else none

/-- Every stored reserved-basis constant is the pinned *declaration*,
and — where the layer still carries it — is valued by its direct pin.
Transpose of `IndOk`'s fourth conjunct.

This is what makes a reduction's *syntactic* match usable: the `.proj`
clause matches a constructor head against `entry.ctor`, and only the
valuation clause turns that into `⟦e'⟧ = psigmaMkT u v A B a b`, which
is the shape `projFstMk` is stated at.

**The declaration clause came back** (the retired lane's record, §12.10).
It was dropped on the first transposition as "syntactic, no consumer",
and `ProofIrrelStepTT`'s unit-like branch is the consumer: `isUnitLikeTy`
accepts a `.const c _` whose `c.str "rec"` is *reserved*, so identifying
`c` as `PUnit` — which is what the unit-like eta law is stated at — is
exactly reading the four other reserved recursors' pinned shapes and
finding that none of them is single-rule, zero-field and index-free.
Without the clause the branch is unprovable; with it, it is a `decide`.

**The declaration clause is unconditional** (task #283).  It used to be
premised on `ConstantInfo.isBasis ci`, which every establishment site
discharged by ignoring it (`ConsHead.ofBasis` is applied at a head that
*is* `pinnedInfo` of its own name, so the clause is `rfl` there, and a
non-reserved cons makes the whole conjunction vacuous).  The premise
therefore bought nothing and cost the only fact a *statement* can want
from the table: that a stored reserved name holds the pin whatever its
kind — which is what lets `Model.eq_equality` (`ConLeche/Denotes.lean`)
speak about the stored `Eq` without hypothesising its declaration. -/
@[expose] def BasisPinnedTT (env : Env) (cval : TConstVal) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    reservedBasisNames.contains n = true →
    ci = pinnedInfo n ∧
    ∀ (t : Term) (ψ : Name → Nat), pinnedStructT n ψ = some t →
      cval n ψ = t

theorem BasisPinnedTT.empty (cval : TConstVal) :
    BasisPinnedTT Env.empty cval := by
  intro n ci h
  simp [Env.find?, Env.empty] at h

end ConLeche.Verify
