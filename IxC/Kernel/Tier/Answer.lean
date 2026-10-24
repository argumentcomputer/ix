module

public import IxC.Kernel.Tier.Ind
public import IxC.Kernel.Frontend.ProjRec

public section

/-!
# The typing tier: the answer view (M7 Q1; answers only)

AuxGen's questions about an unsafe block, or about a family before its
recursors exist, must be answered **as Lean's kernel answers them**: Lean
unfolds a tier definition (`partial` or not safe) and fires the recursor of
an unsafe block.
The tier's checks refuse those reductions (`Ix.Kernel.Tier`, `indC`'s check
view). This module builds the other view: the **answer view**, an index whose
tier constants carry their δ and ι forms.

* **Definitions** (`defsAnswerC`): a definition block the tier accepted, its
  values annotated as the tier annotates them, installed as `defnInfo` with
  their hints. Unsafe opaques and axioms keep their check form (`axiomInfo`):
  Lean unfolds neither.
* **Inductive blocks** (`AnswerView.pushInd`): a block `indC` accepted, its
  formers with **official's capabilities** (`leanCaps`: structure η at one
  constructor without indices in a block with no recursive field, unit-likeness at a
  fieldless constructor without indices, K at a single propositional former
  with one fieldless constructor), its constructors, its projection tables,
  and its recursors **with their typed rules**, the rule bits computed at the
  view (`recRuleBits`).

**The fence.** An `AnswerView` is built only here and keeps its index
private: what leaves it is the cached checker's functions over it (`knot`)
and lookups, never an index a check could run at. No checking or certified
path imports this module (`Tests/Ix/Kernel/Layering.lean`, the answers
fence): its only consumer is the Source service's answering scopes, whose
answers are generation inputs and record no verdict.
-/

namespace Ix.Kernel.Tier

open Ix.Kernel Ix.Kernel.Cached

/-- **The answer view**: an index whose tier constants carry their δ and ι
forms. Its index is private. -/
structure AnswerView (md : Mode) where
  private mk ::
  private fe : FEnv md

namespace AnswerView

/-- The view over a logical index, before any tier constant. -/
def ofLogical (fe : FEnv md) : AnswerView md := ⟨fe⟩

/-- The view with `infos` pushed, in order. -/
def pushInfos (av : AnswerView md) (infos : List (ConstantInfo md)) : AnswerView md :=
  ⟨pushAll av.fe infos⟩

/-- A lookup in the view. -/
def find? (av : AnswerView md) (k : Key md) : Option (ConstantInfo md) := av.fe.find? k

/-- **The cached checker's functions over the view** (at `.verified`, fuel
`checkFuel`): what the answering scopes run. -/
def knot (av : AnswerView md) : CoreFnsI md := coreKnotI .verified av.fe checkFuel

end AnswerView

/-- **Official's capabilities** for former `i` of a checked block
(`nativeCapsAt`'s rules): `isRec` is the block's (some constructor field
mentions a former of the block). -/
def leanCaps (o : TierIndOut md) (isRec : Bool) (i : Nat) : IndCaps md :=
  match o.types[i]?, o.ctors.filter (·.2.1 == i) with
  | some (_, nIdx, s), [(cvC, _, nF)] =>
    let isProp := Level.isEquiv s .zero == some true
    { eta := nIdx == 0 && !isProp && !isRec
      etaCtor := some cvC.name
      etaParams := o.numParams
      etaFields := nF
      unitlike := nIdx == 0 && nF == 0
      unitParams := o.numParams
      ruleK := o.types.length == 1 && nF == 0 && isProp
      sortZ := Level.zeronessOf s }
  | _, _ => {}

/-- Whether a field of the block mentions one of its formers (official's
`is_rec`). -/
def TierIndOut.isRec (o : TierIndOut md) : Bool :=
  let formers := o.types.map (·.1.name)
  o.ctors.any fun (cv, _, nF) =>
    match cv.type.stripPis (o.numParams + nF) with
    | some (bs, _) => (bs.drop o.numParams).any fun (d, _) => formers.any (Frontend.occursConstFast · d)
    | none => false

/-- **A checked block in the answer view**: the formers with official's
capabilities, the constructors, the projection tables, then the recursors
with their rules (bits at the view). -/
def AnswerView.pushInd (av : AnswerView md) (o : TierIndOut md) : AnswerView md :=
  let isRec := o.isRec
  let types := o.types.zipIdx.map fun ((cv, _, _), i) => ConstantInfo.indInfo cv (leanCaps o isRec i)
  let av := av.pushInfos (types ++ o.ctorInfos ++ o.tables.map .projInfo)
  let recs := o.recs.map fun (cv, sh, rules) =>
    ConstantInfo.recInfo cv sh.majorIdx sh.rulePrefix (rules.map (recRuleBits av.find? cv.name))
  av.pushInfos recs

/-- **A definition block's δ forms**, for a block the tier accepted at `fe`
(`checkDeclC`): its headers at `fe`, then its values annotated with the block
installed, each with its hint. -/
def defsAnswerC (fe : FEnv md) (ms : List (ConstantVal md × Expr md × ReducibilityHint)) :
    Except (CheckError md) (List (ConstantInfo md)) := do
  let hs ← headersC fe (ms.map fun (cv, v, _) => (cv, v))
  let fe' := pushHeaders fe hs
  mapC (fun (cvA, (_, v, h)) => do
      let jv ← runC (annotValC .verified fe' cvA v)
      pure (ConstantInfo.defnInfo cvA jv h)) (hs.zip ms)

end Ix.Kernel.Tier
