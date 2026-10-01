module

public import ConLeche.Model.Inductives.StructBodyFrames
public import ConLeche.Verify.Inductives.StructPartsInv
public section

/-!
# The projection table's cons (task #175 S1)

`stageTable`: the P step at the direct install's last stage — the
structure's projection **table**, one constant holding every field's
body (`checkStructProjTable`).  The table's leaf is `Sort 0` (a
member of its dummy type's reading; a table is not a term), and what
the cons owes is the tower law at every field
(`declStep_preserves_of_tower_cons`):

* **(A)** the typing law reads body `i` through the dummy telescope
  (`denoteMeta_projTele_zero`); the opened body is the constructor's
  field domain at the variables (`structProjBody_open`), whose frame
  facts are `bodyFrames`, and `entryTypingCore` closes;
* **(B)** the iota law and **(C)** the η law are the block's own
  (`entryIotaCore`/`entryIotaCoreZero`, `entryEtaCore`), as before.

The squash regime's guard content (`structProjGuards_getD` over the
field-sort run) and the unused earlier fields' invariance
(`openPisAtFvars_leaf_free`) are derived here per field, as the
retired per-slot fold derived them per slot.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta ProjEntry ProjTable projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The table name has the reserved shape. -/
theorem projTableName_isProjFnShape (T : Name) :
    (projTableName T).isProjFnShape = true := rfl

end ConLeche.Model
