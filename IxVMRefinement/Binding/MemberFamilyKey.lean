import IxVMRefinement.Binding.MemberLoadPins

/-! # The family selected by a reading of a pinned standard recursor

A successful family-key read traverses two syntactic Π telescopes, then an
application spine ending in a constant. An annotation can contract lets in
the tails of those telescopes. Every positive read still occurs among the
constant heads of the annotated telescope domains. For the two pinned types
there is just one such occurrence.
-/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Core

private def spineKeys : KExpr → List KKey
  | .const k _ => [k]
  | .app f _ => spineKeys f
  | _ => []

private def binderKeys : KExpr → List KKey
  | .forallE d b _ => spineKeys d ++ binderKeys b
  | _ => []

private def motiveKeys : KExpr → List KKey
  | .forallE d b _ => binderKeys d ++ motiveKeys b
  | _ => []

private theorem spineKeys_eq (e : KExpr) : spineKeys e = (headKey e).toList := by
  induction e with
  | app f x ih _ => exact ih
  | _ => rfl

private theorem spineKeys_ann {ann raw : KExpr} (a : Annotates ann raw) :
    spineKeys raw ⊆ spineKeys ann := by
  induction a with
  | app _ _ ih _ => exact ih
  | const => exact fun _ h => h
  | _ => simp [spineKeys]

private theorem binderKeys_ann {ann raw : KExpr} (a : Annotates ann raw) :
    binderKeys raw ⊆ binderKeys ann := by
  induction a with
  | forallE d _ _ ih =>
    intro k hk
    exact List.mem_append.mpr ((List.mem_append.mp hk).imp (fun h => spineKeys_ann d h) (fun h => ih h))
  | _ => simp [binderKeys]

private theorem motiveKeys_ann {ann raw : KExpr} (a : Annotates ann raw) :
    motiveKeys raw ⊆ motiveKeys ann := by
  induction a with
  | forallE d _ _ ih =>
    intro k hk
    exact List.mem_append.mpr ((List.mem_append.mp hk).imp (fun h => binderKeys_ann d h) (fun h => ih h))
  | _ => simp [motiveKeys]

private theorem spineKeys_erase (e : KExpr) : spineKeys e.erasePw = spineKeys e := by
  induction e <;> simp [Ix.Kernel.Expr.erasePw, spineKeys, *]

private theorem binderKeys_erase (e : KExpr) : binderKeys e.erasePw = binderKeys e := by
  induction e <;> simp [Ix.Kernel.Expr.erasePw, binderKeys, spineKeys_erase, *]

private theorem motiveKeys_erase (e : KExpr) : motiveKeys e.erasePw = motiveKeys e := by
  induction e <;> simp [Ix.Kernel.Expr.erasePw, motiveKeys, binderKeys_erase, *]

private theorem lastBinder_keys {e d : KExpr} {k : KKey} (last : lastBinderDom e = some d)
    (head : k ∈ spineKeys d) : k ∈ binderKeys e := by
  induction e with
  | forallE dom b m _ ih =>
    cases b <;> first
      | exact List.mem_append_right _ (ih last)
      | exact List.mem_append_left _ ((Option.some.inj last).symm ▸ head)
  | _ => cases last

private theorem stripped_keys {n : Nat} {e d b : KExpr} {m : Ix.Kernel.BinderMeta}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {k : KKey}
    (strip : e.stripPis n = some (bs, .forallE d b m)) (head : k ∈ binderKeys d) :
    k ∈ motiveKeys e := by
  induction n generalizing e bs with
  | zero =>
    have eq : e = .forallE d b m := (Prod.mk.inj (Option.some.inj strip)).2
    rw [eq]
    exact List.mem_append_left _ head
  | succ n ih =>
    cases e with
    | forallE dom body md =>
      cases sub : body.stripPis n with
      | none => simp [Ix.Kernel.Expr.stripPis, sub] at strip
      | some pair =>
        obtain ⟨tail, out⟩ := pair
        rw [Ix.Kernel.Expr.stripPis, sub] at strip
        have eq : out = .forallE d b m := (Prod.mk.inj (Option.some.inj strip)).2
        rw [eq] at sub
        exact List.mem_append_right _ (ih sub)
    | _ => cases strip

private theorem familyKey_mem {r : Ixon.Recursor} {raw : KExpr} {k : KKey}
    (key : familyKey r raw = some k) : k ∈ motiveKeys raw := by
  unfold familyKey binderDom at key
  cases hs : raw.stripPis r.params.toNat with
  | none => rw [hs] at key; cases key
  | some pair =>
    obtain ⟨bs, body⟩ := pair
    rw [hs] at key
    cases body with
    | forallE d b bm =>
      cases hl : lastBinderDom d with
      | none => simp [hl] at key
      | some z =>
        have hk : headKey z = some k := by simpa [hl] using key
        exact stripped_keys hs (lastBinder_keys hl (by simp [spineKeys_eq, hk]))
    | _ => cases key

/-- The semantic pin of the selected recursor, together with its family role. -/
def stdRecFamilyPin (r : Ix.Kernel.Role) : Ix.Kernel.Role × Ix.Kernel.ConstantVal .anon :=
  if r = .iffRec then (.iff, Ix.Kernel.iffRecA.toConstantVal)
  else (.nonempty, Ix.Kernel.nonemptyRecA.toConstantVal)

set_option maxRecDepth 100000 in
/-- A successful family-key reading of any source type whose annotation
matches the selected pin identifies the pinned inductive itself. This covers
arbitrary parameter counts and lets in the unannotated reading. -/
theorem familyKey_of_stdRecPin {role : Ix.Kernel.Role} {n : Nat} (p : StdRecPin role n)
    {record : Ixon.Recursor} {raw ann : KExpr} {k : KKey}
    (read : familyKey record raw = some k) (a : Annotates ann raw)
    (pin : ann.erasePw = (stdRecFamilyPin role).2.type.erasePw) :
    k = .role (stdRecFamilyPin role).1 := by
  have mem : k ∈ motiveKeys ann := motiveKeys_ann a (familyKey_mem read)
  rw [← motiveKeys_erase ann, pin, motiveKeys_erase] at mem
  have pins : motiveKeys (stdRecFamilyPin role).2.type = [.role (stdRecFamilyPin role).1] := by
    cases p <;> decide +kernel
  simpa only [pins, List.mem_singleton] using mem

/-- The pinned arities of the recursor and its identified family yield the
same singleton level list at either semantic reading. -/
theorem recLps_of_stdRecPin {role : Ix.Kernel.Role} {n : Nat} (p : StdRecPin role n)
    {record : Ixon.Recursor} {ind : Ixon.Inductive}
    (recLevels : record.lvls.toNat = 1)
    (familyLevels : ind.lvls.toNat = if role = .iffRec then 0 else 1) :
    Ix.Kernel.Reader.recLps (decide (record.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat) = [0] := by
  rw [recLevels, familyLevels]
  cases p <;> decide

end IxVM.Refinement.Binding
