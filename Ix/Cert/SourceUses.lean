import Ix.Compile.SourceInput.Uses
import Ix.Cert.SourceInput

namespace Ix.Cert.SourceUses
open Ix.Compile.SourceInput Ix.Compile.SourceInput.Uses

/-- Every constant/projection/literal leaf, recursively through all expression
children. Free-variable checks and metadata semantics are separate obligations. -/
def Leaf (u : Use) : Ix.Expr → Prop
  | .const n _ _ => u = .constant n
  | .proj n _ b _ => u = .projection n ∨ Leaf u b
  | .lit (.natVal _) _ => u = .natLiteral
  | .lit (.strVal _) _ => u = .strLiteral
  | .app f a _ => Leaf u f ∨ Leaf u a
  | .lam _ t b _ _ | .forallE _ t b _ _ => Leaf u t ∨ Leaf u b
  | .letE _ t v b _ _ => (Leaf u t ∨ Leaf u v) ∨ Leaf u b
  | .mdata _ b _ => Leaf u b
  | _ => False

private theorem mem_insert (u v : Use) (uses : Uses.Set) :
    u ∈ uses.insert v ↔ u = v ∨ u ∈ uses := by
  rw [Std.HashSet.mem_insert,beq_iff_eq]
  exact or_congr eq_comm Iff.rfl

private theorem mem_one (u v : Use) : u ∈ one v ↔ u = v := by
  rw [one,mem_insert]
  simp only [Std.HashSet.not_mem_empty,or_false]

private theorem mem_join (u : Use) (a b : Uses.Set) : u ∈ join a b ↔ u ∈ a ∨ u ∈ b := by
  calc
    u ∈ join a b ↔ (a ∪ b).contains u := by rw [join,Std.HashSet.union_eq,Std.HashSet.mem_iff_contains]
    _ ↔ a.contains u ∨ b.contains u := Std.HashSet.mem_union_iff
    _ ↔ u ∈ a ∨ u ∈ b := or_congr Std.HashSet.contains_iff_mem Std.HashSet.contains_iff_mem

theorem tree_complete (u : Use) (e : Ix.Expr) : u ∈ tree e ↔ Leaf u e := by
  induction e with
  | bvar => simp [tree,Leaf]
  | fvar => simp [tree,Leaf]
  | mvar => simp [tree,Leaf]
  | sort => simp [tree,Leaf]
  | const n => exact mem_one u (.constant n)
  | app f a h ihf iha => simp only [tree,Leaf,mem_join,ihf,iha]
  | lam n t b bi h iht ihb => simp only [tree,Leaf,mem_join,iht,ihb]
  | forallE n t b bi h iht ihb => simp only [tree,Leaf,mem_join,iht,ihb]
  | letE n t v b nd h iht ihv ihb => simp only [tree,Leaf,mem_join,iht,ihv,ihb]
  | mdata d b h ih => exact ih
  | proj n i b h ih => simp only [tree,Leaf,mem_insert,ih]
  | lit l h => cases l with
    | natVal => exact mem_one u .natLiteral
    | strVal => exact mem_one u .strLiteral

theorem collect_complete (u : Use) (e : Ix.Expr) : u ∈ collect e ↔ Leaf u e := by
  rw [collect_eq]
  exact tree_complete u e

/-- Exact term origins as well as exact leaf coverage; no grouping edge is
smuggled into the expression relation. -/
theorem capture_complete (ci : Ix.ConstantInfo) (part : Part) (u : Use) :
    (∃ uses, (part,uses) ∈ capture ci ∧ u ∈ uses) ↔
      ∃ e, (part,e) ∈ terms ci ∧ Leaf u e := by
  rw [capture_eq]
  simp only [trees,List.mem_map]
  constructor
  · rintro ⟨uses,⟨⟨p,e⟩,member,same⟩,inside⟩
    cases same
    exact ⟨e,member,(tree_complete u e).mp inside⟩
  · rintro ⟨e,member,inside⟩
    exact ⟨tree e,⟨(part,e),member,rfl⟩,(tree_complete u e).mpr inside⟩

/-- A successful public capture is tied to the exact original declaration and
complete term/leaf relation. This ranges over every original source query. -/
theorem produced_capture {input : Array Raw} {name : Ix.Name} {out : List (Part × Uses.Set)}
    (accepted : (ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)).captureUsesAt name = .ok out) :
    ∃ ci, (SourceGraph.full (SourceStream.canonical input)).consts.get? name = some ci ∧
      out = capture ci ∧ ∀ part u, (∃ uses, (part,uses) ∈ out ∧ u ∈ uses) ↔
        ∃ e, (part,e) ∈ terms ci ∧ Leaf u e := by
  let carrier := ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)
  change carrier.captureUsesAt name = .ok out at accepted
  cases read : carrier.valueAt name with
  | error e =>
    have impossible : (Except.error e : Except Error (List (Part × Uses.Set))) = .ok out := by
      simpa only [Carrier.captureUsesAt,Functor.map,Except.map,read] using accepted
    cases impossible
  | ok form =>
    have same : capture form.original = out := by
      simpa only [Carrier.captureUsesAt,Functor.map,Except.map,read,Except.ok.injEq] using accepted
    have origin := SourceInput.produced_value_member (input := input) read
    refine ⟨form.original,origin.1,same.symm,?_⟩
    subst out
    exact capture_complete form.original

/-- Capture adds no refusal or missing-value branch to the original producer.
Every declared source gets its exact capture or the original header refusal. -/
theorem declared_capture (input : Array Raw) (name : Ix.Name) (ci : Ix.ConstantInfo)
    (declared : (SourceGraph.full (SourceStream.canonical input)).consts.get? name = some ci) :
    ∃ raw, (Ix.Compile.SourceGraph.Prepass.run input).leanByIx.get? name = some raw ∧
      ci = Canon.constS raw.2 ∧
      (ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)).captureUsesAt name =
        if raw.1 == raw.2.name then .ok (capture ci)
        else .error (.headerMismatch name raw.1 raw.2.name) := by
  obtain ⟨raw,winner,same,result⟩ := SourceInput.declared_coverage input name ci declared
  refine ⟨raw,winner,same,?_⟩
  unfold Carrier.captureUsesAt
  rw [result]
  split <;> rfl

/-- info: 'Ix.Cert.SourceUses.collect_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collect_complete
/-- info: 'Ix.Cert.SourceUses.capture_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_complete
/-- info: 'Ix.Cert.SourceUses.produced_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms produced_capture
/-- info: 'Ix.Cert.SourceUses.declared_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms declared_capture

end Ix.Cert.SourceUses
