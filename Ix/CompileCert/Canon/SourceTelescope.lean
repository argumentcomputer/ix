import Ix.CompileCert.Canon.SourceReadBridge

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

def BinderScope (P : Name → Prop) (b : Binder) : Prop := RefScope P b.2.1

theorem RefScope.mkForalls {P : Name → Prop} {body : Expr}
    (hbody : RefScope P body) {binders : Array Binder}
    (hbinders : ∀ b ∈ binders, BinderScope P b) :
    RefScope P (Ix.Compile.Canon.mkForalls binders body) := by
  unfold Ix.Compile.Canon.mkForalls
  rw [← Array.foldr_toList]
  have each : ∀ b ∈ binders.toList, BinderScope P b := by simpa using hbinders
  generalize binders.toList = xs at each ⊢
  revert each
  induction xs with
  | nil => intro _; exact hbody
  | cons b rest ih =>
    intro each
    obtain ⟨name,typ,info⟩ := b
    have head := each _ List.mem_cons_self
    have tail : ∀ b ∈ rest, BinderScope P b := fun b member =>
      each b (List.mem_cons_of_mem _ member)
    have scopedTail := ih tail
    simpa [BinderScope, RefScope, sourceExprRefs, or_imp, forall_and] using
      And.intro head scopedTail

/-- Peeling source telescopes preserves reference scope for both the body
and every accumulated binder; metadata names remain outside reference scope. -/
theorem RefScope.peelForalls {P : Name → Prop} (count : Nat) {e : Expr}
    (he : RefScope P e) (initial : Array Binder)
    (hi : ∀ b ∈ initial, BinderScope P b) :
    RefScope P (Ix.Compile.Canon.peelForalls count e initial).2 ∧
      ∀ b ∈ (Ix.Compile.Canon.peelForalls count e initial).1, BinderScope P b := by
  induction count generalizing e initial with
  | zero => exact ⟨he,hi⟩
  | succ count ih =>
    have stripped := he.stripMdata
    cases hs : Ix.Compile.Canon.stripMdata e <;> simp only [Ix.Compile.Canon.peelForalls, hs]
    all_goals first
      | exact ⟨by simpa only [hs] using stripped, hi⟩
      | skip
    rename_i name typ body info hash
    have parts : RefScope P typ ∧ RefScope P body := by
      simpa [hs, RefScope, sourceExprRefs, or_imp, forall_and] using stripped
    apply ih parts.2
    intro b member
    rcases (show b ∈ initial ∨ b = (name,typ,info) by simpa using member) with old | rfl
    · exact hi b old
    · exact parts.1

/-- The original block parameter binders read by the expansion initializer
are in the same actual source closure as its first member. -/
theorem SourceReach.parameterBinders {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {seeds : List Name}
    {first : Name} {view : IndView}
    (reached : SourceReach source groups seeds first)
    (found : IndView.ofConst? source.get? first = some view) :
    ∀ binder ∈ (Ix.Compile.Canon.peelForalls view.numParams view.type #[]).1,
      BinderScope (SourceReach source groups seeds) binder := by
  obtain ⟨v,lookup,-,typ,-,-⟩ := IndView.sourceInfo found
  have scopeProof : RefScope (SourceReach source groups seeds) view.type := by
    rw [typ]
    exact reached.type_scope lookup
  exact (scopeProof.peelForalls view.numParams #[] (by simp)).2

end Ix.CompileCert.Canon
