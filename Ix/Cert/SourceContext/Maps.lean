module
public import Std.Data.HashMap.Lemmas

public section
namespace Ix.Cert.SourceContext.Maps
variable {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]

/-- Both passes enumerate complete maps, never a sample of observed uses. -/
def subset (same : α → α → Bool) (left right : Std.HashMap κ α) : Bool :=
  left.toList.all fun (key,value) => (right[key]?).any (same value)
def check (same : α → α → Bool) (left right : Std.HashMap κ α) : Bool :=
  subset same left right && subset same right left
@[expose] def domain (m : Std.HashMap κ α) : List κ := m.toList.map Prod.fst
@[expose] def Agrees (left right : Std.HashMap κ α) : Prop := ∀ key : κ, left[key]? = right[key]?

theorem subset_iff (same : α → α → Bool) (left right : Std.HashMap κ α) :
    subset same left right = true ↔ ∀ (key : κ) (value : α), left[key]? = some value →
      ∃ next, right[key]? = some next ∧ same value next = true := by
  simp only [subset,List.all_eq_true]
  constructor
  · intro all key value found
    have seen := all (key,value) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found)
    cases hit : right[key]? with
    | none => simp [hit] at seen
    | some next => exact ⟨next,rfl,by simpa [hit] using seen⟩
  · intro agrees row member
    obtain ⟨next,hit,equal⟩ := agrees row.1 row.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member)
    simp [hit,equal]

/-- Checked agreement is universal, including every absent lookup. -/
theorem check_sound {same : α → α → Bool}
    (sound : ∀ a b, same a b = true → a = b) {left right : Std.HashMap κ α}
    (accepted : check same left right = true) : Agrees left right := by
  obtain ⟨forward,backward⟩ := Bool.and_eq_true_iff.mp accepted
  have forward := (subset_iff same left right).mp forward
  have backward := (subset_iff same right left).mp backward
  intro key
  cases old : left[key]? with
  | some value =>
    obtain ⟨next,hit,equal⟩ := forward key value old
    rw [hit,sound value next equal]
  | none =>
    cases next : right[key]? with
    | none => rfl
    | some value =>
      obtain ⟨previous,hit,_⟩ := backward key value next
      rw [old] at hit
      cases hit

theorem check_complete {same : α → α → Bool} (refl : ∀ a, same a a = true)
    {left right : Std.HashMap κ α} (agrees : Agrees left right) : check same left right = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply (subset_iff same left right).mpr
    intro key value found
    exact ⟨value,(agrees key).symm.trans found,refl value⟩
  · apply (subset_iff same right left).mpr
    intro key value found
    exact ⟨value,(agrees key).trans found,refl value⟩

/-- This is the complete lookup domain, not a supplied coverage assumption. -/
theorem domain_iff (m : Std.HashMap κ α) (key : κ) :
    key ∈ domain m ↔ ∃ value, m[key]? = some value := by
  simp only [domain,List.mem_map]
  constructor
  · rintro ⟨⟨stored,value⟩,member,same⟩
    dsimp only at same
    subst stored
    exact ⟨value,Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member⟩
  · rintro ⟨value,hit⟩
    exact ⟨(key,value),Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hit,rfl⟩

theorem none_outside (m : Std.HashMap κ α) {key : κ} (outside : key ∉ domain m) : m[key]? = none := by
  cases hit : m[key]? with
  | none => rfl
  | some value => exact (outside ((domain_iff m key).mpr ⟨value,hit⟩)).elim

theorem agreed_domains {left right : Std.HashMap κ α} (agrees : Agrees left right) (key : κ) :
    key ∈ domain left ↔ key ∈ domain right := by
  simp only [domain_iff,agrees key]

end Ix.Cert.SourceContext.Maps
end
