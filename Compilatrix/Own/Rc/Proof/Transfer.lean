import Compilatrix.Own.Rc.Proof.ReleaseValue

/-! Root accounting for suspending callers and retaining join captures.
Reclassifying a root does not increment its count; dropping a disjoint list
of owned tokens preserves the complete values of retained roots, including
aliases shared between the two lists. -/

set_option autoImplicit false

namespace Compilatrix.Own.Rc

def holdRoots (external : Nat → Nat) (held : List RVal) : Nat → Nat :=
  fun l => external l + refsIn l held

theorem balance_hold {H : Heap} {external : Nat → Nat} {active held : List RVal} :
    Balance H external (active ++ held) ↔ Balance H (holdRoots external held) active := by
  constructor <;> intro h l <;>
    have he := h l
    <;> simp only [refsIn_append, holdRoots] at *
    <;> omega

theorem balance_unhold {H : Heap} {external : Nat → Nat} {held : List RVal}
    (h : Balance H (holdRoots external held) []) : Balance H external held := by
  intro l
  have he := h l
  simp only [holdRoots, refsIn] at he
  omega

theorem held_external {external : Nat → Nat} {held : List RVal} {v : RVal}
    (h : v ∈ held) : ExternalRoot (holdRoots external held) v := by
  cases v with
  | loc l =>
    have hp := refsIn_pos h
    change 0 < external l + refsIn l held
    omega
  | lit _ | ctor0 _ | erased => trivial

theorem external_hold {external : Nat → Nat} {held : List RVal} {v : RVal}
    (h : ExternalRoot external v) : ExternalRoot (holdRoots external held) v := by
  cases v with
  | loc l =>
    change 0 < external l at h
    change 0 < external l + refsIn l held
    omega
  | lit _ | ctor0 _ | erased => trivial

/-- Cleanup drops exactly the chosen tokens and preserves every retained
root. The lists need not contain different values: aliasing is accounted for
by multiplicity in Balance, including an alias of a released parent/child. -/
theorem dropAll_retaining (H : Heap) (dropped held : List RVal) {external : Nat → Nat}
    (hb : Balance H external (dropped ++ held)) :
    ∃ H', dropAll H dropped = some H' ∧ Balance H' external held ∧
      (∀ root, root ∈ held → H.value? root = H'.value? root) ∧
      (∀ root, ExternalRoot external root → H.value? root = H'.value? root) := by
  obtain ⟨H', hdrop, hb', hvalues⟩ := dropAll_value H dropped (balance_hold.mp hb)
  exact ⟨H', hdrop, balance_unhold hb',
    fun _ hm => hvalues _ (held_external hm),
    fun _ he => hvalues _ (external_hold he)⟩


end Compilatrix.Own.Rc
