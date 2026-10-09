import Compilatrix.Cfg.Rc.Proof.Physical.DropPrefix

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc

/-- Match the actual completed native cleanup's source action receipt with
the independent source cleanup theorem. Only held and retained roots survive;
discarded lexical roots are deliberately absent from this conclusion. -/
theorem drop_preservation {H H' : Heap} {external : Nat → Nat}
    {held roots kept : List RVal} {captured live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (actions : Own.Plain.evalActions ρo H (Own.Plain.drops captured live) = .ok H')
    (afterRoots : Own.Plain.EnvRoots ρo (Own.Plain.retained captured live) kept) :
    (∀ root ∈ kept, root ∈ roots) ∧
    (∀ root ∈ held ++ kept, H.value? root = H'.value? root) ∧
    (∀ root, ExternalRoot external root → H.value? root = H'.value? root) := by
  have balance : Balance H external (held ++ roots) := by
    intro location
    have counted := before.balance location
    simp only [holdRoots, refsIn_append] at counted ⊢
    omega
  obtain ⟨actual, retained, result, rootReceipt, counts, subset, values, outside⟩ :=
    Own.Plain.drops_sound ρo H captured live before.exactRoots balance
  have heapEqual : actual = H' := by injection result.symm.trans actions
  subst actual
  have rootEqual : retained = kept := Option.some.inj (rootReceipt.symm.trans afterRoots)
  subst retained
  exact ⟨subset, values, outside⟩


end Compilatrix.Cfg.Rc.Native
