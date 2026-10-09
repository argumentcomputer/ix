import Compilatrix.Own.Plain.Proof.StackIdentity
import Compilatrix.Own.Plain.Proof.CaptureRoots

/-! Rebuild borrowed captured-root accounting after terminal cleanup. Only
roots actually retained by the selected saved environment are required to
survive; discarded active variables need not retain valid heap denotations. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem StackViews.head {ρ : Own.Env} {live : List Fir.Var} {joins : Joins}
    {J : List JEntry} (h : StackViews ρ live joins J) :
    match J, joins with
    | e :: rest, (_, captured) :: older =>
      CaptureView e.env ρ captured live ∧ StackViews e.env captured older rest
    | _, _ => True := by
  cases h with
  | nil => trivial
  | cons hv ht => exact ⟨hv, ht⟩

theorem StackDen.retain {H H' : Heap} {owned : List RVal} {joins : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (h : StackDen H owned joins Jf Jo)
    {ρ : Own.Env} {live : List Fir.Var} {kept : List RVal}
    (views : StackViews ρ live joins Jo) (roots : EnvRoots ρ live kept)
    (preserve : ∀ v, v ∈ kept → H.value? v = H'.value? v) : StackDen H' kept joins Jf Jo := by
  induction h generalizing ρ live kept with
  | nil => exact .nil
  | @cons captured older ef eo jf jo he ht ih =>
    have views' : StackViews ρ live ((eo.id, captured) :: older) (eo :: jo) := by
      simpa only [he.id] using views
    obtain ⟨hv, hviews⟩ := StackViews.head views'
    have result : StackDen H' kept ((ef.id, captured) :: older) (ef :: jf) (eo :: jo) := by
      obtain ⟨capRoots, hcap, hsub⟩ := hv.roots roots
      have hpres : ∀ v, v ∈ capRoots → H.value? v = H'.value? v :=
        fun v hm => preserve v (hsub.subset hm)
      have hentry : EntryDen H' kept captured older ef eo :=
        { he with
          env := he.env.transport hcap hpres
          borrowed := ⟨capRoots, hcap, fun _ hm => hsub.subset hm⟩ }
      have htail := ih hviews hcap hpres
      exact .cons hentry (htail.reframe (fun _ hm => hsub.subset hm))
    exact result


end Compilatrix.Own.Plain
