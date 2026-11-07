import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionIncrement

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc

/-- Reconstruct the full canonical source boundary at the exact heap returned
by projection_increment. Existing join denotations, capture views and scopes
are retained by State.bind; this is stronger than its Tokens projection. -/
theorem projection_state_after
    {functions : Own.Plain.Signatures} {H H' : Heap} {external : Nat → Nat}
    {held roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State functions H (holdRoots external held) live ρf ρo roots joins Jf Jo)
    {x y location refs i : Nat} {body : Own.Body} {value : RVal}
    (member : y ∈ live) (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body))
    (field : body.fields[i]? = some value) (fresh : x ∉ live)
    (action : Own.Plain.evalAction (ρo.insert x value) H (.inc x 1) = .ok H') :
    ∃ logical, Own.Proof.Den H' value logical ∧
      Own.Plain.State functions H' (holdRoots external held) (live ++ [x])
        (ρf.insert x logical) (ρo.insert x value) (roots ++ [value]) joins Jf Jo ∧
      (∀ root, H.value? root = H'.value? root) := by
  obtain ⟨heap, effect, balance, values⟩ := Own.Plain.evalAction_inc_field
    (Src.NatMap.get?_insert_self ρo x value) before.counts cell (List.mem_of_getElem? field)
  have equal : heap = H' := Sem.Result.ok.inj (effect.symm.trans action)
  subst heap
  obtain ⟨logical, denotes⟩ := projection_denotation (Tokens.ofState before) member lookup cell field
  have denotes' : Own.Proof.Den H' value logical := by
    change H'.value? value = some logical
    rw [← values value]
    exact denotes
  have balance' : Balance H' (holdRoots external held) (roots ++ [value]) := by
    intro location
    have counted := balance location
    simp only [Balance, refsIn_append, refsIn] at counted ⊢
    omega
  exact ⟨logical, denotes', before.bind x fresh denotes' balance' (fun root _ => values root), values⟩


end IxCC.Cfg.Rc.Proof.Physical.Bridge
