import Compilatrix.Own.Plain.Proof.Bindings
import Compilatrix.Own.Plain.Proof.StackIdentity
import Compilatrix.Own.Plain.Proof.StackScope

/-! Concrete induction invariant for the checked canonical producer. These
fields describe heaps, maps, syntax, and scopes; none presupposes execution
simulation. The final program theorem must construct them at empty entry. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

structure State (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Fir.Var) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (joins : Joins) (Jf : List Fir.JEntry) (Jo : List JEntry) : Prop where
  env : EnvDen H live ρf ρo
  roots : EnvRoots ρo live owned
  counts : Rc.Balance H external owned
  distinct : live.Nodup
  stack : StackDen H owned joins Jf Jo
  views : StackViews ρo live joins Jo
  scope : StackScope functions live joins Jf

theorem state_empty (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (hb : Rc.Balance H external []) :
    State functions H external [] .leaf .leaf [] [] [] [] :=
  ⟨(by intro x hx; simp at hx), rfl, hb, List.nodup_nil, .nil, .nil _ _, .nil _⟩

theorem state_entry (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Rc.Balance H external vs) :
    State functions H external params (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs)
      vs [] [] [] := by
  have he : EnvDen H [] (.leaf : Fir.Env) (.leaf : Own.Env) := by intro x hx; simp at hx
  have hr : EnvRoots (.leaf : Own.Env) [] [] := rfl
  exact ⟨by simpa using he.bindAll params hd hl,
    by simpa using hr.bindAll params vs hl hf,
    hb, by simpa using fresh_nodup_append List.nodup_nil hf, .nil, .nil _ _, .nil _⟩

theorem State.bind {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hd : Proof.Den H' v w) (hb : Rc.Balance H' external (roots ++ [v]))
    (hv : ∀ root, root ∈ roots → H.value? root = H'.value? root) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo := by
  refine ⟨(h.env.transport h.roots hv).insert x hd, h.roots.insert x v hx,
    hb, fresh_nodup_append h.distinct (by simp [fresh, hx]), ?_, h.views.bind x v hx, h.scope.bind x⟩
  exact (h.stack.transport hv).reframe (fun _ hm => List.mem_append_left _ hm)

theorem State.declare {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (j : Fir.JoinId) (ps : List Fir.Var) (rec : Bool) (body : Fir.Code)
    (hf : fresh live ps = true)
    (hb : scopeOk functions (live ++ ps)
      (if rec then (j, ps.length) :: stackArities Jf else stackArities Jf) body = true) :
    let ef : Fir.JEntry :=
      { id := j, charged := false, env := ρf, params := ps, body, isRec := rec }
    let eo : JEntry := {
      id := j, charged := false, env := ρo, params := ps
      body := lowerCode (live ++ ps) (if rec then (j, live) :: joins else joins) body
      isRec := rec }
    State functions H external live ρf ρo roots ((j, live) :: joins) (ef :: Jf) (eo :: Jo) := by
  dsimp only
  refine ⟨h.env, h.roots, h.counts, h.distinct, ?_, ?_, ?_⟩
  · exact .cons (entryDen_declare h.env h.roots joins j ps rec body) h.stack
  · exact .cons (e := {
      id := j, charged := false, env := ρo, params := ps
      body := lowerCode (live ++ ps) (if rec then (j, live) :: joins else joins) body
      isRec := rec }) (CaptureView.declare ρo live h.distinct) h.views
  · exact .cons
      (e := { id := j, charged := false, env := ρf, params := ps, body, isRec := rec })
      (List.Sublist.refl _) ⟨hf, hb⟩ h.scope


end Compilatrix.Own.Plain
