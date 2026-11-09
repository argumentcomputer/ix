import IxCC.Own.Plain.Proof.Bindings
import IxCC.Own.Plain.Proof.StackIdentity
import IxCC.Own.Plain.Proof.StackScope

/-! Concrete induction invariant for the checked canonical producer. These
fields describe heaps, maps, syntax, and scopes; none presupposes execution
simulation. The final program theorem must construct them at empty entry. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

structure State (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Fir.Var) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (joins : Joins) (Jf : List Fir.JEntry) (Jo : List JEntry)
    (imm : List Fir.Var := []) : Prop where
  env : EnvDen H live ρf ρo
  roots : EnvRoots ρo live owned
  counts : Rc.Balance H external owned
  distinct : live.Nodup
  stack : StackDen H owned joins Jf Jo
  views : StackViews ρo live joins Jo
  scope : StackScope functions live joins Jf
  immSub : ∀ x, x ∈ imm → x ∈ live
  immOk : ImmEnv ρo imm

theorem state_empty (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (hb : Rc.Balance H external []) :
    State functions H external [] .leaf .leaf [] [] [] [] :=
  ⟨(by intro x hx; simp at hx), rfl, hb, List.nodup_nil, .nil, .nil _ _, .nil _,
    (by intro x hx; cases hx), (by intro x hx; cases hx)⟩

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
    hb, by simpa using fresh_nodup_append List.nodup_nil hf, .nil, .nil _ _, .nil _,
    (by intro x hx; cases hx), (by intro x hx; cases hx)⟩

theorem State.bind {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hd : Proof.Den H' v w) (hb : Rc.Balance H' external (roots ++ [v]))
    (hv : ∀ root, root ∈ roots → H.value? root = H'.value? root) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo imm := by
  refine ⟨(h.env.transport h.roots hv).insert x hd, h.roots.insert x v hx,
    hb, fresh_nodup_append h.distinct (by simp [fresh, hx]), ?_, h.views.bind x v hx, h.scope.bind x,
    fun y hy => List.mem_append_left _ (h.immSub y hy),
    h.immOk.insert_keep h.immSub x v hx⟩
  exact (h.stack.transport hv).reframe (fun _ hm => List.mem_append_left _ hm)

theorem State.bind_imm {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (himm : ImmVal v)
    (hd : Proof.Den H' v w) (hb : Rc.Balance H' external (roots ++ [v]))
    (hv : ∀ root, root ∈ roots → H.value? root = H'.value? root) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (imm ++ [x]) := by
  have hbase := h.bind x hx hd hb hv
  exact ⟨hbase.env, hbase.roots, hbase.counts, hbase.distinct, hbase.stack, hbase.views, hbase.scope,
    fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ (h.immSub y hy)
      · exact List.mem_append_right _ hy,
    h.immOk.insert_imm h.immSub x v hx himm⟩

theorem State.bind_rhs {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) (r : Fir.Rhs) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (himm : isImmRhs imm r = true → ImmVal v)
    (hd : Proof.Den H' v w) (hb : Rc.Balance H' external (roots ++ [v]))
    (hv : ∀ root, root ∈ roots → H.value? root = H'.value? root)
    (hnotPrim : ∀ op args, r ≠ .prim op args := by intro op args h; cases h) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (nextImm imm x r) := by
  have hnext : nextImm imm x r = if isImmRhs imm r then imm ++ [x] else imm := by
    cases r with
    | prim op args => exact False.elim (hnotPrim op args rfl)
    | _ => rfl
  rw [hnext]
  cases hr : isImmRhs imm r with
  | false => exact h.bind x hx hd hb hv
  | true => exact h.bind_imm x hx (himm hr) hd hb hv

theorem State.bind_prim {functions : Signatures} {H H' : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
    (x : Fir.Var) (op : Lam.Prim) (args : List Fir.Arg) {v : RVal} {w : Fir.Val} (hx : x ∉ live)
    (hs : args.all (argIn live) = true)
    (hargs : ImmEnv ρo (argVars args))
    (himm : ImmVal v)
    (hd : Proof.Den H' v w) (hb : Rc.Balance H' external (roots ++ [v]))
    (hv : ∀ root, root ∈ roots → H.value? root = H'.value? root) :
    State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
      (roots ++ [v]) joins Jf Jo (nextImm imm x (.prim op args)) := by
  have hsub' : ∀ y, y ∈ imm ++ argVars args → y ∈ live := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact h.immSub y hy
    · exact argVars_sub_live hs y hy
  have h' : State functions H external live ρf ρo roots joins Jf Jo (imm ++ argVars args) :=
    { h with immSub := hsub', immOk := h.immOk.append hargs }
  exact h'.bind_imm x hx himm hd hb hv

theorem State.declare {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo imm)
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
    State functions H external live ρf ρo roots ((j, live) :: joins) (ef :: Jf) (eo :: Jo) imm := by
  dsimp only
  refine ⟨h.env, h.roots, h.counts, h.distinct, ?_, ?_, ?_, h.immSub, h.immOk⟩
  · exact .cons (entryDen_declare h.env h.roots joins j ps rec body) h.stack
  · exact .cons (e := {
      id := j, charged := false, env := ρo, params := ps
      body := lowerCode (live ++ ps) (if rec then (j, live) :: joins else joins) body
      isRec := rec }) (CaptureView.declare ρo live h.distinct) h.views
  · exact .cons
      (e := { id := j, charged := false, env := ρf, params := ps, body, isRec := rec })
      (List.Sublist.refl _) ⟨hf, hb⟩ h.scope


end IxCC.Own.Plain
