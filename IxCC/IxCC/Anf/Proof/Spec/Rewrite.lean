import IxCC.Anf.Proof.Spec.Rw

/-! # P4: what a caller's rewrite is

A successful rewrite of a caller's term (`Specialize.rewrite`) keeps the
pass's state well formed and only adds specialisations (`StOk`, `Grows`),
and, for an output that has the final state's specialisations (`Pre`), is
the rewrite relation (`RwE`): each rewritten call site's specialisation is
the one the site builds (`specialize_ok`, a fresh one, or one this run made
that is exactly it), each binding's definition holds of its value
(`defOf_ok`). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open IxCC.Sem (Result)

variable {P Q : Program}

/-! ## Definitions of bindings -/

theorem mapM_mem {α β : Type} {f : α → Option β} : ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
    ∀ {x : α}, x ∈ xs → ∃ y, f x = some y
  | [], _, _, _, hx => by simp at hx
  | x :: xs, ys, h, x', hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact mapM_mem hys hx

theorem defOf_ok {defs : Src.NatMap Def} {d : Nat} {c : Ixon.V3.LetContract} {b : Bind} {idx : Nat}
    (hb : ∀ g, b ≠ .glob g) : DfOk P defs d b (defOf d defs c b idx) := by
  intro ρ k v hD hd hv
  subst hd
  cases b with
  | atom a =>
    rw [evalBind_atom] at hv
    cases a with
    | var i =>
      simp only [Atom.eval] at hv
      cases hx : ρ[i]? with
      | none => rw [hx] at hv; cases hv
      | some x =>
        have hi : i < ρ.length := (List.getElem?_eq_some_iff.1 hx).1
        have hl : (Opd.lvl (ρ.length - 1 - i)).val ρ = some x := by
          rw [lvl_val (by omega), show ρ.length - 1 - (ρ.length - 1 - i) = i by omega]; exact hx
        rw [hx] at hv; cases hv
        simp only [defOf]
        cases hdl : defs.get? (ρ.length - 1 - i) with
        | none => trivial
        | some df => exact (hD _ _ hdl).copy hl
    | lit l =>
      cases l with
      | nat n =>
        simp only [Atom.eval, Result.ofOption] at hv; cases hv
        exact lvl_push ρ _
      | str _ => trivial
    | box => trivial
  | con cc as =>
    simp only [defOf]
    split
    · trivial
    · rw [evalBind_con] at hv
      cases hvs : evalAtoms ρ as with
      | none => rw [hvs] at hv; cases hv
      | some vs =>
        rw [hvs] at hv; cases hv
        have hop := atoms_opd_val hvs
        refine ⟨fun j hj => ?_, vs, opds_append [_] hop, lvl_push ρ _⟩
        obtain ⟨w, hw⟩ := mapM_mem hop hj
        exact lvl_lt hw
  | proj _ _ _ => trivial
  | prim _ _ => trivial
  | glob g => exact absurd rfl (hb g)
  | call _ _ => trivial
  | app _ _ => trivial
  | fn ps fb =>
    cases ps with
    | nil => rw [evalBind_fn_nil] at hv; cases hv
    | cons p ps =>
      rw [evalBind_fn P k ρ _ fb (List.cons_ne_nil _ _)] at hv; cases hv
      refine ⟨Nat.le_refl _, List.cons_ne_nil _ _, ?_⟩
      rw [show (Val.clos ρ (p :: ps).length fb [] :: ρ).length - ρ.length = 1 by simp]
      exact lvl_push ρ _

theorem dfGlob_ok {defs : Src.NatMap Def} {d : Nat} {g : GlobalId} :
    DfOk P defs d (.glob g) (if (P.arity? g).getD 0 > 0 then Def.glob g else Def.blank) := by
  intro ρ k v hD hd hv
  subst hd
  split
  · next hpos =>
    rw [evalBind_glob] at hv
    cases hg : P.global? g with
    | none => rw [hg] at hv; cases hv
    | some gd =>
      rw [hg] at hv
      simp only [Result.ofOption, Result.bind_ok] at hv
      have hps : gd.ps ≠ [] := by
        intro he
        simp [Program.arity?, hg, GDef.arity, he] at hpos
      unfold globVal at hv
      cases hp : gd.ps with
      | nil => exact absurd hp hps
      | cons _ _ =>
        rw [hp] at hv; cases hv
        exact ⟨gd, hg, hps, by rw [hp]; exact lvl_push ρ _⟩
  · trivial

/-! ## Call sites -/

/-- The state after adding a specialisation. -/
def addSpec (st : St) (spec : GDef) : St :=
  { st with prog := st.prog.withGlobals (st.prog.globalList.map (·.2) ++ [spec]), specs := st.specs + 1 }

/-- A fresh specialisation: added at the end of the program. -/
theorem create_goal {inv : Nat} {fkey : Key.GKey} {defs : Src.NatMap Def} {d : Nat} {g : GlobalId} {gd : GDef}
    {mask : List Bool} {as : List Atom} {t : Trees} {keys : List Key.ArgKey} {roots : List (Nat × Opd)}
    {st0 : St} {spec : GDef} (hsite : siteTrees P defs fkey inv d mask as = (t, keys, roots))
    (hst : StOk P st0) (hb : buildSpec P defs t roots g gd (gd.key.spec keys) st0.prog.size = .ok spec) :
    StOk P (addSpec st0 spec) ∧ Grows st0 (addSpec st0 spec) ∧
      (P.global? g = some gd → fixedOk gd g mask = true → Pre P Q (addSpec st0 spec) →
        SiteOk P Q defs d g as st0.prog.size (siteArgs t d as)) := by
  have hgl := globalList_length hst.1
  have hsize : (addSpec st0 spec).prog.size = st0.prog.size + 1 := by
    simp [addSpec, Program.withGlobals, hgl]
  have hget : ∀ i, (addSpec st0 spec).prog.global? i = (st0.prog.globalList.map (·.2) ++ [spec])[i]? :=
    fun i => Prune.Proof.withGlobals_global _ _ i
  have hnew : (addSpec st0 spec).prog.global? st0.prog.size = some spec := by
    rw [hget, List.getElem?_append_right (by omega), hgl]; simp
  refine ⟨⟨withGlobals_wf _ _, by rw [hsize]; have := hst.2; omega⟩, ⟨by rw [hsize]; omega,
    fun s hlt => ?_, rfl, rfl⟩, fun hg hfix hpre => ?_⟩
  · rw [hget, List.getElem?_append_left (by omega), globalList_get hst.1]
  · refine ⟨inv, fkey, gd, mask, t, keys, roots, spec, hg, hfix, hsite, hb, ⟨spec, ?_, rfl, rfl⟩, rfl⟩
    rw [hpre st0.prog.size hst.2 (by rw [hsize]; omega)]
    exact hnew

/-- Creating a fresh specialisation, as `specialize` does. -/
theorem create_ok {inv : Nat} {fkey : Key.GKey} {defs : Src.NatMap Def} {d : Nat} {g : GlobalId}
    {gd : GDef} {mask : List Bool} {as : List Atom} {t : Trees} {keys : List Key.ArgKey}
    {roots : List (Nat × Opd)} (hsite : siteTrees P defs fkey inv d mask as = (t, keys, roots))
    {st0 : St} (hst : StOk P st0) {r : Option (GlobalId × List Atom)} {st' : St}
    (h : (do
          let spec ← specialize.liftM (buildSpec P defs t roots g gd (gd.key.spec keys) st0.prog.size)
          set (addSpec st0 spec)
          pure (some (st0.prog.size, siteArgs t d as)) : M (Option (GlobalId × List Atom))).run st0 =
          .ok (r, st')) :
    StOk P st' ∧ Grows st0 st' ∧ ∀ s args, r = some (s, args) → P.global? g = some gd →
      fixedOk gd g mask = true → Pre P Q st' → SiteOk P Q defs d g as s args := by
  obtain ⟨spec, st2, h1, h⟩ := run_bind_ok h
  obtain ⟨hb, rfl⟩ := run_liftM_ok h1
  obtain ⟨u, st3, h2, h⟩ := run_bind_ok h
  have := run_set_ok h2
  subst this
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨h1, h2, h3⟩ := create_goal (Q := Q) hsite hst hb
  refine ⟨h1, h2, fun s args e hg hfix hpre => ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact h3 hg hfix hpre

/-- A rewritten call site: the state stays well formed and only gains
specialisations; a specialised call is a call site that builds the
specialisation it calls. -/
theorem specialize_ok {inv : Nat} {fkey : Key.GKey} {defs : Src.NatMap Def} {d : Nat} {g : GlobalId}
    {gd : GDef} {mask : List Bool} {as : List Atom} {st st' : St} {r : Option (GlobalId × List Atom)}
    (h : (specialize P inv fkey defs d g gd mask as).run st = .ok (r, st')) (hst : StOk P st) :
    StOk P st' ∧ Grows st st' ∧ ∀ s args, r = some (s, args) → P.global? g = some gd →
      fixedOk gd g mask = true → Pre P Q st' → SiteOk P Q defs d g as s args := by
  rw [specialize.eq_1] at h
  rcases hsite : siteTrees P defs fkey inv d mask as with ⟨t, keys, roots⟩
  rw [hsite] at h
  dsimp only at h
  split at h
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hst, Grows.refl _, fun _ _ e => nomatch e⟩
  · obtain ⟨st0, st1, hget, h⟩ := run_bind_ok h
    have hst0 : st0 = st := (run_get_ok hget).1
    have hst1 : st1 = st := (run_get_ok hget).2
    rw [hst0, hst1] at h
    try dsimp only at h
    split at h
    · -- an equal-keyed specialisation of this run
      next s gd' hfind =>
      have hp := List.find?_some hfind
      have hm := List.mem_of_find?_eq_some hfind
      obtain ⟨hlt, hgd'⟩ := Program.mem_globalList.1 hm
      have hps : P.size ≤ s := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1
      obtain ⟨spec, st2, h1, h⟩ := run_bind_ok h
      obtain ⟨hb, rfl⟩ := run_liftM_ok h1
      split at h
      · next hc =>
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hst, Grows.refl _, fun s' args e hg hfix hpre => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨inv, fkey, gd, mask, t, keys, roots, spec, hg, hfix, hsite, hb,
          ⟨gd', by rw [hpre s hps hlt, hgd'], hc.1.symm, (Exp.beq_eq hc.2).symm⟩, rfl⟩
      · exact create_ok hsite hst h
    · exact create_ok hsite hst h

/-! ## A caller's rewrite -/

section

variable {inv : Nat} {fkey : Key.GKey} {D : List (GlobalId × List Bool)} {fuel : Nat}
  (IH : ∀ {defs : Src.NatMap Def} {d : Nat} {e : Exp} {st : St} {e' : Exp} {st' : St},
    (rewrite P inv fkey D fuel defs d e).run st = .ok (e', st') → StOk P st →
    StOk P st' ∧ Grows st st' ∧ (Pre P Q st' → RwE P Q defs d e e'))
include IH

/-- The rest of a binding's rewrite: its body under the binding's
definition. -/
theorem bind_tail {defs : Src.NatMap Def} {d : Nat} {c : Ixon.V3.LetContract} {b b' : Bind} {body : Exp}
    {df : Def} {st st1 : St} {e' : Exp} {st' : St} (hst : StOk P st1) (hgr : Grows st st1)
    (hb : Pre P Q st1 → RwB P Q defs d b b') (hdf : DfOk P defs d b df)
    (h : (do
      let x ← rewrite P inv fkey D fuel (defs.insert d df) (d + 1) body
      pure (Exp.bind c b' x) : M Exp).run st1 = .ok (e', st')) :
    StOk P st' ∧ Grows st st' ∧ (Pre P Q st' → RwE P Q defs d (.bind c b body) e') := by
  obtain ⟨body', st2, h1, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨hs2, hg2, hr2⟩ := IH h1 hst
  exact ⟨hs2, hgr.trans hg2, fun hpre => .bind (hb (hpre.of_grows hg2)) hdf (hr2 hpre)⟩

end

theorem mapM_alts {defs : Src.NatMap Def} {d : Nat} {f : Alt → M Alt}
    (hf : ∀ (a : Alt) {st : St} {r : Alt} {st' : St}, (f a).run st = .ok (r, st') → StOk P st →
      StOk P st' ∧ Grows st st' ∧ (Pre P Q st' → ∃ key n b b', a = .mk key n b ∧ r = .mk key n b' ∧
        RwE P Q (blankDefs defs d n) (d + n) b b')) :
    ∀ (alts : List Alt) {st : St} {alts' : List Alt} {st' : St}, (alts.mapM f).run st = .ok (alts', st') →
      StOk P st → StOk P st' ∧ Grows st st' ∧ (Pre P Q st' → RwAlts P Q defs d alts alts')
  | [], st, alts', st', h, hst => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨hst, Grows.refl _, fun _ => .nil⟩
  | a :: alts, st, alts', st', h, hst => by
    rw [List.mapM_cons] at h
    obtain ⟨r, st1, h1, h⟩ := run_bind_ok h
    obtain ⟨rs, st2, h2, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hs1, hg1, hr1⟩ := hf a h1 hst
    obtain ⟨hs2, hg2, hr2⟩ := mapM_alts hf alts h2 hs1
    refine ⟨hs2, hg1.trans hg2, fun hpre => ?_⟩
    obtain ⟨key, n, b, b', rfl, rfl, hb⟩ := hr1 (hpre.of_grows hg2)
    exact .cons hb (hr2 hpre)

/-- **A caller's rewrite** keeps the state well formed, only adds
specialisations, and is the rewrite relation for an output with the final
state's specialisations. -/
theorem rewrite_ok : ∀ (fuel : Nat) {inv : Nat} {fkey : Key.GKey} {D : List (GlobalId × List Bool)}
    {defs : Src.NatMap Def} {d : Nat} {e : Exp} {st : St} {e' : Exp} {st' : St},
    (rewrite P inv fkey D fuel defs d e).run st = .ok (e', st') → StOk P st →
    StOk P st' ∧ Grows st st' ∧ (Pre P Q st' → RwE P Q defs d e e')
  | 0, _, _, _, _, _, _, _, _, _, h, _ => by
    rw [rewrite.eq_1] at h; exact (run_throw_ok h).elim
  | fuel + 1, inv, fkey, D, defs, d, e, st, e', st', h, hst => by
    have IH := fun {defs d e st e' st'} => rewrite_ok fuel (inv := inv) (fkey := fkey) (D := D)
      (defs := defs) (d := d) (e := e) (st := st) (e' := e') (st' := st')
    cases e with
    | bind c b body =>
      cases b with
      | fn ps fb =>
        rw [rewrite.eq_2] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        have he := run_modifyGet_ok h1
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        dsimp only at h
        obtain ⟨fb', st1, h2, h⟩ := run_bind_ok h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        try dsimp only at h
        obtain ⟨hs1, hg1, hr1⟩ := IH h2 hst
        exact bind_tail IH hs1 ((Grows.of_prog rfl).trans hg1) (fun hpre => .fn (hr1 hpre))
          (defOf_ok (fun _ e => nomatch e)) h
      | call g as =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.call g as) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        split at h
        · next mask gd hl hg =>
          -- the site's charge changes only the work counter
          obtain ⟨u, stc, hc, h⟩ := run_bind_ok h
          have hpc := run_charge_ok hc
          have hstc : StOk P stc := ⟨by rw [hpc]; exact hst.1, by rw [hpc]; exact hst.2⟩
          have hgc := Grows.of_prog hpc
          try dsimp only at h
          split at h
          · next hfix =>
            obtain ⟨r, st1, h2, h⟩ := run_bind_ok h
            obtain ⟨hs1, hg1, hsite⟩ := specialize_ok (Q := Q) h2 hstc
            split at h
            · next s args =>
              obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
              obtain ⟨rfl, rfl⟩ := run_pure_ok h3
              exact bind_tail IH hs1 (hgc.trans hg1) (fun hpre => .call (hsite s args rfl hg hfix hpre))
                (defOf_ok (fun _ e => nomatch e)) h
            · obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
              obtain ⟨rfl, rfl⟩ := run_pure_ok h3
              exact bind_tail IH hs1 (hgc.trans hg1) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
          · obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
            obtain ⟨rfl, rfl⟩ := run_pure_ok h3
            exact bind_tail IH hstc hgc (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
        · obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
          obtain ⟨rfl, rfl⟩ := run_pure_ok h3
          exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
      | glob g =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.glob g) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) dfGlob_ok h
      | atom a =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.atom a) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
      | con cc as =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.con cc as) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
      | proj cc i x =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.proj cc i x) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
      | prim p as =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.prim p as) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
      | app f as =>
        rw [rewrite.eq_3 P inv fkey D defs d fuel c (.app f as) body (fun _ _ e => nomatch e)] at h
        obtain ⟨idx, st0, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h1
        dsimp only at h
        obtain ⟨b', st1', h3, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h3
        exact bind_tail IH hst (Grows.refl _) (fun _ => .same) (defOf_ok (fun _ e => nomatch e)) h
    | join n r jb body =>
      rw [rewrite.eq_4] at h
      obtain ⟨jb', st1, h1, h⟩ := run_bind_ok h
      obtain ⟨body', st2, h2, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hs1, hg1, hr1⟩ := IH h1 hst
      obtain ⟨hs2, hg2, hr2⟩ := IH h2 hs1
      exact ⟨hs2, hg1.trans hg2, fun hpre => .join (hr1 (hpre.of_grows hg2)) (hr2 hpre)⟩
    | case x alts dflt =>
      rw [rewrite.eq_5] at h
      obtain ⟨alts', st1, h1, h⟩ := run_bind_ok h
      obtain ⟨hs1, hg1, hr1⟩ := mapM_alts (Q := Q) (defs := defs) (d := d) (fun a st r st' h hst => by
        obtain ⟨key, n, b⟩ := a
        dsimp only at h
        obtain ⟨b', st1, h1, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hs1, hg1, hr1⟩ := IH h1 hst
        exact ⟨hs1, hg1, fun hpre => ⟨key, n, b, b', rfl, rfl, hr1 hpre⟩⟩) alts h1 hst
      cases dflt with
      | none =>
        dsimp only at h
        obtain ⟨d', st2, h2, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h2
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        exact ⟨hs1, hg1, fun hpre => .case (hr1 hpre) .none⟩
      | some e0 =>
        dsimp only at h
        obtain ⟨d', st2, h2, h⟩ := run_bind_ok h
        obtain ⟨e0', h3, rfl⟩ := run_map_ok h2
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hs2, hg2, hr2⟩ := IH h3 hs1
        exact ⟨hs2, hg1.trans hg2, fun hpre => .case (hr1 (hpre.of_grows hg2)) (.some (hr2 hpre))⟩
    | tick b =>
      rw [rewrite.eq_6] at h
      obtain ⟨b', st1, h1, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hs1, hg1, hr1⟩ := IH h1 hst
      exact ⟨hs1, hg1, fun hpre => .tick (hr1 hpre)⟩
    | jump j as =>
      rw [rewrite.eq_7 P inv fkey D defs d (.jump j as) fuel (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e)
        (fun _ _ _ e => nomatch e) (fun _ e => nomatch e)] at h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hst, Grows.refl _, fun _ => .jump⟩
    | ret a =>
      rw [rewrite.eq_7 P inv fkey D defs d (.ret a) fuel (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e)
        (fun _ _ _ e => nomatch e) (fun _ e => nomatch e)] at h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hst, Grows.refl _, fun _ => .ret⟩
    | trap =>
      rw [rewrite.eq_7 P inv fkey D defs d .trap fuel (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e)
        (fun _ _ _ e => nomatch e) (fun _ e => nomatch e)] at h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hst, Grows.refl _, fun _ => .trap⟩

end IxCC.Anf.Specialize.Proof
