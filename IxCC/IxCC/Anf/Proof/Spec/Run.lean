import IxCC.Anf.Proof.Spec.Rewrite

/-! # P4 is correct

`Specialize.run` folds over the input's globals, rewriting each listed
caller's body and adding specialisations. Every global of the output below
the input's size is the input's global with its body kept or rewritten
(`RunInv`), and the output has every state's specialisations. So the walk's
simulation applies with P4's configurations (`V`) and rewritten code as the
other pass's closures (`RwClo`): calls of the input's ids simulate by the
fundamental lemma or the rewritten code's simulation one clock down,
redirected calls by `red_sim`, entering rewritten closures by `rw_fund`
(`hyp`). Hence the output refines the input and keeps its shape
(`run_refines`). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open WalkProof (WV WVs VOk)
open IxCC.Sem (Result SimUpTo)

variable {P Q : Program}

/-! ## The fold over the callers -/

theorem foldlM_inv {α β : Type} {Inv : β → Prop} {f : β → α → Except String β} :
    ∀ (xs : List α) (b : β) {b' : β}, (∀ b x b', x ∈ xs → Inv b → f b x = .ok b' → Inv b') → Inv b →
      xs.foldlM f b = .ok b' → Inv b'
  | [], b, b', _, hb, h => by simp only [List.foldlM_nil] at h; cases h; exact hb
  | x :: xs, b, b', hf, hb, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨b1, h1, h2⟩ := except_bind_ok h
    exact foldlM_inv xs b1 (fun b x b' hx => hf b x b' (List.mem_cons_of_mem _ hx))
      (hf b x b1 List.mem_cons_self hb h1) h2

theorem globalList_getElem? {R : Program} (hw : R.WF) (i : Nat) :
    R.globalList[i]? = (R.global? i).map (i, ·) := by
  unfold Program.globalList
  by_cases hi : i < R.size
  · rw [Prune.Proof.filterMap_getElem? (fun x hx => ?_) i, List.getElem?_range hi]
    · rfl
    · obtain ⟨gd, hgd⟩ := hw.2 x (List.mem_range.1 hx)
      exact ⟨_, by rw [hgd]; rfl⟩
  · have : ((List.range R.size).filterMap fun g => (R.global? g).map (g, ·)).length ≤ R.size := by
      refine Nat.le_trans (List.length_filterMap_le _ _) ?_
      simp
    rw [List.getElem?_eq_none (by omega)]
    cases hg : R.global? i with
    | none => rfl
    | some gd => exact absurd (hw.1 i gd hg) hi

/-- What the run keeps after processing some callers, for an output `Q`:
the state is well formed, and each of the input's globals has its
parameters and either its body or a rewrite of it, whose call sites' are
specialisations of an earlier state. -/
structure RunInv (P Q : Program) (st : St) : Prop where
  ok : StOk P st
  known : st.prog.known = P.known
  roots : st.prog.roots = P.roots
  glob : ∀ g gd, P.global? g = some gd → ∃ gd', st.prog.global? g = some gd' ∧ gd'.ps = gd.ps ∧
    (gd'.body = gd.body ∨ ∃ (defs : Src.NatMap Def) (stb : St),
      (∀ args : List Val, args.length = gd.ps.length → DefsOk P defs args.reverse) ∧ SGrows P stb st ∧
      (Pre P Q stb → RwE P Q defs gd.ps.length gd.body gd'.body))

theorem runInv_init (hw : P.WF) : RunInv P Q { prog := P } :=
  ⟨⟨hw, Nat.le_refl _⟩, rfl, rfl, fun g gd h => ⟨gd, h, rfl, .inl rfl⟩⟩

/-- One caller's step keeps the invariant. -/
theorem runInv_step (hw : P.WF) {inv : Nat} {key : Key.GKey} {D : List (GlobalId × List Bool)} {fuel : Nat}
    {st st1 : St} {f : GlobalId} {gd : GDef} (hf : P.global? f = some gd) (hflt : f < P.size)
    (hi : RunInv P Q st) {body : Exp}
    (h1 : (rewrite P inv key D fuel (Src.NatMap.ofList ((List.range gd.ps.length).map (·, Def.blank)))
      gd.ps.length gd.body).run { prog := st.prog, specs := st.specs, work := st.work, nodes := st.nodes } = .ok (body, st1)) :
    RunInv P Q { st1 with prog := st1.prog.withGlobals (st1.prog.globalList.map fun (p : GlobalId × GDef) =>
      if p.1 == f then { p.2 with body } else p.2) } := by
  obtain ⟨hs1, hg1, hr1⟩ := rewrite_ok (Q := Q) _ h1 hi.ok
  have hw1 := hs1.1
  have hgl := globalList_length hw1
  have hget : ∀ i, (st1.prog.withGlobals (st1.prog.globalList.map fun (p : GlobalId × GDef) =>
      if p.1 == f then { p.2 with body } else p.2)).global? i =
      (st1.prog.global? i).map fun gd' => if i == f then { gd' with body } else gd' := by
    intro i
    rw [Prune.Proof.withGlobals_global, List.getElem?_map, globalList_getElem? hw1, Option.map_map]
    rfl
  have hsize : (st1.prog.withGlobals (st1.prog.globalList.map fun (p : GlobalId × GDef) =>
      if p.1 == f then { p.2 with body } else p.2)).size = st1.prog.size := by
    simp only [Program.withGlobals, List.length_map]
    exact (List.length_map _).symm.trans hgl
  have hsg : SGrows P st1 { st1 with prog := st1.prog.withGlobals (st1.prog.globalList.map
      fun (p : GlobalId × GDef) => if p.1 == f then { p.2 with body } else p.2) } := by
    refine ⟨by simp only [hsize]; exact Nat.le_refl _, fun s hs hlt => ?_⟩
    simp only
    rw [hget]
    have hne : (s == f) = false := by
      rw [beq_eq_false_iff_ne]; exact fun e => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (e ▸ hflt) hs)
    cases st1.prog.global? s <;> simp [hne]
  refine ⟨⟨withGlobals_wf _ _, by simp only [hsize]; exact hs1.2⟩, ?_, ?_, fun g gdP hgP => ?_⟩
  · show st1.prog.known = P.known
    rw [hg1.2.2.1]; exact hi.known
  · show st1.prog.roots = P.roots
    rw [hg1.2.2.2]; exact hi.roots
  · obtain ⟨gd', hgd', hps, hbody⟩ := hi.glob g gdP hgP
    have hglt : g < st.prog.size := Nat.lt_of_lt_of_le (hw.1 g gdP hgP) hi.ok.2
    have hg1' : st1.prog.global? g = some gd' := by rw [hg1.2.1 g hglt]; exact hgd'
    by_cases hgf : g = f
    · subst hgf
      rw [hf] at hgP; cases hgP
      refine ⟨{ gd' with body }, by simp only; rw [hget, hg1']; simp, hps,
        .inr ⟨Src.NatMap.ofList ((List.range gd.ps.length).map (·, Def.blank)), st1, ?_, hsg, ?_⟩⟩
      · intro args _; exact DefsOk.ofBlanks _ _
      · intro hpre; exact hr1 hpre
    · refine ⟨gd', by simp only; rw [hget, hg1']; simp [hgf], hps, ?_⟩
      rcases hbody with hb | ⟨defs, stb, hD, hsg', hr⟩
      · exact .inl hb
      · exact .inr ⟨defs, stb, hD, hsg'.trans (hg1.sgrows.trans hsg), hr⟩

/-- The run's output: a state that keeps the invariant for it. -/
theorem run_inv (hw : P.WF) {cert : Cert} (h : run cert P = .ok Q) : ∃ st, RunInv P Q st ∧ Q = st.prog := by
  rw [run.eq_1] at h
  obtain ⟨st, h1, h⟩ := except_bind_ok h
  cases h
  refine ⟨st, foldlM_inv _ _ (fun b x b' hx hb h => ?_) (runInv_init hw) h1, rfl⟩
  obtain ⟨f, gd⟩ := x
  obtain ⟨hflt, hf⟩ := Program.mem_globalList.1 hx
  dsimp only at h
  split at h
  · cases h; exact hb
  · obtain ⟨⟨body, st1⟩, h1, h⟩ := except_bind_ok h
    dsimp only at h
    cases h
    exact runInv_step hw hf hflt hb h1

/-! ## The walk's hypotheses for P4 -/

section

variable {st : St} (hw : P.WF) (hi : RunInv P Q st) (hQ : Q = st.prog)
include hw hi hQ

/-- An input global in the output: its parameters, and its body or a
rewrite of it. -/
theorem run_glob {g : GlobalId} {gd : GDef} (hg : P.global? g = some gd) :
    ∃ gd', Q.global? g = some gd' ∧ gd'.ps = gd.ps ∧
      (gd'.body = gd.body ∨ RwClo P Q gd.ps.length [] gd.body gd'.body) := by
  obtain ⟨gd', hgd', hps, hbody⟩ := hi.glob g gd hg
  refine ⟨gd', by rw [hQ]; exact hgd', hps, ?_⟩
  rcases hbody with hb | ⟨defs, stb, hD, hsg, hr⟩
  · exact .inl hb
  · have hpre : Pre P Q st := fun s _ _ => by rw [hQ]
    refine .inr ⟨defs, ?_, fun args hl => by simpa using hD args hl⟩
    have := hr (hpre.of_sgrows hsg)
    simpa using this

theorem run_globRel : GlobRel P Q := fun g gd hg hps => by
  obtain ⟨gd', hQg, hps', hbody⟩ := run_glob hw hi hQ hg
  refine ⟨gd', hQg, hps', ?_⟩
  rcases hbody with hb | hc
  · rw [hb]; exact .idc .nil .nil
  · exact .xc .nil .nil hc

theorem run_known : Q.known = P.known := by rw [hQ]; exact hi.known

/-- **P4's output satisfies the walk's hypotheses**: valid configurations
read the input, calls and global values of the input's ids simulate one
clock down (the fundamental lemma or the rewritten code's simulation),
redirected calls simulate (`red_sim`), and so does entering rewritten
closures (`rw_fund`). -/
theorem hyp : WalkProof.Hyp P Q (V P Q) (RwClo P Q) where
  known := run_known hw hi hQ
  arity g gd hg := by
    obtain ⟨gd', h1, h2, -⟩ := run_glob hw hi hQ hg
    exact ⟨gd', h1, by rw [h2]⟩
  suffix C ρ ρ' prs ρ₂ ρ'₂ hv h1 h2 := by
    rcases hv with rfl | ⟨D, vs, Hv, hD, rfl, hact, hlv, hs1, hs2⟩
    · exact .inl rfl
    · exact .inr ⟨D, vs, Hv, hD, rfl, hact, hlv, hs1.trans h1, hs2.trans h2⟩
  cknown C ρ ρ' prs hv := by rcases hv with rfl | ⟨D, -, -, -, rfl, -⟩ <;> rfl
  cglob C ρ ρ' prs hv g := by rcases hv with rfl | ⟨D, -, -, -, rfl, -⟩ <;> rfl
  cbody C ρ ρ' prs hv g hin := by
    rcases hv with rfl | ⟨D, -, -, -, rfl, -⟩ <;> simp [Site.cfg] at hin
  inl C ρ ρ' prs ρ₂ hv := by rcases hv with rfl | ⟨D, -, -, -, rfl, -⟩ <;> exact .inl rfl
  call n hlow g vs ws hvs := by
    cases hP : P.global? g with
    | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
    | some gd =>
      obtain ⟨gd', hQg, hps, hbody⟩ := run_glob hw hi hQ hP
      rw [hQg]
      have hvl := hvs.length
      by_cases hl : vs.length = gd.ps.length
      · have hl' : ws.length = gd'.ps.length := by rw [hps, hvl, hl]
        refine (SimUpTo.later (c₁ := fun k => eval P k vs.reverse [] gd.body)
          (c₂ := fun k => eval Q k ws.reverse [] gd'.body) fun m hm => ?_).congr (fun k => ?_) (fun k => ?_)
        · rcases hbody with hb | hc
          · rw [hb]; exact (hlow m (by omega)).2.1 hvs.reverse .nil gd.body
          · exact ((hlow m (by omega)).2.2 .nil hc (WalkProof.of_pw hvs) hl).congr (fun k => by simp)
              (fun k => by simp)
        · simp only [Result.ofOption, Result.bind_ok, callVal, hl, if_true]
        · simp only [Result.ofOption, Result.bind_ok, callVal, hl', if_true]
      · have hl' : ¬ ws.length = gd'.ps.length := by rw [hps, hvl]; exact hl
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        simp only [Result.ofOption, Result.bind_ok, callVal, hl, if_false]
  glob n hlow g := by
    cases hP : P.global? g with
    | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
    | some gd =>
      obtain ⟨gd', hQg, hps, hbody⟩ := run_glob hw hi hQ hP
      rw [hQg]
      simp only [Result.ofOption, Result.bind_ok]
      unfold globVal
      rw [hps]
      cases hp : gd.ps with
      | nil =>
        refine SimUpTo.later fun m hm => ?_
        rcases hbody with hb | hc
        · rw [hb]; exact (hlow m (by omega)).2.1 .nil .nil gd.body
        · rw [hp] at hc
          exact ((hlow m (by omega)).2.2 .nil hc .nil rfl).congr (fun k => by simp) (fun k => by simp)
      | cons p ps =>
        refine SimUpTo.ok ?_
        rcases hbody with hb | hc
        · rw [hb]; exact .idc .nil .nil
        · rw [hp] at hc; exact .xc .nil .nil hc
  red n hlow C ρ ρ' r hV hr :=
    red_sim (fun D hD => spec_sim (run_globRel hw hi hQ) (fun m hm fuel => (hlow m hm).1 fuel) hD) hV hr
  xenter n hlow happ hcall hglob :=
    xc_enter (rw_fund (run_known hw hi hQ) (fun m hm => (hlow m hm).2.1) happ hcall hglob
      (fun m hm D hD => spec_sim (run_globRel hw hi hQ) (fun m' hm' fuel => (hlow m' (by omega)).1 fuel) hD)
      n (Nat.le_refl n))

end

/-! ## P4 is correct -/

/-- **P4 is correct**: on a program whose ids are exactly the globals below
its size, every certificate the re-run accepts gives a program of that
shape that refines the input. -/
theorem run_refines (hw : P.WF) {cert : Cert} (h : run cert P = .ok Q) : Q.WF ∧ Sem.Refines P Q := by
  obtain ⟨st, hi, hQ⟩ := run_inv hw h
  refine ⟨by rw [hQ]; exact hi.ok.1, WalkProof.refines (hyp hw hi hQ) (by rw [hQ]; exact hi.roots)⟩

/-- P4 as a pass: the certificate is the decision list. -/
def specPass : Sem.Transform Program Program where
  name := "P4 specialize"
  Cert := Cert
  pre P := P.WF
  run P c := run c P
  post Q := Q.WF
  correct _ _ _ hw h := run_refines hw h

/-! ## The traced shape (decision D-1) -/

theorem run_refines_traced (hw : P.WF) {cert : Cert} (h : run cert P = .ok Q) : Sem.TRefines P Q :=
  Sem.Refines.ofPure (run_refines hw h).2

/-- P4 as a traced pass. -/
def specTPass : Sem.TTransform Program Program := specPass.lift

end IxCC.Anf.Specialize.Proof
