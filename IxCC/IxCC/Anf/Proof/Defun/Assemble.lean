import IxCC.Anf.Proof.Defun.Keys
import IxCC.Anf.Proof.Defun.Dispatch

/-! # P8's output: its globals and its dispatchers

Where `assemble` puts each global of a successful run (`assemble_get`): the
rewritten input globals at their ids (`assemble_old`), with the state the walk
reached when it made them, which the final state extends (`AccLe`,
`globalsGo_mem`); the dispatcher of each arity `1 … M` at `dispId`
(`assemble_disp`); the lifted functions after them (`assemble_lifted`); and no
global at an absent id below the input's size (`assemble_absent`). Every
closure source's global takes its captures and its arity (`sources_global`).

With the sources' distinct keys (`sources_keys`) these discharge the
hypotheses of the dispatcher lemmas, which therefore hold of P8's own output
(`run_dispatch_exact`, `run_dispatch_under`, `run_dispatch_over`). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-! ## The assembled program -/

/-- `b` has collected at least what `a` has. -/
def AccLe (a b : Acc) : Prop :=
  (∀ l ∈ a.lifted, l ∈ b.lifted) ∧ (∀ h, a.escapes.contains h = true → b.escapes.contains h = true) ∧
    a.maxApp ≤ b.maxApp

theorem AccLe.refl (a : Acc) : AccLe a a := ⟨fun _ h => h, fun _ h => h, Nat.le_refl _⟩

theorem AccLe.trans {a b c : Acc} (h1 : AccLe a b) (h2 : AccLe b c) : AccLe a c :=
  ⟨fun l hl => h2.1 l (h1.1 l hl), fun h hh => h2.2.1 h (h1.2.1 h hh), Nat.le_trans h1.2.2 h2.2.2⟩

theorem Grows.le {K : Key.GKey} {a b : Acc} (h : Grows K a b) : AccLe a b := by
  obtain ⟨_, -, -, hl, he, hm⟩ := h
  exact ⟨hl, he, hm⟩

theorem global_le {P : Program} {g : GlobalId} {gd gd' : GDef} {acc acc' : Acc}
    (h : Defun.global P g gd acc = .ok (gd', acc')) : AccLe acc acc' :=
  (global_grows h).le

theorem globalsGo_out {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {accF : Acc} {PF : List GlobalId},
    globalsGo P l acc parents out = .ok (gs, accF, PF) →
    gs.map (·.1) = out.reverse.map (·.1) ++ l.map (·.1) ∧ ∀ x ∈ out, x ∈ gs
  | [], _, _, out, _, _, _, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨by simp, fun x hx => List.mem_reverse.2 hx⟩
  | (g, gd) :: rest, acc, parents, out, gs, accF, PF, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      obtain ⟨h1, h2⟩ := globalsGo_out rest _ _ _ h
      exact ⟨by rw [h1]; simp, fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩

theorem globalsGo_le {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {accF : Acc} {PF : List GlobalId},
    globalsGo P l acc parents out = .ok (gs, accF, PF) → AccLe acc accF
  | [], _, _, _, _, _, _, h => by
    simp only [globalsGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact AccLe.refl _
  | (g, gd) :: rest, acc, parents, out, gs, accF, PF, h => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g gd acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      exact (global_le hg).trans (globalsGo_le rest _ _ _ h)

/-- Every walked global is in the output list in the form `global` gave it,
from a state that the final one extends. -/
theorem globalsGo_mem {P : Program} : ∀ (l : List (GlobalId × GDef)) (acc : Acc) (parents : List GlobalId)
    (out : List (GlobalId × GDef)) {gs : List (GlobalId × GDef)} {accF : Acc} {PF : List GlobalId},
    globalsGo P l acc parents out = .ok (gs, accF, PF) → ∀ g gd, (g, gd) ∈ l →
      ∃ gd' a a', (g, gd') ∈ gs ∧ Defun.global P g gd a = .ok (gd', a') ∧ AccLe a' accF
  | [], _, _, _, _, _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | (g0, gd0) :: rest, acc, parents, out, gs, accF, PF, h, g, gd, hm => by
    simp only [globalsGo] at h
    cases hg : Defun.global P g0 gd0 acc with
    | error e => simp only [hg] at h; cases h
    | ok r =>
      obtain ⟨gd', acc1⟩ := r
      simp only [hg] at h
      rcases List.mem_cons.1 hm with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨gd', acc, acc1, (globalsGo_out rest _ _ _ h).2 _ List.mem_cons_self, hg, globalsGo_le rest _ _ _ h⟩
      · exact globalsGo_mem rest _ _ _ h g gd hm

theorem map_fst_eq {α β γ : Type} {f : α × β → α × γ} (hf : ∀ a b, (f (a, b)).1 = a) :
    ∀ l : List (α × β), (l.map f).map (·.1) = l.map (·.1)
  | [] => rfl
  | (a, b) :: l => by simp only [List.map_cons, hf, map_fst_eq hf l]

theorem numbered_nodup {α : Type} : ∀ (k : Nat) (xs : List α), ((numbered k xs).map (·.1)).Nodup
  | _, [] => List.nodup_nil
  | k, x :: xs => by
    simp only [numbered, List.map_cons]
    refine List.nodup_cons.2 ⟨fun h => ?_, numbered_nodup (k + 1) xs⟩
    obtain ⟨⟨i, y⟩, hm, he⟩ := List.mem_map.1 h
    have := (mem_numbered hm).2
    dsimp only at he
    omega

/-- **The output's globals**: a rewritten global, a dispatcher, or a lifted
function, at the id `assemble` gives it (the ids are distinct). -/
theorem assemble_get {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {g : GlobalId} {x : GDef}
    (hx : (g, x) ∈ gs ∨ (∃ i, i < acc.maxApp ∧ g = P.size + i ∧ x = dispatcher P.size (sources P acc) (i + 1)) ∨
      ∃ l, (g, l) ∈ liftedAt P acc ∧ x = l.toGDef) :
    (assemble P gs acc).global? g = some x := by
  have hA : gs.map (·.1) = P.globalList.map (·.1) := by
    have := (globalsGo_out _ _ _ _ hr.walk).1
    simpa using this
  unfold assemble Program.global?
  dsimp only
  apply Src.NatMap.get?_ofList
  · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append, hA,
      map_fst_eq (fun _ _ => rfl), List.map_map]
    refine ⟨⟨globalList_ids_nodup P, ?_, ?_⟩, numbered_nodup _ _, ?_⟩
    · exact nodup_map_of_inj (fun a b h => by dsimp only [Function.comp] at h; omega) List.nodup_range
    · intro a ha b hb
      obtain ⟨⟨g', gd⟩, hm, rfl⟩ := List.mem_map.1 ha
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      have h1 : g' < P.size := (mem_globalList.1 hm).1
      show g' ≠ P.size + i
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
    · intro a ha b hb
      obtain ⟨⟨i, l⟩, hm, rfl⟩ := List.mem_map.1 hb
      have h1 : liftBase P acc ≤ i := (mem_numbered hm).2
      unfold liftBase at h1
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨⟨g', gd⟩, hm', rfl⟩ := List.mem_map.1 ha
        have h2 : g' < P.size := (mem_globalList.1 hm').1
        show g' ≠ i
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_trans (Nat.le_add_right _ _) h1))
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
        have h2 : j < acc.maxApp := List.mem_range.1 hj
        show P.size + j ≠ i
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left h2 _) h1)
  · rcases hx with hx | ⟨i, hi, rfl, rfl⟩ | ⟨l, hl, rfl⟩
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    · exact List.mem_append_right _ (List.mem_map.2 ⟨(g, l), hl, rfl⟩)

/-- An input global has its rewritten form at its id. -/
theorem assemble_old {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {g : GlobalId} {gd : GDef} (hlt : g < P.size) (hg : P.global? g = some gd) :
    ∃ gd' a a', (assemble P gs acc).global? g = some gd' ∧ Defun.global P g gd a = .ok (gd', a') ∧ AccLe a' acc := by
  obtain ⟨gd', a, a', hm, hgl, hle⟩ := globalsGo_mem _ _ _ _ hr.walk g gd (mem_globalList.2 ⟨hlt, hg⟩)
  exact ⟨gd', a, a', assemble_get hr (.inl hm), hgl, hle⟩

/-- The dispatcher of each arity `1 … M` is at `dispId`. -/
theorem assemble_disp {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ acc.maxApp) :
    (assemble P gs acc).global? (dispId P.size m) = some (dispatcher P.size (sources P acc) m) := by
  have he : dispId P.size m = P.size + (m - 1) := Nat.add_sub_assoc h1 P.size
  have hd : dispatcher P.size (sources P acc) m = dispatcher P.size (sources P acc) (m - 1 + 1) := by
    rw [Nat.sub_add_cancel h1]
  have hi : m - 1 < acc.maxApp := by omega
  exact assemble_get hr (g := dispId P.size m) (x := dispatcher P.size (sources P acc) m)
    (.inr (.inl ⟨m - 1, hi, he, hd⟩))

theorem assemble_lifted {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {i : GlobalId} {l : Lifted} (h : (i, l) ∈ liftedAt P acc) :
    (assemble P gs acc).global? i = some l.toGDef :=
  assemble_get hr (.inr (.inr ⟨l, h, rfl⟩))

/-- An absent id below the input's size stays absent. -/
theorem assemble_absent {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {g : GlobalId} (hlt : g < P.size) (hg : P.global? g = none) :
    (assemble P gs acc).global? g = none := by
  cases hq : (assemble P gs acc).global? g with
  | none => rfl
  | some gd =>
    rcases assemble_mem hq with hm | ⟨hle, -⟩ | ⟨hle, -⟩
    · have hgs := globalsGo_ps P.globalList {} [] [] (by simp) (fun g gd hx => by
        obtain ⟨hlt, hgd⟩ := mem_globalList.1 hx
        exact ⟨hgd, hlt⟩) hr.walk
      obtain ⟨gd0, hgd0, -, -⟩ := hgs _ _ hm
      rw [hg] at hgd0
      cases hgd0
    · exact absurd hle (Nat.not_le.2 hlt)
    · exact absurd hle (Nat.not_le.2 hlt)

/-- Every closure source's global takes its captures and its arity. -/
theorem sources_global {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {s : Source} (hs : s ∈ sources P acc) :
    ∃ gd, (assemble P gs acc).global? s.id = some gd ∧ gd.ps.length = s.caps + s.arity := by
  unfold sources at hs
  rcases List.mem_append.1 hs with hs | hs
  · unfold escapeSources at hs
    obtain ⟨h, hh, hsh⟩ := List.mem_filterMap.1 hs
    by_cases he : acc.escapes.contains h = true
    · rw [ite_eq_left he] at hsh
      cases hg : P.global? h with
      | none => rw [hg] at hsh; cases hsh
      | some hd =>
        rw [hg] at hsh
        cases hsh
        obtain ⟨gd', a, a', hq, hgl, -⟩ := assemble_old hr (List.mem_range.1 hh) hg
        refine ⟨gd', hq, ?_⟩
        rw [global_ps hgl]
        exact (Nat.zero_add _).symm
    · rw [ite_eq_right he] at hsh
      cases hsh
  · obtain ⟨⟨i, l⟩, hm, rfl⟩ := List.mem_map.1 hs
    exact ⟨l.toGDef, assemble_lifted hr hm, by simp [Lifted.toGDef]⟩

/-- A source in a list whose keys are distinct has no earlier source with its key. -/
theorem split_nodup {srcs : List Source} (hk : (srcs.map (·.key)).Nodup) {s : Source} (hs : s ∈ srcs) :
    ∃ pre post, srcs = pre ++ s :: post ∧ ∀ s' ∈ pre, s'.key ≠ s.key := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hs
  refine ⟨pre, post, rfl, fun s' hs' he => ?_⟩
  rw [List.map_append, List.nodup_append] at hk
  exact hk.2.2 s'.key (List.mem_map.2 ⟨s', hs', rfl⟩) s.key (List.mem_map.2 ⟨s, List.mem_cons_self, rfl⟩) he

/-! ## The dispatchers of P8's output -/

/-- **Exactly the missing arguments**, on P8's output: the call of the
dispatcher is the call of the source's global, two charges in all. -/
theorem run_dispatch_exact {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {s : Source} (hs : s ∈ sources P acc) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ acc.maxApp)
    {k : Nat} {ρ : List Val} {as : List Atom} {j : Nat} {fs args : List Val} (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : m = s.arity - j) :
    ∃ gd, (assemble P gs acc).global? s.id = some gd ∧
      evalBind (assemble P gs acc) (k + 2) ρ (.call (dispId P.size m) as) =
        eval (assemble P gs acc) k (fs ++ args).reverse [] gd.body := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_nodup (sources_keys hr) hs
  obtain ⟨gd, hgd, hps⟩ := sources_global hr hs
  exact ⟨gd, hgd, dispatch_exact (assemble_disp hr h1 h2) hsplit hpre hgd hps hj hfs hv hargs hm⟩

/-- **Fewer arguments**, on P8's output: the cell with `j + m` arguments. -/
theorem run_dispatch_under {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {s : Source} (hs : s ∈ sources P acc) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ acc.maxApp)
    {k : Nat} {ρ : List Val} {as : List Atom} {j : Nat} {fs args : List Val} (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : m < s.arity - j) :
    evalBind (assemble P gs acc) (k + 1) ρ (.call (dispId P.size m) as) = .ok (.con (.clo s.key (j + m)) (fs ++ args)) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_nodup (sources_keys hr) hs
  exact dispatch_under (assemble_disp hr h1 h2) hsplit hpre hj hfs hv hargs hm

/-- **More arguments**, on P8's output: the call of the source's global on
the fields and the first `r` arguments, then the dispatcher of arity `m - r`
on its result and the rest. -/
theorem run_dispatch_over {P : Program} {gs : List (GlobalId × GDef)} {acc : Acc} {parents : List GlobalId}
    (hr : Ran P gs acc parents) {s : Source} (hs : s ∈ sources P acc) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ acc.maxApp)
    {k : Nat} {ρ : List Val} {as : List Atom} {j : Nat} {fs args : List Val} (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : s.arity - j < m) :
    ∃ gd, (assemble P gs acc).global? s.id = some gd ∧
      evalBind (assemble P gs acc) (k + 2) ρ (.call (dispId P.size m) as) =
        (eval (assemble P gs acc) k (fs ++ args.take (s.arity - j)).reverse [] gd.body).bind fun v =>
          eval (assemble P gs acc) k (v :: args.drop (s.arity - j)).reverse []
            (dispatcher P.size (sources P acc) (m - (s.arity - j))).body := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_nodup (sources_keys hr) hs
  obtain ⟨gd, hgd, hps⟩ := sources_global hr hs
  exact ⟨gd, hgd, dispatch_over (assemble_disp hr h1 h2) hsplit hpre hgd hps hj hfs hv hargs hm
    (assemble_disp hr (by omega) (by omega))⟩

end IxCC.Anf.Defun.Proof
