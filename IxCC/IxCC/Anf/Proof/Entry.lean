import IxCC.Anf.Entry
import IxCC.Anf.Proof.Rel.Ident
import IxCC.Anf.Proof.Defun.Correct
import IxCC.Src.Proof.NatMap

/-! # The entries are correct

`Entry.run decl P` keeps every global of `P` at its id and adds the entries
above `P`'s size (`run_extends`, `run_wf`), so `P`'s code simulates itself in
the output (`Rel.Ident.level_ext`). A root it keeps runs as before
(`Rel.run_simUpTo`); an entry, on an input of exactly its `n` parameters, runs
what its root runs one charge later (`run_entry`: the root's value, then one
application of all the arguments, which is `Anf.run`), which `SimUpTo.laterR`
absorbs. So the output refines the input on every input of the declared
count (`run_refines`), and on such an input every root of the output takes
exactly the input's length (`run_exactArity`), which is P8's premise. -/

set_option autoImplicit false

namespace IxCC.Anf.Entry.Proof

open IxCC.Sem (Result SimUpTo Sim later Lang)
open IxCC.Anf.Rel (Pw IdV)

/-! ## The plan -/

theorem plan_length (P : Program) : ∀ (next : GlobalId) (xs : List (GlobalId × Nat)),
    (plan P next xs).1.length = xs.length
  | _, [] => rfl
  | next, (r, n) :: rest => by
    unfold plan
    split
    · simp only [List.length_cons, plan_length P next rest]
    · simp only [List.length_cons, plan_length P (next + 1) rest]

/-- The entries are numbered `next, next + 1, …`. -/
theorem plan_keys (P : Program) : ∀ (next : GlobalId) (xs : List (GlobalId × Nat)),
    (plan P next xs).2.map (·.1) = List.range' next (plan P next xs).2.length
  | _, [] => rfl
  | next, (r, n) :: rest => by
    unfold plan
    split
    · exact plan_keys P next rest
    · simp only [List.map_cons, List.length_cons, List.range'_succ, plan_keys P (next + 1) rest]

/-- The root at a position: kept, or pointed at its entry. -/
theorem plan_root (P : Program) : ∀ (next : GlobalId) (xs : List (GlobalId × Nat)) (j : Nat)
    (r : GlobalId) (n : Nat), xs[j]? = some (r, n) →
    ∃ r', (plan P next xs).1[j]? = some r' ∧
      ((P.arity? r = some n ∧ r' = r) ∨ (r', entryDef P r n) ∈ (plan P next xs).2)
  | _, [], _, _, _, h => by simp at h
  | next, (r0, n0) :: rest, j, r, n, h => by
    unfold plan
    split
    · rename_i ha
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r0, rfl, .inl ⟨ha, rfl⟩⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨r', h1, h2⟩ := plan_root P next rest j r n h
        exact ⟨r', by simpa using h1, h2⟩
    · cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨next, rfl, .inr List.mem_cons_self⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨r', h1, h2⟩ := plan_root P (next + 1) rest j r n h
        refine ⟨r', by simpa using h1, ?_⟩
        rcases h2 with h2 | h2
        · exact .inl h2
        · exact .inr (List.mem_cons_of_mem _ h2)

/-! ## Inserting the entries -/

theorem get?_foldl_insert_not : ∀ (es : List (GlobalId × GDef)) (M : Src.NatMap GDef) (k : Nat),
    k ∉ es.map (·.1) → (es.foldl (fun m e => m.insert e.1 e.2) M).get? k = M.get? k
  | [], _, _, _ => rfl
  | e :: es, M, k, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, get?_foldl_insert_not es _ k h.2, Src.NatMap.get?_insert, if_neg h.1]

theorem get?_foldl_insert_mem : ∀ (es : List (GlobalId × GDef)) (M : Src.NatMap GDef) (k : Nat) (gd : GDef),
    (es.map (·.1)).Nodup → (k, gd) ∈ es → (es.foldl (fun m e => m.insert e.1 e.2) M).get? k = some gd
  | [], _, _, _, _, h => by simp at h
  | e :: es, M, k, gd, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [get?_foldl_insert_not es _ _ hn.1, Src.NatMap.get?_insert_self]
    · exact get?_foldl_insert_mem es _ k gd hn.2 h

/-! ## The output -/

variable {decl : List Nat} {P E : Program}

/-- What a successful run is made of. -/
theorem run_ok (h : run decl P = .ok E) :
    P.roots.length = decl.length ∧
      E = { P with globals := (plan P P.size (P.roots.zip decl)).2.foldl (fun m e => m.insert e.1 e.2) P.globals
                   size := P.size + (plan P P.size (P.roots.zip decl)).2.length
                   roots := (plan P P.size (P.roots.zip decl)).1 } := by
  unfold run at h
  split at h
  · rename_i hl
    cases h
    exact ⟨hl, rfl⟩
  · cases h

theorem keys_nodup (P : Program) (next : GlobalId) (xs : List (GlobalId × Nat)) :
    ((plan P next xs).2.map (·.1)).Nodup := by
  rw [plan_keys]; exact List.nodup_range'

theorem key_ge {P : Program} {next : GlobalId} {xs : List (GlobalId × Nat)} {g : GlobalId}
    (h : g ∈ (plan P next xs).2.map (·.1)) : next ≤ g ∧ g < next + (plan P next xs).2.length := by
  rw [plan_keys, List.mem_range'_1] at h
  exact h

/-- Every global of the input is the output's, at its id. -/
theorem run_global_old (hw : P.WF) (h : run decl P = .ok E) {g : GlobalId} {gd : GDef}
    (hg : P.global? g = some gd) : E.global? g = some gd := by
  obtain ⟨-, rfl⟩ := run_ok h
  show (List.foldl _ P.globals _).get? g = some gd
  rw [get?_foldl_insert_not _ _ _ fun hm => absurd (key_ge hm).1 (Nat.not_le.2 (hw.1 g gd hg))]
  exact hg

/-- An entry is the output's global at its id. -/
theorem run_global_new (h : run decl P = .ok E) {g : GlobalId} {gd : GDef}
    (hm : (g, gd) ∈ (plan P P.size (P.roots.zip decl)).2) : E.global? g = some gd := by
  obtain ⟨-, rfl⟩ := run_ok h
  exact get?_foldl_insert_mem _ _ _ _ (keys_nodup _ _ _) hm

theorem run_tables (h : run decl P = .ok E) : E.known = P.known ∧ E.ctors = P.ctors := by
  obtain ⟨-, rfl⟩ := run_ok h
  exact ⟨rfl, rfl⟩

theorem run_extends (hw : P.WF) (h : run decl P = .ok E) : Rel.Ident.Extends P E :=
  ⟨(run_tables h).1, fun _ _ hg => run_global_old hw h hg⟩

/-- **The entries keep the shape of the ids**: `0 … size - 1`. -/
theorem run_wf (hw : P.WF) (h : run decl P = .ok E) : E.WF := by
  have hE := run_ok h
  refine ⟨fun g gd hg => ?_, fun g hg => ?_⟩
  · obtain ⟨-, hEq⟩ := hE
    by_cases hm : g ∈ (plan P P.size (P.roots.zip decl)).2.map (·.1)
    · have := (key_ge hm).2
      rw [hEq]; exact this
    · have hP : P.global? g = some gd := by
        rw [hEq] at hg
        change (List.foldl _ P.globals _).get? g = some gd at hg
        rwa [get?_foldl_insert_not _ _ _ hm] at hg
      rw [hEq]; exact Nat.lt_of_lt_of_le (hw.1 g gd hP) (Nat.le_add_right _ _)
  · obtain ⟨-, hEq⟩ := hE
    have hg' : g < P.size + (plan P P.size (P.roots.zip decl)).2.length := by rw [hEq] at hg; exact hg
    by_cases hlt : g < P.size
    · obtain ⟨gd, hgd⟩ := hw.2 g hlt
      exact ⟨gd, run_global_old hw h hgd⟩
    · have hm : g ∈ (plan P P.size (P.roots.zip decl)).2.map (·.1) := by
        rw [plan_keys, List.mem_range'_1]; omega
      obtain ⟨⟨g', gd⟩, hmem, rfl⟩ := List.mem_map.1 hm
      exact ⟨gd, run_global_new h hmem⟩

theorem run_roots_length (h : run decl P = .ok E) : E.roots.length = P.roots.length := by
  obtain ⟨hl, rfl⟩ := run_ok h
  show (plan P P.size (P.roots.zip decl)).1.length = _
  rw [plan_length, List.length_zip, hl, Nat.min_self]

/-- The output's root at a position: the input's, or its entry at the
declared count. -/
theorem run_root (h : run decl P = .ok E) {j : Nat} {r' : GlobalId} (hr : E.roots[j]? = some r') :
    ∃ r n, P.roots[j]? = some r ∧ decl[j]? = some n ∧
      ((P.arity? r = some n ∧ r' = r) ∨ E.global? r' = some (entryDef P r n)) := by
  have hj : j < E.roots.length := (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨hl, hEq⟩ := run_ok h
  have hjP : j < P.roots.length := by rw [← run_roots_length h]; exact hj
  obtain ⟨r, hrP⟩ : ∃ r, P.roots[j]? = some r := ⟨_, List.getElem?_eq_getElem hjP⟩
  obtain ⟨n, hdn⟩ : ∃ n, decl[j]? = some n := ⟨_, List.getElem?_eq_getElem (hl ▸ hjP : j < decl.length)⟩
  have hz : (P.roots.zip decl)[j]? = some (r, n) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨hrP, hdn⟩
  obtain ⟨r'', h1, h2⟩ := plan_root P P.size _ j r n hz
  have : r'' = r' := by
    rw [hEq] at hr
    change (plan P P.size (P.roots.zip decl)).1[j]? = some r' at hr
    rw [h1] at hr; exact Option.some.inj hr
  subst this
  refine ⟨r, n, hrP, hdn, ?_⟩
  rcases h2 with h2 | h2
  · exact .inl h2
  · exact .inr (run_global_new h h2)

/-- **An input of the declared count has exactly the arity of its root in
the output** (P8's premise, `Defun.Proof.ExactArity`). -/
theorem run_exactArity (hw : P.WF) (h : run decl P = .ok E) {i : Nat × List Nat} (hi : DeclExact decl i) :
    Defun.Proof.ExactArity E i := by
  intro r' gd hr hg
  obtain ⟨r, n, -, hdn, hcase⟩ := run_root h hr
  rw [hi n hdn]
  rcases hcase with ⟨ha, rfl⟩ | he
  · obtain ⟨gd0, hg0, hn⟩ := Option.map_eq_some_iff.1 ha
    rw [run_global_old hw h hg0, Option.some.injEq] at hg
    subst hg
    exact hn.symm
  · rw [he, Option.some.injEq] at hg
    subst hg
    simp [entryDef]

/-! ## An entry runs its root -/

/-- The entry's body over its parameters is a run of its root. -/
theorem eval_body (Q : Program) (r : GlobalId) {xs : List Val} (k : Nat) :
    eval Q k xs.reverse [] (body r xs.length) = Anf.run Q k r xs := by
  have hargs : ∀ v : Val, evalAtoms (v :: xs.reverse) ((List.range xs.length).map fun j => Atom.var (xs.length - j)) =
      some xs := fun v => by
    have := Defun.Proof.evalAtoms_downFrom [v] xs []
    simpa [Defun.downFrom] using this
  unfold body
  rw [eval_bind, run_eq, evalBind_glob, evalBind_glob]
  congr 1
  funext v
  rw [eval_bind, evalBind_app]
  simp only [Atom.eval, List.getElem?_cons_zero, Result.ofOption, Result.bind_ok, hargs, eval_ret']
  exact Result.bind_pure _

/-- **An entry, on exactly its parameters, runs its root one charge later.** -/
theorem run_entry {Q : Program} {e r : GlobalId} {n : Nat} {gd : GDef} (hE : Q.global? e = some gd)
    (hgd : gd = entryDef P r n) {xs : List Val} (hxs : xs.length = n) (k : Nat) :
    Anf.run Q k e xs = later k fun k => Anf.run Q k r xs := by
  subst hgd
  rw [run_eq, evalBind_glob, hE]
  simp only [Result.ofOption, Result.bind_ok]
  cases n with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero hxs
    subst hx
    rw [Defun.Proof.globVal_caf (by simp [entryDef])]
    have hlb : ∀ (c : Nat → Result Val) (g : Val → Result Val),
        (later k c).bind g = later k fun j => (c j).bind g := fun c g => by cases k <;> rfl
    rw [hlb]
    congr 1
    funext k'
    simp only [applyN_nil']
    rw [Result.bind_pure]
    exact eval_body Q r (xs := []) k'
  | succ n =>
    rw [Defun.Proof.globVal_fn (by simp [entryDef]), Result.bind_ok]
    have hl : xs.length = (entryDef P r (n + 1)).ps.length := by simp [entryDef, hxs]
    rw [Defun.Proof.applyN_exact hl (by simp [entryDef])]
    congr 1
    funext k'
    rw [List.append_nil]
    show eval Q k' xs.reverse [] (body r (n + 1)) = _
    rw [← hxs]
    exact eval_body Q r k'

/-! ## Refinement -/

theorem lits_idv : ∀ (ns : List Nat),
    Pw IdV (ns.map fun n => Val.lit (.nat n)) (ns.map fun n => Val.lit (.nat n))
  | [] => .nil
  | _ :: ns => .cons .lit (lits_idv ns)

/-- **The entries refine** their input on every input of the declared count. -/
theorem run_refines (hw : P.WF) (h : run decl P = .ok E) : Sem.RefinesOn (DeclExact decl) P E := by
  have L := Rel.Ident.level_ext (run_extends hw h)
  intro i hi
  have hsim : Sim IdV id (Lang.run P i) (Lang.run E i) := SimUpTo.sim fun N => by
    show SimUpTo IdV N (anfRun P i) (anfRun E i)
    unfold anfRun
    cases hr : E.roots[i.1]? with
    | none =>
      have : P.roots[i.1]? = none := by
        rw [List.getElem?_eq_none_iff] at hr ⊢
        rw [← run_roots_length h]; exact hr
      rw [this]; exact SimUpTo.stuck _
    | some r' =>
      obtain ⟨r, n, hp, hd, hcase⟩ := run_root h hr
      rw [hp]
      have hs := Rel.run_simUpTo Rel.Ident.structural (L N).glob (L N).app r (lits_idv i.2)
      rcases hcase with ⟨-, rfl⟩ | he
      · exact hs
      · have hlen : (i.2.map fun n => Val.lit (.nat n)).length = n := by
          rw [List.length_map]; exact hi n hd
        exact (SimUpTo.laterR (run_mono E r _) hs).congr (fun _ => rfl)
          (fun k => run_entry he rfl hlen k)
  exact (hsim.refines (Lang.mono P i) (Lang.mono E i)).mono fun _ _ h => Rel.Ident.obs h

end IxCC.Anf.Entry.Proof
