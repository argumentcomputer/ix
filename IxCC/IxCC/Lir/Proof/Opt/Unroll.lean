import IxCC.Lir.Opt.Unroll
import IxCC.Lir.Proof.Opt.Potential
import IxCC.Lir.Proof.Opt.Inline
import IxCC.Lir.Proof.Steps
import IxCC.Lir.Proof.Eval
import IxCC.Src.Proof.NatMap
import IxCC.Sem.Forward
import IxCC.Sem.Simulation

/-!
# Direct soundness proofs for bounded loop unrolling & odd-fixnum loop versioning (`Lir.Opt.Unroll`)

Proves:
1. `unrollLoopSite_sim : Sem.Sim Eq (fun k => U * k + (U - 1))` (and `unrollLoopSiteChecked_sim` /
   `unrollLoopSiteChecked_wellFormed`) directly via `PotentialForward`.
2. `versionOddLoopSite_sim : Sem.Sim Eq id` (and `versionOddLoopSiteChecked_sim` /
   `versionOddLoopSiteChecked_wellFormed`) directly via `Sem.Forward`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word Env Frame State Step semStep
  semStep_next semStep_fail semStep_trap semStep_done evalArgs bindParams enter
  takeEdge step step_stmt step_call step_term step_jump step_br step_brOvf
  step_ret_done step_ret_caller step_tail step_fail step_trap star_of_step
  eval eval_mono runs_eval env_insert_self env_insert_ne env_insert_get env_empty)

/-! ## Part 1: `NatSet`, sorted list, `listIndexOf`, `flatMap`, and `bindParams` helpers -/

private theorem natSet_contains_leaf (k : Nat) : (Src.NatMap.leaf : Src.NatSet).contains k = false := rfl

private theorem array_getElem!_of_getElem? {α : Type} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : a[i]! = x := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  simp [hlt]

private theorem natSet_contains_insert (s : Src.NatSet) (k k' : Nat) :
    (s.insert k).contains k' = (k' == k || s.contains k') := by
  simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  by_cases h : k' = k
  · subst h; simp
  · have hne : (k' == k) = false := beq_false_of_ne h
    simp [h, hne]

private theorem natSet_contains_foldl_insert :
    ∀ (xs : List Nat) (s : Src.NatSet) (k : Nat),
      (xs.foldl (fun a x => a.insert x) s).contains k = true ↔ k ∈ xs ∨ s.contains k = true
  | [], s, k => by simp
  | x :: rest, s, k => by
      simp only [List.foldl_cons, List.mem_cons]
      rw [natSet_contains_foldl_insert rest (s.insert x) k, natSet_contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro (hr | (rfl | hs))
        · exact .inl (.inr hr)
        · exact .inl (.inl rfl)
        · exact .inr hs
      · rintro ((rfl | hr) | hs)
        · exact .inr (.inl rfl)
        · exact .inl hr
        · exact .inr (.inr hs)

private theorem natSet_ofList_contains (xs : List Nat) (k : Nat) :
    (Src.NatSet.ofList xs).contains k = true ↔ k ∈ xs := by
  have hfold : ∀ (ys : List Nat) (m : Src.NatSet),
      ((ys.map (·, ())).foldl (fun m (p : Nat × Unit) => Src.NatMap.insert m p.1 p.2) m).contains k = true ↔
        k ∈ ys ∨ m.contains k = true := by
    intro ys
    induction ys with
    | nil => intro m; simp
    | cons y rest ih =>
        intro m
        simp only [List.map_cons, List.foldl_cons, List.mem_cons]
        rw [ih (Src.NatMap.insert m y ())]
        have hi : (Src.NatMap.insert m y ()).contains k = (k == y || m.contains k) := natSet_contains_insert m y k
        rw [hi]; simp only [Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro (hr | (rfl | hm))
          · exact .inl (.inr hr)
          · exact .inl (.inl rfl)
          · exact .inr hm
        · rintro ((rfl | hr) | hm)
          · exact .inr (.inl rfl)
          · exact .inl hr
          · exact .inr (.inr hm)
  simpa [Src.NatSet.ofList, Src.NatMap.ofList, natSet_contains_leaf] using hfold xs .leaf

private theorem natSet_ofList_contains_false (xs : List Nat) (k : Nat) :
    (Src.NatSet.ofList xs).contains k = false ↔ k ∉ xs := by
  cases h : (Src.NatSet.ofList xs).contains k
  · constructor
    · intro _ hmem; have := (natSet_ofList_contains xs k).2 hmem; rw [h] at this; cases this
    · intro _; rfl
  · constructor
    · intro hf; cases hf
    · intro hnm; exact absurd ((natSet_ofList_contains xs k).1 h) hnm

private theorem natSet_mem_toList {s : Src.NatSet} {k : Nat} (h : s.contains k = true) :
    (k, ()) ∈ s.toList := by
  simp only [Src.NatMap.contains, Option.isSome_iff_exists] at h
  obtain ⟨u, hu⟩ := h
  cases u
  exact Src.NatMap.mem_toList hu

private theorem isStrictlySorted_cons_cons {a b : Nat} {rest : List Nat}
    (h : isStrictlySorted (a :: b :: rest) = true) :
    a < b ∧ isStrictlySorted (b :: rest) = true := by
  simpa [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] using h

private theorem isStrictlySorted_lt :
    ∀ {xs : List Nat} {i j a b : Nat},
      isStrictlySorted xs = true →
      xs[i]? = some a → xs[j]? = some b → i < j → a < b
  | [], _, _, _, _, _, ha, _, _ => by simp at ha
  | [_], i, j, _, _, _, ha, hb, hij => by
      have hi : i < 1 := (List.getElem?_eq_some_iff.1 ha).1
      have hj : j < 1 := (List.getElem?_eq_some_iff.1 hb).1
      omega
  | x :: y :: rest, 0, j + 1, a, b, hs, ha, hb, _ => by
      obtain ⟨hxy, hsr⟩ := isStrictlySorted_cons_cons hs
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha; subst ha
      simp only [List.getElem?_cons_succ] at hb
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb; subst hb; exact hxy
      | succ j' =>
          have hyb := isStrictlySorted_lt hsr (i := 0) (j := j' + 1) (by rfl) hb (by omega)
          omega
  | x :: y :: rest, i + 1, j + 1, a, b, hs, ha, hb, hij => by
      obtain ⟨_, hsr⟩ := isStrictlySorted_cons_cons hs
      simp only [List.getElem?_cons_succ] at ha hb
      exact isStrictlySorted_lt hsr ha hb (by omega)
  | _ :: _ :: _, _, 0, _, _, _, _, _, hij => by omega

private theorem isStrictlySorted_head_le {xs : List Nat} {h i b : Nat}
    (hs : isStrictlySorted xs = true) (hhead : xs.head? = some h) (hi : xs[i]? = some b) :
    h ≤ b := by
  cases xs with
  | nil => simp at hhead
  | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; omega
      | succ i' =>
          have hlt := isStrictlySorted_lt hs (i := 0) (j := i' + 1) rfl hi (by omega)
          omega

private theorem isStrictlySorted_le_getLastD :
    ∀ {xs : List Nat} {d i b : Nat},
      isStrictlySorted xs = true → xs[i]? = some b → b ≤ xs.getLastD d
  | [], _, _, _, _, hi => by simp at hi
  | [x], d, i, b, _, hi => by
      have hlt : i < 1 := (List.getElem?_eq_some_iff.1 hi).1
      have : i = 0 := by omega
      subst this; simp at hi; subst hi; simp [List.getLastD]
  | x :: y :: rest, d, i, b, hs, hi => by
      obtain ⟨hxy, hsr⟩ := isStrictlySorted_cons_cons hs
      have hlast : (x :: y :: rest).getLastD d = (y :: rest).getLastD d := rfl
      rw [hlast]
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
          have hy := isStrictlySorted_le_getLastD (d := d) (i := 0) hsr rfl
          omega
      | succ i' =>
          simp only [List.getElem?_cons_succ] at hi
          exact isStrictlySorted_le_getLastD hsr hi

private theorem listIndexOf_go_eq_some :
    ∀ (xs : List Nat) (target i idx : Nat),
      listIndexOf.go target i xs = some idx → i ≤ idx ∧ xs[idx - i]? = some target
  | [], _, _, _, h => by simp [listIndexOf.go] at h
  | x :: rest, target, i, idx, h => by
      unfold listIndexOf.go at h
      by_cases hx : (x == target) = true
      · simp only [hx, ↓reduceIte, Option.some.injEq] at h
        have hx' : x = target := by simpa using hx
        subst h; subst hx'; simp
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hle, hget⟩ := listIndexOf_go_eq_some rest target (i + 1) idx h
        refine ⟨by omega, ?_⟩
        have hsub : idx - i = (idx - (i + 1)) + 1 := by omega
        rw [hsub, List.getElem?_cons_succ]
        exact hget

private theorem listIndexOf_eq_some {xs : List Nat} {target idx : Nat}
    (h : listIndexOf xs target = some idx) : xs[idx]? = some target := by
  have := (listIndexOf_go_eq_some xs target 0 idx h).2
  simpa using this

private theorem mem_listIndexOf_go :
    ∀ (xs : List Nat) (target i : Nat),
      target ∈ xs → ∃ idx, listIndexOf.go target i xs = some idx
  | [], _, _, hm => by cases hm
  | x :: rest, target, i, hm => by
      unfold listIndexOf.go
      by_cases hx : (x == target) = true
      · simp [hx]
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        have hne : x ≠ target := fun heq => by subst heq; simp at hx
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact absurd rfl hne
        · exact mem_listIndexOf_go rest target (i + 1) hm'

private theorem mem_listIndexOf {xs : List Nat} {target : Nat} (hm : target ∈ xs) :
    ∃ idx, listIndexOf xs target = some idx ∧ xs[idx]? = some target := by
  obtain ⟨idx, h⟩ := mem_listIndexOf_go xs target 0 hm
  exact ⟨idx, h, listIndexOf_eq_some h⟩

private theorem listIndexOf_of_sorted {xs : List Nat} {idx target : Nat}
    (hs : isStrictlySorted xs = true) (h : xs[idx]? = some target) :
    listIndexOf xs target = some idx := by
  obtain ⟨idx', hidx', hget'⟩ := mem_listIndexOf (List.mem_of_getElem? h)
  have heq : idx' = idx := by
    by_cases hlt : idx' < idx
    · exact absurd (isStrictlySorted_lt hs hget' h hlt) (Nat.lt_irrefl _)
    · by_cases hgt : idx < idx'
      · exact absurd (isStrictlySorted_lt hs h hget' hgt) (Nat.lt_irrefl _)
      · omega
  rwa [heq] at hidx'

private theorem listIndexOf_none_of_not_mem {xs : List Nat} {target : Nat} (hnm : target ∉ xs) :
    listIndexOf xs target = none := by
  cases h : listIndexOf xs target with
  | none => rfl
  | some idx => exact absurd (List.mem_of_getElem? (listIndexOf_eq_some h)) hnm

private theorem getElem?_flatMap_const_len {α β : Type} :
    ∀ {xs : List α} {f : α → List β} (m : Nat),
      (∀ a ∈ xs, (f a).length = m) → 0 < m →
      ∀ (q r : Nat), r < m →
        (xs.flatMap f)[q * m + r]? = (xs[q]?).bind fun a => (f a)[r]?
  | [], _, _, _, _, q, r, _ => by simp
  | x :: rest, f, m, hlen, hm, q, r, hr => by
      simp only [List.flatMap_cons]
      have hxlen : (f x).length = m := hlen x (by simp)
      cases q with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
          rw [List.getElem?_append_left (by omega)]
      | succ q' =>
          have hge : (f x).length ≤ (q' + 1) * m + r := by
            rw [hxlen, Nat.add_mul, Nat.one_mul]; omega
          rw [List.getElem?_append_right hge, hxlen]
          have hsub : (q' + 1) * m + r - m = q' * m + r := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          rw [hsub, List.getElem?_cons_succ]
          exact getElem?_flatMap_const_len m (fun a ha => hlen a (by simp [ha])) hm q' r hr

private theorem length_flatMap_const_len {α β : Type} :
    ∀ {xs : List α} {f : α → List β} (m : Nat),
      (∀ a ∈ xs, (f a).length = m) →
      (xs.flatMap f).length = xs.length * m
  | [], _, _, _ => by simp
  | x :: rest, f, m, hlen => by
      have ih := length_flatMap_const_len (xs := rest) (f := f) m (fun a ha => hlen a (by simp [ha]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, hlen x (by simp), ih,
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem buildTrampBlocks_length (F : Func) (nonLeafExits : List Label) (delta trampRegBase stride : Nat) :
    (buildTrampBlocks F nonLeafExits delta trampRegBase stride).length = nonLeafExits.length := by
  simp [buildTrampBlocks]

private theorem buildTrampBlocks_getElem? (F : Func) (nonLeafExits : List Label)
    (delta trampRegBase stride tidx x : Nat) (hx : nonLeafExits[tidx]? = some x) :
    (buildTrampBlocks F nonLeafExits delta trampRegBase stride)[tidx]? =
      some (let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
            let regStart := trampRegBase + tidx * stride
            let ps := (List.range nParams).map (regStart + ·)
            { params := ps
              body := #[]
              term := .jump { target := x + delta, args := ps.map .v }
              cold := (F.blocks[x]?.map (·.cold)).getD false }) := by
  unfold buildTrampBlocks
  rw [List.getElem?_map, List.getElem?_zipIdx]
  simp [hx]

private theorem nodup_map_add_range (base n : Nat) :
    ((List.range n).map (base + ·)).Nodup := by
  have h : ∀ (xs : List Nat), xs.Nodup → (xs.map (base + ·)).Nodup := by
    intro xs hn
    induction xs with
    | nil => simp
    | cons a rest ih =>
        rw [List.nodup_cons] at hn
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih hn.2⟩
        intro hm
        rw [List.mem_map] at hm
        obtain ⟨b, hb, heq⟩ := hm
        have : b = a := Nat.add_left_cancel heq
        subst this; exact hn.1 hb
  exact h (List.range n) List.nodup_range

private theorem mem_map_add_range_ge {base n r : Nat} (h : r ∈ (List.range n).map (base + ·)) :
    base ≤ r := by
  rw [List.mem_map] at h
  obtain ⟨i, _, rfl⟩ := h
  omega

private theorem bindParams_of_eq_len :
    ∀ (ρ : Env) (ps : List VReg) (vs : List Word),
      ps.length = vs.length → ∃ ρ', bindParams ρ ps vs = some ρ'
  | ρ, [], [], _ => ⟨ρ, rfl⟩
  | ρ, p :: ps, v :: vs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact bindParams_of_eq_len (ρ.insert p v) ps vs h
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp at h

private theorem bindParams_len_eq :
    ∀ {ρ ρ' : Env} {ps : List VReg} {vs : List Word},
      bindParams ρ ps vs = some ρ' → ps.length = vs.length
  | _, _, [], [], _ => rfl
  | _, _, _ :: _, _ :: _, h => by simp only [bindParams] at h; rw [List.length_cons, List.length_cons, bindParams_len_eq h]
  | _, _, [], _ :: _, h | _, _, _ :: _, [], h => by simp [bindParams] at h

private theorem bindParams_nodup_evalArgs :
    ∀ {ps : List VReg} {vs : List Word} {ρ ρ' : Env},
      ps.Nodup →
      bindParams ρ ps vs = some ρ' →
      evalArgs ρ' (ps.map .v) = some vs ∧ (∀ u, u ∉ ps → ρ'[u]? = ρ[u]?)
  | [], [], ρ, ρ', _, h => by
      simp only [bindParams, Option.some.injEq] at h; subst h
      exact ⟨rfl, fun _ _ => rfl⟩
  | p :: ps, v :: vs, ρ, ρ', hnd, h => by
      rw [List.nodup_cons] at hnd
      simp only [bindParams] at h
      obtain ⟨hev, hpres⟩ := bindParams_nodup_evalArgs hnd.2 h
      refine ⟨?_, ?_⟩
      · have hp : ρ'[p]? = some v := by rw [hpres p hnd.1, env_insert_self]
        unfold evalArgs at hev ⊢
        simp only [List.map_cons, List.mapM_cons, Arg.eval, hp, Option.bind_eq_bind,
          Option.bind_some, hev, Option.pure_def]
      · intro u hu
        rw [List.mem_cons, not_or] at hu
        rw [hpres u hu.2, env_insert_ne _ _ (Ne.symm hu.1)]
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [bindParams] at h

private theorem bindParams_nodup_getElem? :
    ∀ {ps : List VReg} {vs : List Word} {ρ ρ' : Env} {idx : Nat} {p : VReg} {v : Word},
      ps.Nodup →
      bindParams ρ ps vs = some ρ' →
      ps[idx]? = some p → vs[idx]? = some v →
      ρ'[p]? = some v
  | [], [], _, _, _, _, _, _, _, hp, _ => by simp at hp
  | a :: ps, w :: vs, ρ, ρ', idx, p, v, hnd, hbp, hp, hv => by
      rw [List.nodup_cons] at hnd
      simp only [bindParams] at hbp
      cases idx with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hv
          subst hp; subst hv
          have hpres := (bindParams_nodup_evalArgs hnd.2 hbp).2
          rw [hpres a hnd.1, env_insert_self]
      | succ idx' =>
          simp only [List.getElem?_cons_succ] at hp hv
          exact bindParams_nodup_getElem? hnd.2 hbp hp hv
  | [], _ :: _, _, _, _, _, _, _, h, _, _ | _ :: _, [], _, _, _, _, _, _, h, _, _ => by
      simp [bindParams] at h

private theorem term_setEdges_map (t : Term) (f : Label → Label) :
    t.setEdges (t.edges.map fun e => { e with target := f e.target }) =
    match t with
    | .jump e => .jump { e with target := f e.target }
    | .br c w a b t' f' => .br c w a b { t' with target := f t'.target } { f' with target := f f'.target }
    | .brOvf o x a b ok ovf => .brOvf o x a b { ok with target := f ok.target } { ovf with target := f ovf.target }
    | .ret as => .ret as
    | .tail g as => .tail g as
    | .fail r => .fail r
    | .trap => .trap := by
  cases t <;> rfl

/-! ## Part 2: `collectBlocksDefs`, `availAtPos`, `checkStmtsAvail`, and `LoopCloneFacts` -/

private theorem collectBlocksDefs_foldl_mono (F : Func) :
    ∀ (lbls : List Label) (acc : Src.NatSet) (x : VReg),
      acc.contains x = true →
      (lbls.foldl (init := acc) fun acc b =>
        match F.blocks[b]? with
        | none => acc
        | some blk =>
            let acc := blk.params.foldl (fun s x => s.insert x) acc
            let acc := blk.body.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) acc
            blk.term.defs.foldl (fun s x => s.insert x) acc).contains x = true
  | [], acc, x, h => h
  | b :: rest, acc, x, h => by
      simp only [List.foldl_cons]
      apply collectBlocksDefs_foldl_mono F rest _ x
      cases F.blocks[b]? with
      | none => exact h
      | some blk =>
          dsimp only
          rw [natSet_contains_foldl_insert]
          right
          have hbody : ∀ (sts : List Stmt) (s : Src.NatSet),
              s.contains x = true →
              (sts.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) s).contains x = true := by
            intro sts
            induction sts with
            | nil => intro s hs; exact hs
            | cons st r ih =>
                intro s hs
                simp only [List.foldl_cons]
                apply ih
                rw [natSet_contains_foldl_insert]; exact .inr hs
          rw [← Array.foldl_toList]
          apply hbody
          rw [natSet_contains_foldl_insert]; exact .inr h

private theorem collectBlocksDefs_mem {F : Func} {lbls : List Label} {b : Label} {blk : Block}
    (hmem : b ∈ lbls) (hB : F.blocks[b]? = some blk) :
    (∀ x ∈ blk.params, (collectBlocksDefs F lbls).contains x = true) ∧
    (∀ s ∈ blk.body.toList, ∀ x ∈ s.defs, (collectBlocksDefs F lbls).contains x = true) ∧
    (∀ x ∈ blk.term.defs, (collectBlocksDefs F lbls).contains x = true) := by
  have hstep : ∀ (ls : List Label) (acc : Src.NatSet), b ∈ ls →
      let res := ls.foldl (init := acc) fun acc b =>
        match F.blocks[b]? with
        | none => acc
        | some blk =>
            let acc := blk.params.foldl (fun s x => s.insert x) acc
            let acc := blk.body.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) acc
            blk.term.defs.foldl (fun s x => s.insert x) acc
      (∀ x ∈ blk.params, res.contains x = true) ∧
      (∀ s ∈ blk.body.toList, ∀ x ∈ s.defs, res.contains x = true) ∧
      (∀ x ∈ blk.term.defs, res.contains x = true) := by
    intro ls
    induction ls with
    | nil => intro _ hm; cases hm
    | cons a rest ih =>
        intro acc hm
        simp only [List.foldl_cons]
        rcases List.mem_cons.1 hm with rfl | hm'
        · rw [hB]; dsimp only
          have hbody_mono : ∀ (sts : List Stmt) (s : Src.NatSet) (x : VReg),
              s.contains x = true →
              (sts.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) s).contains x = true := by
            intro sts
            induction sts with
            | nil => intro s x hs; exact hs
            | cons st r ihr =>
                intro s x hs; simp only [List.foldl_cons]
                apply ihr; rw [natSet_contains_foldl_insert]; exact .inr hs
          have hbody_in : ∀ (sts : List Stmt) (s : Src.NatSet) (st : Stmt) (x : VReg),
              st ∈ sts → x ∈ st.defs →
              (sts.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) s).contains x = true := by
            intro sts
            induction sts with
            | nil => intro _ _ _ h; cases h
            | cons st0 r ihr =>
                intro s st x hst hx
                simp only [List.foldl_cons]
                rcases List.mem_cons.1 hst with rfl | hst'
                · apply hbody_mono; rw [natSet_contains_foldl_insert]; exact .inl hx
                · exact ihr _ st x hst' hx
          refine ⟨fun x hx => collectBlocksDefs_foldl_mono F rest _ x ?_,
                  fun s hs x hx => collectBlocksDefs_foldl_mono F rest _ x ?_,
                  fun x hx => collectBlocksDefs_foldl_mono F rest _ x ?_⟩
          · rw [natSet_contains_foldl_insert]; right
            rw [← Array.foldl_toList]; apply hbody_mono
            rw [natSet_contains_foldl_insert]; exact .inl hx
          · rw [natSet_contains_foldl_insert]; right
            rw [← Array.foldl_toList]; exact hbody_in blk.body.toList _ s x hs hx
          · rw [natSet_contains_foldl_insert]; exact .inl hx
        · exact ih _ hm'
  exact hstep lbls .leaf hmem

/-- Available-register set after executing the first `pos` statements of `body` starting from `av0`. -/
def availAtPos (av0 : Src.NatSet) (body : Array Stmt) (pos : Nat) : Src.NatSet :=
  (body.toList.take pos).foldl (fun a s => s.defs.foldl (fun m x => m.insert x) a) av0

private theorem availAtPos_zero (av0 : Src.NatSet) (body : Array Stmt) :
    availAtPos av0 body 0 = av0 := rfl

private theorem availAtPos_succ (av0 : Src.NatSet) (body : Array Stmt) {pos : Nat}
    (hlt : pos < body.size) :
    availAtPos av0 body (pos + 1) =
      (body[pos]'hlt).defs.foldl (fun m x => m.insert x) (availAtPos av0 body pos) := by
  unfold availAtPos
  have htake : body.toList.take (pos + 1) = body.toList.take pos ++ [body[pos]'hlt] := by
    rw [List.take_succ_eq_append_getElem (by simpa using hlt)]
    rfl
  rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem checkStmtsAvail_props (clonedDefs : Src.NatSet) :
    ∀ (stmts : List Stmt) (av0 avEnd : Src.NatSet),
      checkStmtsAvail clonedDefs av0 stmts = some avEnd →
      (stmts.foldl (fun a s => s.defs.foldl (fun m x => m.insert x) a) av0 = avEnd) ∧
      ∀ (pos : Nat) (s : Stmt), stmts[pos]? = some s →
        ∀ x ∈ s.uses,
          clonedDefs.contains x = false ∨
          ((stmts.take pos).foldl (fun a s => s.defs.foldl (fun m x => m.insert x) a) av0).contains x = true
  | [], av0, avEnd, h => by
      simp only [checkStmtsAvail, Option.some.injEq] at h; subst h
      exact ⟨rfl, fun _ _ hs => by simp at hs⟩
  | st :: rest, av0, avEnd, h => by
      unfold checkStmtsAvail at h
      split at h
      · rename_i hok
        obtain ⟨hend, hrest⟩ := checkStmtsAvail_props clonedDefs rest _ avEnd h
        refine ⟨by simpa [List.foldl_cons] using hend, ?_⟩
        intro pos s hs x hx
        cases pos with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; subst hs
            simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
            simpa [List.take] using hok x hx
        | succ pos' =>
            simp only [List.getElem?_cons_succ] at hs
            simpa [List.take_succ_cons, List.foldl_cons] using hrest pos' s hs x hx
      · cases h

private theorem checkStmtsAvail_end {clonedDefs av0 avEnd : Src.NatSet} {body : Array Stmt}
    (h : checkStmtsAvail clonedDefs av0 body.toList = some avEnd) :
    availAtPos av0 body body.size = avEnd := by
  unfold availAtPos
  have htake : body.toList.take body.size = body.toList := List.take_of_length_le (by simp)
  rw [htake]
  exact (checkStmtsAvail_props clonedDefs body.toList av0 avEnd h).1

private theorem checkStmtsAvail_at {clonedDefs av0 avEnd : Src.NatSet} {body : Array Stmt}
    (h : checkStmtsAvail clonedDefs av0 body.toList = some avEnd)
    {pos : Nat} (hlt : pos < body.size) :
    ∀ x ∈ (body[pos]'hlt).uses,
      clonedDefs.contains x = false ∨ (availAtPos av0 body pos).contains x = true := by
  have hget : body.toList[pos]? = some (body[pos]'hlt) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt]
  exact (checkStmtsAvail_props clonedDefs body.toList av0 avEnd h).2 pos _ hget

private theorem blockRegsLt_of_func' {F : Func} {off : VReg} (h : funcRegsLt F off = true)
    {b : Nat} {B : Block} (hB : F.blocks[b]? = some B) : blockRegsLt off B = true := by
  simp only [funcRegsLt, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 B (Array.mem_toList_iff.2 (Array.mem_of_getElem? hB))

private theorem listLt_mem' {off : VReg} {xs : List VReg} (h : listLt off xs = true)
    {x : VReg} (hx : x ∈ xs) : x < off := by
  simp only [listLt, List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx

private theorem blockRegsLt_parts {off : VReg} {B : Block} (h : blockRegsLt off B = true) :
    listLt off B.params = true ∧
    (∀ s ∈ B.body.toList, listLt off s.uses = true ∧ listLt off s.defs = true) ∧
    listLt off B.term.uses = true ∧
    listLt off B.term.defs = true ∧
    listLt off B.term.edgeUses = true := by
  simp only [blockRegsLt, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, fun s hs => h.1.1.1.2 s hs, h.1.1.2, h.1.2, h.2⟩

private theorem edgeUses_mem {t : Term} {e : Edge} (he : e ∈ t.edges) {a : Arg} (ha : a ∈ e.args)
    {x : VReg} (hx : x ∈ a.uses) : x ∈ t.edgeUses :=
  List.mem_flatMap.2 ⟨e, he, List.mem_flatMap.2 ⟨a, ha, hx⟩⟩

/-- Unpacked semantic facts extracted once from `loopCloneOk F h nodes leafExits nonLeafExits off availMap = true`,
shared by both `unrollLoopSite_forward` and `versionOddLoopSite_forward`. -/
private structure LoopCloneFacts (F : Func) (h : Nat) (nodes leafExits nonLeafExits : List Nat)
    (off : VReg) (availMap : Array Src.NatSet) : Prop where
  h_pos : 0 < h
  nodes_ne : nodes ≠ []
  nodes_head : nodes.head? = some h
  nodes_sorted : isStrictlySorted nodes = true
  leaf_sorted : isStrictlySorted leafExits = true
  nonLeaf_sorted : isStrictlySorted nonLeafExits = true
  nodes_lt : ∀ b ∈ nodes, b < F.blocks.size
  leaf_ok : ∀ b ∈ leafExits, 0 < b ∧ b < F.blocks.size ∧ b ∉ nodes
  nonLeaf_ok : ∀ b ∈ nonLeafExits, nodes.getLastD h + 1 ≤ b ∧ b < F.blocks.size ∧ b ∉ nodes ∧ b ∉ leafExits
  regs_lt : funcRegsLt F off = true
  leaf_no_edges : ∀ b ∈ leafExits, ∀ blk, F.blocks[b]? = some blk → blk.term.edges = []
  node_edges : ∀ b ∈ nodes, ∀ blk, F.blocks[b]? = some blk →
    ∀ e ∈ blk.term.edges,
      e.target = h ∨
      (e.target ∈ nodes ∧ b < e.target) ∨
      (e.target ∈ leafExits ∧ b < e.target) ∨
      e.target ∈ nonLeafExits
  outside_edges : ∀ u < F.blocks.size, u ∉ nodes → ∀ blk, F.blocks[u]? = some blk →
    ∀ e ∈ blk.term.edges,
      (e.target ∉ nodes ∨ e.target = h) ∧
      (e.target ∈ leafExits → ∃ tBlk avT, F.blocks[e.target]? = some tBlk ∧ availMap[e.target]? = some avT ∧
        ∀ x, avT.contains x = true → x ∈ tBlk.params)
  outside_no_cloned : ∀ u < F.blocks.size, u ∉ nodes → u ∉ leafExits → ∀ blk, F.blocks[u]? = some blk →
    (∀ s ∈ blk.body.toList, ∀ x ∈ s.uses, (collectBlocksDefs F (nodes ++ leafExits)).contains x = false) ∧
    (∀ x ∈ blk.term.uses, (collectBlocksDefs F (nodes ++ leafExits)).contains x = false) ∧
    (∀ x ∈ blk.term.edgeUses, (collectBlocksDefs F (nodes ++ leafExits)).contains x = false)
  avail_h : ∃ hBlk avH, F.blocks[h]? = some hBlk ∧ availMap[h]? = some avH ∧
    ∀ x, avH.contains x = true → x ∈ hBlk.params
  avail_block : ∀ b ∈ nodes ++ leafExits, ∀ blk, F.blocks[b]? = some blk →
    ∃ av0 av1, availMap[b]? = some av0 ∧
      checkStmtsAvail (collectBlocksDefs F (nodes ++ leafExits)) av0 blk.body.toList = some av1 ∧
      (∀ x ∈ blk.term.uses, (collectBlocksDefs F (nodes ++ leafExits)).contains x = false ∨ av1.contains x = true) ∧
      let av2 := blk.term.defs.foldl (fun a x => a.insert x) av1
      (∀ x ∈ blk.term.edgeUses, (collectBlocksDefs F (nodes ++ leafExits)).contains x = false ∨ av2.contains x = true) ∧
      (∀ e ∈ blk.term.edges,
        ((e.target ∈ nodes ∧ e.target ≠ h) ∨ e.target ∈ leafExits) →
        ∃ tBlk avT, F.blocks[e.target]? = some tBlk ∧ availMap[e.target]? = some avT ∧
          ∀ x, avT.contains x = true → av2.contains x = true ∨ x ∈ tBlk.params)

private theorem loopCloneFacts_of_ok {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hok : loopCloneOk F h nodes leafExits nonLeafExits off availMap = true) :
    LoopCloneFacts F h nodes leafExits nonLeafExits off availMap := by
  unfold loopCloneOk at hok
  dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hne⟩, hhead⟩, hns⟩, hls⟩, hnls⟩, hnlt⟩, hleaf⟩, hnonleaf⟩, hregs⟩,
    hleafE⟩, hnodeE⟩, hout⟩, havail⟩ := hok
  simp only [decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at hpos hne hhead
  unfold checkLoopAvail at havail
  dsimp only at havail
  simp only [Bool.and_eq_true] at havail
  obtain ⟨⟨_, havH⟩, havB⟩ := havail
  refine ⟨hpos, hne, hhead, hns, hls, hnls, ?_, ?_, ?_, hregs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [List.all_eq_true, decide_eq_true_eq] at hnlt; exact hnlt b hb
  · intro b hb
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hleaf
    obtain ⟨⟨h0, hlt⟩, hnn⟩ := hleaf b hb
    exact ⟨h0, hlt, (natSet_ofList_contains_false nodes b).1 hnn⟩
  · intro b hb
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hnonleaf
    obtain ⟨⟨⟨hc, hlt⟩, hnn⟩, hnl⟩ := hnonleaf b hb
    exact ⟨hc, hlt, (natSet_ofList_contains_false nodes b).1 hnn, (natSet_ofList_contains_false leafExits b).1 hnl⟩
  · intro b hb blk hB
    simp only [List.all_eq_true] at hleafE
    have h1 := hleafE b hb; rw [hB] at h1
    exact List.isEmpty_iff.1 h1
  · intro b hb blk hB e he
    simp only [List.all_eq_true] at hnodeE
    have h1 := hnodeE b hb; rw [hB] at h1
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rcases h1 e he with ((heq | ⟨hn, hlt⟩) | ⟨hl, hlt⟩) | hnl
    · exact .inl heq
    · exact .inr (.inl ⟨(natSet_ofList_contains nodes e.target).1 hn, hlt⟩)
    · exact .inr (.inr (.inl ⟨(natSet_ofList_contains leafExits e.target).1 hl, hlt⟩))
    · exact .inr (.inr (.inr ((natSet_ofList_contains nonLeafExits e.target).1 hnl)))
  · intro u hu hun blk hB e he
    simp only [List.all_eq_true] at hout
    have h1 := hout u (List.mem_range.2 hu)
    have hnf : (Src.NatSet.ofList nodes).contains u = false := (natSet_ofList_contains_false nodes u).2 hun
    simp only [hnf, Bool.false_eq_true, ↓reduceIte, hB, Bool.and_eq_true] at h1
    have h2 := (List.all_eq_true.1 h1.1) e he
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h2
    refine ⟨?_, ?_⟩
    · rcases h2.1 with hnn | heq
      · exact .inl ((natSet_ofList_contains_false nodes e.target).1 hnn)
      · exact .inr heq
    · intro hle
      have hlt' : (Src.NatSet.ofList leafExits).contains e.target = true :=
        (natSet_ofList_contains leafExits e.target).2 hle
      rcases h2.2 with hfl | hm
      · rw [hlt'] at hfl; cases hfl
      · cases htb : F.blocks[e.target]? with
        | none => rw [htb] at hm; cases hm
        | some tBlk =>
            cases hav : availMap[e.target]? with
            | none => rw [htb, hav] at hm; cases hm
            | some avT =>
                rw [htb, hav] at hm
                refine ⟨tBlk, avT, rfl, rfl, fun x hx => ?_⟩
                have hm' := (List.all_eq_true.1 hm) (x, ()) (natSet_mem_toList hx)
                simpa using hm'
  · intro u hu hun hul blk hB
    simp only [List.all_eq_true] at hout
    have h1 := hout u (List.mem_range.2 hu)
    have hnf : (Src.NatSet.ofList nodes).contains u = false := (natSet_ofList_contains_false nodes u).2 hun
    have hlf : (Src.NatSet.ofList leafExits).contains u = false := (natSet_ofList_contains_false leafExits u).2 hul
    simp only [hnf, hlf, Bool.false_eq_true, ↓reduceIte, hB, Bool.and_eq_true, Bool.false_or] at h1
    obtain ⟨⟨hb, ht⟩, he⟩ := h1.2
    refine ⟨?_, ?_, ?_⟩
    · intro s hs x hx
      have hsb := (List.all_eq_true.1 hb) s hs
      simpa [Bool.not_eq_true'] using (List.all_eq_true.1 hsb) x hx
    · intro x hx
      simpa [Bool.not_eq_true'] using (List.all_eq_true.1 ht) x hx
    · intro x hx
      simpa [Bool.not_eq_true'] using (List.all_eq_true.1 he) x hx
  · cases hbh : F.blocks[h]? with
    | none => rw [hbh] at havH; cases havH
    | some hBlk =>
        cases hav : availMap[h]? with
        | none => rw [hbh, hav] at havH; cases havH
        | some avH =>
            rw [hbh, hav] at havH
            refine ⟨hBlk, avH, rfl, rfl, fun x hx => ?_⟩
            simpa using (List.all_eq_true.1 havH) (x, ()) (natSet_mem_toList hx)
  · intro b hb blk hB
    have h1 := (List.all_eq_true.1 havB) b hb
    rw [hB] at h1
    cases hav : availMap[b]? with
    | none => rw [hav] at h1; cases h1
    | some av0 =>
        rw [hav] at h1; dsimp only at h1
        cases hchk : checkStmtsAvail (collectBlocksDefs F (nodes ++ leafExits)) av0 blk.body.toList with
        | none => rw [hchk] at h1; cases h1
        | some av1 =>
            rw [hchk] at h1
            dsimp only at h1
            simp only [Bool.and_eq_true] at h1
            obtain ⟨ht, he, hedges⟩ := h1
            refine ⟨av0, av1, rfl, hchk, ?_, ?_, ?_⟩
            · intro x hx
              have htx := (List.all_eq_true.1 ht) x hx
              simpa [Bool.or_eq_true, Bool.not_eq_true'] using htx
            · intro x hx
              have hex := (List.all_eq_true.1 he) x hx
              simpa [Bool.or_eq_true, Bool.not_eq_true'] using hex
            · intro e he' hcond
              have hedge := (List.all_eq_true.1 hedges) e he'
              have hcondB : ((Src.NatSet.ofList nodes).contains e.target && e.target != h ||
                  (Src.NatSet.ofList leafExits).contains e.target) = true := by
                simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne]
                rcases hcond with ⟨hn, hne⟩ | hl
                · exact .inl ⟨(natSet_ofList_contains nodes e.target).2 hn, hne⟩
                · exact .inr ((natSet_ofList_contains leafExits e.target).2 hl)
              simp only [hcondB, ↓reduceIte] at hedge
              cases htb : F.blocks[e.target]? with
              | none => rw [htb] at hedge; cases hedge
              | some tBlk =>
                  cases havT : availMap[e.target]? with
                  | none => rw [htb, havT] at hedge; cases hedge
                  | some avT =>
                      rw [htb, havT] at hedge
                      refine ⟨tBlk, avT, rfl, rfl, fun x hx => ?_⟩
                      have htx := (List.all_eq_true.1 hedge) (x, ()) (natSet_mem_toList hx)
                      simpa [Bool.or_eq_true] using htx

private theorem LoopCloneFacts.cut_le_size {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap) :
    nodes.getLastD h + 1 ≤ F.blocks.size := by
  have hmem : nodes.getLastD h ∈ nodes := by
    cases hnodes : nodes with
    | nil => exact absurd hnodes hf.nodes_ne
    | cons a rest =>
        have hmem_last : ∀ (x : Nat) (xs : List Nat), (x :: xs).getLastD h ∈ x :: xs := by
          intro x xs
          induction xs generalizing x with
          | nil => simp [List.getLastD]
          | cons y ys ih =>
              show (y :: ys).getLastD h ∈ x :: y :: ys
              exact List.mem_cons_of_mem x (ih y)
        exact hmem_last a rest
  have := hf.nodes_lt _ hmem
  omega

private theorem LoopCloneFacts.h_lt_cut {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap) :
    h < nodes.getLastD h + 1 := by
  cases hnodes : nodes with
  | nil => exact absurd hnodes hf.nodes_ne
  | cons a rest =>
      have ha : a = h := by have := hf.nodes_head; rw [hnodes] at this; simpa using this
      subst ha
      have hs := hf.nodes_sorted; rw [hnodes] at hs
      have hle := isStrictlySorted_le_getLastD (d := a) (i := 0) hs rfl
      omega

private theorem LoopCloneFacts.node_lt_cut {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap)
    {b : Nat} (hb : b ∈ nodes) : b < nodes.getLastD h + 1 := by
  obtain ⟨idx, _, hget⟩ := mem_listIndexOf hb
  have hle := isStrictlySorted_le_getLastD (d := h) hf.nodes_sorted hget
  omega

private theorem LoopCloneFacts.h_le_node {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap)
    {b : Nat} (hb : b ∈ nodes) : h ≤ b := by
  obtain ⟨idx, _, hget⟩ := mem_listIndexOf hb
  exact isStrictlySorted_head_le hf.nodes_sorted hf.nodes_head hget

private theorem LoopCloneFacts.zero_not_mem_nodes {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap) : 0 ∉ nodes := by
  intro h0
  have := hf.h_le_node h0
  have := hf.h_pos
  omega

private theorem LoopCloneFacts.zero_not_mem_leaf {F : Func} {h : Nat} {nodes leafExits nonLeafExits : List Nat}
    {off : VReg} {availMap : Array Src.NatSet}
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap) : 0 ∉ leafExits := by
  intro h0
  have := (hf.leaf_ok 0 h0).1
  omega

/-! ## Part 3: `LoopOuterRel`, `LoopCopyRel`, and `loopMap*` operational lemmas -/

private theorem loopMapReg_zero' (clonedDefs : Src.NatSet) (off : Nat) (x : VReg) :
    loopMapReg clonedDefs off 0 x = x := by
  simp [loopMapReg]

private theorem loopMapArg_zero' (clonedDefs : Src.NatSet) (off : Nat) (a : Arg) :
    loopMapArg clonedDefs off 0 a = a := by
  cases a <;> simp [loopMapArg, loopMapReg_zero']

private theorem loopMapBase_zero' (clonedDefs : Src.NatSet) (off : Nat) (b : Base) :
    loopMapBase clonedDefs off 0 b = b := by
  cases b <;> simp [loopMapBase, loopMapReg_zero']

private theorem loopMapAddr_zero' (clonedDefs : Src.NatSet) (off : Nat) (m : Addr) :
    loopMapAddr clonedDefs off 0 m = m := by
  rcases m with ⟨b, i, d⟩
  cases b <;> cases i <;> simp [loopMapAddr, loopMapBase_zero', loopMapReg_zero']

private theorem loopMapRhs_zero' (clonedDefs : Src.NatSet) (off : Nat) (r : Rhs) :
    loopMapRhs clonedDefs off 0 r = r := by
  cases r <;> simp [loopMapRhs, loopMapArg_zero', loopMapAddr_zero']

private theorem loopMapLimb_zero' (clonedDefs : Src.NatSet) (off : Nat) (op : LimbOp) :
    loopMapLimb clonedDefs off 0 op = op := by
  cases op <;> simp [loopMapLimb, loopMapArg_zero']

private theorem loopMapStmt_zero' (clonedDefs : Src.NatSet) (off : Nat) (s : Stmt) :
    loopMapStmt clonedDefs off 0 s = s := by
  have hreg : loopMapReg clonedDefs off 0 = id := funext (loopMapReg_zero' clonedDefs off)
  have harg : loopMapArg clonedDefs off 0 = id := funext (loopMapArg_zero' clonedDefs off)
  cases s <;> simp [loopMapStmt, loopMapReg_zero', loopMapRhs_zero', loopMapLimb_zero',
    loopMapAddr_zero', loopMapArg_zero', hreg, harg]

private theorem loopMapReg_not_mem' {clonedDefs : Src.NatSet} {off c : Nat} {x : VReg}
    (h : clonedDefs.contains x = false) : loopMapReg clonedDefs off c x = x := by
  simp [loopMapReg, h]

private theorem loopMapReg_mem_pos' {clonedDefs : Src.NatSet} {off c : Nat} {x : VReg}
    (hc : 0 < c) (h : clonedDefs.contains x = true) : loopMapReg clonedDefs off c x = c * off + x := by
  have hne : (c == 0) = false := beq_false_of_ne (by omega)
  simp [loopMapReg, hne, h]

private theorem loopMapReg_inj_on_cloned {clonedDefs : Src.NatSet} {off c u d : Nat}
    (hu : clonedDefs.contains u = true) (hd : clonedDefs.contains d = true)
    (heq : loopMapReg clonedDefs off c u = loopMapReg clonedDefs off c d) : u = d := by
  cases c with
  | zero => simpa [loopMapReg_zero'] using heq
  | succ c' =>
      rw [loopMapReg_mem_pos' (by omega) hu, loopMapReg_mem_pos' (by omega) hd] at heq
      exact Nat.add_left_cancel heq

private theorem loopMapReg_ne_outer {clonedDefs : Src.NatSet} {off c u d : Nat}
    (hu : u < off) (hun : clonedDefs.contains u = false) (hd : clonedDefs.contains d = true) :
    u ≠ loopMapReg clonedDefs off c d := by
  cases c with
  | zero =>
      rw [loopMapReg_zero']
      intro heq; subst heq; rw [hun] at hd; cases hd
  | succ c' =>
      rw [loopMapReg_mem_pos' (by omega) hd]
      have hge : off ≤ (c' + 1) * off := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      omega

/-- Outside `nodes ++ leafExits` in `fi`: `ρ₂` agrees with `ρ₁` on every register `< off`
not in `clonedDefs`. -/
def LoopOuterRel (clonedDefs : Src.NatSet) (off : VReg) (ρ₁ ρ₂ : Env) : Prop :=
  ∀ u, u < off → clonedDefs.contains u = false → ρ₂[u]? = ρ₁[u]?

/-- Inside `nodes ++ leafExits` at copy `c` with available set `av`:
agrees on all outer regs (`< off`, `∉ clonedDefs`) AND all cloned regs `< off` in `av`. -/
def LoopCopyRel (clonedDefs : Src.NatSet) (off c : Nat) (av : Src.NatSet) (ρ₁ ρ₂ : Env) : Prop :=
  LoopOuterRel clonedDefs off ρ₁ ρ₂ ∧
  ∀ u, u < off → clonedDefs.contains u = true → av.contains u = true →
    ρ₂[loopMapReg clonedDefs off c u]? = ρ₁[u]?

private theorem LoopOuterRel.refl (clonedDefs : Src.NatSet) (off : VReg) (ρ : Env) :
    LoopOuterRel clonedDefs off ρ ρ := fun _ _ _ => rfl

private theorem LoopOuterRel.insert_same {clonedDefs : Src.NatSet} {off : VReg} {ρ₁ ρ₂ : Env}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) (x : VReg) (v : Word) :
    LoopOuterRel clonedDefs off (ρ₁.insert x v) (ρ₂.insert x v) := by
  intro u hu hnc
  rw [env_insert_get, env_insert_get]
  split
  · rfl
  · exact h u hu hnc

private theorem LoopOuterRel.insert_ge_right {clonedDefs : Src.NatSet} {off : VReg} {ρ₁ ρ₂ : Env}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) {x : VReg} (hx : off ≤ x) (v : Word) :
    LoopOuterRel clonedDefs off ρ₁ (ρ₂.insert x v) := by
  intro u hu hnc
  rw [env_insert_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hx))]
  exact h u hu hnc

private theorem LoopOuterRel.bindParams_same {clonedDefs : Src.NatSet} {off : VReg} :
    ∀ {ps : List VReg} {vs : List Word} {ρ₁ ρ₂ ρ₁' : Env},
      LoopOuterRel clonedDefs off ρ₁ ρ₂ →
      bindParams ρ₁ ps vs = some ρ₁' →
      ∃ ρ₂', bindParams ρ₂ ps vs = some ρ₂' ∧ LoopOuterRel clonedDefs off ρ₁' ρ₂'
  | [], [], ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams, Option.some.injEq] at hb; subst hb; exact ⟨ρ₂, rfl, h⟩
  | p :: ps, v :: vs, ρ₁, ρ₂, ρ₁', h, hb => by
      simp only [bindParams] at hb ⊢
      exact LoopOuterRel.bindParams_same (h.insert_same p v) hb
  | [], _ :: _, _, _, _, _, hb | _ :: _, [], _, _, _, _, hb => by simp [bindParams] at hb

private theorem LoopOuterRel.toCopyLeaf {clonedDefs : Src.NatSet} {off c : Nat} {ρ₁ ρ₂ : Env}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) :
    LoopCopyRel clonedDefs off c .leaf ρ₁ ρ₂ :=
  ⟨h, fun _ _ _ hav => by rw [natSet_contains_leaf] at hav; cases hav⟩

private theorem LoopCopyRel.mono {clonedDefs : Src.NatSet} {off c : Nat} {av1 av2 : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av1 ρ₁ ρ₂)
    (hsub : ∀ x, av2.contains x = true → av1.contains x = true) :
    LoopCopyRel clonedDefs off c av2 ρ₁ ρ₂ :=
  ⟨h.1, fun u hu hc hav => h.2 u hu hc (hsub u hav)⟩

private theorem LoopCopyRel.get_eq {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂) {u : VReg}
    (hu : u < off) (hav : clonedDefs.contains u = false ∨ av.contains u = true) :
    ρ₂[loopMapReg clonedDefs off c u]? = ρ₁[u]? := by
  cases hc : clonedDefs.contains u with
  | false => rw [loopMapReg_not_mem' hc]; exact h.1 u hu hc
  | true =>
      rcases hav with hf | ha
      · rw [hc] at hf; cases hf
      · exact h.2 u hu hc ha

private theorem LoopCopyRel.insert_def {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {d : VReg} (hd : clonedDefs.contains d = true) (v : Word) :
    LoopCopyRel clonedDefs off c (av.insert d) (ρ₁.insert d v) (ρ₂.insert (loopMapReg clonedDefs off c d) v) := by
  refine ⟨?_, ?_⟩
  · intro u hu hnc
    have hne1 : u ≠ d := fun heq => by subst heq; rw [hnc] at hd; cases hd
    have hne2 : u ≠ loopMapReg clonedDefs off c d := loopMapReg_ne_outer hu hnc hd
    rw [env_insert_ne _ _ (Ne.symm hne2), env_insert_ne _ _ (Ne.symm hne1)]
    exact h.1 u hu hnc
  · intro u hu huc hav
    rw [natSet_contains_insert, Bool.or_eq_true, beq_iff_eq] at hav
    by_cases hud : u = d
    · subst hud; rw [env_insert_self, env_insert_self]
    · have hne2 : loopMapReg clonedDefs off c u ≠ loopMapReg clonedDefs off c d :=
        fun heq => hud (loopMapReg_inj_on_cloned huc hd heq)
      rcases hav with heq | hav'
      · exact absurd heq hud
      · rw [env_insert_ne _ _ (Ne.symm hne2), env_insert_ne _ _ (Ne.symm hud)]
        exact h.2 u hu huc hav'

private theorem LoopCopyRel.bindParams_defs {clonedDefs : Src.NatSet} {off c : Nat} :
    ∀ {ps : List VReg} {vs : List Word} {av : Src.NatSet} {ρ₁ ρ₂ ρ₁' : Env},
      LoopCopyRel clonedDefs off c av ρ₁ ρ₂ →
      (∀ d ∈ ps, clonedDefs.contains d = true) →
      bindParams ρ₁ ps vs = some ρ₁' →
      ∃ ρ₂', bindParams ρ₂ (ps.map (loopMapReg clonedDefs off c)) vs = some ρ₂' ∧
        LoopCopyRel clonedDefs off c (ps.foldl (fun a x => a.insert x) av) ρ₁' ρ₂'
  | [], [], av, ρ₁, ρ₂, ρ₁', h, _, hb => by
      simp only [bindParams, Option.some.injEq] at hb; subst hb
      exact ⟨ρ₂, rfl, h⟩
  | p :: ps, v :: vs, av, ρ₁, ρ₂, ρ₁', h, hps, hb => by
      simp only [List.map_cons, List.foldl_cons, bindParams] at hb ⊢
      exact LoopCopyRel.bindParams_defs
        (h.insert_def (hps p (by simp)) v)
        (fun d hd => hps d (by simp [hd])) hb
  | [], _ :: _, _, _, _, _, _, _, hb | _ :: _, [], _, _, _, _, _, _, hb => by simp [bindParams] at hb

private theorem loopMapArg_eval {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {a : Arg} (hlt : listLt off a.uses = true)
    (hav : ∀ x ∈ a.uses, clonedDefs.contains x = false ∨ av.contains x = true) :
    (loopMapArg clonedDefs off c a).eval ρ₂ = a.eval ρ₁ := by
  cases a with
  | imm _ => rfl
  | v x =>
      have hx : x ∈ (Arg.v x).uses := by simp [Arg.uses, Arg.vreg?]
      exact h.get_eq (listLt_mem' hlt hx) (hav x hx)

private theorem loopMapArgs_eval {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂) :
    ∀ {as : List Arg},
      (∀ a ∈ as, listLt off a.uses = true) →
      (∀ a ∈ as, ∀ x ∈ a.uses, clonedDefs.contains x = false ∨ av.contains x = true) →
      evalArgs ρ₂ (as.map (loopMapArg clonedDefs off c)) = evalArgs ρ₁ as
  | [], _, _ => rfl
  | a :: rest, hlt, hav => by
      simp only [List.map_cons, evalArgs, List.mapM_cons,
        loopMapArg_eval h (hlt a (by simp)) (hav a (by simp)),
        show List.mapM (Arg.eval ρ₂) (rest.map (loopMapArg clonedDefs off c)) = List.mapM (Arg.eval ρ₁) rest from
          loopMapArgs_eval h (fun a' ha' => hlt a' (by simp [ha'])) (fun a' ha' => hav a' (by simp [ha']))]

private theorem loopMapAddr_eval {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} {ctx : Word} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {m : Addr} (hlt : listLt off m.uses = true)
    (hav : ∀ x ∈ m.uses, clonedDefs.contains x = false ∨ av.contains x = true) :
    (loopMapAddr clonedDefs off c m).eval ρ₂ ctx = m.eval ρ₁ ctx := by
  rcases m with ⟨base, idx, disp⟩
  cases base with
  | none =>
      cases idx with
      | none => rfl
      | some p =>
          rcases p with ⟨x, s⟩
          have hx : x ∈ (Addr.mk none (some (x, s)) disp).uses := by simp [Addr.uses]
          simp only [loopMapAddr, Addr.eval, Option.map_none, Option.map_some, h.get_eq (listLt_mem' hlt hx) (hav x hx)]
  | some b =>
      cases b with
      | ctx =>
          cases idx with
          | none => rfl
          | some p =>
              rcases p with ⟨x, s⟩
              have hx : x ∈ (Addr.mk (some .ctx) (some (x, s)) disp).uses := by simp [Addr.uses]
              simp only [loopMapAddr, loopMapBase, Addr.eval, Option.map_some,
                h.get_eq (listLt_mem' hlt hx) (hav x hx)]
      | v bx =>
          have hbxm : bx ∈ (Addr.mk (some (.v bx)) idx disp).uses := by simp [Addr.uses, Base.uses]
          have hbx := h.get_eq (listLt_mem' hlt hbxm) (hav bx hbxm)
          cases idx with
          | none => simp only [loopMapAddr, loopMapBase, Addr.eval, Option.map_none, Option.map_some, hbx]
          | some p =>
              rcases p with ⟨x, s⟩
              have hxm : x ∈ (Addr.mk (some (.v bx)) (some (x, s)) disp).uses := by simp [Addr.uses]
              simp only [loopMapAddr, loopMapBase, Addr.eval, Option.map_some, hbx,
                h.get_eq (listLt_mem' hlt hxm) (hav x hxm)]

private theorem loopMapRhs_eval {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} {mem : X86.Memory} {ctx : Word} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {r : Rhs} (hlt : listLt off r.uses = true)
    (hav : ∀ x ∈ r.uses, clonedDefs.contains x = false ∨ av.contains x = true) :
    (loopMapRhs clonedDefs off c r).eval ρ₂ mem ctx = r.eval ρ₁ mem ctx := by
  cases r with
  | arg a => exact loopMapArg_eval h hlt hav
  | bin o w a b =>
      simp only [Rhs.uses, listLt_append] at hlt
      simp only [loopMapRhs, Rhs.eval,
        loopMapArg_eval h hlt.1 (fun x hx => hav x (by simp [Rhs.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [Rhs.uses, hx]))]
  | load w e m =>
      simp only [loopMapRhs, Rhs.eval, loopMapAddr_eval h hlt hav]
  | addr m => exact loopMapAddr_eval h hlt hav
  | select cond w a b t f =>
      simp only [Rhs.uses, listLt_append] at hlt
      simp only [loopMapRhs, Rhs.eval,
        loopMapArg_eval h hlt.1.1.1 (fun x hx => hav x (by simp [Rhs.uses, hx])),
        loopMapArg_eval h hlt.1.1.2 (fun x hx => hav x (by simp [Rhs.uses, hx])),
        loopMapArg_eval h hlt.1.2 (fun x hx => hav x (by simp [Rhs.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [Rhs.uses, hx]))]
  | test cond w a b =>
      simp only [Rhs.uses, listLt_append] at hlt
      simp only [loopMapRhs, Rhs.eval,
        loopMapArg_eval h hlt.1 (fun x hx => hav x (by simp [Rhs.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [Rhs.uses, hx]))]
  | bsr64 a =>
      simp only [loopMapRhs, Rhs.eval, loopMapArg_eval h hlt hav]

private theorem loopMapLimb_eval {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ : Env} (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {op : LimbOp} (hlt : listLt off op.uses = true)
    (hav : ∀ x ∈ op.uses, clonedDefs.contains x = false ∨ av.contains x = true) :
    (loopMapLimb clonedDefs off c op).eval ρ₂ = op.eval ρ₁ := by
  cases op with
  | mulWide64 a b =>
      simp only [LimbOp.uses, listLt_append] at hlt
      simp only [loopMapLimb, LimbOp.eval,
        loopMapArg_eval h hlt.1 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [LimbOp.uses, hx]))]
  | divWide64 hi lo d =>
      simp only [LimbOp.uses, listLt_append] at hlt
      simp only [loopMapLimb, LimbOp.eval,
        loopMapArg_eval h hlt.1.1 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.1.2 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [LimbOp.uses, hx]))]
  | addCarry64 a b cin =>
      simp only [LimbOp.uses, listLt_append] at hlt
      simp only [loopMapLimb, LimbOp.eval,
        loopMapArg_eval h hlt.1.1 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.1.2 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [LimbOp.uses, hx]))]
  | subBorrow64 a b bin =>
      simp only [LimbOp.uses, listLt_append] at hlt
      simp only [loopMapLimb, LimbOp.eval,
        loopMapArg_eval h hlt.1.1 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.1.2 (fun x hx => hav x (by simp [LimbOp.uses, hx])),
        loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [LimbOp.uses, hx]))]

private theorem loopMapStmt_exec {clonedDefs : Src.NatSet} {off c : Nat} {av : Src.NatSet}
    {ρ₁ ρ₂ ρ₁' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (h : LoopCopyRel clonedDefs off c av ρ₁ ρ₂)
    {s : Stmt} (hlt : listLt off s.uses = true)
    (hav : ∀ x ∈ s.uses, clonedDefs.contains x = false ∨ av.contains x = true)
    (hdefs : ∀ d ∈ s.defs, clonedDefs.contains d = true)
    (hx : s.exec ρ₁ mem ctx = some (ρ₁', mem')) :
    ∃ ρ₂', (loopMapStmt clonedDefs off c s).exec ρ₂ mem ctx = some (ρ₂', mem') ∧
      LoopCopyRel clonedDefs off c (s.defs.foldl (fun a x => a.insert x) av) ρ₁' ρ₂' := by
  cases s with
  | assign x r =>
      simp only [Stmt.uses] at hlt hav
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      refine ⟨ρ₂.insert (loopMapReg clonedDefs off c x) v,
        by simp [loopMapStmt, Stmt.exec, loopMapRhs_eval h hlt hav, hv], ?_⟩
      simpa [Stmt.defs] using h.insert_def (hdefs x (by simp [Stmt.defs])) v
  | limb r1 r2 op =>
      simp only [Stmt.uses] at hlt hav
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      refine ⟨(ρ₂.insert (loopMapReg clonedDefs off c r1) v1).insert (loopMapReg clonedDefs off c r2) v2,
        by simp [loopMapStmt, Stmt.exec, loopMapLimb_eval h hlt hav, hv], ?_⟩
      simpa [Stmt.defs] using (h.insert_def (hdefs r1 (by simp [Stmt.defs])) v1).insert_def
        (hdefs r2 (by simp [Stmt.defs])) v2
  | store w m a =>
      simp only [Stmt.uses, listLt_append] at hlt
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨addr, haddr, val, hval, hwr⟩ := hx
      have hma := loopMapAddr_eval (ctx := ctx) h hlt.1 (fun x hx => hav x (by simp [Stmt.uses, hx]))
      have haa := loopMapArg_eval h hlt.2 (fun x hx => hav x (by simp [Stmt.uses, hx]))
      cases hw : mem.write? w addr val with
      | error _ => rw [hw] at hwr; cases hwr
      | ok mem'' =>
          rw [hw] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨ρ₂, by simp [loopMapStmt, Stmt.exec, hma, haa, haddr, hval, hw], h⟩
  | call _ _ _ => simp [Stmt.exec] at hx

/-- For outside blocks (where no used register lies in `clonedDefs`), `LoopOuterRel` suffices
to evaluate arguments identically and execute statements identically while preserving `LoopOuterRel`. -/
private theorem outer_arg_eval {clonedDefs : Src.NatSet} {off : VReg} {ρ₁ ρ₂ : Env}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) {a : Arg} (hlt : listLt off a.uses = true)
    (hnc : ∀ x ∈ a.uses, clonedDefs.contains x = false) : a.eval ρ₂ = a.eval ρ₁ := by
  simpa [loopMapArg_zero'] using
    loopMapArg_eval (c := 0) h.toCopyLeaf hlt (fun x hx => .inl (hnc x hx))

private theorem outer_evalArgs {clonedDefs : Src.NatSet} {off : VReg} {ρ₁ ρ₂ : Env}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) {as : List Arg}
    (hlt : ∀ a ∈ as, listLt off a.uses = true)
    (hnc : ∀ a ∈ as, ∀ x ∈ a.uses, clonedDefs.contains x = false) :
    evalArgs ρ₂ as = evalArgs ρ₁ as := by
  have heq : as.map (loopMapArg clonedDefs off 0) = as := by
    clear hlt hnc
    induction as with | nil => rfl | cons a r ih => simp only [List.map_cons, loopMapArg_zero', ih]
  have h1 := loopMapArgs_eval (c := 0) h.toCopyLeaf hlt (fun a ha x hx => .inl (hnc a ha x hx))
  rwa [heq] at h1

private theorem outer_stmt_exec {clonedDefs : Src.NatSet} {off : VReg}
    {ρ₁ ρ₂ ρ₁' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (h : LoopOuterRel clonedDefs off ρ₁ ρ₂) {s : Stmt} (hlt : listLt off s.uses = true)
    (hnc : ∀ x ∈ s.uses, clonedDefs.contains x = false)
    (hx : s.exec ρ₁ mem ctx = some (ρ₁', mem')) :
    ∃ ρ₂', s.exec ρ₂ mem ctx = some (ρ₂', mem') ∧ LoopOuterRel clonedDefs off ρ₁' ρ₂' := by
  have hc := h.toCopyLeaf (c := 0)
  cases s with
  | assign x r =>
      simp only [Stmt.uses] at hlt hnc
      have hr : r.eval ρ₂ mem ctx = r.eval ρ₁ mem ctx := by
        simpa [loopMapRhs_zero'] using loopMapRhs_eval (c := 0) hc hlt (fun u hu => .inl (hnc u hu))
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨v, hv, rfl, rfl⟩ := hx
      exact ⟨ρ₂.insert x v, by simp [Stmt.exec, hr, hv], h.insert_same x v⟩
  | limb r1 r2 op =>
      simp only [Stmt.uses] at hlt hnc
      have hop : op.eval ρ₂ = op.eval ρ₁ := by
        simpa [loopMapLimb_zero'] using loopMapLimb_eval (c := 0) hc hlt (fun u hu => .inl (hnc u hu))
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨⟨v1, v2⟩, hv, rfl, rfl⟩ := hx
      exact ⟨(ρ₂.insert r1 v1).insert r2 v2, by simp [Stmt.exec, hop, hv],
        (h.insert_same r1 v1).insert_same r2 v2⟩
  | store w m a =>
      simp only [Stmt.uses, listLt_append] at hlt
      have hm : m.eval ρ₂ ctx = m.eval ρ₁ ctx := by
        simpa [loopMapAddr_zero'] using loopMapAddr_eval (c := 0) hc hlt.1 (fun u hu => .inl (hnc u (by simp [Stmt.uses, hu])))
      have ha : a.eval ρ₂ = a.eval ρ₁ :=
        outer_arg_eval h hlt.2 (fun u hu => hnc u (by simp [Stmt.uses, hu]))
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨addr, haddr, val, hval, hwr⟩ := hx
      cases hw : mem.write? w addr val with
      | error _ => rw [hw] at hwr; cases hwr
      | ok mem'' =>
          rw [hw] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr
          obtain ⟨rfl, rfl⟩ := hwr
          exact ⟨ρ₂, by simp [Stmt.exec, hm, ha, haddr, hval, hw], h⟩
  | call _ _ _ => simp [Stmt.exec] at hx

/-- Helper: execute a 0-statement trampoline block jumping to `x + delta` and binding `F.blocks[x].params`. -/
private theorem step_trampoline {q : Program} {F' : Func} {fi trampLbl x delta regStart nParams : Nat}
    {mem : X86.Memory} {ctx : Word} {fr₂ : Frame} {rest₂ : List Frame}
    {vals : List Word} {ρ₁ ρ₂ ρ₁' : Env} {clonedDefs : Src.NatSet} {off : VReg}
    {tgtBlk tgtBlk' : Block} {cold : Bool}
    (hqfi : q.funcs[fi]? = some F')
    (hfn2 : fr₂.fn = fi)
    (htramp : F'.blocks[trampLbl]? = some
      { params := (List.range nParams).map (regStart + ·)
        body := #[]
        term := .jump { target := x + delta, args := ((List.range nParams).map (regStart + ·)).map .v }
        cold := cold })
    (htgt : F'.blocks[x + delta]? = some tgtBlk')
    (hpar : tgtBlk'.params = tgtBlk.params)
    (hnpar : tgtBlk.params.length = nParams)
    (hreg_ge : off ≤ regStart)
    (hlt_fwd : trampLbl < x + delta)
    (houter : LoopOuterRel clonedDefs off ρ₁ ρ₂)
    (hbp1 : bindParams ρ₁ tgtBlk.params vals = some ρ₁') :
    ∃ ρ₂t ρ₂',
      bindParams ρ₂ ((List.range nParams).map (regStart + ·)) vals = some ρ₂t ∧
      step q { mem := mem, ctx := ctx, stack := { fr₂ with label := trampLbl, pos := 0, env := ρ₂t } :: rest₂ } =
        .next { mem := mem, ctx := ctx, stack := { fr₂ with label := x + delta, pos := 0, env := ρ₂' } :: rest₂ } false ∧
      LoopOuterRel clonedDefs off ρ₁' ρ₂' := by
  have hlen_vals : nParams = vals.length := by rw [← hnpar]; exact bindParams_len_eq hbp1
  have hps_len : ((List.range nParams).map (regStart + ·)).length = vals.length := by simp [hlen_vals]
  obtain ⟨ρ₂t, hbp_t⟩ := bindParams_of_eq_len ρ₂ _ vals hps_len
  obtain ⟨hev_t, hpres_t⟩ := bindParams_nodup_evalArgs (nodup_map_add_range regStart nParams) hbp_t
  have houter_t : LoopOuterRel clonedDefs off ρ₁ ρ₂t := by
    intro u hu hnc
    have hun : u ∉ (List.range nParams).map (regStart + ·) := fun hm =>
      Nat.not_lt.2 (Nat.le_trans hreg_ge (mem_map_add_range_ge hm)) hu
    rw [hpres_t u hun]; exact houter u hu hnc
  obtain ⟨ρ₂', hbp2, houter'⟩ := houter_t.bindParams_same hbp1
  refine ⟨ρ₂t, ρ₂', hbp_t, ?_, houter'⟩
  have hst : step q { mem := mem, ctx := ctx, stack := { fr₂ with label := trampLbl, pos := 0, env := ρ₂t } :: rest₂ } =
      takeEdge F' { mem := mem, ctx := ctx, stack := { fr₂ with label := trampLbl, pos := 0, env := ρ₂t } :: rest₂ }
        { fr₂ with label := trampLbl, pos := 0, env := ρ₂t } rest₂ ρ₂t
        { target := x + delta, args := ((List.range nParams).map (regStart + ·)).map .v } := by
    unfold step; dsimp only; rw [hfn2, hqfi]; dsimp only; rw [htramp]; simp
  rw [hst]
  have hte := takeEdge_ok (F := F') (s := { mem := mem, ctx := ctx, stack := { fr₂ with label := trampLbl, pos := 0, env := ρ₂t } :: rest₂ })
    (fr := { fr₂ with label := trampLbl, pos := 0, env := ρ₂t }) (rest := rest₂) (ρ := ρ₂t)
    (e := { target := x + delta, args := ((List.range nParams).map (regStart + ·)).map .v })
    hev_t htgt (by rw [hpar]; exact hbp2)
  have hfwd : decide (x + delta ≤ trampLbl) = false := by simp; omega
  simpa [hfwd] using hte

private theorem step_term_ge {p : Program} {F : Func} {B : Block} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hlt : ¬ fr.pos < B.body.size) :
    step p { mem := mem, ctx := ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem := mem, ctx := ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t f =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              takeEdge F { mem := mem, ctx := ctx, stack := fr :: rest } fr rest fr.env
                (if c.holds w va vb then t else f)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem := mem, ctx := ctx, stack := fr :: rest } fr rest
                (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret ras =>
          match evalArgs fr.env ras with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | c :: rest' =>
                  match bindParams c.env c.dsts vals with
                  | some ρ => .next { mem := mem, ctx := ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g tas =>
          match evalArgs fr.env tas >>= enter p g with
          | some calleeF => .next { mem := mem, ctx := ctx, stack := calleeF :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step
  simp only [hf, hb, hlt, ↓reduceDIte]; rfl

private theorem loopMapArg_zero_map (clonedDefs : Src.NatSet) (off : VReg) (as : List Arg) :
    as.map (loopMapArg clonedDefs off 0) = as := by
  induction as with
  | nil => rfl
  | cons a r ih => simp [loopMapArg_zero', ih]


/-- Any non-stuck `Sem.Final` LIR step must be a `.fail`, `.trap`, or top-level `.ret` terminator. -/
private theorem takeEdge_ne_final {F : Func} {s : State} {fr : Frame} {rest : List Frame}
    {ρ : Env} {e : Edge} {r : Sem.Result (List Word × X86.Memory)}
    (hfin : Sem.Final (takeEdge F s fr rest ρ e).toSem r) (hne : r ≠ .stuck) : False := by
  unfold takeEdge at hfin
  cases hev : evalArgs ρ e.args with
  | none => rw [hev] at hfin; cases hfin; exact hne rfl
  | some vs =>
      cases htgt : F.blocks[e.target]? with
      | none => rw [hev, htgt] at hfin; cases hfin; exact hne rfl
      | some tb =>
          rw [hev, htgt] at hfin; dsimp only at hfin
          cases hbp : bindParams ρ tb.params vs with
          | none => rw [hbp] at hfin; cases hfin; exact hne rfl
          | some _ => rw [hbp] at hfin; cases hfin

private theorem final_ne_stuck_elim {p : Program} {mem : X86.Memory} {ctx : Word}
    {fr : Frame} {rest : List Frame} {r : Sem.Result (List Word × X86.Memory)}
    (hfin : Sem.Final (semStep p { mem := mem, ctx := ctx, stack := fr :: rest }) r)
    (hne : r ≠ .stuck) :
    ∃ F B, p.funcs[fr.fn]? = some F ∧ F.blocks[fr.label]? = some B ∧ ¬ fr.pos < B.body.size ∧
      ((∃ res, B.term = .fail res ∧ r = .resource res) ∨
       (B.term = .trap ∧ r = .trap) ∨
       (∃ ras vs, B.term = .ret ras ∧ evalArgs fr.env ras = some vs ∧ rest = [] ∧ r = .ok (vs, mem))) := by
  have hunf : semStep p { mem := mem, ctx := ctx, stack := fr :: rest } =
      (step p { mem := mem, ctx := ctx, stack := fr :: rest }).toSem := rfl
  rw [hunf] at hfin
  unfold step at hfin; dsimp only at hfin
  cases hF : p.funcs[fr.fn]? with
  | none => rw [hF] at hfin; cases hfin; exact absurd rfl hne
  | some F =>
      rw [hF] at hfin; dsimp only at hfin
      cases hB : F.blocks[fr.label]? with
      | none => rw [hB] at hfin; cases hfin; exact absurd rfl hne
      | some B =>
          rw [hB] at hfin; dsimp only at hfin
          by_cases hlt : fr.pos < B.body.size
          · simp only [hlt, ↓reduceDIte] at hfin
            cases hs : B.body[fr.pos]'hlt with
            | call _ g as =>
                rw [hs] at hfin; dsimp only at hfin
                cases hev : evalArgs fr.env as >>= enter p g with
                | none => rw [hev] at hfin; cases hfin; exact absurd rfl hne
                | some _ => rw [hev] at hfin; cases hfin
            | assign _ _ | limb _ _ _ | store _ _ _ =>
                rw [hs] at hfin; dsimp only at hfin
                cases hx : (B.body[fr.pos]'hlt).exec fr.env mem ctx with
                | none => rw [hs] at hx; rw [hx] at hfin; cases hfin; exact absurd rfl hne
                | some _ => rw [hs] at hx; rw [hx] at hfin; cases hfin
          · simp only [hlt, ↓reduceDIte] at hfin
            refine ⟨F, B, rfl, hB, hlt, ?_⟩
            cases ht : B.term with
            | fail res =>
                rw [ht] at hfin; cases hfin; exact .inl ⟨res, rfl, rfl⟩
            | trap =>
                rw [ht] at hfin; cases hfin; exact .inr (.inl ⟨rfl, rfl⟩)
            | ret ras =>
                rw [ht] at hfin; dsimp only at hfin
                cases hev : evalArgs fr.env ras with
                | none => rw [hev] at hfin; cases hfin; exact absurd rfl hne
                | some vs =>
                    rw [hev] at hfin; dsimp only at hfin
                    cases rest with
                    | nil => cases hfin; exact .inr (.inr ⟨ras, vs, rfl, hev, rfl, rfl⟩)
                    | cons c rest' =>
                        dsimp only at hfin
                        cases hbp : bindParams c.env c.dsts vs with
                        | none => rw [hbp] at hfin; cases hfin; exact absurd rfl hne
                        | some _ => rw [hbp] at hfin; cases hfin
            | jump e =>
                rw [ht] at hfin; exact (takeEdge_ne_final hfin hne).elim
            | br c w a b' t f =>
                rw [ht] at hfin; dsimp only at hfin
                cases ha : a.eval fr.env with
                | none => rw [ha] at hfin; cases hfin; exact absurd rfl hne
                | some va =>
                    cases hb' : b'.eval fr.env with
                    | none => rw [ha, hb'] at hfin; cases hfin; exact absurd rfl hne
                    | some vb =>
                        rw [ha, hb'] at hfin
                        exact (takeEdge_ne_final hfin hne).elim
            | brOvf o x a b' ok ovf =>
                rw [ht] at hfin; dsimp only at hfin
                cases ha : a.eval fr.env with
                | none => rw [ha] at hfin; cases hfin; exact absurd rfl hne
                | some va =>
                    cases hb' : b'.eval fr.env with
                    | none => rw [ha, hb'] at hfin; cases hfin; exact absurd rfl hne
                    | some vb =>
                        rw [ha, hb'] at hfin
                        exact (takeEdge_ne_final hfin hne).elim
            | tail g as =>
                rw [ht] at hfin; dsimp only at hfin
                cases hev : evalArgs fr.env as >>= enter p g with
                | none => rw [hev] at hfin; cases hfin; exact absurd rfl hne
                | some _ => rw [hev] at hfin; cases hfin

/-! ## Part 4: Direct soundness proof for `unrollLoopSite` (`PotentialForward`) -/

section UnrollLayout

variable (F : Func) (h : Nat) (nodes leafExits nonLeafExits : List Nat) (U : Nat) (off : VReg)

private def unrollCut : Nat := nodes.getLastD h + 1
private def unrollStride : Nat := nodes.length + leafExits.length + nonLeafExits.length
private def unrollDelta : Nat := nonLeafExits.length + (U - 1) * unrollStride nodes leafExits nonLeafExits
private def unrollCopyNodeBase (c : Nat) : Nat :=
  unrollCut h nodes + nonLeafExits.length + (c - 1) * unrollStride nodes leafExits nonLeafExits
private def unrollCopyExitBase (c : Nat) : Nat :=
  unrollCopyNodeBase h nodes leafExits nonLeafExits c + nodes.length
private def unrollCopyTrampBase (c : Nat) : Nat :=
  if c == 0 then unrollCut h nodes
  else unrollCopyNodeBase h nodes leafExits nonLeafExits c + nodes.length + leafExits.length
private def unrollRemapOrig (L : Nat) : Nat :=
  if L < unrollCut h nodes then L else L + unrollDelta nodes leafExits nonLeafExits U

private def unrollRemapTarget (c : Nat) (tgt : Nat) : Nat :=
  if tgt == h then
    if c + 1 < U then unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1) else h
  else if (Src.NatSet.ofList nodes).contains tgt then
    if c == 0 then tgt
    else match listIndexOf nodes tgt with
    | some idx => unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx
    | none => tgt
  else
    match listIndexOf leafExits tgt with
    | some eidx =>
        if c == 0 then unrollRemapOrig h nodes leafExits nonLeafExits U tgt
        else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx
    | none =>
        match listIndexOf nonLeafExits tgt with
        | some tidx => unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx
        | none => unrollRemapOrig h nodes leafExits nonLeafExits U tgt

private theorem buildUnrolled_blocks_prefix_node {b : Nat} {B : Block}
    (hcut : unrollCut h nodes ≤ F.blocks.size)
    (hb : b < unrollCut h nodes)
    (hmem : (Src.NatSet.ofList nodes).contains b = true)
    (hB : F.blocks[b]? = some B) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[b]? =
      some { B with
        term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off 0
          (unrollRemapTarget h nodes leafExits nonLeafExits U 0) B.term } := by
  have hltF : b < F.blocks.size := by omega
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp [unrollCut] at hb ⊢; exact hb)]
  rw [List.getElem?_map, List.getElem?_range (by simp only [unrollCut] at hb; exact hb)]
  simp only [Option.map_some, hget, hmem, ↓reduceIte]
  rfl

private theorem buildUnrolled_blocks_prefix_other {b : Nat} {B : Block}
    (hb : b < unrollCut h nodes)
    (hnm : (Src.NatSet.ofList nodes).contains b = false)
    (hB : F.blocks[b]? = some B) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[b]? =
      some { B with
        term := B.term.setEdges (B.term.edges.map fun e =>
          { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) } := by
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp [unrollCut] at hb ⊢; exact hb)]
  rw [List.getElem?_map, List.getElem?_range (by simp only [unrollCut] at hb; exact hb)]
  simp only [Option.map_some, hget, hnm, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem buildUnrolled_blocks_copy0_tramp {tidx x : Nat}
    (hx : nonLeafExits[tidx]? = some x) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[unrollCut h nodes + tidx]? =
      some (let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
            let regStart := U * off + tidx * off
            let ps := (List.range nParams).map (regStart + ·)
            { params := ps
              body := #[]
              term := .jump { target := x + unrollDelta nodes leafExits nonLeafExits U, args := ps.map .v }
              cold := (F.blocks[x]?.map (·.cold)).getD false }) := by
  have htidx : tidx < nonLeafExits.length := (List.getElem?_eq_some_iff.1 hx).1
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [unrollCut]), List.length_map, List.length_range]
  have hsub0 : unrollCut h nodes + tidx - (nodes.getLastD h + 1) = tidx := by simp [unrollCut]
  rw [hsub0, List.getElem?_append_left (by rw [buildTrampBlocks_length]; exact htidx)]
  have htr := buildTrampBlocks_getElem? F nonLeafExits (unrollDelta nodes leafExits nonLeafExits U)
    (U * off + 0 * (nonLeafExits.length * off)) off tidx x hx
  simpa [unrollDelta, unrollStride] using htr

private theorem buildUnrolled_blocks_copy_node {c idx b : Nat} {B : Block}
    (hc1 : 1 ≤ c) (hcU : c < U)
    (hidx : nodes[idx]? = some b) (hB : F.blocks[b]? = some B) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[
      unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx]? =
      some { params := B.params.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c)
             body := B.body.map (loopMapStmt (collectBlocksDefs F (nodes ++ leafExits)) off c)
             term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off c
               (unrollRemapTarget h nodes leafExits nonLeafExits U c) B.term
             cold := B.cold } := by
  have hidxLt : idx < nodes.length := (List.getElem?_eq_some_iff.1 hidx).1
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [unrollCopyNodeBase, unrollCut]; omega),
    List.length_map, List.length_range]
  have hsub1 : unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx - (nodes.getLastD h + 1) =
      nonLeafExits.length + ((c - 1) * unrollStride nodes leafExits nonLeafExits + idx) := by
    simp only [unrollCopyNodeBase, unrollCut]; omega
  rw [hsub1]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  have hSpos : 0 < unrollStride nodes leafExits nonLeafExits := by
    simp only [unrollStride]; omega
  have hltFlat : (c - 1) * unrollStride nodes leafExits nonLeafExits + idx <
      (U - 1) * unrollStride nodes leafExits nonLeafExits := by
    have h1 : (c - 1 + 1) * unrollStride nodes leafExits nonLeafExits ≤
        (U - 1) * unrollStride nodes leafExits nonLeafExits := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    simp only [unrollStride] at h1 ⊢; omega
  rw [List.getElem?_append_left (by
    rw [length_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
      (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]), List.length_range]
    exact hltFlat)]
  rw [getElem?_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
    (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]) hSpos
    (c - 1) idx (by simp only [unrollStride]; omega)]
  rw [List.getElem?_range (by omega)]
  simp only [Option.bind_some]
  rw [List.getElem?_append_left (by simp [hidxLt]), List.getElem?_map, hidx]
  have hcEq : c - 1 + 1 = c := by omega
  simp only [Option.map_some, hcEq, hget]
  rfl

private theorem buildUnrolled_blocks_copy_exit {c eidx b : Nat} {B : Block}
    (hc1 : 1 ≤ c) (hcU : c < U)
    (heidx : leafExits[eidx]? = some b) (hB : F.blocks[b]? = some B) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[
      unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx]? =
      some { params := B.params.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c)
             body := B.body.map (loopMapStmt (collectBlocksDefs F (nodes ++ leafExits)) off c)
             term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off c (fun l => l) B.term
             cold := B.cold } := by
  have heidxLt : eidx < leafExits.length := (List.getElem?_eq_some_iff.1 heidx).1
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [unrollCopyExitBase, unrollCopyNodeBase, unrollCut]; omega),
    List.length_map, List.length_range]
  have hsub1 : unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx - (nodes.getLastD h + 1) =
      nonLeafExits.length + ((c - 1) * unrollStride nodes leafExits nonLeafExits + (nodes.length + eidx)) := by
    simp only [unrollCopyExitBase, unrollCopyNodeBase, unrollCut]; omega
  rw [hsub1]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  have hSpos : 0 < unrollStride nodes leafExits nonLeafExits := by simp only [unrollStride]; omega
  have hltFlat : (c - 1) * unrollStride nodes leafExits nonLeafExits + (nodes.length + eidx) <
      (U - 1) * unrollStride nodes leafExits nonLeafExits := by
    have h1 : (c - 1 + 1) * unrollStride nodes leafExits nonLeafExits ≤
        (U - 1) * unrollStride nodes leafExits nonLeafExits := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    simp only [unrollStride] at h1 ⊢; omega
  rw [List.getElem?_append_left (by
    rw [length_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
      (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]), List.length_range]
    exact hltFlat)]
  rw [getElem?_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
    (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]) hSpos
    (c - 1) (nodes.length + eidx) (by simp only [unrollStride]; omega)]
  rw [List.getElem?_range (by omega)]
  simp only [Option.bind_some]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp [heidxLt]), List.getElem?_map, heidx]
  have hcEq : c - 1 + 1 = c := by omega
  simp only [Option.map_some, hcEq, hget]

private theorem buildUnrolled_blocks_copy_tramp {c tidx x : Nat}
    (hc1 : 1 ≤ c) (hcU : c < U)
    (hx : nonLeafExits[tidx]? = some x) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[
      unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx]? =
      some (let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
            let regStart := U * off + c * (nonLeafExits.length * off) + tidx * off
            let ps := (List.range nParams).map (regStart + ·)
            { params := ps
              body := #[]
              term := .jump { target := x + unrollDelta nodes leafExits nonLeafExits U, args := ps.map .v }
              cold := (F.blocks[x]?.map (·.cold)).getD false }) := by
  have htidxLt : tidx < nonLeafExits.length := (List.getElem?_eq_some_iff.1 hx).1
  have hcne : (c == 0) = false := beq_false_of_ne (by omega)
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [unrollCopyTrampBase, hcne, unrollCopyNodeBase, unrollCut]; omega),
    List.length_map, List.length_range]
  have hsub1 : unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx - (nodes.getLastD h + 1) =
      nonLeafExits.length + ((c - 1) * unrollStride nodes leafExits nonLeafExits + (nodes.length + leafExits.length + tidx)) := by
    simp only [unrollCopyTrampBase, hcne, Bool.false_eq_true, ↓reduceIte, unrollCopyNodeBase, unrollCut]; omega
  rw [hsub1]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  have hSpos : 0 < unrollStride nodes leafExits nonLeafExits := by simp only [unrollStride]; omega
  have hltFlat : (c - 1) * unrollStride nodes leafExits nonLeafExits + (nodes.length + leafExits.length + tidx) <
      (U - 1) * unrollStride nodes leafExits nonLeafExits := by
    have h1 : (c - 1 + 1) * unrollStride nodes leafExits nonLeafExits ≤
        (U - 1) * unrollStride nodes leafExits nonLeafExits := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    simp only [unrollStride] at h1 ⊢; omega
  rw [List.getElem?_append_left (by
    rw [length_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
      (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]), List.length_range]
    exact hltFlat)]
  rw [getElem?_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
    (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]) hSpos
    (c - 1) (nodes.length + leafExits.length + tidx) (by simp only [unrollStride]; omega)]
  rw [List.getElem?_range (by omega)]
  simp only [Option.bind_some]
  rw [List.getElem?_append_right (by simp; omega), List.length_map]
  have hsub2 : nodes.length + leafExits.length + tidx - nodes.length = leafExits.length + tidx := by omega
  rw [hsub2, List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  have hcEq : c - 1 + 1 = c := by omega
  rw [hcEq]
  have htr := buildTrampBlocks_getElem? F nonLeafExits (unrollDelta nodes leafExits nonLeafExits U)
    (U * off + c * (nonLeafExits.length * off)) off tidx x hx
  simpa [unrollDelta, unrollStride] using htr

private theorem buildUnrolled_blocks_suffix {b : Nat} {B : Block}
    (hge : unrollCut h nodes ≤ b) (hB : F.blocks[b]? = some B) :
    (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).blocks[
      b + unrollDelta nodes leafExits nonLeafExits U]? =
      some { B with
        term := B.term.setEdges (B.term.edges.map fun e =>
          { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) } := by
  have hlt : b < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
  have hget : F.blocks[nodes.getLastD h + 1 + (b - (nodes.getLastD h + 1))]! = B := by
    rw [show nodes.getLastD h + 1 + (b - (nodes.getLastD h + 1)) = b by simp only [unrollCut] at hge; omega]
    exact array_getElem!_of_getElem? hB
  unfold buildUnrolledFunc
  dsimp only
  rw [List.getElem?_toArray]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [unrollCut] at hge ⊢; omega),
    List.length_map, List.length_range]
  have hsub1 : b + unrollDelta nodes leafExits nonLeafExits U - (nodes.getLastD h + 1) =
      nonLeafExits.length + ((U - 1) * unrollStride nodes leafExits nonLeafExits + (b - (nodes.getLastD h + 1))) := by
    simp only [unrollDelta, unrollCut] at hge ⊢; omega
  rw [hsub1]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by
    rw [length_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
      (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]), List.length_range]; omega),
    length_flatMap_const_len (m := unrollStride nodes leafExits nonLeafExits)
      (fun ci _ => by simp [unrollStride, buildTrampBlocks_length, Nat.add_assoc]),
    List.length_range, Nat.add_sub_cancel_left]
  rw [List.getElem?_map, List.getElem?_range (by simp only [unrollCut] at hge ⊢; omega)]
  simp only [Option.map_some, hget]
  rfl

end UnrollLayout

/-! ### Unrolling amortized potential & simulation relation -/

/-- Per-frame potential in `q` for `U`-way loop unrolling (`≤ U - 1`):
- `fr.fn ≠ fi`: `0`
- `fr.label < cut` (prefix + copy `0`): `U - 1`
- copy `c = ci + 1 ∈ [1 .. U - 1]` node block: `U - 1 - c`
- trampolines, cloned leaf exits, suffix blocks: `0`. -/
def unrollFramePot (fi cut K E T U : Nat) (fr : Frame) : Nat :=
  let lbl : Nat := fr.label
  if (fr.fn : Nat) != fi then 0
  else if lbl < cut then U - 1
  else
    let stride := K + E + T
    let c0 := cut + T
    if lbl < c0 then 0
    else if lbl < c0 + (U - 1) * stride then
      if stride == 0 then 0
      else
        let rel := lbl - c0
        let ci := rel / stride
        let inCopy := rel % stride
        if inCopy < K then U - 1 - (ci + 1)
        else 0
    else 0

def unrollPot (fi cut K E T U : Nat) (s : State) : Nat :=
  (s.stack.map (unrollFramePot fi cut K E T U)).sum

private theorem unrollPot_cons (fi cut K E T U : Nat) (mem : X86.Memory) (ctx : Word) (fr : Frame) (rest : List Frame) :
    unrollPot fi cut K E T U { mem := mem, ctx := ctx, stack := fr :: rest } =
      unrollFramePot fi cut K E T U fr + (rest.map (unrollFramePot fi cut K E T U)).sum := rfl

private theorem unrollFramePot_congr (fi cut K E T U : Nat) {f₁ f₂ : Frame}
    (hfn : f₁.fn = f₂.fn) (hlbl : f₁.label = f₂.label) :
    unrollFramePot fi cut K E T U f₁ = unrollFramePot fi cut K E T U f₂ := by
  unfold unrollFramePot; rw [hfn, hlbl]

private theorem unrollFramePot_le (fi cut K E T U : Nat) (fr : Frame) :
    unrollFramePot fi cut K E T U fr ≤ U - 1 := by
  unfold unrollFramePot
  dsimp only
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · split
          · omega
          · split
            · exact Nat.sub_le _ _
            · omega
        · omega

private theorem unrollFramePot_ne (fi cut K E T U : Nat) {fr : Frame} (hne : fr.fn ≠ fi) :
    unrollFramePot fi cut K E T U fr = 0 := by
  unfold unrollFramePot
  have : ((fr.fn : Nat) != fi) = true := by simpa using hne
  simp [this]

private theorem unrollFramePot_lt_cut (fi cut K E T U : Nat) {fr : Frame}
    (hfn : fr.fn = fi) (hlt : fr.label < cut) :
    unrollFramePot fi cut K E T U fr = U - 1 := by
  unfold unrollFramePot
  simp [hfn, hlt]

private theorem unrollFramePot_copy_node (fi cut K E T U c idx : Nat) {fr : Frame}
    (hfn : fr.fn = fi) (hc1 : 1 ≤ c) (hcU : c < U) (hidx : idx < K)
    (hlbl : fr.label = cut + T + (c - 1) * (K + E + T) + idx) :
    unrollFramePot fi cut K E T U fr = U - 1 - c := by
  unfold unrollFramePot
  dsimp only
  have hSpos : 0 < K + E + T := by omega
  have hSne : (K + E + T == 0) = false := beq_false_of_ne (by omega)
  have h1 : ¬ fr.label < cut := by rw [hlbl]; exact Nat.not_lt.2 (by omega)
  have h2 : ¬ fr.label < cut + T := by rw [hlbl]; exact Nat.not_lt.2 (by omega)
  have h3 : fr.label < cut + T + (U - 1) * (K + E + T) := by
    rw [hlbl]
    have hmul : (c - 1 + 1) * (K + E + T) ≤ (U - 1) * (K + E + T) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by omega : idx < K + E + T) _) (by omega)
  have hrel : fr.label - (cut + T) = (c - 1) * (K + E + T) + idx := by
    rw [hlbl, Nat.add_assoc, Nat.add_sub_cancel_left]
  have hdiv : ((c - 1) * (K + E + T) + idx) / (K + E + T) = c - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div hSpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hmod : ((c - 1) * (K + E + T) + idx) % (K + E + T) = idx := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [hfn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, hSne, hrel, hdiv, hmod, hidx]
  congr 1; omega

private theorem unrollFramePot_copy_exit (fi cut K E T U c eidx : Nat) {fr : Frame}
    (hfn : fr.fn = fi) (hc1 : 1 ≤ c) (hcU : c < U) (heidx : eidx < E)
    (hlbl : fr.label = cut + T + (c - 1) * (K + E + T) + K + eidx) :
    unrollFramePot fi cut K E T U fr = 0 := by
  unfold unrollFramePot
  dsimp only
  have hSpos : 0 < K + E + T := by omega
  have hSne : (K + E + T == 0) = false := beq_false_of_ne (by omega)
  have h1 : ¬ fr.label < cut := by rw [hlbl]; exact Nat.not_lt.2 (by omega)
  have h2 : ¬ fr.label < cut + T := by rw [hlbl]; exact Nat.not_lt.2 (by omega)
  have h3 : fr.label < cut + T + (U - 1) * (K + E + T) := by
    rw [hlbl]
    have hmul : (c - 1 + 1) * (K + E + T) ≤ (U - 1) * (K + E + T) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    rw [Nat.add_assoc (cut + T + (c - 1) * (K + E + T)) K eidx]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by omega : K + eidx < K + E + T) _) (by omega)
  have hrel : fr.label - (cut + T) = (c - 1) * (K + E + T) + (K + eidx) := by
    rw [hlbl, Nat.add_assoc (cut + T + _), Nat.add_assoc (cut + T), Nat.add_sub_cancel_left]
  have hmod : ((c - 1) * (K + E + T) + (K + eidx)) % (K + E + T) = K + eidx := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hnk : ¬ K + eidx < K := by omega
  simp only [hfn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, hSne, hrel, hmod, hnk]

private theorem unrollFramePot_suffix (fi cut K E T U : Nat) {fr : Frame}
    (hfn : fr.fn = fi) (hge : cut + T + (U - 1) * (K + E + T) ≤ fr.label) :
    unrollFramePot fi cut K E T U fr = 0 := by
  unfold unrollFramePot
  dsimp only
  have h1 : ¬ fr.label < cut := Nat.not_lt.2 (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hge)
  have h2 : ¬ fr.label < cut + T := Nat.not_lt.2 (Nat.le_trans (Nat.le_add_right _ _) hge)
  have h3 : ¬ fr.label < cut + T + (U - 1) * (K + E + T) := Nat.not_lt.2 hge
  simp [hfn, h1, h2, h3]

private theorem unrollRemapOrig_le_iff (h : Nat) (nodes leafExits nonLeafExits : List Nat) (U u v : Nat) :
    decide (unrollRemapOrig h nodes leafExits nonLeafExits U v ≤
            unrollRemapOrig h nodes leafExits nonLeafExits U u) = decide (v ≤ u) := by
  unfold unrollRemapOrig
  split <;> split <;> (try rfl) <;> simp only [decide_eq_decide] <;>
    exact ⟨fun h => by omega, fun h => by omega⟩

/-- Active/suspended frame relation for `unrollLoopSite`. -/
inductive UnrollFrameRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (U : Nat) (off : VReg)
    (availMap : Array Src.NatSet) (isTop : Bool) : Frame → Frame → Prop where
  | other {fr : Frame} :
      fr.fn ≠ fi →
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap isTop fr fr
  | outside {b pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} :
      F.blocks[b]? = some blk →
      b ∉ nodes →
      b ∉ leafExits →
      pos ≤ blk.body.size →
      (isTop = false → d₂ = d₁) →
      LoopOuterRel (collectBlocksDefs F (nodes ++ leafExits)) off ρ₁ ρ₂ →
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U b, pos, ρ₂, d₂⟩
  | loopNode {b idx c pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} {av0 : Src.NatSet} :
      c < U →
      nodes[idx]? = some b →
      F.blocks[b]? = some blk →
      availMap[b]? = some av0 →
      pos ≤ blk.body.size →
      (isTop = false → 0 < pos ∧ d₂ = d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c) ∧
        (∀ d ∈ d₁, (collectBlocksDefs F (nodes ++ leafExits)).contains d = true) ∧
        ∃ g as, blk.body[pos - 1]? = some (.call d₁ g as)) →
      LoopCopyRel (collectBlocksDefs F (nodes ++ leafExits)) off c
        (availAtPos av0 blk.body (if isTop then pos else pos - 1)) ρ₁ ρ₂ →
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, if c = 0 then b else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂, d₂⟩
  | leafExit {b eidx c pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} {av0 : Src.NatSet} :
      c < U →
      leafExits[eidx]? = some b →
      F.blocks[b]? = some blk →
      availMap[b]? = some av0 →
      pos ≤ blk.body.size →
      (isTop = false → 0 < pos ∧ d₂ = d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c) ∧
        (∀ d ∈ d₁, (collectBlocksDefs F (nodes ++ leafExits)).contains d = true) ∧
        ∃ g as, blk.body[pos - 1]? = some (.call d₁ g as)) →
      LoopCopyRel (collectBlocksDefs F (nodes ++ leafExits)) off c
        (availAtPos av0 blk.body (if isTop then pos else pos - 1)) ρ₁ ρ₂ →
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U b
             else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx, pos, ρ₂, d₂⟩

inductive UnrollStackRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (U : Nat) (off : VReg)
    (availMap : Array Src.NatSet) : Bool → List Frame → List Frame → Prop where
  | nil {isTop : Bool} : UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap isTop [] []
  | cons {isTop : Bool} {fr₁ fr₂ : Frame} {rest₁ rest₂ : List Frame} :
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap isTop fr₁ fr₂ →
      UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap false rest₁ rest₂ →
      UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap isTop (fr₁ :: rest₁) (fr₂ :: rest₂)

def UnrollStateRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (U : Nat) (off : VReg)
    (availMap : Array Src.NatSet) (s₁ s₂ : State) : Prop :=
  s₁.mem = s₂.mem ∧ s₁.ctx = s₂.ctx ∧
  UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap true s₁.stack s₂.stack

private theorem unroll_enter_rel {p q : Program} {F : Func} {fi g h : Nat}
    {nodes leafExits nonLeafExits : List Nat} {U : Nat} {off : VReg} {availMap : Array Src.NatSet}
    {vs : List Word} {fr₁ : Frame}
    (hpfi : p.funcs[fi]? = some F)
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap)
    (hq : q = { funcs := p.funcs.set! fi (buildUnrolledFunc F h nodes leafExits nonLeafExits U off), main := p.main })
    (hent : enter p g vs = some fr₁) :
    ∃ fr₂, enter q g vs = some fr₂ ∧
      UnrollFrameRel F fi h nodes leafExits nonLeafExits U off availMap true fr₁ fr₂ := by
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨G, hG, ρ, hbp, rfl⟩ := hent
  by_cases hg : g = fi
  · subst hg
    rw [hpfi] at hG; cases hG
    have hqF : q.funcs[g]? = some (buildUnrolledFunc F h nodes leafExits nonLeafExits U off) := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt]
    have hpar : (buildUnrolledFunc F h nodes leafExits nonLeafExits U off).params = F.params := rfl
    have h0lt : 0 < F.blocks.size := by have := hf.h_pos; have := hf.h_lt_cut; have := hf.cut_le_size; omega
    have hb0 : F.blocks[0]? = some F.blocks[0] := Array.getElem?_eq_getElem h0lt
    have h0cut : 0 < unrollCut h nodes := by simp only [unrollCut]; omega
    have hremap0 : unrollRemapOrig h nodes leafExits nonLeafExits U 0 = 0 := by
      simp [unrollRemapOrig, h0cut]
    refine ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] }, by simp [enter, hqF, hpar, hbp], ?_⟩
    rw [← hremap0]
    exact .outside hb0 hf.zero_not_mem_nodes hf.zero_not_mem_leaf (Nat.zero_le _)
      (fun hc => by cases hc) (LoopOuterRel.refl _ _ _)
  · have hqF : q.funcs[g]? = some G := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hg, hG]
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqF, hbp], .other hg⟩

theorem unrollLoopSite_forward {p q : Program} {F : Func} {fi h : Nat}
    {nodes leafExits nonLeafExits : List Nat} {U : Nat} {off : VReg} {availMap : Array Src.NatSet}
    (hpfi : p.funcs[fi]? = some F)
    (hU : 2 ≤ U)
    (hok : loopCloneOk F h nodes leafExits nonLeafExits off availMap = true)
    (hq : q = { funcs := p.funcs.set! fi (buildUnrolledFunc F h nodes leafExits nonLeafExits U off), main := p.main }) :
    PotentialForward (semStep p) (semStep q) Eq
      (UnrollStateRel F fi h nodes leafExits nonLeafExits U off availMap)
      (fun _ s₂ => unrollPot fi (unrollCut h nodes) nodes.length leafExits.length nonLeafExits.length U s₂) U := by
  have hf := loopCloneFacts_of_ok hok
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  let cut := unrollCut h nodes
  let K := nodes.length
  let E := leafExits.length
  let T := nonLeafExits.length
  let stride := unrollStride nodes leafExits nonLeafExits
  let delta := unrollDelta nodes leafExits nonLeafExits U
  let F' := buildUnrolledFunc F h nodes leafExits nonLeafExits U off
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  have hqfi : q.funcs[fi]? = some F' := by
    rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt, F']
  have hcut_le : cut ≤ F.blocks.size := hf.cut_le_size
  have hh_lt_cut : h < cut := hf.h_lt_cut
  have hKpos : 0 < K := by
    cases hns : nodes with
    | nil => exact absurd hns hf.nodes_ne
    | cons _ _ => simp [K, hns]
  have hh0 : nodes[0]? = some h := by
    cases hns : nodes with
    | nil => exact absurd hns hf.nodes_ne
    | cons a rest =>
        have := hf.nodes_head; rw [hns] at this; simpa using this
  have hdelta_eq : cut + delta = cut + T + (U - 1) * stride := by
    simp only [delta, unrollDelta, stride, T]; omega
  -- Helper 1: matching a `ret` back to suspended caller frame `(rest₁, rest₂)`
  have matchRet : ∀ (mem : X86.Memory) (ctx : Word) (fr₂ : Frame) (rest₁ rest₂ : List Frame)
      (vs : List Word) (s₁' : State) (b : Bool),
      UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap false rest₁ rest₂ →
      (match rest₁ with
       | [] => Step.done vs mem
       | c :: rest' =>
           match bindParams c.env c.dsts vs with
           | some ρ => Step.next { mem := mem, ctx := ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
           | none => Step.stuck) = .next s₁' b →
      ∃ s₂',
        (match rest₂ with
         | [] => Step.done vs mem
         | c :: rest' =>
             match bindParams c.env c.dsts vs with
             | some ρ => Step.next { mem := mem, ctx := ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
             | none => Step.stuck) = .next s₂' b ∧
        UnrollStateRel F fi h nodes leafExits nonLeafExits U off availMap s₁' s₂' ∧
        b.toNat + unrollPot fi cut K E T U s₂' ≤
          U * b.toNat + unrollPot fi cut K E T U { mem := mem, ctx := ctx, stack := fr₂ :: rest₂ } := by
    intro mem ctx fr₂ rest₁ rest₂ vs s₁' b hrest hret
    cases hrest with
    | nil => cases hret
    | @cons _ fr0 fr0₂ rest₁' rest₂' hcf hrr =>
        dsimp only at hret ⊢
        cases hcf with
        | other hne =>
            cases hbp : bindParams fr0.env fr0.dsts vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                refine ⟨_, rfl, ⟨rfl, rfl, .cons (.other hne) hrr⟩, ?_⟩
                simp only [unrollPot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                have hpeq : unrollFramePot fi cut K E T U { fr0 with env := ρ', dsts := [] } =
                    unrollFramePot fi cut K E T U fr0 := rfl
                omega
        | @outside b0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 hB0 hnn hnl hpos0 hdst houter =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨ρ₂', hbp2, houter'⟩ := houter.bindParams_same hbp
                rw [hdst rfl, hbp2]
                refine ⟨_, rfl, ⟨rfl, rfl, .cons (.outside hB0 hnn hnl hpos0 (fun hc => by cases hc) houter') hrr⟩, ?_⟩
                simp only [unrollPot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                have hpeq : unrollFramePot fi cut K E T U
                    { fn := fi, label := unrollRemapOrig h nodes leafExits nonLeafExits U b0, pos := pos0, env := ρ₂', dsts := [] } =
                    unrollFramePot fi cut K E T U
                    { fn := fi, label := unrollRemapOrig h nodes leafExits nonLeafExits U b0, pos := pos0, env := ρ₂, dsts := d₁ } := rfl
                rw [hpeq]
                omega
        | @loopNode b0 idx0 c0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 av0 hcU hidx0 hB0 hav0 hpos0 hcall0 hcopy =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨hposGt, hd2eq, hddefs, g0, as0, hcallAt⟩ := hcall0 rfl
                obtain ⟨ρ₂', hbp2, hcopy'⟩ := hcopy.bindParams_defs hddefs hbp
                rw [hd2eq, hbp2]
                have hposPred : pos0 - 1 < blk0.body.size := by omega
                have hposEq : pos0 - 1 + 1 = pos0 := by omega
                have hstEq : blk0.body[pos0 - 1]'hposPred = .call d₁ g0 as0 :=
                  (Array.getElem?_eq_some_iff.1 hcallAt).2
                have havStep : d₁.foldl (fun a x => a.insert x) (availAtPos av0 blk0.body (pos0 - 1)) =
                    availAtPos av0 blk0.body pos0 := by
                  rw [← hposEq, availAtPos_succ av0 blk0.body hposPred, hstEq]; rfl
                simp only [Bool.false_eq_true, ↓reduceIte] at hcopy'
                rw [havStep] at hcopy'
                refine ⟨_, rfl, ⟨rfl, rfl, .cons (.loopNode hcU hidx0 hB0 hav0 hpos0 (fun hc => by cases hc)
                  (by simpa using hcopy')) hrr⟩, ?_⟩
                simp only [unrollPot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                have hpeq : unrollFramePot fi cut K E T U
                    { fn := fi, label := if c0 = 0 then b0 else unrollCopyNodeBase h nodes leafExits nonLeafExits c0 + idx0,
                      pos := pos0, env := ρ₂', dsts := [] } =
                    unrollFramePot fi cut K E T U
                    { fn := fi, label := if c0 = 0 then b0 else unrollCopyNodeBase h nodes leafExits nonLeafExits c0 + idx0,
                      pos := pos0, env := ρ₂, dsts := d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c0) } := rfl
                rw [hpeq]
                omega
        | @leafExit b0 eidx0 c0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 av0 hcU heidx0 hB0 hav0 hpos0 hcall0 hcopy =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨hposGt, hd2eq, hddefs, g0, as0, hcallAt⟩ := hcall0 rfl
                obtain ⟨ρ₂', hbp2, hcopy'⟩ := hcopy.bindParams_defs hddefs hbp
                rw [hd2eq, hbp2]
                have hposPred : pos0 - 1 < blk0.body.size := by omega
                have hposEq : pos0 - 1 + 1 = pos0 := by omega
                have hstEq : blk0.body[pos0 - 1]'hposPred = .call d₁ g0 as0 :=
                  (Array.getElem?_eq_some_iff.1 hcallAt).2
                have havStep : d₁.foldl (fun a x => a.insert x) (availAtPos av0 blk0.body (pos0 - 1)) =
                    availAtPos av0 blk0.body pos0 := by
                  rw [← hposEq, availAtPos_succ av0 blk0.body hposPred, hstEq]; rfl
                simp only [Bool.false_eq_true, ↓reduceIte] at hcopy'
                rw [havStep] at hcopy'
                refine ⟨_, rfl, ⟨rfl, rfl, .cons (.leafExit hcU heidx0 hB0 hav0 hpos0 (fun hc => by cases hc)
                  (by simpa using hcopy')) hrr⟩, ?_⟩
                simp only [unrollPot, List.map_cons, List.sum_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                have hpeq : unrollFramePot fi cut K E T U
                    { fn := fi, label := if c0 = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U b0
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c0 + eidx0,
                      pos := pos0, env := ρ₂', dsts := [] } =
                    unrollFramePot fi cut K E T U
                    { fn := fi, label := if c0 = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U b0
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c0 + eidx0,
                      pos := pos0, env := ρ₂, dsts := d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c0) } := rfl
                rw [hpeq]
                omega
  -- Helper 2: outside block `takeEdge` matching in `F'`
  have outsideTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (u pos : Nat) (blk : Block)
      (ρ₁ ρ₂ : Env) (d₁ d₂ : List VReg) (rest₁ rest₂ : List Frame) (e : Edge) (s₁' : State) (b : Bool),
      F.blocks[u]? = some blk →
      u ∉ nodes → u ∉ leafExits →
      e ∈ blk.term.edges →
      LoopOuterRel clonedDefs off ρ₁ ρ₂ →
      (∀ a ∈ e.args, listLt off a.uses = true) →
      (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false) →
      UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap false rest₁ rest₂ →
      takeEdge F { mem := mem, ctx := ctx, stack := ⟨fi, u, pos, ρ₁, d₁⟩ :: rest₁ }
        ⟨fi, u, pos, ρ₁, d₁⟩ rest₁ ρ₁ e = .next s₁' b →
      ∃ s₂',
        takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ }
          ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ rest₂ ρ₂
          { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target } = .next s₂' b ∧
        UnrollStateRel F fi h nodes leafExits nonLeafExits U off availMap s₁' s₂' ∧
        b.toNat + unrollPot fi cut K E T U s₂' ≤
          U * b.toNat + unrollPot fi cut K E T U
            { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ } := by
    intro mem ctx u pos blk ρ₁ ρ₂ d₁ d₂ rest₁ rest₂ e s₁' b hB hun hul he houter heargs henc hrest hte
    have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
    obtain ⟨heNode, heLeaf⟩ := hf.outside_edges u huLt hun blk hB e he
    unfold takeEdge at hte
    cases hev : evalArgs ρ₁ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hftgt : F.blocks[e.target]? with
        | none => rw [hev, hftgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hftgt] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                have hev2 : evalArgs ρ₂ ({ e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }).args = some vs := by
                  dsimp only; rw [outer_evalArgs houter heargs henc, hev]
                have htgt2 : ∃ tgtB', F'.blocks[unrollRemapOrig h nodes leafExits nonLeafExits U e.target]? = some tgtB' ∧
                    tgtB'.params = tgtB.params := by
                  unfold unrollRemapOrig
                  by_cases hlt : (e.target : Nat) < unrollCut h nodes
                  · simp only [hlt, ↓reduceIte]
                    cases hns : (Src.NatSet.ofList nodes).contains e.target with
                    | true =>
                        exact ⟨_, buildUnrolled_blocks_prefix_node F h nodes leafExits nonLeafExits U off hcut_le hlt hns hftgt, rfl⟩
                    | false =>
                        exact ⟨_, buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off hlt hns hftgt, rfl⟩
                  · simp only [hlt, ↓reduceIte]
                    exact ⟨_, buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off (Nat.le_of_not_lt hlt) hftgt, rfl⟩
                obtain ⟨tgtB', htgt2', hpar2⟩ := htgt2
                have hchg : decide (unrollRemapOrig h nodes leafExits nonLeafExits U e.target ≤
                    unrollRemapOrig h nodes leafExits nonLeafExits U u) = decide (e.target ≤ u) :=
                  unrollRemapOrig_le_iff h nodes leafExits nonLeafExits U u e.target
                have hpot_step : ∀ ρ₂' d₂',
                    (decide (e.target ≤ u)).toNat +
                      unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂'⟩ ≤
                    U * (decide (e.target ≤ u)).toNat +
                      unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ := by
                  intro ρ₂' d₂'
                  by_cases hback : e.target ≤ u
                  · simp only [hback, decide_true, Bool.toNat_true]
                    have hp' := unrollFramePot_le fi cut K E T U
                      ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂'⟩
                    omega
                  · simp only [hback, decide_false, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                    by_cases hucut : u < unrollCut h nodes
                    · have hpu : unrollFramePot fi cut K E T U
                          ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ = U - 1 :=
                        unrollFramePot_lt_cut fi cut K E T U rfl (by
                          change unrollRemapOrig h nodes leafExits nonLeafExits U u < unrollCut h nodes
                          simp only [unrollRemapOrig, hucut, ↓reduceIte])
                      rw [hpu]; exact unrollFramePot_le ..
                    · have htge : cut ≤ e.target :=
                        Nat.le_trans (Nat.le_of_not_lt hucut) (Nat.le_of_lt (Nat.lt_of_not_ge hback))
                      have hpt : unrollFramePot fi cut K E T U
                          ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂'⟩ = 0 :=
                        unrollFramePot_suffix fi cut K E T U rfl (by
                          have hnl : ¬ e.target < unrollCut h nodes := Nat.not_lt_of_ge htge
                          simp only [unrollRemapOrig, hnl, ↓reduceIte]
                          have hde : cut + delta = cut + T + (U - 1) * (K + E + T) := hdelta_eq
                          rw [← hde]
                          exact Nat.add_le_add_right htge delta)
                      omega
                by_cases hth : e.target = h
                · -- Entering loop header `h` at copy `0`!
                  obtain ⟨hBlk, avH, hhB, havH, havHsub⟩ := hf.avail_h
                  obtain rfl : hBlk = tgtB := Option.some.inj (hhB.symm.trans (hth ▸ hftgt))
                  have hparDefs : ∀ d ∈ hBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_left _ (List.mem_of_getElem? hh0)) hhB).1
                  obtain ⟨ρ₂', hbp2, hcopy0⟩ := houter.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
                  have hbp2' : bindParams ρ₂ hBlk.params vs = some ρ₂' := by
                    have hmap : hBlk.params.map (loopMapReg clonedDefs off 0) = hBlk.params := by
                      induction hBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                    rwa [hmap] at hbp2
                  have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ }
                      ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ rest₂ ρ₂
                      { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂⟩ :: rest₂ }
                        (decide (e.target ≤ u)) := by
                    rw [← hchg]; exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2')
                  have hcopyH : LoopCopyRel clonedDefs off 0 (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
                    hcopy0.mono fun x hx => by
                      rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
                  have hremH : unrollRemapOrig h nodes leafExits nonLeafExits U e.target = h := by
                    rw [hth]; simp only [unrollRemapOrig]; simp [show h < unrollCut h nodes from hh_lt_cut]
                  refine ⟨_, hte2, ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                  · rw [hremH, hth]
                    exact .loopNode (c := 0) (by omega) hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc)
                      (by simpa using hcopyH)
                  · simp only [unrollPot, List.map_cons, List.sum_cons]
                    have := hpot_step ρ₂' d₂; omega
                · by_cases htl : e.target ∈ leafExits
                  · -- Entering leaf exit at copy `0`!
                    obtain ⟨eidx, _, heidx⟩ := mem_listIndexOf htl
                    obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := heLeaf htl
                    obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                    have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                      (collectBlocksDefs_mem (List.mem_append_right _ htl) htB).1
                    obtain ⟨ρ₂', hbp2, hcopy0⟩ := houter.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
                    have hbp2' : bindParams ρ₂ tBlk.params vs = some ρ₂' := by
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      rwa [hmap] at hbp2
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ }
                        ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ rest₂ ρ₂
                        { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂⟩ :: rest₂ }
                          (decide (e.target ≤ u)) := by
                      rw [← hchg]; exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2')
                    have hcopyT : LoopCopyRel clonedDefs off 0 (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                      hcopy0.mono fun x hx => by
                        rw [natSet_contains_foldl_insert]; exact .inl (havTsub x hx)
                    refine ⟨_, hte2, ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                    · exact .leafExit (c := 0) (by omega) heidx htB havT (Nat.zero_le _) (fun hc => by cases hc)
                        (by simpa using hcopyT)
                    · simp only [unrollPot, List.map_cons, List.sum_cons]
                      have := hpot_step ρ₂' d₂; omega
                  · -- Staying in outside non-leaf block!
                    have htnn : e.target ∉ nodes := by
                      rcases heNode with hnn | heq
                      · exact hnn
                      · exact absurd heq hth
                    obtain ⟨ρ₂', hbp2, houter'⟩ := houter.bindParams_same hbp
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ }
                        ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ rest₂ ρ₂
                        { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂⟩ :: rest₂ }
                          (decide (e.target ≤ u)) := by
                      rw [← hchg]; exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2)
                    refine ⟨_, hte2, ⟨rfl, rfl, .cons (.outside hftgt htnn htl (Nat.zero_le _) (fun hc => by cases hc) houter') hrest⟩, ?_⟩
                    simp only [unrollPot, List.map_cons, List.sum_cons]
                    have := hpot_step ρ₂' d₂; omega
  -- Helper 3: loop-node `takeEdge` matching in `F'` (covers all 4 edge targets: `h`, `nodes`, `leafExits`, `nonLeafExits`!)
  have loopNodeTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (u idx c pos : Nat) (blk : Block) (av2 : Src.NatSet)
      (ρ₁ ρ₂ ρ₂fr : Env) (d₁ d₂ : List VReg) (rest₁ rest₂ : List Frame) (e : Edge) (s₁' : State) (b : Bool),
      c < U →
      nodes[idx]? = some u →
      F.blocks[u]? = some blk →
      e ∈ blk.term.edges →
      (∀ e' ∈ blk.term.edges, ((e'.target ∈ nodes ∧ e'.target ≠ h) ∨ e'.target ∈ leafExits) →
        ∃ tBlk avT, F.blocks[e'.target]? = some tBlk ∧ availMap[e'.target]? = some avT ∧
          ∀ x, avT.contains x = true → av2.contains x = true ∨ x ∈ tBlk.params) →
      LoopCopyRel clonedDefs off c av2 ρ₁ ρ₂ →
      (∀ a ∈ e.args, listLt off a.uses = true) →
      (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false ∨ av2.contains x = true) →
      UnrollStackRel F fi h nodes leafExits nonLeafExits U off availMap false rest₁ rest₂ →
      takeEdge F { mem := mem, ctx := ctx, stack := ⟨fi, u, pos, ρ₁, d₁⟩ :: rest₁ }
        ⟨fi, u, pos, ρ₁, d₁⟩ rest₁ ρ₁ e = .next s₁' b →
      let qLbl := if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx
      let qEdge : Edge := { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                            args := e.args.map (loopMapArg clonedDefs off c) }
      ∃ cStep s₂',
        step q { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ } =
          takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ }
            ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ rest₂ ρ₂ qEdge →
        Sem.Star (semStep q) { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ } cStep s₂' ∧
        UnrollStateRel F fi h nodes leafExits nonLeafExits U off availMap s₁' s₂' ∧
        b.toNat + unrollPot fi cut K E T U s₂' ≤
          U * cStep + unrollPot fi cut K E T U { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ } := by
    intro mem ctx u idx c pos blk av2 ρ₁ ρ₂ ρ₂fr d₁ d₂ rest₁ rest₂ e s₁' b hcU hidx hB he havEdges hcopy heargs heav hrest hte
    have huMem : u ∈ nodes := List.mem_of_getElem? hidx
    have huCut : u < cut := hf.node_lt_cut huMem
    have hidxLt : idx < K := (List.getElem?_eq_some_iff.1 hidx).1
    have hpot_cur : unrollFramePot fi cut K E T U
        ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ = U - 1 - c := by
      by_cases hc0 : c = 0
      · subst hc0; simp only [↓reduceIte, Nat.sub_zero]
        exact unrollFramePot_lt_cut fi cut K E T U rfl huCut
      · simp only [hc0, ↓reduceIte]
        exact unrollFramePot_copy_node fi cut K E T U c idx rfl (by omega) hcU hidxLt rfl
    unfold takeEdge at hte
    cases hev : evalArgs ρ₁ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hftgt : F.blocks[e.target]? with
        | none => rw [hev, hftgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hftgt] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                have hev2 : evalArgs ρ₂ (e.args.map (loopMapArg clonedDefs off c)) = some vs := by
                  rw [loopMapArgs_eval hcopy heargs heav, hev]
                rcases hf.node_edges u huMem blk hB e he with hth | ⟨htn, hult⟩ | ⟨htl, hult⟩ | htnl
                · -- Case A: Back-edge `e.target = h`!
                  have hh_le_u : h ≤ u := hf.h_le_node huMem
                  have hbp1 : decide (e.target ≤ u) = true := by rw [hth]; simp [hh_le_u]
                  obtain ⟨hBlk, avH, hhB, havH, havHsub⟩ := hf.avail_h
                  obtain rfl : hBlk = tgtB := Option.some.inj (hhB.symm.trans (hth ▸ hftgt))
                  have hparDefs : ∀ d ∈ hBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_left _ (List.mem_of_getElem? hh0)) hhB).1
                  by_cases hcnext : c + 1 < U
                  · -- Jump forward to copy `c + 1` header `copyNodeBase (c + 1)` (`c_q = 0`, pot drops `U-1-c -> U-1-(c+1)`)!
                    have hrem : unrollRemapTarget h nodes leafExits nonLeafExits U c e.target =
                        unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1) := by
                      unfold unrollRemapTarget; simp [hth, hcnext]
                    have htgt2 := buildUnrolled_blocks_copy_node F h nodes leafExits nonLeafExits U off
                      (c := c + 1) (idx := 0) (by omega) hcnext hh0 hhB
                    simp only [Nat.add_zero] at htgt2
                    obtain ⟨ρ₂', hbp2, hcopyN⟩ := hcopy.1.toCopyLeaf (c := c + 1) |>.bindParams_defs hparDefs hbp
                    have hcopyH : LoopCopyRel clonedDefs off (c + 1) (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
                      hcopyN.mono fun x hx => by
                        rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
                    have hfwd : decide (unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1) ≤
                        if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx) = false := by
                      by_cases hc0 : c = 0
                      · subst hc0; simp only [↓reduceIte, decide_eq_false_iff_not]
                        simp only [unrollCopyNodeBase]; omega
                      · simp only [hc0, ↓reduceIte, decide_eq_false_iff_not, unrollCopyNodeBase, Nat.add_sub_cancel]
                        have hmul : (c - 1 + 1) * unrollStride nodes leafExits nonLeafExits =
                            c * unrollStride nodes leafExits nonLeafExits := by congr 1; omega
                        rw [Nat.add_mul, Nat.one_mul] at hmul
                        simp only [unrollStride] at hmul ⊢; omega
                    refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1), 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                        ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                        { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                          args := e.args.map (loopMapArg clonedDefs off c) } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1), 0, ρ₂', d₂⟩ :: rest₂ } false := by
                      rw [hrem, ← hfwd]; exact takeEdge_ok hev2 htgt2 hbp2
                    refine ⟨star_of_step (hst.trans hte2), ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                    · have hne0 : c + 1 ≠ 0 := by omega
                      rw [hth]
                      simpa [hne0] using UnrollFrameRel.loopNode (F := F) (fi := fi) (h := h)
                        (nodes := nodes) (leafExits := leafExits) (nonLeafExits := nonLeafExits)
                        (U := U) (off := off) (availMap := availMap) (isTop := true)
                        (b := h) (idx := 0) (c := c + 1) (pos := 0) (d₁ := d₁) (d₂ := d₂)
                        hcnext hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyH)
                    · simp only [unrollPot, List.map_cons, List.sum_cons, hbp1, Bool.toNat_true, Nat.mul_zero, Nat.zero_add, hpot_cur]
                      have hpnew : unrollFramePot fi cut K E T U
                          ⟨fi, unrollCopyNodeBase h nodes leafExits nonLeafExits (c + 1), 0, ρ₂', d₂⟩ = U - 1 - (c + 1) :=
                        unrollFramePot_copy_node fi cut K E T U (c + 1) 0 rfl (by omega) hcnext hKpos (by simp [unrollCopyNodeBase, cut, K, E, T, unrollStride])
                      omega
                  · -- Wrap around from copy `c = U - 1 ≥ 1` back to copy `0` header `h` (`c_q = 1`, pot `0 -> U - 1`)!
                    have hc_eq : c = U - 1 := by omega
                    have hc_ne0 : c ≠ 0 := by omega
                    have hrem : unrollRemapTarget h nodes leafExits nonLeafExits U c e.target = h := by
                      unfold unrollRemapTarget; simp [hth, hcnext]
                    have htgt2 := buildUnrolled_blocks_prefix_node F h nodes leafExits nonLeafExits U off
                      hcut_le hh_lt_cut ((natSet_ofList_contains nodes h).2 (List.mem_of_getElem? hh0)) hhB
                    obtain ⟨ρ₂', hbp2, hcopy0⟩ := hcopy.1.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
                    have hbp2' : bindParams ρ₂ hBlk.params vs = some ρ₂' := by
                      have hmap : hBlk.params.map (loopMapReg clonedDefs off 0) = hBlk.params := by
                        induction hBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      rwa [hmap] at hbp2
                    have hcopyH : LoopCopyRel clonedDefs off 0 (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
                      hcopy0.mono fun x hx => by
                        rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
                    have hback : decide (h ≤ if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx) = true := by
                      simp only [hc_ne0, ↓reduceIte, decide_eq_true_eq, unrollCopyNodeBase]; omega
                    refine ⟨1, { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                        ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                        { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                          args := e.args.map (loopMapArg clonedDefs off c) } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ } true := by
                      rw [hrem, ← hback]; exact takeEdge_ok hev2 htgt2 hbp2'
                    refine ⟨star_of_step (hst.trans hte2), ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                    · rw [hth]
                      simpa using UnrollFrameRel.loopNode (F := F) (fi := fi) (h := h)
                        (nodes := nodes) (leafExits := leafExits) (nonLeafExits := nonLeafExits)
                        (U := U) (off := off) (availMap := availMap) (isTop := true)
                        (b := h) (idx := 0) (c := 0) (pos := 0) (d₁ := d₁) (d₂ := d₂)
                        (by omega) hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyH)
                    · simp only [unrollPot, List.map_cons, List.sum_cons, hbp1, Bool.toNat_true, Nat.mul_one, hpot_cur]
                      have hpnew : unrollFramePot fi cut K E T U ⟨fi, h, 0, ρ₂', d₂⟩ = U - 1 :=
                        unrollFramePot_lt_cut fi cut K E T U rfl hh_lt_cut
                      omega
                · -- Case B: Strictly forward internal edge `e.target ∈ nodes ∧ u < e.target`!
                  have ht_ne_h : e.target ≠ h := Nat.ne_of_gt (Nat.lt_of_le_of_lt (hf.h_le_node huMem) hult)
                  have hbp0 : decide (e.target ≤ u) = false := decide_eq_false (Nat.not_le.2 hult)
                  obtain ⟨idx', hidx'Of, hidx'⟩ := mem_listIndexOf htn
                  have hidx'Lt : idx' < K := (List.getElem?_eq_some_iff.1 hidx').1
                  have hidx_lt : idx < idx' := by
                    by_cases hle : idx' ≤ idx
                    · cases Nat.eq_or_lt_of_le hle with
                      | inl heq => subst heq; rw [hidx] at hidx'; cases hidx'; omega
                      | inr hlt => have := isStrictlySorted_lt hf.nodes_sorted hidx' hidx hlt; omega
                    · omega
                  have htCut : e.target < cut := hf.node_lt_cut htn
                  obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := havEdges e he (.inl ⟨htn, ht_ne_h⟩)
                  obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                  have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_left _ htn) htB).1
                  obtain ⟨ρ₂', hbp2, hcopy1⟩ := hcopy.bindParams_defs hparDefs hbp
                  have hcopyT : LoopCopyRel clonedDefs off c (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                    hcopy1.mono fun x hx => by
                      rw [natSet_contains_foldl_insert]
                      rcases havTsub x hx with h1 | h2
                      · exact .inr h1
                      · exact .inl h2
                  have hrem : unrollRemapTarget h nodes leafExits nonLeafExits U c e.target =
                      if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx' := by
                    unfold unrollRemapTarget
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hmemB : (Src.NatSet.ofList nodes).contains e.target = true := (natSet_ofList_contains nodes e.target).2 htn
                    simp only [hneB, Bool.false_eq_true, ↓reduceIte, hmemB, hidx'Of]
                    by_cases hc0 : c = 0 <;> simp [hc0]
                  have htgt2 : ∃ B', F'.blocks[if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx']? = some B' ∧
                      B'.params = tBlk.params.map (loopMapReg clonedDefs off c) := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte]
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      exact ⟨_, buildUnrolled_blocks_prefix_node F h nodes leafExits nonLeafExits U off
                        hcut_le htCut ((natSet_ofList_contains nodes e.target).2 htn) htB, hmap.symm⟩
                    · simp only [hc0, ↓reduceIte]
                      exact ⟨_, buildUnrolled_blocks_copy_node F h nodes leafExits nonLeafExits U off
                        (by omega) hcU hidx' htB, rfl⟩
                  obtain ⟨B', hB', hpar'⟩ := htgt2
                  have hfwd : decide ((if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx') ≤
                      (if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx)) = false := by
                    by_cases hc0 : c = 0 <;> simp [hc0] <;> omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx', 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx', 0, ρ₂', d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd]; exact takeEdge_ok hev2 hB' (by rw [hpar']; exact hbp2)
                  refine ⟨star_of_step (hst.trans hte2), ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                  · exact .loopNode hcU hidx' htB havT (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyT)
                  · simp only [unrollPot, List.map_cons, List.sum_cons, hbp0, Bool.toNat_false, Nat.zero_add, Nat.mul_zero, hpot_cur]
                    have hpnew : unrollFramePot fi cut K E T U
                        ⟨fi, if c = 0 then e.target else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx', 0, ρ₂', d₂⟩ = U - 1 - c := by
                      by_cases hc0 : c = 0
                      · subst hc0; simp only [↓reduceIte, Nat.sub_zero]; exact unrollFramePot_lt_cut fi cut K E T U rfl htCut
                      · simp only [hc0, ↓reduceIte]; exact unrollFramePot_copy_node fi cut K E T U c idx' rfl (by omega) hcU hidx'Lt rfl
                    omega
                · -- Case C: Forward exit to `e.target ∈ leafExits` (`u < e.target`)!
                  have htnn : e.target ∉ nodes := (hf.leaf_ok e.target htl).2.2
                  have ht_ne_h : e.target ≠ h := fun heq => htnn (heq ▸ List.mem_of_getElem? hh0)
                  have hbp0 : decide (e.target ≤ u) = false := by simp; omega
                  obtain ⟨eidx, heidxOf, heidx⟩ := mem_listIndexOf htl
                  have heidxLt : eidx < E := (List.getElem?_eq_some_iff.1 heidx).1
                  obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := havEdges e he (.inr htl)
                  obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                  have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_right _ htl) htB).1
                  obtain ⟨ρ₂', hbp2, hcopy1⟩ := hcopy.bindParams_defs hparDefs hbp
                  have hcopyT : LoopCopyRel clonedDefs off c (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                    hcopy1.mono fun x hx => by
                      rw [natSet_contains_foldl_insert]
                      rcases havTsub x hx with h1 | h2
                      · exact .inr h1
                      · exact .inl h2
                  have hrem : unrollRemapTarget h nodes leafExits nonLeafExits U c e.target =
                      if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U e.target
                      else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx := by
                    unfold unrollRemapTarget
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hnnB : (Src.NatSet.ofList nodes).contains e.target = false := (natSet_ofList_contains_false nodes e.target).2 htnn
                    simp only [hneB, hnnB, Bool.false_eq_true, ↓reduceIte, heidxOf]
                    by_cases hc0 : c = 0 <;> simp [hc0]
                  have htgt2 : ∃ B', F'.blocks[if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U e.target
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx]? = some B' ∧
                      B'.params = tBlk.params.map (loopMapReg clonedDefs off c) := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte]
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      unfold unrollRemapOrig
                      by_cases hlt : e.target < unrollCut h nodes
                      · simp only [hlt, ↓reduceIte]
                        exact ⟨_, buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off
                          hlt ((natSet_ofList_contains_false nodes e.target).2 htnn) htB, hmap.symm⟩
                      · simp only [hlt, ↓reduceIte]
                        exact ⟨_, buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off
                          (Nat.le_of_not_lt hlt) htB, hmap.symm⟩
                    · simp only [hc0, ↓reduceIte]
                      exact ⟨_, buildUnrolled_blocks_copy_exit F h nodes leafExits nonLeafExits U off
                        (by omega) hcU heidx htB, rfl⟩
                  obtain ⟨B', hB', hpar'⟩ := htgt2
                  have hfwd : decide ((if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U e.target
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx) ≤
                      (if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx)) = false := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte, decide_eq_false_iff_not, unrollRemapOrig]
                      split <;> omega
                    · simp only [hc0, ↓reduceIte, decide_eq_false_iff_not, unrollCopyExitBase, unrollCopyNodeBase]
                      omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U e.target
                          else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U e.target
                          else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx, 0, ρ₂', d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd]; exact takeEdge_ok hev2 hB' (by rw [hpar']; exact hbp2)
                  refine ⟨star_of_step (hst.trans hte2), ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                  · exact .leafExit hcU heidx htB havT (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyT)
                  · simp only [unrollPot, List.map_cons, List.sum_cons, hbp0, Bool.toNat_false, Nat.zero_add, Nat.mul_zero, hpot_cur]
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte, Nat.sub_zero]
                      have := unrollFramePot_le fi cut K E T U
                        ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U e.target, 0, ρ₂', d₂⟩
                      omega
                    · simp only [hc0, ↓reduceIte]
                      have hpnew : unrollFramePot fi cut K E T U
                          ⟨fi, unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx, 0, ρ₂', d₂⟩ = 0 :=
                        unrollFramePot_copy_exit fi cut K E T U c eidx rfl (by omega) hcU heidxLt
                          (by simp [unrollCopyExitBase, unrollCopyNodeBase, cut, K, E, T, unrollStride])
                      omega
                · -- Case D: Forward exit to `e.target ∈ nonLeafExits` via 0-stmt trampoline (2 steps, `c = 0`, pot → `0`)!
                  obtain ⟨htCutGe, htLtF, htnn, htNotLeaf⟩ := hf.nonLeaf_ok e.target htnl
                  have htCutGe' : cut ≤ e.target := htCutGe
                  have ht_ne_h : e.target ≠ h := Nat.ne_of_gt (Nat.lt_of_lt_of_le hh_lt_cut htCutGe')
                  have hbp0 : decide (e.target ≤ u) = false := decide_eq_false (Nat.not_le.2 (Nat.lt_of_lt_of_le huCut htCutGe'))
                  obtain ⟨tidx, htidxOf, htidx⟩ := mem_listIndexOf htnl
                  have htidxLt : tidx < T := (List.getElem?_eq_some_iff.1 htidx).1
                  have hrem : unrollRemapTarget h nodes leafExits nonLeafExits U c e.target =
                      unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx := by
                    unfold unrollRemapTarget
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hnnB : (Src.NatSet.ofList nodes).contains e.target = false := (natSet_ofList_contains_false nodes e.target).2 htnn
                    have hnlNone : listIndexOf leafExits e.target = none := listIndexOf_none_of_not_mem htNotLeaf
                    simp only [hneB, hnnB, Bool.false_eq_true, ↓reduceIte, hnlNone, htidxOf]
                  have htrampBlk : ∃ regStart cold, off ≤ regStart ∧
                      F'.blocks[unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx]? = some
                        { params := (List.range tgtB.params.length).map (regStart + ·)
                          body := #[]
                          term := .jump { target := e.target + delta, args := ((List.range tgtB.params.length).map (regStart + ·)).map .v }
                          cold := cold } := by
                    by_cases hc0 : c = 0
                    · subst hc0
                      have hb := buildUnrolled_blocks_copy0_tramp F h nodes leafExits nonLeafExits U off htidx
                      have hregGe : off ≤ U * off + tidx * off :=
                        Nat.le_trans (Nat.le_mul_of_pos_left off (by omega)) (Nat.le_add_right _ _)
                      refine ⟨U * off + tidx * off, (F.blocks[e.target]?.map (·.cold)).getD false, hregGe, ?_⟩
                      simpa [unrollCopyTrampBase, hftgt, delta, F'] using hb
                    · have hb := buildUnrolled_blocks_copy_tramp F h nodes leafExits nonLeafExits U off (by omega) hcU htidx
                      have hregGe : off ≤ U * off + c * (nonLeafExits.length * off) + tidx * off :=
                        Nat.le_trans (Nat.le_mul_of_pos_left off (by omega))
                          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
                      refine ⟨U * off + c * (nonLeafExits.length * off) + tidx * off,
                        (F.blocks[e.target]?.map (·.cold)).getD false, hregGe, ?_⟩
                      simpa [hftgt, delta, F'] using hb
                  obtain ⟨regStart, cold, hregGe, htramp⟩ := htrampBlk
                  have hsuf := buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off htCutGe hftgt
                  have htrampLt : unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx < e.target + delta := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [unrollCopyTrampBase, BEq.rfl, ↓reduceIte, delta, unrollDelta]; omega
                    · have hcne : (c == 0) = false := beq_false_of_ne hc0
                      simp only [unrollCopyTrampBase, hcne, Bool.false_eq_true, ↓reduceIte, unrollCopyNodeBase, delta, unrollDelta]
                      have hmul : (c - 1 + 1) * unrollStride nodes leafExits nonLeafExits ≤
                          (U - 1) * unrollStride nodes leafExits nonLeafExits := Nat.mul_le_mul_right _ (by omega)
                      rw [Nat.add_mul, Nat.one_mul] at hmul
                      simp only [unrollStride] at hmul ⊢; omega
                  obtain ⟨ρ₂t, ρ₂', hbpt, hstepTramp, houter'⟩ := step_trampoline (q := q) (F' := F')
                    (fi := fi) (trampLbl := unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx)
                    (x := e.target) (delta := delta) (regStart := regStart) (nParams := tgtB.params.length)
                    (fr₂ := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩)
                    (rest₂ := rest₂) (tgtBlk := tgtB) (cold := cold)
                    hqfi rfl htramp hsuf rfl rfl hregGe htrampLt hcopy.1 hbp
                  have hfwd1 : decide (unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx ≤
                      (if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx)) = false := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte, unrollCopyTrampBase, BEq.rfl, decide_eq_false_iff_not]; omega
                    · have hcne : (c == 0) = false := beq_false_of_ne hc0
                      simp only [hc0, hcne, Bool.false_eq_true, ↓reduceIte, unrollCopyTrampBase,
                        unrollCopyNodeBase, decide_eq_false_iff_not]; omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, e.target + delta, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte1 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := unrollRemapTarget h nodes leafExits nonLeafExits U c e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, unrollCopyTrampBase h nodes leafExits nonLeafExits c + tidx, 0, ρ₂t, d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd1]; exact takeEdge_ok hev2 htramp hbpt
                  have hstar : Sem.Star (semStep q)
                      { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      0 { mem := mem, ctx := ctx, stack := ⟨fi, e.target + delta, 0, ρ₂', d₂⟩ :: rest₂ } :=
                    Sem.Star.free (by rw [semStep_next]; exact hst.trans hte1) (star_of_step hstepTramp)
                  have hremOrig : unrollRemapOrig h nodes leafExits nonLeafExits U e.target = e.target + delta := by
                    have hnl : ¬ e.target < unrollCut h nodes := Nat.not_lt_of_ge htCutGe
                    simp [unrollRemapOrig, hnl, delta]
                  refine ⟨hstar, ⟨rfl, rfl, .cons ?_ hrest⟩, ?_⟩
                  · rw [← hremOrig]
                    exact .outside hftgt htnn htNotLeaf (Nat.zero_le _) (fun hc => by cases hc) houter'
                  · simp only [unrollPot, List.map_cons, List.sum_cons, hbp0, Bool.toNat_false, Nat.zero_add, Nat.mul_zero, hpot_cur]
                    have hpnew : unrollFramePot fi cut K E T U ⟨fi, e.target + delta, 0, ρ₂', d₂⟩ = 0 :=
                      unrollFramePot_suffix fi cut K E T U rfl (by
                        have hde : cut + delta = cut + T + (U - 1) * (K + E + T) := hdelta_eq
                        rw [← hde]
                        exact Nat.add_le_add_right htCutGe delta)
                    omega
  -- Construct `PotentialForward`
  refine ⟨by omega, ?_, ?_⟩
  · -- `next`
    intro s₁ s₁' s₂ b hrel hstep1
    rw [semStep_next] at hstep1
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq
    obtain rfl : ctx₁ = ctx₂ := hctx_eq
    cases hstack with
    | nil => simp [step] at hstep1
    | @cons _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        cases hfr with
        | other hfn =>
            unfold step at hstep1; dsimp only at hstep1
            cases hG : p.funcs[fr₁.fn]? with
            | none => rw [hG] at hstep1; cases hstep1
            | some G =>
                have hqG : q.funcs[fr₁.fn]? = some G := by
                  rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hG]
                rw [hG] at hstep1; dsimp only at hstep1
                cases hB : G.blocks[fr₁.label]? with
                | none => rw [hB] at hstep1; cases hstep1
                | some B =>
                    rw [hB] at hstep1; dsimp only at hstep1
                    have hp0 : unrollFramePot fi cut K E T U fr₁ = 0 := unrollFramePot_ne fi cut K E T U hfn
                    by_cases hltB : fr₁.pos < B.body.size
                    · simp only [hltB, ↓reduceDIte] at hstep1
                      cases hs : B.body[fr₁.pos]'hltB with
                      | call rs' g' as' =>
                          rw [hs] at hstep1; dsimp only at hstep1
                          cases hev : evalArgs fr₁.env as' with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g' vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                                  have hstep2 := step_call (p := q) (F := G) (B := B) (fr := fr₁) (rest := rest₂)
                                    (mem := mem₁) (ctx := ctx₁) hqG hB hltB hs hev hent2
                                  refine .inl ⟨1, _, star_of_step hstep2,
                                    ⟨rfl, rfl, .cons hcalRel (.cons (.other hfn) hrest)⟩, ?_⟩
                                  rw [unrollPot_cons, unrollPot_cons, List.map_cons, List.sum_cons, Bool.toNat_true, Nat.mul_one, hp0]
                                  have h1 := unrollFramePot_le fi cut K E T U calFr₂
                                  have h2 : unrollFramePot fi cut K E T U { fr₁ with pos := fr₁.pos + 1, dsts := rs' } = 0 :=
                                    unrollFramePot_ne fi cut K E T U hfn
                                  rw [h2]; dsimp only [cut, K, E, T] at h1; omega
                      | assign _ _ | limb _ _ _ | store _ _ _ =>
                          rw [hs] at hstep1; dsimp only at hstep1
                          cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                          | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                          | some p' =>
                              rcases p' with ⟨ρ₁', mem₁'⟩
                              have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                              simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                              have hnc : (B.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                              have hstep2 := step_stmt (p := q) (F := G) (B := B) (fr := fr₁) (rest := rest₂)
                                (mem := mem₁) (ctx := ctx₁) hqG hB hltB rfl hnc hx'
                              refine .inl ⟨0, _, star_of_step hstep2, ⟨rfl, rfl, .cons (.other hfn) hrest⟩, ?_⟩
                              rw [unrollPot_cons, unrollPot_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero, hp0]
                              have h2 : unrollFramePot fi cut K E T U { fr₁ with pos := fr₁.pos + 1, env := ρ₁' } = 0 :=
                                unrollFramePot_ne fi cut K E T U hfn
                              rw [h2]; omega
                    · simp only [hltB, ↓reduceDIte] at hstep1
                      have hstep2_unfold := step_term_ge (p := q) (F := G) (B := B) (mem := mem₁) (ctx := ctx₁) (fr := fr₁) (rest := rest₂) hqG hB hltB
                      have sameEdge : ∀ (ρ : Env) (e : Edge),
                          takeEdge G { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ e = .next s₁' b →
                          ∃ s₂', takeEdge G { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ e = .next s₂' b ∧
                            UnrollStateRel F fi h nodes leafExits nonLeafExits U off availMap s₁' s₂' ∧
                            b.toNat + unrollPot fi cut K E T U s₂' ≤
                              U * b.toNat + unrollPot fi cut K E T U { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } := by
                        intro ρ e hte
                        unfold takeEdge at hte
                        cases hev : evalArgs ρ e.args with
                        | none => rw [hev] at hte; cases hte
                        | some vs =>
                            cases htgt : G.blocks[e.target]? with
                            | none => rw [hev, htgt] at hte; cases hte
                            | some tb =>
                                rw [hev, htgt] at hte; dsimp only at hte
                                cases hbp : bindParams ρ tb.params vs with
                                | none => rw [hbp] at hte; cases hte
                                | some ρ' =>
                                    rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                                    refine ⟨_, takeEdge_ok hev htgt hbp, ⟨rfl, rfl, .cons (.other hfn) hrest⟩, ?_⟩
                                    rw [unrollPot_cons, unrollPot_cons, hp0]
                                    have h2 : unrollFramePot fi cut K E T U { fr₁ with label := e.target, pos := 0, env := ρ' } = 0 :=
                                      unrollFramePot_ne fi cut K E T U hfn
                                    rw [h2]
                                    cases decide (e.target ≤ fr₁.label) <;> simp <;> omega
                      cases ht : B.term with
                      | jump e =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameEdge fr₁.env e hstep1
                          exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | br c w a b' t f =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1 hstep2_unfold
                                  obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameEdge fr₁.env (if c.holds w va vb then t else f) hstep1
                                  exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | brOvf o x a b' ok ovf =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1 hstep2_unfold
                                  obtain ⟨s₂', hte2, hrel', hpot'⟩ := sameEdge (fr₁.env.insert x (o.eval va vb).1)
                                    (if (o.eval va vb).2 then ovf else ok) hstep1
                                  exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                      | ret ras =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases hev : evalArgs fr₁.env ras with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1 hstep2_unfold; dsimp only at hstep2_unfold
                              obtain ⟨s₂', hret2, hrel', hpot'⟩ := matchRet mem₁ ctx₁ fr₁ rest₁ rest₂ vs s₁' b hrest hstep1
                              exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), hrel', hpot'⟩
                      | tail g tas =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases hev : evalArgs fr₁.env tas with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                                  simp only [hev, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                                  refine .inl ⟨1, _, star_of_step hstep2_unfold, ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                                  rw [unrollPot_cons, unrollPot_cons, Bool.toNat_true, Nat.mul_one, hp0]
                                  have h1 := unrollFramePot_le fi cut K E T U calFr₂
                                  dsimp only [cut, K, E, T] at h1; omega
                      | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @outside u pos ρ₁ ρ₂ d₁ d₂ blk hB hun hul hposLe _ houter =>
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
            obtain ⟨_, hstLt, htUsesLt, _, heUsesLt⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨hstNc, htNc, heNc⟩ := hf.outside_no_cloned u huLt hun hul blk hB
            have hB2 : F'.blocks[unrollRemapOrig h nodes leafExits nonLeafExits U u]? =
                some { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) } := by
              unfold unrollRemapOrig
              by_cases hlt : u < unrollCut h nodes
              · simp only [hlt, ↓reduceIte]
                exact buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off
                  hlt ((natSet_ofList_contains_false nodes u).2 hun) hB
              · simp only [hlt, ↓reduceIte]
                exact buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off (Nat.le_of_not_lt hlt) hB
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuNc : ∀ x ∈ (blk.body[pos]'hltB).uses, clonedDefs.contains x = false := hstNc _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuNc; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ as' = some vs := by
                            rw [outer_evalArgs houter (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          have hstep2 := step_call (p := q) (F := F')
                            (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                              { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) })
                            (fr := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩)
                            (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqfi hB2 hltB hs hev2 hent2
                          refine .inl ⟨1, _, star_of_step hstep2,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.outside hB hun hul (by omega) (fun _ => rfl) houter) hrest)⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, List.map_cons, List.sum_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          have h2 : unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos + 1, ρ₂, rs'⟩ =
                              unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ := rfl
                          dsimp only [cut, K, E, T] at h1 h2; rw [h2]; omega
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, houter'⟩ := outer_stmt_exec houter hsuLt hsuNc hx'
                      have hnc : (blk.body[pos]'hltB).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F')
                        (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                          { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) })
                        (fr := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩)
                        (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqfi hB2 hltB rfl hnc hx2
                      refine .inl ⟨0, _, star_of_step hstep2,
                        ⟨rfl, rfl, .cons (.outside hB hun hul (by omega) (fun hc => by cases hc) houter') hrest⟩, ?_⟩
                      rw [unrollPot_cons, unrollPot_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                      have h2 : unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos + 1, ρ₂', d₂⟩ =
                          unrollFramePot fi cut K E T U ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ := rfl
                      dsimp only [cut, K, E, T] at h2; rw [h2]; omega
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hstep2_unfold := step_term_ge (p := q) (F := F')
                (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) })
                (mem := mem₁) (ctx := ctx₁)
                (fr := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩) (rest := rest₂)
                hqfi hB2 hltB
              dsimp only at hstep2_unfold
              rw [term_setEdges_map] at hstep2_unfold
              have hEdgeOk : ∀ e ∈ blk.term.edges,
                  (∀ a ∈ e.args, listLt off a.uses = true) ∧
                  (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false) := fun e he =>
                ⟨fun a ha => by simp only [listLt, List.all_eq_true, decide_eq_true_eq]; intro x hx; exact listLt_mem' heUsesLt (edgeUses_mem he ha hx),
                 fun a ha x hx => heNc x (edgeUses_mem he ha hx)⟩
              cases ht : blk.term with
              | jump e =>
                  rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                  have he : e ∈ blk.term.edges := by simp [ht, Term.edges]
                  obtain ⟨h1, h2⟩ := hEdgeOk e he
                  obtain ⟨s₂', hte2, hrel', hpot'⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ d₁ d₂ rest₁ rest₂ e s₁' b hB hun hul he houter h1 h2 hrest hstep1
                  exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | br c w a b' t f =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 : a.eval ρ₂ = some va := by rw [outer_arg_eval houter htUsesLt.1 (fun x hx => htNc x (by simp [Term.uses, hx])), ha]
                          have hb2 : b'.eval ρ₂ = some vb := by rw [outer_arg_eval houter htUsesLt.2 (fun x hx => htNc x (by simp [Term.uses, hx])), hb']
                          rw [ha2, hb2] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hcond : c.holds w va vb <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : f ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk f he
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ d₁ d₂ rest₁ rest₂ f s₁' b hB hun hul he houter h1 h2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                          · have he : t ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk t he
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ d₁ d₂ rest₁ rest₂ t s₁' b hB hun hul he houter h1 h2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | brOvf o x a b' ok ovf =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 : a.eval ρ₂ = some va := by rw [outer_arg_eval houter htUsesLt.1 (fun z hz => htNc z (by simp [Term.uses, hz])), ha]
                          have hb2 : b'.eval ρ₂ = some vb := by rw [outer_arg_eval houter htUsesLt.2 (fun z hz => htNc z (by simp [Term.uses, hz])), hb']
                          rw [ha2, hb2] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : ok ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk ok he
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert x (o.eval va vb).1) d₁ d₂ rest₁ rest₂ ok s₁' b
                              hB hun hul he (houter.insert_same x _) h1 h2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
                          · have he : ovf ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk ovf he
                            obtain ⟨s₂', hte2, hrel', hpot'⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert x (o.eval va vb).1) d₁ d₂ rest₁ rest₂ ovf s₁' b
                              hB hun hul he (houter.insert_same x _) h1 h2 hrest hstep1
                            exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), hrel', hpot'⟩
              | ret ras =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ ras = some vs := by
                        rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel', hpot'⟩ := matchRet mem₁ ctx₁
                        ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), hrel', hpot'⟩
              | tail g tas =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ tas = some vs := by
                            rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          simp only [hev2, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                          refine .inl ⟨1, _, star_of_step hstep2_unfold, ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          dsimp only [cut, K, E, T] at h1; omega
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @loopNode u idx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hcU hidx hB hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huMem : u ∈ nodes := List.mem_of_getElem? hidx
            have huCut : u < cut := hf.node_lt_cut huMem
            obtain ⟨_, hstLt, htUsesLt, _, heUsesLt⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨_, hbodyDefs, htDefs⟩ := collectBlocksDefs_mem (List.mem_append_left _ huMem) hB
            obtain ⟨av0', av1, hav0', hchk, htAv, heAv, havEdges⟩ := hf.avail_block u (List.mem_append_left _ huMem) blk hB
            rw [hav0] at hav0'; cases hav0'
            let qLbl := if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧
                ∃ (hsz : B2.body.size = blk.body.size),
                (∀ k (hk : k < blk.body.size), B2.body[k]'(hsz ▸ hk) = loopMapStmt clonedDefs off c (blk.body[k]'hk)) ∧
                B2.term = mapLoopTerm clonedDefs off c (unrollRemapTarget h nodes leafExits nonLeafExits U c) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have hblk := buildUnrolled_blocks_prefix_node F h nodes leafExits nonLeafExits U off
                  hcut_le huCut ((natSet_ofList_contains nodes u).2 huMem) hB
                refine ⟨{ blk with term := mapLoopTerm clonedDefs off 0 (unrollRemapTarget h nodes leafExits nonLeafExits U 0) blk.term },
                  by simpa [qLbl, clonedDefs, F'] using hblk, rfl, fun k hk => by simp [loopMapStmt_zero'], rfl⟩
              · have hblk := buildUnrolled_blocks_copy_node F h nodes leafExits nonLeafExits U off
                  (by omega) hcU hidx hB
                refine ⟨_, by simpa [qLbl, hc0] using hblk, by simp, fun k hk => by simp [clonedDefs], rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2body, hB2term⟩ := hB2
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hltB2 : pos < B2.body.size := hB2sz ▸ hltB
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuAv := checkStmtsAvail_at hchk hltB
              have hsdCl : ∀ d ∈ (blk.body[pos]'hltB).defs, clonedDefs.contains d = true := hbodyDefs _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuAv hsdCl; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (as'.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          have hs2 : B2.body[pos]'hltB2 = .call (rs'.map (loopMapReg clonedDefs off c)) g' (as'.map (loopMapArg clonedDefs off c)) := by
                            rw [hB2body pos hltB, hs]; rfl
                          have hstep2 := step_call (p := q) (F := F') (B := B2)
                            (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            hqfi hB2 hltB2 hs2 hev2 hent2
                          have hcallAt : blk.body[pos]? = some (.call rs' g' as') := by
                            rw [Array.getElem?_eq_getElem hltB, hs]
                          refine .inl ⟨1, _, star_of_step hstep2,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.loopNode hcU hidx hB hav0 (by omega)
                              (fun _ => ⟨by omega, rfl, hsdCl, g', as', by simpa using hcallAt⟩)
                              (by simpa using hcopy)) hrest)⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, List.map_cons, List.sum_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          have h2 : unrollFramePot fi cut K E T U ⟨fi, qLbl, pos + 1, ρ₂, rs'.map (loopMapReg clonedDefs off c)⟩ =
                              unrollFramePot fi cut K E T U ⟨fi, qLbl, pos, ρ₂, d₂⟩ := rfl
                          dsimp only [cut, K, E, T, qLbl] at h1 h2; rw [h2]; omega
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, hcopy'⟩ := loopMapStmt_exec hcopy hsuLt hsuAv hsdCl hx'
                      have hnc : (loopMapStmt clonedDefs off c (blk.body[pos]'hltB)).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F') (B := B2)
                        (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                        hqfi hB2 hltB2 (hB2body pos hltB) hnc hx2
                      rw [← availAtPos_succ av0 blk.body hltB] at hcopy'
                      refine .inl ⟨0, _, star_of_step hstep2,
                        ⟨rfl, rfl, .cons (.loopNode hcU hidx hB hav0 (by omega) (fun hc => by cases hc)
                          (by simpa using hcopy')) hrest⟩, ?_⟩
                      rw [unrollPot_cons, unrollPot_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                      have h2 : unrollFramePot fi cut K E T U ⟨fi, qLbl, pos + 1, ρ₂', d₂⟩ =
                          unrollFramePot fi cut K E T U ⟨fi, qLbl, pos, ρ₂, d₂⟩ := rfl
                      dsimp only [cut, K, E, T, qLbl] at h2; rw [h2]; omega
            · -- Terminator of loop node `u`!
              simp only [hltB, ↓reduceDIte] at hstep1
              have hposEq : pos = blk.body.size := by omega
              subst hposEq
              rw [checkStmtsAvail_end hchk] at hcopy
              have hltB2 : ¬ blk.body.size < B2.body.size := by omega
              have hstep2_unfold := step_term_ge (p := q) (F := F') (B := B2) (mem := mem₁) (ctx := ctx₁)
                (fr := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩) (rest := rest₂) hqfi hB2 hltB2
              dsimp only at hstep2_unfold
              rw [hB2term] at hstep2_unfold
              have hEdgeLt : ∀ e ∈ blk.term.edges, ∀ a ∈ e.args, listLt off a.uses = true :=
                fun e he a ha => by
                  simp only [listLt, List.all_eq_true, decide_eq_true_eq]
                  intro x hx; exact listLt_mem' heUsesLt (edgeUses_mem he ha hx)
              have hEdgeAv : ∀ e ∈ blk.term.edges, ∀ a ∈ e.args, ∀ x ∈ a.uses,
                  clonedDefs.contains x = false ∨ (blk.term.defs.foldl (fun a x => a.insert x) av1).contains x = true :=
                fun e he a ha x hx => heAv x (edgeUses_mem he ha hx)
              cases ht : blk.term with
              | jump e =>
                  rw [ht] at hstep1 hstep2_unfold; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  have he : e ∈ blk.term.edges := by simp [ht, Term.edges]
                  have hav2 : blk.term.defs.foldl (fun a x => a.insert x) av1 = av1 := by simp [ht, Term.defs]
                  obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                    (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ e s₁' b
                    hcU hidx hB he havEdges (by rw [hav2]; exact hcopy) (hEdgeLt e he) (hEdgeAv e he) hrest hstep1
                  exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | br cond w a b' t f =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  have hav2 : blk.term.defs.foldl (fun a x => a.insert x) av1 = av1 := by simp [ht, Term.defs]
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 := loopMapArg_eval hcopy htUsesLt.1 (fun x hx => htAv x (by simp [Term.uses, hx]))
                          have hb2 := loopMapArg_eval hcopy htUsesLt.2 (fun x hx => htAv x (by simp [Term.uses, hx]))
                          rw [ha2, hb2, ha, hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hcond : cond.holds w va vb <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : f ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ f s₁' b
                              hcU hidx hB he havEdges (by rw [hav2]; exact hcopy) (hEdgeLt f he) (hEdgeAv f he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : t ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ t s₁' b
                              hcU hidx hB he havEdges (by rw [hav2]; exact hcopy) (hEdgeLt t he) (hEdgeAv t he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | brOvf o x a b' ok ovf =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  have hxCl : clonedDefs.contains x = true := htDefs x (by simp [ht, Term.defs])
                  have hav2 : blk.term.defs.foldl (fun a z => a.insert z) av1 = av1.insert x := by simp [ht, Term.defs]
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 := loopMapArg_eval hcopy htUsesLt.1 (fun z hz => htAv z (by simp [Term.uses, hz]))
                          have hb2 := loopMapArg_eval hcopy htUsesLt.2 (fun z hz => htAv z (by simp [Term.uses, hz]))
                          rw [ha2, hb2, ha, hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          have hcopy' : LoopCopyRel clonedDefs off c (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) := by
                            rw [hav2]; exact hcopy.insert_def hxCl _
                          cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : ok ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) ρ₂
                              d₁ d₂ rest₁ rest₂ ok s₁' b hcU hidx hB he havEdges hcopy' (hEdgeLt ok he) (hEdgeAv ok he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : ovf ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) ρ₂
                              d₁ d₂ rest₁ rest₂ ovf s₁' b hcU hidx hB he havEdges hcopy' (hEdgeLt ovf he) (hEdgeAv ovf he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | ret ras =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                        rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel', hpot'⟩ := matchRet mem₁ ctx₁
                        ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), hrel', hpot'⟩
              | tail g tas =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (tas.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          simp only [hev2, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                          refine .inl ⟨1, _, star_of_step hstep2_unfold, ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          dsimp only [cut, K, E, T] at h1; omega
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @leafExit u eidx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hcU heidx hB hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huMem : u ∈ leafExits := List.mem_of_getElem? heidx
            have hun : u ∉ nodes := (hf.leaf_ok u huMem).2.2
            have hnoEdges : blk.term.edges = [] := hf.leaf_no_edges u huMem blk hB
            obtain ⟨_, hstLt, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨_, hbodyDefs, _⟩ := collectBlocksDefs_mem (List.mem_append_right _ huMem) hB
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_right _ huMem) blk hB
            rw [hav0] at hav0'; cases hav0'
            let qLbl := if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U u
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧
                ∃ (hsz : B2.body.size = blk.body.size),
                (∀ k (hk : k < blk.body.size), B2.body[k]'(hsz ▸ hk) = loopMapStmt clonedDefs off c (blk.body[k]'hk)) ∧
                B2.term = mapLoopTerm clonedDefs off c (fun l => l) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have htermEq : blk.term.setEdges (blk.term.edges.map fun e =>
                    { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) =
                    mapLoopTerm clonedDefs off 0 (fun l => l) blk.term := by
                  cases ht' : blk.term <;> simp [ht', Term.edges] at hnoEdges ⊢ <;>
                    simp [Term.setEdges, mapLoopTerm, loopMapArg_zero_map]
                by_cases hlt : u < unrollCut h nodes
                · have hblk := buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off
                    hlt ((natSet_ofList_contains_false nodes u).2 hun) hB
                  refine ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) },
                    by simpa [qLbl, unrollRemapOrig, hlt, F'] using hblk, rfl,
                    fun k hk => by simp [loopMapStmt_zero'], htermEq⟩
                · have hblk := buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off
                    (Nat.le_of_not_lt hlt) hB
                  refine ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) },
                    by simpa [qLbl, unrollRemapOrig, hlt, F'] using hblk, rfl,
                    fun k hk => by simp [loopMapStmt_zero'], htermEq⟩
              · have hblk := buildUnrolled_blocks_copy_exit F h nodes leafExits nonLeafExits U off
                  (by omega) hcU heidx hB
                refine ⟨_, by simpa [qLbl, hc0] using hblk, by simp, fun k hk => by simp [clonedDefs], rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2body, hB2term⟩ := hB2
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hltB2 : pos < B2.body.size := hB2sz ▸ hltB
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuAv := checkStmtsAvail_at hchk hltB
              have hsdCl : ∀ d ∈ (blk.body[pos]'hltB).defs, clonedDefs.contains d = true := hbodyDefs _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuAv hsdCl; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (as'.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          have hs2 : B2.body[pos]'hltB2 = .call (rs'.map (loopMapReg clonedDefs off c)) g' (as'.map (loopMapArg clonedDefs off c)) := by
                            rw [hB2body pos hltB, hs]; rfl
                          have hstep2 := step_call (p := q) (F := F') (B := B2)
                            (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            hqfi hB2 hltB2 hs2 hev2 hent2
                          have hcallAt : blk.body[pos]? = some (.call rs' g' as') := by
                            rw [Array.getElem?_eq_getElem hltB, hs]
                          refine .inl ⟨1, _, star_of_step hstep2,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.leafExit hcU heidx hB hav0 (by omega)
                              (fun _ => ⟨by omega, rfl, hsdCl, g', as', by simpa using hcallAt⟩)
                              (by simpa using hcopy)) hrest)⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, List.map_cons, List.sum_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          have h2 : unrollFramePot fi cut K E T U ⟨fi, qLbl, pos + 1, ρ₂, rs'.map (loopMapReg clonedDefs off c)⟩ =
                              unrollFramePot fi cut K E T U ⟨fi, qLbl, pos, ρ₂, d₂⟩ := rfl
                          dsimp only [cut, K, E, T, qLbl] at h1 h2; rw [h2]; omega
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, hcopy'⟩ := loopMapStmt_exec hcopy hsuLt hsuAv hsdCl hx'
                      have hnc : (loopMapStmt clonedDefs off c (blk.body[pos]'hltB)).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F') (B := B2)
                        (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                        hqfi hB2 hltB2 (hB2body pos hltB) hnc hx2
                      rw [← availAtPos_succ av0 blk.body hltB] at hcopy'
                      refine .inl ⟨0, _, star_of_step hstep2,
                        ⟨rfl, rfl, .cons (.leafExit hcU heidx hB hav0 (by omega) (fun hc => by cases hc)
                          (by simpa using hcopy')) hrest⟩, ?_⟩
                      rw [unrollPot_cons, unrollPot_cons, Bool.toNat_false, Nat.zero_add, Nat.mul_zero]
                      have h2 : unrollFramePot fi cut K E T U ⟨fi, qLbl, pos + 1, ρ₂', d₂⟩ =
                          unrollFramePot fi cut K E T U ⟨fi, qLbl, pos, ρ₂, d₂⟩ := rfl
                      dsimp only [cut, K, E, T, qLbl] at h2; rw [h2]; omega
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hposEq : pos = blk.body.size := by omega
              subst hposEq
              rw [checkStmtsAvail_end hchk] at hcopy
              have hltB2 : ¬ blk.body.size < B2.body.size := by omega
              cases ht : blk.term with
              | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ => simp [ht, Term.edges] at hnoEdges
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
              | ret ras =>
                  rw [ht] at hstep1 htUsesLt htAv; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                        rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      have hstep2_unfold := step_term_ge (p := q) (F := F') (B := B2) (mem := mem₁) (ctx := ctx₁)
                        (fr := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩) (rest := rest₂) hqfi hB2 hltB2
                      dsimp only at hstep2_unfold
                      rw [hB2term, ht] at hstep2_unfold; dsimp only [mapLoopTerm] at hstep2_unfold
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel', hpot'⟩ := matchRet mem₁ ctx₁
                        ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), hrel', hpot'⟩
              | tail g tas =>
                  rw [ht] at hstep1 htUsesLt htAv; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (tas.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := unroll_enter_rel hpfi hf hq hent
                          have hstep2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } =
                              .next { mem := mem₁, ctx := ctx₁, stack := calFr₂ :: rest₂ } true := by
                            unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]
                            simp [hltB2, mapLoopTerm, hev2, hent2]
                          refine .inl ⟨1, _, star_of_step hstep2, ⟨rfl, rfl, .cons hcalRel hrest⟩, ?_⟩
                          rw [unrollPot_cons, unrollPot_cons, Bool.toNat_true, Nat.mul_one]
                          have h1 := unrollFramePot_le fi cut K E T U calFr₂
                          dsimp only [cut, K, E, T] at h1; omega
  · -- `final` (concisely discharged via `final_ne_stuck_elim`!)
    intro s₁ s₂ r hrel hfin hne
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq
    obtain rfl : ctx₁ = ctx₂ := hctx_eq
    cases hstack with
    | nil =>
        have hst : step p { mem := mem₁, ctx := ctx₁, stack := [] } = .stuck := rfl
        rw [semStep, hst] at hfin; cases hfin; exact absurd rfl hne
    | @cons _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        obtain ⟨G, B, hG, hB, hltB, hterm⟩ := final_ne_stuck_elim hfin hne
        cases hfr with
        | other hfn =>
            have hqG : q.funcs[fr₁.fn]? = some G := by
              rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hG]
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [fr₁] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht, hev]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @outside u pos ρ₁ ρ₂ d₁ d₂ blk hBu hun hul _ _ houter =>
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hBu).1
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨_, htNc, _⟩ := hf.outside_no_cloned u huLt hun hul blk hBu
            have hB2 : F'.blocks[unrollRemapOrig h nodes leafExits nonLeafExits U u]? =
                some { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) } := by
              unfold unrollRemapOrig
              by_cases hlt : u < unrollCut h nodes
              · simp only [hlt, ↓reduceIte]
                exact buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off
                  hlt ((natSet_ofList_contains_false nodes u).2 hun) hBu
              · simp only [hlt, ↓reduceIte]
                exact buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off (Nat.le_of_not_lt hlt) hBu
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htNc
              have hev2 : evalArgs ρ₂ ras = some vs := by
                rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, unrollRemapOrig h nodes leafExits nonLeafExits U u, pos, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @loopNode u idx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hcU hidx hBu hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            dsimp only at hltB
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have hposEq : pos = blk.body.size := by omega
            subst hposEq
            have huMem : u ∈ nodes := List.mem_of_getElem? hidx
            have huCut : u < cut := hf.node_lt_cut huMem
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_left _ huMem) blk hBu
            rw [hav0] at hav0'; cases hav0'
            rw [checkStmtsAvail_end hchk] at hcopy
            let qLbl := if c = 0 then u else unrollCopyNodeBase h nodes leafExits nonLeafExits c + idx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧ B2.body.size = blk.body.size ∧
                B2.term = mapLoopTerm clonedDefs off c (unrollRemapTarget h nodes leafExits nonLeafExits U c) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have hblk := buildUnrolled_blocks_prefix_node F h nodes leafExits nonLeafExits U off
                  hcut_le huCut ((natSet_ofList_contains nodes u).2 huMem) hBu
                exact ⟨{ blk with term := mapLoopTerm clonedDefs off 0 (unrollRemapTarget h nodes leafExits nonLeafExits U 0) blk.term },
                  by simpa [qLbl, clonedDefs, F'] using hblk, rfl, rfl⟩
              · have hblk := buildUnrolled_blocks_copy_node F h nodes leafExits nonLeafExits U off
                  (by omega) hcU hidx hBu
                exact ⟨_, by simpa [qLbl, hc0] using hblk, by simp, rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2term⟩ := hB2
            have hltB2 : ¬ blk.body.size < B2.body.size := by omega
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htAv
              have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @leafExit u eidx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hcU heidx hBu hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            dsimp only at hltB
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have hposEq : pos = blk.body.size := by omega
            subst hposEq
            have huMem : u ∈ leafExits := List.mem_of_getElem? heidx
            have hun : u ∉ nodes := (hf.leaf_ok u huMem).2.2
            have hnoEdges : blk.term.edges = [] := hf.leaf_no_edges u huMem blk hBu
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_right _ huMem) blk hBu
            rw [hav0] at hav0'; cases hav0'
            rw [checkStmtsAvail_end hchk] at hcopy
            let qLbl := if c = 0 then unrollRemapOrig h nodes leafExits nonLeafExits U u
                        else unrollCopyExitBase h nodes leafExits nonLeafExits c + eidx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧ B2.body.size = blk.body.size ∧
                B2.term = mapLoopTerm clonedDefs off c (fun l => l) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have htermEq : blk.term.setEdges (blk.term.edges.map fun e =>
                    { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) =
                    mapLoopTerm clonedDefs off 0 (fun l => l) blk.term := by
                  cases ht' : blk.term <;> simp [ht', Term.edges] at hnoEdges ⊢ <;>
                    simp [Term.setEdges, mapLoopTerm, loopMapArg_zero_map]
                by_cases hlt : u < unrollCut h nodes
                · have hblk := buildUnrolled_blocks_prefix_other F h nodes leafExits nonLeafExits U off
                    hlt ((natSet_ofList_contains_false nodes u).2 hun) hBu
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) },
                    by simpa [qLbl, unrollRemapOrig, hlt, F'] using hblk, rfl, htermEq⟩
                · have hblk := buildUnrolled_blocks_suffix F h nodes leafExits nonLeafExits U off (Nat.le_of_not_lt hlt) hBu
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := unrollRemapOrig h nodes leafExits nonLeafExits U e.target }) },
                    by simpa [qLbl, unrollRemapOrig, hlt, F'] using hblk, rfl, htermEq⟩
              · have hblk := buildUnrolled_blocks_copy_exit F h nodes leafExits nonLeafExits U off (by omega) hcU heidx hBu
                exact ⟨_, by simpa [qLbl, hc0] using hblk, by simp, rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2term⟩ := hB2
            have hltB2 : ¬ blk.body.size < B2.body.size := by omega
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htAv
              have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩

/-! ### Public `unrollLoopSite` simulation & well-formedness theorems -/

/-- **Single-site `U`-way loop unrolling simulation**:
`unrollLoopSite p fi h U = some q` simulates `p` with exact value/memory equality
and linear clock map `k ↦ U * k + (U - 1)`. -/
theorem unrollLoopSite_sim {p q : Program} {fi h U : Nat}
    (hunroll : unrollLoopSite p fi h U = some q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => U * k + (U - 1))
      (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  unfold unrollLoopSite at hunroll
  by_cases hU : U < 2
  · simp [hU] at hunroll
  · simp only [hU, ↓reduceIte] at hunroll
    cases hpfi : p.funcs[fi]? with
    | none => rw [hpfi] at hunroll; cases hunroll
    | some F =>
        rw [hpfi] at hunroll; dsimp only at hunroll
        cases hcls : classifyLoopExits F h with
        | none => rw [hcls] at hunroll; cases hunroll
        | some triple =>
            rcases triple with ⟨nodes, leafExits, nonLeafExits⟩
            rw [hcls] at hunroll; dsimp only at hunroll
            split at hunroll
            · rename_i hok
              cases hunroll
              have hf := loopCloneFacts_of_ok hok
              have hfwd := unrollLoopSite_forward (U := U) hpfi (by omega) hok rfl
              cases hinit1 : Lir.State.initial p args mem ctx with
              | none =>
                  refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
                    fun k hk => by simp [eval, hinit1] at hk⟩
              | some s₁ =>
                  simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff,
                    Option.some.injEq] at hinit1
                  obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
                  obtain ⟨fr₂, hent₂, hfrRel⟩ := unroll_enter_rel hpfi hf rfl hent₁
                  have hinit2 : Lir.State.initial
                      { funcs := p.funcs.set! fi (buildUnrolledFunc F h nodes leafExits nonLeafExits U (nextFreshVReg F)), main := p.main }
                      args mem ctx = some { mem := mem, ctx := ctx, stack := [fr₂] } := by
                    unfold Lir.State.initial; rw [hent₂]; rfl
                  have hrel0 : UnrollStateRel F fi h nodes leafExits nonLeafExits U (nextFreshVReg F)
                      (computeLoopAvail F h nodes leafExits)
                      { mem := mem, ctx := ctx, stack := [fr₁] }
                      { mem := mem, ctx := ctx, stack := [fr₂] } :=
                    ⟨rfl, rfl, .cons hfrRel .nil⟩
                  have hpot0 : unrollPot fi (unrollCut h nodes) nodes.length leafExits.length nonLeafExits.length U
                      { mem := mem, ctx := ctx, stack := [fr₂] } ≤ U - 1 := by
                    simp only [unrollPot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
                    exact unrollFramePot_le ..
                  exact hfwd.sim hrel0 hpot0
                    (runs_eval (by unfold Lir.State.initial; rw [hent₁]; rfl))
                    (runs_eval hinit2)
            · cases hunroll

theorem unrollLoopSiteChecked_wellFormed {p : Program} {fi h U : Nat}
    (hwf : p.wellFormed = true) :
    (unrollLoopSiteChecked p fi h U).1.wellFormed = true := by
  unfold unrollLoopSiteChecked
  cases unrollLoopSite p fi h U with
  | none => exact hwf
  | some q =>
      dsimp only
      split
      · rename_i hok; simp [hwf] at hok; exact hok
      · exact hwf

theorem unrollLoopSiteChecked_sim (p : Program) (fi h U : Nat) (hU : 1 ≤ U)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq (fun k => U * k + (U - 1))
      (fun k => eval p k args mem ctx)
      (fun k => eval (unrollLoopSiteChecked p fi h U).1 k args mem ctx) := by
  have hself : Sem.Sim Eq (fun k => U * k + (U - 1))
      (fun k => eval p k args mem ctx) (fun k => eval p k args mem ctx) := by
    refine ⟨fun k _ => ⟨k, Sem.Result.Refines.refl (fun _ => rfl)⟩, fun k hk => ?_⟩
    by_cases h1 : eval p k args mem ctx = .timeout
    · exact .inl h1
    · exfalso
      have hle : k ≤ U * k + (U - 1) := by
        have : 1 * k ≤ U * k := Nat.mul_le_mul_right k hU; omega
      have hm := eval_mono p args mem ctx hle h1
      dsimp only at hm
      rw [hk] at hm
      exact h1 hm.symm
  unfold unrollLoopSiteChecked
  cases hu : unrollLoopSite p fi h U with
  | none => exact hself
  | some q =>
      dsimp only
      split
      · exact unrollLoopSite_sim hu args mem ctx
      · exact hself

/-! ## Part 5: Direct soundness proof for `versionOddLoopSite` (`Sem.Forward`) -/

section VersionLayout

variable (F : Func) (h : Nat) (nodes leafExits nonLeafExits : List Nat)
  (testParamIdxs : List Nat) (outerTestRegs : List VReg) (off : VReg)

private def verCut : Nat := nodes.getLastD h + 1
private def verDisp : Nat := verCut h nodes
private def verSlowHop : Nat := verCut h nodes + 1
private def verFastHop : Nat := verCut h nodes + 2
private def verSlowTrampBase : Nat := verCut h nodes + 3
private def verFastNodeBase : Nat := verCut h nodes + 3 + nonLeafExits.length
private def verFastExitBase : Nat := verFastNodeBase h nodes nonLeafExits + nodes.length
private def verFastTrampBase : Nat := verFastExitBase h nodes nonLeafExits + leafExits.length
private def verDelta : Nat := 3 + nonLeafExits.length + nodes.length + leafExits.length + nonLeafExits.length

private def verRemapOrig (L : Nat) : Nat :=
  if L < verCut h nodes then L else L + verDelta nodes leafExits nonLeafExits

private def verRemapOutside (tgt : Nat) : Nat :=
  if tgt == h then verDisp h nodes else verRemapOrig h nodes leafExits nonLeafExits tgt

private def verRemapSlowTarget (tgt : Nat) : Nat :=
  if tgt == h || (Src.NatSet.ofList nodes).contains tgt then tgt
  else match listIndexOf nonLeafExits tgt with
  | some tidx => verSlowTrampBase h nodes + tidx
  | none => verRemapOrig h nodes leafExits nonLeafExits tgt

private def verRemapFastTarget (tgt : Nat) : Nat :=
  if tgt == h then verDisp h nodes
  else if (Src.NatSet.ofList nodes).contains tgt then
    match listIndexOf nodes tgt with
    | some idx => verFastNodeBase h nodes nonLeafExits + idx
    | none => tgt
  else match listIndexOf leafExits tgt with
  | some eidx => verFastExitBase h nodes nonLeafExits + eidx
  | none =>
      match listIndexOf nonLeafExits tgt with
      | some tidx => verFastTrampBase h nodes leafExits nonLeafExits + tidx
      | none => verRemapOrig h nodes leafExits nonLeafExits tgt

private theorem verRemapOrig_le_iff (u v : Nat) :
    decide (verRemapOrig h nodes leafExits nonLeafExits v ≤
            verRemapOrig h nodes leafExits nonLeafExits u) = decide (v ≤ u) := by
  unfold verRemapOrig
  split <;> split <;> (try rfl) <;> simp only [decide_eq_decide] <;>
    exact ⟨fun _ => by omega, fun _ => by omega⟩

private theorem buildVersioned_blocks_prefix_node {b : Nat} {B : Block}
    (hb : b < verCut h nodes)
    (hmem : (Src.NatSet.ofList nodes).contains b = true)
    (hB : F.blocks[b]? = some B) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[b]? =
      some { B with
        term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off 0
          (verRemapSlowTarget h nodes leafExits nonLeafExits) B.term
        cold := true } := by
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp [verCut] at hb ⊢; exact hb)]
  rw [List.getElem?_map, List.getElem?_range (by simp only [verCut] at hb; exact hb)]
  simp only [Option.map_some, hget, hmem, ↓reduceIte]
  rfl

private theorem buildVersioned_blocks_prefix_other {b : Nat} {B : Block}
    (hb : b < verCut h nodes)
    (hnm : (Src.NatSet.ofList nodes).contains b = false)
    (hB : F.blocks[b]? = some B) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[b]? =
      some { B with
        term := B.term.setEdges (B.term.edges.map fun e =>
          { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) } := by
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp [verCut] at hb ⊢; exact hb)]
  rw [List.getElem?_map, List.getElem?_range (by simp only [verCut] at hb; exact hb)]
  simp only [Option.map_some, hget, hnm, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem buildVersioned_blocks_disp {hBlk : Block} (hhB : F.blocks[h]? = some hBlk) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[verDisp h nodes]? =
      some (let dispParams := (List.range hBlk.params.length).map (2 * off + ·)
            let andBase := max (2 * off + hBlk.params.length) (3 * off + 2 * nonLeafExits.length * off)
            let testRegs := outerTestRegs ++ testParamIdxs.map (fun i => dispParams[i]?.getD (2 * off))
            let (dispBody, testReg) := buildDispAndChain testRegs andBase
            { params := dispParams
              body := dispBody.toArray
              term := .br .tnz .w64 (.v testReg) (.imm 1)
                { target := verFastHop h nodes, args := [] }
                { target := verSlowHop h nodes, args := [] }
              cold := hBlk.cold }) := by
  have hget : F.blocks[h]! = hBlk := array_getElem!_of_getElem? hhB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verDisp, verCut]), List.length_map, List.length_range]
  simp only [verDisp, verCut, Nat.sub_self, List.cons_append, List.getElem?_cons_zero, hget]
  rfl

private theorem buildVersioned_blocks_slowHop {hBlk : Block} (hhB : F.blocks[h]? = some hBlk) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[verSlowHop h nodes]? =
      some (let dispParams := (List.range hBlk.params.length).map (2 * off + ·)
            { params := []
              body := #[]
              term := .jump { target := h, args := dispParams.map .v }
              cold := true }) := by
  have hget : F.blocks[h]! = hBlk := array_getElem!_of_getElem? hhB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verSlowHop, verCut]), List.length_map, List.length_range]
  simp only [verSlowHop, verCut, Nat.add_sub_cancel_left, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero, hget]

private theorem buildVersioned_blocks_fastHop {hBlk : Block} (hhB : F.blocks[h]? = some hBlk) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[verFastHop h nodes]? =
      some (let dispParams := (List.range hBlk.params.length).map (2 * off + ·)
            { params := []
              body := #[]
              term := .jump { target := verFastNodeBase h nodes nonLeafExits, args := dispParams.map .v }
              cold := hBlk.cold }) := by
  have hget : F.blocks[h]! = hBlk := array_getElem!_of_getElem? hhB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verFastHop, verCut]), List.length_map, List.length_range]
  simp only [verFastHop, verCut, Nat.add_sub_cancel_left, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_cons_zero, hget]
  rfl

private theorem buildVersioned_blocks_slowTramp {tidx x : Nat}
    (hx : nonLeafExits[tidx]? = some x) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[
      verSlowTrampBase h nodes + tidx]? =
      some (let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
            let regStart := 3 * off + tidx * off
            let ps := (List.range nParams).map (regStart + ·)
            { params := ps
              body := #[]
              term := .jump { target := x + verDelta nodes leafExits nonLeafExits, args := ps.map .v }
              cold := (F.blocks[x]?.map (·.cold)).getD false }) := by
  have htidx : tidx < nonLeafExits.length := (List.getElem?_eq_some_iff.1 hx).1
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verSlowTrampBase, verCut]; omega), List.length_map, List.length_range]
  have hsub : verSlowTrampBase h nodes + tidx - (nodes.getLastD h + 1) = tidx + 3 := by simp [verSlowTrampBase, verCut]; omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [buildTrampBlocks_length]; exact htidx)]
  simpa [verDelta] using buildTrampBlocks_getElem? F nonLeafExits (verDelta nodes leafExits nonLeafExits)
    (3 * off) off tidx x hx

private theorem buildVersioned_blocks_fastNode {idx b : Nat} {B : Block}
    (hidx : nodes[idx]? = some b) (hB : F.blocks[b]? = some B) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[
      verFastNodeBase h nodes nonLeafExits + idx]? =
      some { params := B.params.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off 1)
             body := B.body.map (loopMapStmt (collectBlocksDefs F (nodes ++ leafExits)) off 1)
             term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off 1
               (verRemapFastTarget h nodes leafExits nonLeafExits) B.term
             cold := B.cold } := by
  have hidxLt : idx < nodes.length := (List.getElem?_eq_some_iff.1 hidx).1
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verFastNodeBase, verCut]; omega), List.length_map, List.length_range]
  have hsub : verFastNodeBase h nodes nonLeafExits + idx - (nodes.getLastD h + 1) = (nonLeafExits.length + idx) + 3 := by
    simp [verFastNodeBase, verCut]; omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp [hidxLt]), List.getElem?_map, hidx]
  simp only [Option.map_some, hget]
  rfl

private theorem buildVersioned_blocks_fastExit {eidx b : Nat} {B : Block}
    (heidx : leafExits[eidx]? = some b) (hB : F.blocks[b]? = some B) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[
      verFastExitBase h nodes nonLeafExits + eidx]? =
      some { params := B.params.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off 1)
             body := B.body.map (loopMapStmt (collectBlocksDefs F (nodes ++ leafExits)) off 1)
             term := mapLoopTerm (collectBlocksDefs F (nodes ++ leafExits)) off 1 (fun l => l) B.term
             cold := B.cold } := by
  have heidxLt : eidx < leafExits.length := (List.getElem?_eq_some_iff.1 heidx).1
  have hget : F.blocks[b]! = B := array_getElem!_of_getElem? hB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verFastExitBase, verFastNodeBase, verCut]; omega), List.length_map, List.length_range]
  have hsub : verFastExitBase h nodes nonLeafExits + eidx - (nodes.getLastD h + 1) =
      (nonLeafExits.length + (nodes.length + eidx)) + 3 := by
    simp [verFastExitBase, verFastNodeBase, verCut]; omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp [heidxLt]), List.getElem?_map, heidx]
  simp only [Option.map_some, hget]

private theorem buildVersioned_blocks_fastTramp {tidx x : Nat}
    (hx : nonLeafExits[tidx]? = some x) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[
      verFastTrampBase h nodes leafExits nonLeafExits + tidx]? =
      some (let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
            let regStart := 3 * off + nonLeafExits.length * off + tidx * off
            let ps := (List.range nParams).map (regStart + ·)
            { params := ps
              body := #[]
              term := .jump { target := x + verDelta nodes leafExits nonLeafExits, args := ps.map .v }
              cold := (F.blocks[x]?.map (·.cold)).getD false }) := by
  have htidx : tidx < nonLeafExits.length := (List.getElem?_eq_some_iff.1 hx).1
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verFastTrampBase, verFastExitBase, verFastNodeBase, verCut]; omega),
    List.length_map, List.length_range]
  have hsub : verFastTrampBase h nodes leafExits nonLeafExits + tidx - (nodes.getLastD h + 1) =
      (nonLeafExits.length + (nodes.length + (leafExits.length + tidx))) + 3 := by
    simp [verFastTrampBase, verFastExitBase, verFastNodeBase, verCut]; omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by rw [buildTrampBlocks_length]; exact htidx)]
  simpa [verDelta] using buildTrampBlocks_getElem? F nonLeafExits (verDelta nodes leafExits nonLeafExits)
    (3 * off + nonLeafExits.length * off) off tidx x hx

private theorem buildVersioned_blocks_suffix {b : Nat} {B : Block}
    (hge : verCut h nodes ≤ b) (hB : F.blocks[b]? = some B) :
    (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).blocks[
      b + verDelta nodes leafExits nonLeafExits]? =
      some { B with
        term := B.term.setEdges (B.term.edges.map fun e =>
          { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) } := by
  have hlt : b < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
  have hget : F.blocks[nodes.getLastD h + 1 + (b - (nodes.getLastD h + 1))]! = B := by
    rw [show nodes.getLastD h + 1 + (b - (nodes.getLastD h + 1)) = b by simp only [verCut] at hge; omega]
    exact array_getElem!_of_getElem? hB
  unfold buildVersionedOddFunc; dsimp only
  rw [List.getElem?_toArray]; simp only [List.append_assoc]
  rw [List.getElem?_append_right (by simp [verCut] at hge ⊢; omega), List.length_map, List.length_range]
  have hsub : b + verDelta nodes leafExits nonLeafExits - (nodes.getLastD h + 1) =
      (nonLeafExits.length + (nodes.length + (leafExits.length + (nonLeafExits.length + (b - (nodes.getLastD h + 1)))))) + 3 := by
    simp [verDelta, verCut] at hge ⊢; omega
  rw [hsub]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (by rw [buildTrampBlocks_length]; omega),
    buildTrampBlocks_length, Nat.add_sub_cancel_left]
  rw [List.getElem?_map, List.getElem?_range (by simp only [verCut] at hge ⊢; omega)]
  simp only [Option.map_some, hget]
  rfl

end VersionLayout

/-- Active/suspended frame relation for `versionOddLoopSite` (`c = 0`: slow loop; `c = 1`: fast loop). -/
inductive VersionFrameRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (off : VReg)
    (availMap : Array Src.NatSet) (isTop : Bool) : Frame → Frame → Prop where
  | other {fr : Frame} :
      fr.fn ≠ fi →
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap isTop fr fr
  | outside {b pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} :
      F.blocks[b]? = some blk →
      b ∉ nodes →
      b ∉ leafExits →
      pos ≤ blk.body.size →
      (isTop = false → d₂ = d₁) →
      LoopOuterRel (collectBlocksDefs F (nodes ++ leafExits)) off ρ₁ ρ₂ →
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, verRemapOrig h nodes leafExits nonLeafExits b, pos, ρ₂, d₂⟩
  | loopNode {b idx c pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} {av0 : Src.NatSet} :
      c < 2 →
      nodes[idx]? = some b →
      F.blocks[b]? = some blk →
      availMap[b]? = some av0 →
      pos ≤ blk.body.size →
      (isTop = false → 0 < pos ∧ d₂ = d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c) ∧
        (∀ d ∈ d₁, (collectBlocksDefs F (nodes ++ leafExits)).contains d = true) ∧
        ∃ g as, blk.body[pos - 1]? = some (.call d₁ g as)) →
      LoopCopyRel (collectBlocksDefs F (nodes ++ leafExits)) off c
        (availAtPos av0 blk.body (if isTop then pos else pos - 1)) ρ₁ ρ₂ →
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, if c = 0 then b else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂, d₂⟩
  | leafExit {b eidx c pos : Nat} {ρ₁ ρ₂ : Env} {d₁ d₂ : List VReg} {blk : Block} {av0 : Src.NatSet} :
      c < 2 →
      leafExits[eidx]? = some b →
      F.blocks[b]? = some blk →
      availMap[b]? = some av0 →
      pos ≤ blk.body.size →
      (isTop = false → 0 < pos ∧ d₂ = d₁.map (loopMapReg (collectBlocksDefs F (nodes ++ leafExits)) off c) ∧
        (∀ d ∈ d₁, (collectBlocksDefs F (nodes ++ leafExits)).contains d = true) ∧
        ∃ g as, blk.body[pos - 1]? = some (.call d₁ g as)) →
      LoopCopyRel (collectBlocksDefs F (nodes ++ leafExits)) off c
        (availAtPos av0 blk.body (if isTop then pos else pos - 1)) ρ₁ ρ₂ →
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap isTop
        ⟨fi, b, pos, ρ₁, d₁⟩
        ⟨fi, if c = 0 then verRemapOrig h nodes leafExits nonLeafExits b
             else verFastExitBase h nodes nonLeafExits + eidx, pos, ρ₂, d₂⟩

inductive VersionStackRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (off : VReg)
    (availMap : Array Src.NatSet) : Bool → List Frame → List Frame → Prop where
  | nil {isTop : Bool} : VersionStackRel F fi h nodes leafExits nonLeafExits off availMap isTop [] []
  | cons {isTop : Bool} {fr₁ fr₂ : Frame} {rest₁ rest₂ : List Frame} :
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap isTop fr₁ fr₂ →
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap false rest₁ rest₂ →
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap isTop (fr₁ :: rest₁) (fr₂ :: rest₂)

def VersionStateRelCore (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (off : VReg)
    (availMap : Array Src.NatSet) (s₁ s₂ : State) : Prop :=
  s₁.mem = s₂.mem ∧ s₁.ctx = s₂.ctx ∧
  VersionStackRel F fi h nodes leafExits nonLeafExits off availMap true s₁.stack s₂.stack

private def frameParamsDef (F : Func) (fi : FunId) (fr : Frame) : Prop :=
  fr.fn = fi → ∀ r ∈ F.params, fr.env[r]?.isSome = true

def VersionStateRel (F : Func) (fi h : Nat)
    (nodes leafExits nonLeafExits : List Nat) (off : VReg)
    (availMap : Array Src.NatSet) (s₁ s₂ : State) : Prop :=
  (∀ fr ∈ s₁.stack, frameParamsDef F fi fr) ∧
  VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁ s₂

private theorem env_insert_isSome {ρ : Env} {x y : VReg} {v : Word}
    (h : ρ[y]?.isSome = true) : (ρ.insert x v)[y]?.isSome = true := by
  by_cases hxy : x = y
  · subst hxy; rw [env_insert_self]; rfl
  · rw [env_insert_ne _ _ hxy]; exact h

private theorem bindParams_preserves_isSome : ∀ {ps : List VReg} {vs : List Word} {ρ ρ' : Env} {y : VReg},
    bindParams ρ ps vs = some ρ' → ρ[y]?.isSome = true → ρ'[y]?.isSome = true
  | [], [], _, _, _, hbp, hy => by simp [bindParams] at hbp; subst hbp; exact hy
  | _ :: ps, _ :: vs, _, _, _, hbp, hy => by
      simp only [bindParams] at hbp
      exact bindParams_preserves_isSome hbp (env_insert_isSome hy)
  | [], _ :: _, _, _, _, hbp, _ | _ :: _, [], _, _, _, hbp, _ => by simp [bindParams] at hbp

private theorem bindParams_mem_isSome : ∀ {ps : List VReg} {vs : List Word} {ρ ρ' : Env},
    bindParams ρ ps vs = some ρ' → ∀ r ∈ ps, ρ'[r]?.isSome = true
  | [], [], _, _, _, _, hr => by cases hr
  | p :: ps, v :: vs, ρ, ρ', hbp, r, hr => by
      simp only [bindParams] at hbp
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hmem
      · exact bindParams_preserves_isSome hbp (by rw [env_insert_self]; rfl)
      · exact bindParams_mem_isSome hbp r hmem
  | [], _ :: _, _, _, hbp, _, _ | _ :: _, [], _, _, hbp, _, _ => by simp [bindParams] at hbp

private theorem stmt_exec_preserves_isSome {s : Stmt} {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (hx : s.exec ρ mem ctx = some (ρ', mem')) {y : VReg} (hy : ρ[y]?.isSome = true) :
    ρ'[y]?.isSome = true := by
  cases s with
  | assign x r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨_, _, rfl, _⟩ := hx; exact env_insert_isSome hy
  | limb r1 r2 op =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨_, _, rfl, _⟩ := hx; exact env_insert_isSome (env_insert_isSome hy)
  | store w m a =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨_, _, _, _, hwr⟩ := hx
      cases h : mem.write? w _ _ with
      | error _ => rw [h] at hwr; cases hwr
      | ok _ => rw [h] at hwr; simp only [Option.some.injEq, Prod.mk.injEq] at hwr; obtain ⟨rfl, _⟩ := hwr; exact hy
  | call _ _ _ => simp [Stmt.exec] at hx

private theorem enter_frameParamsDef {p : Program} {F : Func} {fi g : FunId} {vs : List Word} {fr : Frame}
    (hpfi : p.funcs[fi]? = some F) (hent : enter p g vs = some fr) :
    frameParamsDef F fi fr := by
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨G, hG, ρ, hbp, rfl⟩ := hent
  intro hgf r hr
  subst hgf; rw [hpfi] at hG; cases hG
  exact bindParams_mem_isSome hbp r hr

private theorem step_preserves_frameParamsDef {p : Program} {F : Func} {fi : FunId}
    (hpfi : p.funcs[fi]? = some F) {s₁ s₁' : State} {b : Bool}
    (hpd : ∀ fr ∈ s₁.stack, frameParamsDef F fi fr)
    (hstep : step p s₁ = .next s₁' b) :
    ∀ fr ∈ s₁'.stack, frameParamsDef F fi fr := by
  have htake : ∀ {G : Func} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame} {ρ : Env} {e : Edge},
      (∀ f ∈ rest, frameParamsDef F fi f) →
      (fr.fn = fi → ∀ r ∈ F.params, ρ[r]?.isSome = true) →
      takeEdge G { mem, ctx, stack := fr :: rest } fr rest ρ e = .next s₁' b →
      ∀ f ∈ s₁'.stack, frameParamsDef F fi f := by
    intro G mem ctx fr rest ρ e hrest hfr hte
    unfold takeEdge at hte
    cases hev : evalArgs ρ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases htb : G.blocks[e.target]? with
        | none => rw [hev, htb] at hte; cases hte
        | some tB =>
            rw [hev, htb] at hte; dsimp only at hte
            cases hbp : bindParams ρ tB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                intro f hf
                simp only [List.mem_cons] at hf
                rcases hf with rfl | hmr
                · intro hfn r hr; exact bindParams_preserves_isSome hbp (hfr hfn r hr)
                · exact hrest f hmr
  rcases s₁ with ⟨mem, ctx, st⟩
  cases st with
  | nil => simp [step] at hstep
  | cons fr rest =>
      have hfrPd : frameParamsDef F fi fr := hpd fr (by simp)
      have hrestPd : ∀ f ∈ rest, frameParamsDef F fi f := fun f hf => hpd f (by simp [hf])
      unfold step at hstep; dsimp only at hstep
      cases hG : p.funcs[fr.fn]? with
      | none => rw [hG] at hstep; cases hstep
      | some G =>
          rw [hG] at hstep; dsimp only at hstep
          cases hB : G.blocks[fr.label]? with
          | none => rw [hB] at hstep; cases hstep
          | some B =>
              rw [hB] at hstep; dsimp only at hstep
              by_cases hlt : fr.pos < B.body.size
              · simp only [hlt, ↓reduceDIte] at hstep
                cases hs : B.body[fr.pos]'hlt with
                | call rs g cas =>
                    rw [hs] at hstep; dsimp only at hstep
                    cases hev : evalArgs fr.env cas with
                    | none => rw [hev] at hstep; cases hstep
                    | some vs =>
                        rw [hev] at hstep; simp only [Option.bind_eq_bind, Option.bind_some] at hstep
                        cases hent : enter p g vs with
                        | none => rw [hent] at hstep; cases hstep
                        | some cal =>
                            rw [hent] at hstep; simp only [Step.next.injEq] at hstep; obtain ⟨rfl, rfl⟩ := hstep
                            intro f hf; simp only [List.mem_cons] at hf
                            rcases hf with rfl | rfl | hmr
                            · exact enter_frameParamsDef hpfi hent
                            · exact hfrPd
                            · exact hrestPd f hmr
                | assign _ _ | limb _ _ _ | store _ _ _ =>
                    rw [hs] at hstep; dsimp only at hstep; rw [← hs] at hstep
                    cases hx : (B.body[fr.pos]'hlt).exec fr.env mem ctx with
                    | none => rw [hx] at hstep; cases hstep
                    | some res =>
                        obtain ⟨ρ', mem'⟩ := res
                        rw [hx] at hstep; simp only [Step.next.injEq] at hstep; obtain ⟨rfl, rfl⟩ := hstep
                        intro f hf; simp only [List.mem_cons] at hf
                        rcases hf with rfl | hmr
                        · intro hfn r hr; exact stmt_exec_preserves_isSome hx (hfrPd hfn r hr)
                        · exact hrestPd f hmr
              · simp only [hlt, ↓reduceDIte] at hstep
                cases ht : B.term with
                | jump e => rw [ht] at hstep; dsimp only at hstep; exact htake hrestPd hfrPd hstep
                | br c w a b' t f =>
                    rw [ht] at hstep; dsimp only at hstep
                    cases ha : a.eval fr.env with
                    | none => rw [ha] at hstep; cases hstep
                    | some va =>
                        cases hb : b'.eval fr.env with
                        | none => rw [ha, hb] at hstep; cases hstep
                        | some vb => rw [ha, hb] at hstep; dsimp only at hstep; exact htake hrestPd hfrPd hstep
                | brOvf o x a b' ok ovf =>
                    rw [ht] at hstep; dsimp only at hstep
                    cases ha : a.eval fr.env with
                    | none => rw [ha] at hstep; cases hstep
                    | some va =>
                        cases hb : b'.eval fr.env with
                        | none => rw [ha, hb] at hstep; cases hstep
                        | some vb =>
                            rw [ha, hb] at hstep; dsimp only at hstep
                            exact htake hrestPd (fun hfn r hr => env_insert_isSome (hfrPd hfn r hr)) hstep
                | ret ras =>
                    rw [ht] at hstep; dsimp only at hstep
                    cases hev : evalArgs fr.env ras with
                    | none => rw [hev] at hstep; cases hstep
                    | some vs =>
                        rw [hev] at hstep; dsimp only at hstep
                        cases rest with
                        | nil => cases hstep
                        | cons c r' =>
                            dsimp only at hstep
                            cases hbp : bindParams c.env c.dsts vs with
                            | none => rw [hbp] at hstep; cases hstep
                            | some ρ' =>
                                rw [hbp] at hstep; simp only [Step.next.injEq] at hstep; obtain ⟨rfl, rfl⟩ := hstep
                                intro f hf; simp only [List.mem_cons] at hf
                                rcases hf with rfl | hmr
                                · intro hfn r hr; exact bindParams_preserves_isSome hbp (hrestPd c (by simp) hfn r hr)
                                · exact hrestPd f (by simp [hmr])
                | tail g tas =>
                    rw [ht] at hstep; dsimp only at hstep
                    cases hev : evalArgs fr.env tas with
                    | none => rw [hev] at hstep; cases hstep
                    | some vs =>
                        rw [hev] at hstep; simp only [Option.bind_eq_bind, Option.bind_some] at hstep
                        cases hent : enter p g vs with
                        | none => rw [hent] at hstep; cases hstep
                        | some cal =>
                            rw [hent] at hstep; simp only [Step.next.injEq] at hstep; obtain ⟨rfl, rfl⟩ := hstep
                            intro f hf; simp only [List.mem_cons] at hf
                            rcases hf with rfl | hmr
                            · exact enter_frameParamsDef hpfi hent
                            · exact hrestPd f hmr
                | fail _ => rw [ht] at hstep; cases hstep
                | trap => rw [ht] at hstep; cases hstep

private theorem step_dispBody_aux {q : Program} {F' : Func} {fi lbl : Nat} {dispBlk : Block}
    {mem : X86.Memory} {ctx : Word} {d₂ : List VReg} {rest₂ : List Frame}
    (hqfi : q.funcs[fi]? = some F') (hdisp : F'.blocks[lbl]? = some dispBlk) :
    ∀ (regs : List Nat) (k : Nat) (accReg nextReg : Nat) (bound : Nat) (ρ : Env),
      k ≤ dispBlk.body.size →
      dispBlk.body.toList.drop k = (buildDispAndChainAux accReg nextReg regs).1 →
      bound ≤ nextReg →
      ρ[accReg]?.isSome = true →
      (∀ r ∈ regs, r < nextReg ∧ ρ[r]?.isSome = true) →
      ∃ ρ' vFinal,
        Sem.Star (semStep q) { mem, ctx, stack := ⟨fi, lbl, k, ρ, d₂⟩ :: rest₂ } 0
          { mem, ctx, stack := ⟨fi, lbl, dispBlk.body.size, ρ', d₂⟩ :: rest₂ } ∧
        (∀ z < bound, ρ'[z]? = ρ[z]?) ∧
        ρ'[(buildDispAndChainAux accReg nextReg regs).2]? = some vFinal
  | [], k, accReg, _, _, ρ, hkle, hdrop, _, hacc, _ => by
      simp only [buildDispAndChainAux] at hdrop ⊢
      have hkeq : k = dispBlk.body.size := by
        have := congrArg List.length hdrop
        simp only [List.length_drop, Array.length_toList, List.length_nil] at this; omega
      cases hga : ρ[accReg]? with
      | none => simp [hga] at hacc
      | some v => exact ⟨ρ, v, hkeq ▸ Sem.Star.refl _, fun _ _ => rfl, hga⟩
  | r :: rest, k, accReg, nextReg, bound, ρ, hkle, hdrop, hbound, hacc, hregs => by
      simp only [buildDispAndChainAux] at hdrop ⊢
      have hlen : dispBlk.body.size - k = ((buildDispAndChainAux nextReg (nextReg + 1) rest).1).length + 1 := by
        have := congrArg List.length hdrop
        simp only [List.length_drop, Array.length_toList, List.length_cons] at this; exact this
      have hklt : k < dispBlk.body.size := by omega
      have hget : dispBlk.body[k]'hklt = .assign nextReg (.bin .and .w64 (.v accReg) (.v r)) := by
        have h1 : (dispBlk.body.toList.drop k)[0]? = some (.assign nextReg (.bin .and .w64 (.v accReg) (.v r))) := by
          rw [hdrop]; rfl
        rw [List.getElem?_drop, Nat.add_zero, Array.getElem?_toList, Array.getElem?_eq_getElem hklt] at h1
        exact Option.some.inj h1
      have hdrop1 : dispBlk.body.toList.drop (k + 1) = (buildDispAndChainAux nextReg (nextReg + 1) rest).1 := by
        rw [← List.drop_drop, hdrop]; first | rfl | done
      cases hva : ρ[accReg]? with
      | none => simp [hva] at hacc
      | some va =>
          have hrInfo := hregs r (by simp)
          cases hvr : ρ[r]? with
          | none => simp [hvr] at hrInfo
          | some vr =>
              let ρ1 : Env := ρ.insert nextReg (X86.Width.w64.truncate (va &&& vr))
              have hx : (Stmt.assign nextReg (.bin .and .w64 (.v accReg) (.v r))).exec ρ mem ctx =
                  some (ρ1, mem) := by
                simp [Stmt.exec, Rhs.eval, Arg.eval, BinOp.eval, hva, hvr, ρ1]
              have hstep1 : step q { mem, ctx, stack := ⟨fi, lbl, k, ρ, d₂⟩ :: rest₂ } =
                  .next { mem, ctx, stack := ⟨fi, lbl, k + 1, ρ1, d₂⟩ :: rest₂ } false :=
                step_stmt (fr := ⟨fi, lbl, k, ρ, d₂⟩) hqfi hdisp hklt hget rfl hx
              have hacc1 : ρ1[nextReg]?.isSome = true := by
                rw [show ρ1[nextReg]? = some (X86.Width.w64.truncate (va &&& vr)) from env_insert_self _ _ _]
                rfl
              have hregs1 : ∀ r' ∈ rest, r' < nextReg + 1 ∧ ρ1[r']?.isSome = true := by
                intro r' hr'
                obtain ⟨hlt', his'⟩ := hregs r' (by simp [hr'])
                refine ⟨Nat.lt_succ_of_lt hlt', ?_⟩
                rw [show ρ1[r']? = ρ[r']? from env_insert_ne _ _ (Nat.ne_of_gt hlt')]; exact his'
              obtain ⟨ρ', vFinal, hstar, hpres, hfin⟩ :=
                step_dispBody_aux hqfi hdisp rest (k + 1) nextReg (nextReg + 1) bound ρ1
                  (by omega) hdrop1 (by omega) hacc1 hregs1
              refine ⟨ρ', vFinal, Sem.Star.free (by rw [semStep_next]; exact hstep1) hstar, ?_, hfin⟩
              intro z hz
              rw [hpres z hz]
              exact env_insert_ne _ _ (by omega)

private theorem step_dispBody {q : Program} {F' : Func} {fi lbl : Nat} {dispBlk : Block}
    {mem : X86.Memory} {ctx : Word} {d₂ : List VReg} {rest₂ : List Frame}
    (hqfi : q.funcs[fi]? = some F') (hdisp : F'.blocks[lbl]? = some dispBlk)
    {regs : List Nat} {andBase : Nat} {bound : Nat} {ρ : Env}
    (hne : regs ≠ [])
    (hbody : dispBlk.body.toList = (buildDispAndChain regs andBase).1)
    (hbound : bound ≤ andBase)
    (hregs : ∀ r ∈ regs, r < andBase ∧ ρ[r]?.isSome = true) :
    ∃ ρ' vFinal,
      Sem.Star (semStep q) { mem, ctx, stack := ⟨fi, lbl, 0, ρ, d₂⟩ :: rest₂ } 0
        { mem, ctx, stack := ⟨fi, lbl, dispBlk.body.size, ρ', d₂⟩ :: rest₂ } ∧
      (∀ z < bound, ρ'[z]? = ρ[z]?) ∧
      ρ'[(buildDispAndChain regs andBase).2]? = some vFinal := by
  cases regs with
  | nil => exact absurd rfl hne
  | cons r0 rest =>
      cases rest with
      | nil =>
          simp only [buildDispAndChain] at hbody ⊢
          have hsz : dispBlk.body.size = 0 := by
            have := congrArg List.length hbody; simpa using this
          have hr0 := hregs r0 (by simp)
          cases hg : ρ[r0]? with
          | none => simp [hg] at hr0
          | some v =>
              refine ⟨ρ, v, ?_, fun _ _ => rfl, hg⟩
              rw [hsz]; exact Sem.Star.refl _
      | cons r1 rs =>
          simp only [buildDispAndChain] at hbody ⊢
          exact step_dispBody_aux hqfi hdisp (r1 :: rs) 0 r0 andBase bound ρ
            (Nat.zero_le _) (by simpa using hbody) hbound (hregs r0 (by simp)).2
            (fun r hr => hregs r (by simp [hr]))

private theorem version_enter_rel {p q : Program} {F : Func} {fi g h : Nat}
    {nodes leafExits nonLeafExits testParamIdxs : List Nat} {outerTestRegs : List VReg}
    {off : VReg} {availMap : Array Src.NatSet}
    {vs : List Word} {fr₁ : Frame}
    (hpfi : p.funcs[fi]? = some F)
    (hf : LoopCloneFacts F h nodes leafExits nonLeafExits off availMap)
    (hq : q = { funcs := p.funcs.set! fi (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off), main := p.main })
    (hent : enter p g vs = some fr₁) :
    ∃ fr₂, enter q g vs = some fr₂ ∧
      VersionFrameRel F fi h nodes leafExits nonLeafExits off availMap true fr₁ fr₂ := by
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  simp only [enter, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hent
  obtain ⟨G, hG, ρ, hbp, rfl⟩ := hent
  by_cases hg : g = fi
  · subst hg
    rw [hpfi] at hG; cases hG
    have hqF : q.funcs[g]? = some (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off) := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt]
    have hpar : (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off).params = F.params := rfl
    have h0lt : 0 < F.blocks.size := by have := hf.h_pos; have := hf.h_lt_cut; have := hf.cut_le_size; omega
    have hb0 : F.blocks[0]? = some F.blocks[0] := Array.getElem?_eq_getElem h0lt
    have h0cut : 0 < verCut h nodes := by simp only [verCut]; omega
    have hremap0 : verRemapOrig h nodes leafExits nonLeafExits 0 = 0 := by simp [verRemapOrig, h0cut]
    refine ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] }, by simp [enter, hqF, hpar, hbp], ?_⟩
    rw [← hremap0]
    exact .outside hb0 hf.zero_not_mem_nodes hf.zero_not_mem_leaf (Nat.zero_le _)
      (fun hc => by cases hc) (LoopOuterRel.refl _ _ _)
  · have hqF : q.funcs[g]? = some G := by
      rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hg, hG]
    exact ⟨{ fn := g, label := 0, pos := 0, env := ρ, dsts := [] },
      by simp [enter, hqF, hbp], .other hg⟩

theorem versionOddLoopSite_forward {p q : Program} {F : Func} {fi h : Nat}
    {nodes leafExits nonLeafExits testParamIdxs : List Nat} {outerTestRegs : List VReg}
    {off : VReg} {availMap : Array Src.NatSet}
    (hpfi : p.funcs[fi]? = some F)
    (hok : versionOddLoopOk F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off availMap = true)
    (hq : q = { funcs := p.funcs.set! fi (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off), main := p.main }) :
    Sem.Forward (semStep p) (semStep q) Eq
      (VersionStateRel F fi h nodes leafExits nonLeafExits off availMap) := by
  unfold versionOddLoopOk at hok; dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hlok, hnonEmpty⟩, htestOk⟩, houterOk⟩, houtPredOk⟩ := hok
  have hf := loopCloneFacts_of_ok hlok
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  let cut := verCut h nodes
  let delta := verDelta nodes leafExits nonLeafExits
  let F' := buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
  have hfiLt : fi < p.funcs.size := (Array.getElem?_eq_some_iff.1 hpfi).1
  have hqfi : q.funcs[fi]? = some F' := by
    rw [hq]; simp [Array.set!_eq_setIfInBounds, hfiLt, F']
  have hh_lt_cut : h < cut := hf.h_lt_cut
  have hh0 : nodes[0]? = some h := by
    cases hns : nodes with
    | nil => exact absurd hns hf.nodes_ne
    | cons a rest => have := hf.nodes_head; rw [hns] at this; simpa using this
  have hpredDir : ∀ u < F.blocks.size, u ∉ nodes → ∀ blk, F.blocks[u]? = some blk →
      ∀ e ∈ blk.term.edges, e.target = h → u < h ∨ cut ≤ u := by
    intro u hu hun blk hB e he hth
    have h1 := (List.all_eq_true.1 houtPredOk) u (List.mem_range.2 hu)
    have hnf : (Src.NatSet.ofList nodes).contains u = false := (natSet_ofList_contains_false nodes u).2 hun
    simp only [hnf, Bool.false_eq_true, ↓reduceIte, hB] at h1
    have h2 := (List.all_eq_true.1 h1) e he
    simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq] at h2
    rcases h2 with (hne | hlt) | hge
    · exact absurd hth hne
    · exact .inl hlt
    · exact .inr hge
  -- Helper 0: shared odd-fixnum dispatch from `verDisp` (`disp → disp.body → fastHop/slowHop → fastNodeBase/h`)
  have dispDispatch : ∀ (mem : X86.Memory) (ctx : Word) (ρ₁ ρ₁' ρ₂ : Env) (d₁ d₂ : List VReg)
      (rest₁ rest₂ : List Frame) (vs : List Word) (hBlk : Block) (avH : Src.NatSet)
      (uLbl uPos : Nat) (ρ₂fr : Env) (eQ : Edge) (b : Bool),
      F.blocks[h]? = some hBlk →
      availMap[h]? = some avH →
      (∀ x, avH.contains x = true → x ∈ hBlk.params) →
      bindParams ρ₁ hBlk.params vs = some ρ₁' →
      LoopOuterRel clonedDefs off ρ₁ ρ₂ →
      (∀ r ∈ F.params, ρ₁[r]?.isSome = true) →
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap false rest₁ rest₂ →
      evalArgs ρ₂ eQ.args = some vs →
      eQ.target = verDisp h nodes →
      decide (verDisp h nodes ≤ uLbl) = b →
      ∃ cStep s₂',
        step q { mem := mem, ctx := ctx, stack := ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ :: rest₂ } =
          takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ :: rest₂ }
            ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ rest₂ ρ₂ eQ →
        Sem.Star (semStep q) { mem := mem, ctx := ctx, stack := ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ :: rest₂ } cStep s₂' ∧
        b.toNat ≤ cStep ∧
        VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap
          { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₁', d₁⟩ :: rest₁ } s₂' := by
    intro mem ctx ρ₁ ρ₁' ρ₂ d₁ d₂ rest₁ rest₂ vs hBlk avH uLbl uPos ρ₂fr eQ b
      hhB havH havHsub hbp houter hpd1 hrest hev2 heQtgt hchg1
    have hparDefs : ∀ d ∈ hBlk.params, clonedDefs.contains d = true :=
      (collectBlocksDefs_mem (List.mem_append_left _ (List.mem_of_getElem? hh0)) hhB).1
    let dispParams := (List.range hBlk.params.length).map (2 * off + ·)
    let andBase := max (2 * off + hBlk.params.length) (3 * off + 2 * nonLeafExits.length * off)
    let testRegs := outerTestRegs ++ testParamIdxs.map (fun i => dispParams[i]?.getD (2 * off))
    have hdispLen : dispParams.length = vs.length := by
      have := bindParams_len_eq hbp; simp [dispParams, this]
    obtain ⟨ρ₂d, hbpD⟩ := bindParams_of_eq_len ρ₂ dispParams vs hdispLen
    have hdispNd : dispParams.Nodup := nodup_map_add_range (2 * off) hBlk.params.length
    obtain ⟨hevD, hpresD⟩ := bindParams_nodup_evalArgs hdispNd hbpD
    have houterD : LoopOuterRel clonedDefs off ρ₁ ρ₂d := by
      intro z hz hnc
      have hzn : z ∉ dispParams := fun hm =>
        Nat.not_lt.2 (Nat.le_trans (Nat.le_mul_of_pos_left off Nat.zero_lt_two) (mem_map_add_range_ge hm)) hz
      rw [hpresD z hzn]; exact houter z hz hnc
    have hdispBlk := buildVersioned_blocks_disp F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hhB
    have hslowHopBlk := buildVersioned_blocks_slowHop F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hhB
    have hfastHopBlk := buildVersioned_blocks_fastHop F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hhB
    have htestRegsNe : testRegs ≠ [] := by
      intro hemp
      simp only [testRegs, List.append_eq_nil_iff, List.map_eq_nil_iff] at hemp
      simp [hemp.1, hemp.2] at hnonEmpty
    have htestRegsOk : ∀ r ∈ testRegs, r < andBase ∧ ρ₂d[r]?.isSome = true := by
      intro r hr
      simp only [testRegs, List.mem_append, List.mem_map] at hr
      rcases hr with hrOut | ⟨i, hiMem, rfl⟩
      · have h1 := (List.all_eq_true.1 houterOk) r hrOut
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h1
        obtain ⟨⟨hFpar, hrLt⟩, hrNc⟩ := h1
        have hFmem : r ∈ F.params := by simpa using hFpar
        refine ⟨Nat.lt_of_lt_of_le hrLt (Nat.le_trans (Nat.le_trans
          (Nat.le_mul_of_pos_left off Nat.zero_lt_two) (Nat.le_add_right _ _)) (Nat.le_max_left _ _)), ?_⟩
        rw [houterD r hrLt hrNc]; exact hpd1 r hFmem
      · have htiLt : i < hBlk.params.length := by
          rw [hhB] at htestOk
          have := (List.all_eq_true.1 htestOk) i hiMem
          simpa using this
        have hget : dispParams[i]? = some (2 * off + i) := by
          simp [dispParams, List.getElem?_range htiLt]
        have hvsLen : i < vs.length := by have := bindParams_len_eq hbp; omega
        obtain ⟨vi, hvi⟩ : ∃ v, vs[i]? = some v := ⟨vs[i], List.getElem?_eq_getElem hvsLen⟩
        rw [hget]; dsimp only [Option.getD_some]
        refine ⟨Nat.lt_of_lt_of_le (Nat.add_lt_add_left htiLt _) (Nat.le_max_left _ _), ?_⟩
        rw [bindParams_nodup_getElem? hdispNd hbpD hget hvi]; rfl
    have hstep1_q : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ :: rest₂ }
        ⟨fi, uLbl, uPos, ρ₂fr, d₂⟩ rest₂ ρ₂ eQ =
        .next { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, 0, ρ₂d, d₂⟩ :: rest₂ } b := by
      rw [← hchg1, ← heQtgt]; exact takeEdge_ok hev2 (heQtgt ▸ hdispBlk) hbpD
    let dispB : Block :=
      { params := dispParams
        body := (buildDispAndChain testRegs andBase).1.toArray
        term := .br .tnz .w64 (.v (buildDispAndChain testRegs andBase).2) (.imm 1)
          { target := verFastHop h nodes, args := [] }
          { target := verSlowHop h nodes, args := [] }
        cold := hBlk.cold }
    have hdispBlk' : F'.blocks[verDisp h nodes]? = some dispB := hdispBlk
    obtain ⟨ρ₂e, vTest, hstarBody, hpresE, htestVal⟩ :=
      step_dispBody (regs := testRegs) (andBase := andBase) (bound := 2 * off + hBlk.params.length)
        hqfi hdispBlk' htestRegsNe (by simp [dispB]) (Nat.le_max_left _ _) htestRegsOk
    have hevE : evalArgs ρ₂e (dispParams.map .v) = some vs := by
      have heqArgs : evalArgs ρ₂e (dispParams.map .v) = evalArgs ρ₂d (dispParams.map .v) := by
        have hgo : ∀ (ps : List VReg), (∀ z ∈ ps, z < 2 * off + hBlk.params.length) →
            evalArgs ρ₂e (ps.map .v) = evalArgs ρ₂d (ps.map .v) := by
          intro ps hps
          induction ps with
          | nil => rfl
          | cons z zs ih =>
              have hz : ρ₂e[z]? = ρ₂d[z]? := hpresE z (hps z (by simp))
              have ih' : List.mapM (Arg.eval ρ₂e) (zs.map Arg.v) =
                  List.mapM (Arg.eval ρ₂d) (zs.map Arg.v) :=
                ih (fun w hw => hps w (by simp [hw]))
              simp only [evalArgs, List.map_cons, List.mapM_cons, Arg.eval, hz, ih']
        exact hgo dispParams (fun z hz => by
          simp only [dispParams, List.mem_map, List.mem_range] at hz
          obtain ⟨k, hk, rfl⟩ := hz; exact Nat.add_lt_add_left hk _)
      rw [heqArgs, hevD]
    have houterE : LoopOuterRel clonedDefs off ρ₁ ρ₂e := by
      intro z hz hnc
      rw [hpresE z (Nat.lt_of_lt_of_le hz (Nat.le_trans
        (Nat.le_mul_of_pos_left off Nat.zero_lt_two) (Nat.le_add_right _ _)))]
      exact houterD z hz hnc
    cases hcond : Cond.tnz.holds .w64 vTest 1 with
    | true =>
        -- Fast path: `disp (body) → fastHop (0) → fastNodeBase (0)`!
        have hstep2_q : step q { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ } =
            .next { mem := mem, ctx := ctx, stack := ⟨fi, verFastHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ } false := by
          unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hdispBlk']; dsimp only
          simp only [Nat.lt_irrefl, ↓reduceDIte, dispB, Arg.eval, htestVal, hcond, ↓reduceIte]
          have hfwd2 : decide (verFastHop h nodes ≤ verDisp h nodes) = false :=
            decide_eq_false (by unfold verFastHop verDisp; omega)
          rw [← hfwd2]
          exact takeEdge_ok (F := F') (s := { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ })
            (fr := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩) (rest := rest₂) (ρ := ρ₂e)
            (e := { target := verFastHop h nodes, args := [] }) rfl hfastHopBlk rfl
        have hfastNode0 := buildVersioned_blocks_fastNode F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hh0 hhB
        simp only [Nat.add_zero] at hfastNode0
        obtain ⟨ρ₂', hbp2, hcopy1⟩ := houterE.toCopyLeaf (c := 1) |>.bindParams_defs hparDefs hbp
        have hcopyH : LoopCopyRel clonedDefs off 1 (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
          hcopy1.mono fun x hx => by rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
        have hstep3_q : step q { mem := mem, ctx := ctx, stack := ⟨fi, verFastHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ } =
            .next { mem := mem, ctx := ctx, stack := ⟨fi, verFastNodeBase h nodes nonLeafExits, 0, ρ₂', d₂⟩ :: rest₂ } false := by
          unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hfastHopBlk]
          simp only [Array.size_empty, Nat.not_lt_zero, ↓reduceDIte]
          have hfwd3 : decide (verFastNodeBase h nodes nonLeafExits ≤ verFastHop h nodes) = false :=
            decide_eq_false (by unfold verFastNodeBase verFastHop; omega)
          rw [← hfwd3]
          exact takeEdge_ok (F := F') (s := { mem := mem, ctx := ctx, stack := ⟨fi, verFastHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ })
            (fr := ⟨fi, verFastHop h nodes, 0, ρ₂e, d₂⟩) (rest := rest₂) (ρ := ρ₂e)
            (e := { target := verFastNodeBase h nodes nonLeafExits, args := dispParams.map .v })
            hevE hfastNode0 hbp2
        refine ⟨b.toNat, { mem := mem, ctx := ctx, stack := ⟨fi, verFastNodeBase h nodes nonLeafExits, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
        have hstar23 : Sem.Star (semStep q)
            { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ } 0
            { mem := mem, ctx := ctx, stack := ⟨fi, verFastNodeBase h nodes nonLeafExits, 0, ρ₂', d₂⟩ :: rest₂ } :=
          Sem.Star.free (by rw [semStep_next]; exact hstep2_q) (star_of_step hstep3_q)
        have hstar := ((star_of_step (hst.trans hstep1_q)).trans hstarBody).trans hstar23
        refine ⟨by simpa using hstar, Nat.le_refl _, ⟨rfl, rfl, .cons ?_ hrest⟩⟩
        simpa using VersionFrameRel.loopNode (F := F) (fi := fi) (h := h)
          (nodes := nodes) (leafExits := leafExits) (nonLeafExits := nonLeafExits)
          (off := off) (availMap := availMap) (isTop := true)
          (b := h) (idx := 0) (c := 1) (pos := 0) (d₁ := d₁) (d₂ := d₂)
          (by omega) hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyH)
    | false =>
        -- Slow path: `disp (body) → slowHop (0) → h (1)`!
        have hstep2_q : step q { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ } =
            .next { mem := mem, ctx := ctx, stack := ⟨fi, verSlowHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ } false := by
          unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hdispBlk']; dsimp only
          simp only [Nat.lt_irrefl, ↓reduceDIte, dispB, Arg.eval, htestVal, hcond, Bool.false_eq_true, ↓reduceIte]
          have hfwd2 : decide (verSlowHop h nodes ≤ verDisp h nodes) = false :=
            decide_eq_false (by unfold verSlowHop verDisp; omega)
          rw [← hfwd2]
          exact takeEdge_ok (F := F') (s := { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ })
            (fr := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩) (rest := rest₂) (ρ := ρ₂e)
            (e := { target := verSlowHop h nodes, args := [] }) rfl hslowHopBlk rfl
        have hslowH := buildVersioned_blocks_prefix_node F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
          hh_lt_cut ((natSet_ofList_contains nodes h).2 (List.mem_of_getElem? hh0)) hhB
        obtain ⟨ρ₂', hbp2, hcopy0⟩ := houterE.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
        have hbp2' : bindParams ρ₂e hBlk.params vs = some ρ₂' := by
          have hmap : hBlk.params.map (loopMapReg clonedDefs off 0) = hBlk.params := by
            induction hBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
          rwa [hmap] at hbp2
        have hcopyH : LoopCopyRel clonedDefs off 0 (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
          hcopy0.mono fun x hx => by rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
        have hstep3_q : step q { mem := mem, ctx := ctx, stack := ⟨fi, verSlowHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ } =
            .next { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ } true := by
          unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hslowHopBlk]
          simp only [Array.size_empty, Nat.not_lt_zero, ↓reduceDIte]
          have hback3 : decide (h ≤ verSlowHop h nodes) = true :=
            decide_eq_true (by unfold verSlowHop; exact Nat.le_trans (Nat.le_of_lt hh_lt_cut) (Nat.le_succ _))
          rw [← hback3]
          exact takeEdge_ok (F := F') (s := { mem := mem, ctx := ctx, stack := ⟨fi, verSlowHop h nodes, 0, ρ₂e, d₂⟩ :: rest₂ })
            (fr := ⟨fi, verSlowHop h nodes, 0, ρ₂e, d₂⟩) (rest := rest₂) (ρ := ρ₂e)
            (e := { target := h, args := dispParams.map .v })
            hevE hslowH hbp2'
        refine ⟨b.toNat + 1, { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
        have hstar23 : Sem.Star (semStep q)
            { mem := mem, ctx := ctx, stack := ⟨fi, verDisp h nodes, dispB.body.size, ρ₂e, d₂⟩ :: rest₂ } 1
            { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ } :=
          Sem.Star.free (by rw [semStep_next]; exact hstep2_q) (star_of_step hstep3_q)
        have hstar := ((star_of_step (hst.trans hstep1_q)).trans hstarBody).trans hstar23
        refine ⟨by simpa using hstar, by omega, ⟨rfl, rfl, .cons ?_ hrest⟩⟩
        simpa using VersionFrameRel.loopNode (F := F) (fi := fi) (h := h)
          (nodes := nodes) (leafExits := leafExits) (nonLeafExits := nonLeafExits)
          (off := off) (availMap := availMap) (isTop := true)
          (b := h) (idx := 0) (c := 0) (pos := 0) (d₁ := d₁) (d₂ := d₂)
          (by omega) hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyH)
  -- Helper 1: matching a `ret` to suspended caller frame `(rest₁, rest₂)`
  have matchRet : ∀ (mem : X86.Memory) (ctx : Word) (rest₁ rest₂ : List Frame)
      (vs : List Word) (s₁' : State) (b : Bool),
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap false rest₁ rest₂ →
      (match rest₁ with
       | [] => Step.done vs mem
       | c :: rest' =>
           match bindParams c.env c.dsts vs with
           | some ρ => Step.next { mem := mem, ctx := ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
           | none => Step.stuck) = .next s₁' b →
      ∃ s₂',
        (match rest₂ with
         | [] => Step.done vs mem
         | c :: rest' =>
             match bindParams c.env c.dsts vs with
             | some ρ => Step.next { mem := mem, ctx := ctx, stack := { c with env := ρ, dsts := [] } :: rest' } false
             | none => Step.stuck) = .next s₂' b ∧
        VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁' s₂' := by
    intro mem ctx rest₁ rest₂ vs s₁' b hrest hret
    cases hrest with
    | nil => cases hret
    | @cons _ fr0 fr0₂ rest₁' rest₂' hcf hrr =>
        dsimp only at hret ⊢
        cases hcf with
        | other hne =>
            cases hbp : bindParams fr0.env fr0.dsts vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                exact ⟨_, rfl, ⟨rfl, rfl, .cons (.other hne) hrr⟩⟩
        | @outside b0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 hB0 hnn hnl hpos0 hdst houter =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨ρ₂', hbp2, houter'⟩ := houter.bindParams_same hbp
                rw [hdst rfl, hbp2]
                exact ⟨_, rfl, ⟨rfl, rfl, .cons (.outside hB0 hnn hnl hpos0 (fun hc => by cases hc) houter') hrr⟩⟩
        | @loopNode b0 idx0 c0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 av0 hc2 hidx0 hB0 hav0 hpos0 hcall0 hcopy =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨hposGt, hd2eq, hddefs, g0, as0, hcallAt⟩ := hcall0 rfl
                obtain ⟨ρ₂', hbp2, hcopy'⟩ := hcopy.bindParams_defs hddefs hbp
                rw [hd2eq, hbp2]
                have hposPred : pos0 - 1 < blk0.body.size := by omega
                have hposEq : pos0 - 1 + 1 = pos0 := by omega
                have hstEq : blk0.body[pos0 - 1]'hposPred = .call d₁ g0 as0 :=
                  (Array.getElem?_eq_some_iff.1 hcallAt).2
                have havStep : d₁.foldl (fun a x => a.insert x) (availAtPos av0 blk0.body (pos0 - 1)) =
                    availAtPos av0 blk0.body pos0 := by
                  rw [← hposEq, availAtPos_succ av0 blk0.body hposPred, hstEq]; rfl
                simp only [Bool.false_eq_true, ↓reduceIte] at hcopy'
                rw [havStep] at hcopy'
                exact ⟨_, rfl, ⟨rfl, rfl, .cons (.loopNode hc2 hidx0 hB0 hav0 hpos0 (fun hc => by cases hc)
                  (by simpa using hcopy')) hrr⟩⟩
        | @leafExit b0 eidx0 c0 pos0 ρ₁ ρ₂ d₁ d₂ blk0 av0 hc2 heidx0 hB0 hav0 hpos0 hcall0 hcopy =>
            cases hbp : bindParams ρ₁ d₁ vs with
            | none => rw [hbp] at hret; cases hret
            | some ρ₁' =>
                rw [hbp] at hret; simp only [Step.next.injEq] at hret; obtain ⟨rfl, rfl⟩ := hret
                obtain ⟨hposGt, hd2eq, hddefs, g0, as0, hcallAt⟩ := hcall0 rfl
                obtain ⟨ρ₂', hbp2, hcopy'⟩ := hcopy.bindParams_defs hddefs hbp
                rw [hd2eq, hbp2]
                have hposPred : pos0 - 1 < blk0.body.size := by omega
                have hposEq : pos0 - 1 + 1 = pos0 := by omega
                have hstEq : blk0.body[pos0 - 1]'hposPred = .call d₁ g0 as0 :=
                  (Array.getElem?_eq_some_iff.1 hcallAt).2
                have havStep : d₁.foldl (fun a x => a.insert x) (availAtPos av0 blk0.body (pos0 - 1)) =
                    availAtPos av0 blk0.body pos0 := by
                  rw [← hposEq, availAtPos_succ av0 blk0.body hposPred, hstEq]; rfl
                simp only [Bool.false_eq_true, ↓reduceIte] at hcopy'
                rw [havStep] at hcopy'
                exact ⟨_, rfl, ⟨rfl, rfl, .cons (.leafExit hc2 heidx0 hB0 hav0 hpos0 (fun hc => by cases hc)
                  (by simpa using hcopy')) hrr⟩⟩
  -- Helper 2: outside block `takeEdge` matching in `F'` (via `dispDispatch` when entering `h`)
  have outsideTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (u pos : Nat) (blk : Block)
      (ρ₁ ρ₂ ρ₂fr : Env) (d₁ d₂ : List VReg) (rest₁ rest₂ : List Frame) (e : Edge) (s₁' : State) (b : Bool),
      F.blocks[u]? = some blk →
      u ∉ nodes → u ∉ leafExits →
      e ∈ blk.term.edges →
      LoopOuterRel clonedDefs off ρ₁ ρ₂ →
      (∀ r ∈ F.params, ρ₁[r]?.isSome = true) →
      (∀ a ∈ e.args, listLt off a.uses = true) →
      (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false) →
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap false rest₁ rest₂ →
      takeEdge F { mem := mem, ctx := ctx, stack := ⟨fi, u, pos, ρ₁, d₁⟩ :: rest₁ }
        ⟨fi, u, pos, ρ₁, d₁⟩ rest₁ ρ₁ e = .next s₁' b →
      ∃ cStep s₂',
        step q { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ :: rest₂ } =
          takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ :: rest₂ }
            ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
            { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target } →
        Sem.Star (semStep q) { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ :: rest₂ } cStep s₂' ∧
        b.toNat ≤ cStep ∧
        VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁' s₂' := by
    intro mem ctx u pos blk ρ₁ ρ₂ ρ₂fr d₁ d₂ rest₁ rest₂ e s₁' b hB hun hul he houter hpd1 heargs henc hrest hte
    have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
    obtain ⟨heNode, heLeaf⟩ := hf.outside_edges u huLt hun blk hB e he
    unfold takeEdge at hte
    cases hev : evalArgs ρ₁ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hftgt : F.blocks[e.target]? with
        | none => rw [hev, hftgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hftgt] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                have hev2 : evalArgs ρ₂ e.args = some vs := by
                  rw [outer_evalArgs houter heargs henc, hev]
                by_cases hth : e.target = h
                · -- Entering loop header `h` via multi-operand odd-fixnum dispatch `u_q → disp → fastHop/slowHop → fastNodeBase/h`!
                  obtain ⟨hBlk, avH, hhB, havH, havHsub⟩ := hf.avail_h
                  obtain rfl : hBlk = tgtB := Option.some.inj (hhB.symm.trans (hth ▸ hftgt))
                  have hdir := hpredDir u huLt hun blk hB e he hth
                  have hchg1 : decide (verDisp h nodes ≤ verRemapOrig h nodes leafExits nonLeafExits u) =
                      decide (e.target ≤ u) := by
                    rw [hth]; unfold verDisp verRemapOrig
                    rcases hdir with hlt | hge
                    · have huc : u < verCut h nodes := Nat.lt_trans hlt hh_lt_cut
                      simp only [huc, ↓reduceIte, decide_eq_decide]
                      exact ⟨fun h1 => absurd (Nat.lt_of_lt_of_le huc h1) (Nat.lt_irrefl _),
                        fun h1 => absurd (Nat.lt_of_le_of_lt h1 hlt) (Nat.lt_irrefl _)⟩
                    · have hnu : ¬ u < verCut h nodes := Nat.not_lt_of_ge hge
                      simp only [hnu, ↓reduceIte, decide_eq_decide]
                      exact ⟨fun _ => Nat.le_trans (Nat.le_of_lt hh_lt_cut) hge,
                        fun _ => Nat.le_trans hge (Nat.le_add_right _ _)⟩
                  have hremOut : verRemapOutside h nodes leafExits nonLeafExits e.target = verDisp h nodes := by
                    simp [verRemapOutside, hth]
                  obtain ⟨cStep, s₂', hgo⟩ := dispDispatch mem ctx ρ₁ ρ₁' ρ₂ d₁ d₂ rest₁ rest₂ vs hBlk avH
                    (verRemapOrig h nodes leafExits nonLeafExits u) pos ρ₂fr
                    { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target } (decide (e.target ≤ u))
                    hhB havH havHsub hbp houter hpd1 hrest hev2 hremOut hchg1
                  refine ⟨cStep, s₂', fun hst => ?_⟩
                  obtain ⟨hstar, hle, hrel'⟩ := hgo hst
                  exact ⟨hstar, hle, by rw [hth]; exact hrel'⟩
                · -- Non-header outside target (`e.target ≠ h`)
                  have htnn : e.target ∉ nodes := by
                    rcases heNode with hnn | heq
                    · exact hnn
                    · exact absurd heq hth
                  have hremOut : verRemapOutside h nodes leafExits nonLeafExits e.target =
                      verRemapOrig h nodes leafExits nonLeafExits e.target := by
                    have hneB : (e.target == h) = false := beq_false_of_ne hth
                    simp [verRemapOutside, hneB]
                  have htgt2 : ∃ tgtB', F'.blocks[verRemapOrig h nodes leafExits nonLeafExits e.target]? = some tgtB' ∧
                      tgtB'.params = tgtB.params := by
                    unfold verRemapOrig
                    by_cases hlt : e.target < verCut h nodes
                    · simp only [hlt, ↓reduceIte]
                      exact ⟨_, buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                        hlt ((natSet_ofList_contains_false nodes e.target).2 htnn) hftgt, rfl⟩
                    · simp only [hlt, ↓reduceIte]
                      exact ⟨_, buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                        (Nat.le_of_not_lt hlt) hftgt, rfl⟩
                  obtain ⟨tgtB', htgt2', hpar2⟩ := htgt2
                  have hchg := verRemapOrig_le_iff h nodes leafExits nonLeafExits u e.target
                  by_cases htl : e.target ∈ leafExits
                  · obtain ⟨eidx, _, heidx⟩ := mem_listIndexOf htl
                    obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := heLeaf htl
                    obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                    have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                      (collectBlocksDefs_mem (List.mem_append_right _ htl) htB).1
                    obtain ⟨ρ₂', hbp2, hcopy0⟩ := houter.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
                    have hbp2' : bindParams ρ₂ tBlk.params vs = some ρ₂' := by
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      rwa [hmap] at hbp2
                    have hcopyT : LoopCopyRel clonedDefs off 0 (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                      hcopy0.mono fun x hx => by rw [natSet_contains_foldl_insert]; exact .inl (havTsub x hx)
                    refine ⟨(decide (e.target ≤ u)).toNat, { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits e.target, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ :: rest₂ }
                        ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                        { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits e.target, 0, ρ₂', d₂⟩ :: rest₂ }
                          (decide (e.target ≤ u)) := by
                      rw [hremOut, ← hchg]; exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2')
                    exact ⟨star_of_step (hst.trans hte2), Nat.le_refl _,
                      ⟨rfl, rfl, .cons (.leafExit (c := 0) (by omega) heidx htB havT (Nat.zero_le _) (fun hc => by cases hc)
                        (by simpa using hcopyT)) hrest⟩⟩
                  · obtain ⟨ρ₂', hbp2, houter'⟩ := houter.bindParams_same hbp
                    refine ⟨(decide (e.target ≤ u)).toNat, { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits e.target, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ :: rest₂ }
                        ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                        { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits e.target, 0, ρ₂', d₂⟩ :: rest₂ }
                          (decide (e.target ≤ u)) := by
                      rw [hremOut, ← hchg]; exact takeEdge_ok hev2 htgt2' (by rw [hpar2]; exact hbp2)
                    exact ⟨star_of_step (hst.trans hte2), Nat.le_refl _,
                      ⟨rfl, rfl, .cons (.outside hftgt htnn htl (Nat.zero_le _) (fun hc => by cases hc) houter') hrest⟩⟩
  -- Helper 3: loop-node `takeEdge` matching in `F'` (`c = 0`: slow copy; `c = 1`: fast copy)
  have loopNodeTakeEdge : ∀ (mem : X86.Memory) (ctx : Word) (u idx c pos : Nat) (blk : Block) (av2 : Src.NatSet)
      (ρ₁ ρ₂ ρ₂fr : Env) (d₁ d₂ : List VReg) (rest₁ rest₂ : List Frame) (e : Edge) (s₁' : State) (b : Bool),
      c < 2 →
      nodes[idx]? = some u →
      F.blocks[u]? = some blk →
      e ∈ blk.term.edges →
      (∀ e' ∈ blk.term.edges, ((e'.target ∈ nodes ∧ e'.target ≠ h) ∨ e'.target ∈ leafExits) →
        ∃ tBlk avT, F.blocks[e'.target]? = some tBlk ∧ availMap[e'.target]? = some avT ∧
          ∀ x, avT.contains x = true → av2.contains x = true ∨ x ∈ tBlk.params) →
      LoopCopyRel clonedDefs off c av2 ρ₁ ρ₂ →
      (∀ r ∈ F.params, ρ₁[r]?.isSome = true) →
      (∀ a ∈ e.args, listLt off a.uses = true) →
      (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false ∨ av2.contains x = true) →
      VersionStackRel F fi h nodes leafExits nonLeafExits off availMap false rest₁ rest₂ →
      takeEdge F { mem := mem, ctx := ctx, stack := ⟨fi, u, pos, ρ₁, d₁⟩ :: rest₁ }
        ⟨fi, u, pos, ρ₁, d₁⟩ rest₁ ρ₁ e = .next s₁' b →
      let qLbl := if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx
      let qRemap := if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                    else verRemapFastTarget h nodes leafExits nonLeafExits
      let qEdge : Edge := { target := qRemap e.target, args := e.args.map (loopMapArg clonedDefs off c) }
      ∃ cStep s₂',
        step q { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ } =
          takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ }
            ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ rest₂ ρ₂ qEdge →
        Sem.Star (semStep q) { mem := mem, ctx := ctx, stack := ⟨fi, qLbl, pos, ρ₂fr, d₂⟩ :: rest₂ } cStep s₂' ∧
        b.toNat ≤ cStep ∧
        VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁' s₂' := by
    intro mem ctx u idx c pos blk av2 ρ₁ ρ₂ ρ₂fr d₁ d₂ rest₁ rest₂ e s₁' b hc2 hidx hB he havEdges hcopy hpd1 heargs heav hrest hte
    have huMem : u ∈ nodes := List.mem_of_getElem? hidx
    have huCut : u < cut := hf.node_lt_cut huMem
    have hidxLt : idx < nodes.length := (List.getElem?_eq_some_iff.1 hidx).1
    unfold takeEdge at hte
    cases hev : evalArgs ρ₁ e.args with
    | none => rw [hev] at hte; cases hte
    | some vs =>
        cases hftgt : F.blocks[e.target]? with
        | none => rw [hev, hftgt] at hte; cases hte
        | some tgtB =>
            rw [hev, hftgt] at hte; dsimp only at hte
            cases hbp : bindParams ρ₁ tgtB.params vs with
            | none => rw [hbp] at hte; cases hte
            | some ρ₁' =>
                rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                have hev2 : evalArgs ρ₂ (e.args.map (loopMapArg clonedDefs off c)) = some vs := by
                  rw [loopMapArgs_eval hcopy heargs heav, hev]
                rcases hf.node_edges u huMem blk hB e he with hth | ⟨htn, hult⟩ | ⟨htl, hult⟩ | htnl
                · -- Back-edge `e.target = h`: `c = 0` jumps to `h`; `c = 1` re-dispatches via `verDisp`!
                  have hh_le_u : h ≤ u := hf.h_le_node huMem
                  have hbp1 : decide (e.target ≤ u) = true := by rw [hth]; simp [hh_le_u]
                  obtain ⟨hBlk, avH, hhB, havH, havHsub⟩ := hf.avail_h
                  obtain rfl : hBlk = tgtB := Option.some.inj (hhB.symm.trans (hth ▸ hftgt))
                  by_cases hc0 : c = 0
                  · subst hc0
                    have hparDefs : ∀ d ∈ hBlk.params, clonedDefs.contains d = true :=
                      (collectBlocksDefs_mem (List.mem_append_left _ (List.mem_of_getElem? hh0)) hhB).1
                    obtain ⟨ρ₂', hbp2, hcopyN⟩ := hcopy.1.toCopyLeaf (c := 0) |>.bindParams_defs hparDefs hbp
                    have hcopyH : LoopCopyRel clonedDefs off 0 (availAtPos avH hBlk.body 0) ρ₁' ρ₂' :=
                      hcopyN.mono fun x hx => by rw [natSet_contains_foldl_insert]; exact .inl (havHsub x hx)
                    have hrem : verRemapSlowTarget h nodes leafExits nonLeafExits e.target = h := by
                      simp [verRemapSlowTarget, hth]
                    have hmap : hBlk.params.map (loopMapReg clonedDefs off 0) = hBlk.params := by
                      induction hBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                    have hB' := buildVersioned_blocks_prefix_node F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                      hh_lt_cut ((natSet_ofList_contains nodes h).2 (List.mem_of_getElem? hh0)) hhB
                    have hback : decide (h ≤ u) = true := by simp [hh_le_u]
                    refine ⟨1, { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                    simp only [↓reduceIte] at hst ⊢
                    have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, u, pos, ρ₂fr, d₂⟩ :: rest₂ }
                        ⟨fi, u, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                        { target := verRemapSlowTarget h nodes leafExits nonLeafExits e.target,
                          args := e.args.map (loopMapArg clonedDefs off 0) } =
                        .next { mem := mem, ctx := ctx, stack := ⟨fi, h, 0, ρ₂', d₂⟩ :: rest₂ } true := by
                      rw [hrem, ← hback]; exact takeEdge_ok hev2 hB' (by simpa [hmap] using hbp2)
                    refine ⟨star_of_step (hst.trans hte2), by simp [hbp1], ⟨rfl, rfl, .cons ?_ hrest⟩⟩
                    rw [hth]
                    simpa using VersionFrameRel.loopNode (F := F) (fi := fi) (h := h)
                      (nodes := nodes) (leafExits := leafExits) (nonLeafExits := nonLeafExits)
                      (off := off) (availMap := availMap) (isTop := true)
                      (b := h) (idx := 0) (c := 0) (pos := 0) (d₁ := d₁) (d₂ := d₂)
                      (by omega) hh0 hhB havH (Nat.zero_le _) (fun hc => by cases hc) (by simpa using hcopyH)
                  · have hc1 : c = 1 := by omega
                    subst hc1
                    simp only [Nat.one_ne_zero, ↓reduceIte]
                    have hremF : verRemapFastTarget h nodes leafExits nonLeafExits e.target = verDisp h nodes := by
                      simp [verRemapFastTarget, hth]
                    have hchgF : decide (verDisp h nodes ≤ verFastNodeBase h nodes nonLeafExits + idx) = true :=
                      decide_eq_true (by unfold verDisp verFastNodeBase; omega)
                    obtain ⟨cStep, s₂', hgo⟩ := dispDispatch mem ctx ρ₁ ρ₁' ρ₂ d₁ d₂ rest₁ rest₂ vs hBlk avH
                      (verFastNodeBase h nodes nonLeafExits + idx) pos ρ₂fr
                      { target := verRemapFastTarget h nodes leafExits nonLeafExits e.target,
                        args := e.args.map (loopMapArg clonedDefs off 1) } true
                      hhB havH havHsub hbp hcopy.1 hpd1 hrest hev2 hremF hchgF
                    refine ⟨cStep, s₂', fun hst => ?_⟩
                    obtain ⟨hstar, hle, hrel'⟩ := hgo hst
                    exact ⟨hstar, by rw [hbp1]; exact hle, by rw [hth]; exact hrel'⟩
                · -- Forward internal edge `e.target ∈ nodes ∧ u < e.target` (`0 ≤ 0`)!
                  have ht_ne_h : e.target ≠ h := Nat.ne_of_gt (Nat.lt_of_le_of_lt (hf.h_le_node huMem) hult)
                  have hbp0 : decide (e.target ≤ u) = false := decide_eq_false (Nat.not_le.2 hult)
                  obtain ⟨idx', hidx'Of, hidx'⟩ := mem_listIndexOf htn
                  have hidx_lt : idx < idx' := by
                    by_cases hle : idx' ≤ idx
                    · cases Nat.eq_or_lt_of_le hle with
                      | inl heq => subst heq; rw [hidx] at hidx'; cases hidx'; omega
                      | inr hlt => have := isStrictlySorted_lt hf.nodes_sorted hidx' hidx hlt; omega
                    · omega
                  have htCut : e.target < cut := hf.node_lt_cut htn
                  obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := havEdges e he (.inl ⟨htn, ht_ne_h⟩)
                  obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                  have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_left _ htn) htB).1
                  obtain ⟨ρ₂', hbp2, hcopy1⟩ := hcopy.bindParams_defs hparDefs hbp
                  have hcopyT : LoopCopyRel clonedDefs off c (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                    hcopy1.mono fun x hx => by
                      rw [natSet_contains_foldl_insert]
                      rcases havTsub x hx with h1 | h2
                      · exact .inr h1
                      · exact .inl h2
                  have hrem : (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                      else verRemapFastTarget h nodes leafExits nonLeafExits) e.target =
                      if c = 0 then e.target else verFastNodeBase h nodes nonLeafExits + idx' := by
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hmemB : (Src.NatSet.ofList nodes).contains e.target = true := (natSet_ofList_contains nodes e.target).2 htn
                    by_cases hc0 : c = 0 <;> simp [hc0, verRemapSlowTarget, verRemapFastTarget, hneB, hmemB, hidx'Of]
                  have htgt2 : ∃ B', F'.blocks[if c = 0 then e.target else verFastNodeBase h nodes nonLeafExits + idx']? = some B' ∧
                      B'.params = tBlk.params.map (loopMapReg clonedDefs off c) := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte]
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      exact ⟨_, buildVersioned_blocks_prefix_node F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                        htCut ((natSet_ofList_contains nodes e.target).2 htn) htB, hmap.symm⟩
                    · have hc1 : c = 1 := by omega
                      subst hc1; simp only [Nat.one_ne_zero, ↓reduceIte]
                      exact ⟨_, buildVersioned_blocks_fastNode F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hidx' htB, rfl⟩
                  obtain ⟨B', hB', hpar'⟩ := htgt2
                  have hfwd : decide ((if c = 0 then e.target else verFastNodeBase h nodes nonLeafExits + idx') ≤
                      (if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx)) = false := by
                    by_cases hc0 : c = 0 <;> simp [hc0] <;> omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then e.target else verFastNodeBase h nodes nonLeafExits + idx', 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits else verRemapFastTarget h nodes leafExits nonLeafExits) e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then e.target else verFastNodeBase h nodes nonLeafExits + idx', 0, ρ₂', d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd]; exact takeEdge_ok hev2 hB' (by rw [hpar']; exact hbp2)
                  exact ⟨star_of_step (hst.trans hte2), by simp [hbp0],
                    ⟨rfl, rfl, .cons (.loopNode hc2 hidx' htB havT (Nat.zero_le _) (fun hc => by cases hc)
                      (by simpa using hcopyT)) hrest⟩⟩
                · -- Forward exit to `e.target ∈ leafExits` (`0 ≤ 0`)!
                  have htnn : e.target ∉ nodes := (hf.leaf_ok e.target htl).2.2
                  have ht_ne_h : e.target ≠ h := fun heq => htnn (heq ▸ List.mem_of_getElem? hh0)
                  have htnnl : e.target ∉ nonLeafExits := fun hm => (hf.nonLeaf_ok e.target hm).2.2.2 htl
                  have hbp0 : decide (e.target ≤ u) = false := by simp; omega
                  obtain ⟨eidx, heidxOf, heidx⟩ := mem_listIndexOf htl
                  obtain ⟨tBlk, avT, htB, havT, havTsub⟩ := havEdges e he (.inr htl)
                  obtain rfl : tBlk = tgtB := Option.some.inj (htB.symm.trans hftgt)
                  have hparDefs : ∀ d ∈ tBlk.params, clonedDefs.contains d = true :=
                    (collectBlocksDefs_mem (List.mem_append_right _ htl) htB).1
                  obtain ⟨ρ₂', hbp2, hcopy1⟩ := hcopy.bindParams_defs hparDefs hbp
                  have hcopyT : LoopCopyRel clonedDefs off c (availAtPos avT tBlk.body 0) ρ₁' ρ₂' :=
                    hcopy1.mono fun x hx => by
                      rw [natSet_contains_foldl_insert]
                      rcases havTsub x hx with h1 | h2
                      · exact .inr h1
                      · exact .inl h2
                  have hrem : (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                      else verRemapFastTarget h nodes leafExits nonLeafExits) e.target =
                      if c = 0 then verRemapOrig h nodes leafExits nonLeafExits e.target
                      else verFastExitBase h nodes nonLeafExits + eidx := by
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hnnB : (Src.NatSet.ofList nodes).contains e.target = false := (natSet_ofList_contains_false nodes e.target).2 htnn
                    have hnlNone : listIndexOf nonLeafExits e.target = none := listIndexOf_none_of_not_mem htnnl
                    by_cases hc0 : c = 0 <;> simp [hc0, verRemapSlowTarget, verRemapFastTarget, hneB, hnnB, hnlNone, heidxOf]
                  have htgt2 : ∃ B', F'.blocks[if c = 0 then verRemapOrig h nodes leafExits nonLeafExits e.target
                        else verFastExitBase h nodes nonLeafExits + eidx]? = some B' ∧
                      B'.params = tBlk.params.map (loopMapReg clonedDefs off c) := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte]
                      have hmap : tBlk.params.map (loopMapReg clonedDefs off 0) = tBlk.params := by
                        induction tBlk.params with | nil => rfl | cons x r ih => simp [loopMapReg_zero', ih]
                      unfold verRemapOrig
                      by_cases hlt : e.target < verCut h nodes
                      · simp only [hlt, ↓reduceIte]
                        exact ⟨_, buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                          hlt ((natSet_ofList_contains_false nodes e.target).2 htnn) htB, hmap.symm⟩
                      · simp only [hlt, ↓reduceIte]
                        exact ⟨_, buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                          (Nat.le_of_not_lt hlt) htB, hmap.symm⟩
                    · have hc1 : c = 1 := by omega
                      subst hc1; simp only [Nat.one_ne_zero, ↓reduceIte]
                      exact ⟨_, buildVersioned_blocks_fastExit F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off heidx htB, rfl⟩
                  obtain ⟨B', hB', hpar'⟩ := htgt2
                  have hfwd : decide ((if c = 0 then verRemapOrig h nodes leafExits nonLeafExits e.target
                        else verFastExitBase h nodes nonLeafExits + eidx) ≤
                      (if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx)) = false := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [↓reduceIte, decide_eq_false_iff_not, verRemapOrig]
                      split <;> omega
                    · simp only [hc0, ↓reduceIte, decide_eq_false_iff_not, verFastExitBase, verFastNodeBase]; omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then verRemapOrig h nodes leafExits nonLeafExits e.target
                          else verFastExitBase h nodes nonLeafExits + eidx, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte2 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits else verRemapFastTarget h nodes leafExits nonLeafExits) e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then verRemapOrig h nodes leafExits nonLeafExits e.target
                          else verFastExitBase h nodes nonLeafExits + eidx, 0, ρ₂', d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd]; exact takeEdge_ok hev2 hB' (by rw [hpar']; exact hbp2)
                  exact ⟨star_of_step (hst.trans hte2), by simp [hbp0],
                    ⟨rfl, rfl, .cons (.leafExit hc2 heidx htB havT (Nat.zero_le _) (fun hc => by cases hc)
                      (by simpa using hcopyT)) hrest⟩⟩
                · -- Forward exit to `e.target ∈ nonLeafExits` via 0-stmt trampoline (2 steps, `0 ≤ 0`)!
                  obtain ⟨htCutGe, htLtF, htnn, htNotLeaf⟩ := hf.nonLeaf_ok e.target htnl
                  have htCutGe' : cut ≤ e.target := htCutGe
                  have ht_ne_h : e.target ≠ h := Nat.ne_of_gt (Nat.lt_of_lt_of_le hh_lt_cut htCutGe')
                  have hbp0 : decide (e.target ≤ u) = false := decide_eq_false (Nat.not_le.2 (Nat.lt_of_lt_of_le huCut htCutGe'))
                  obtain ⟨tidx, htidxOf, htidx⟩ := mem_listIndexOf htnl
                  have htidxLt : tidx < nonLeafExits.length := (List.getElem?_eq_some_iff.1 htidx).1
                  let trampLbl := (if c = 0 then verSlowTrampBase h nodes else verFastTrampBase h nodes leafExits nonLeafExits) + tidx
                  have hrem : (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                      else verRemapFastTarget h nodes leafExits nonLeafExits) e.target = trampLbl := by
                    have hneB : (e.target == h) = false := beq_false_of_ne ht_ne_h
                    have hnnB : (Src.NatSet.ofList nodes).contains e.target = false := (natSet_ofList_contains_false nodes e.target).2 htnn
                    have hnlNone : listIndexOf leafExits e.target = none := listIndexOf_none_of_not_mem htNotLeaf
                    by_cases hc0 : c = 0 <;> simp [hc0, trampLbl, verRemapSlowTarget, verRemapFastTarget, hneB, hnnB, hnlNone, htidxOf]
                  have htrampBlk : ∃ regStart cold, off ≤ regStart ∧
                      F'.blocks[trampLbl]? = some
                        { params := (List.range tgtB.params.length).map (regStart + ·)
                          body := #[]
                          term := .jump { target := e.target + delta, args := ((List.range tgtB.params.length).map (regStart + ·)).map .v }
                          cold := cold } := by
                    by_cases hc0 : c = 0
                    · subst hc0
                      have hb := buildVersioned_blocks_slowTramp F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off htidx
                      have hregGe : off ≤ 3 * off + tidx * off :=
                        Nat.le_trans (Nat.le_mul_of_pos_left off (by decide)) (Nat.le_add_right _ _)
                      refine ⟨3 * off + tidx * off, (F.blocks[e.target]?.map (·.cold)).getD false, hregGe, ?_⟩
                      simpa [trampLbl, hftgt, delta, F'] using hb
                    · have hb := buildVersioned_blocks_fastTramp F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off htidx
                      have hregGe : off ≤ 3 * off + nonLeafExits.length * off + tidx * off :=
                        Nat.le_trans (Nat.le_mul_of_pos_left off (by decide))
                          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
                      refine ⟨3 * off + nonLeafExits.length * off + tidx * off,
                        (F.blocks[e.target]?.map (·.cold)).getD false, hregGe, ?_⟩
                      simpa [trampLbl, hc0, hftgt, delta, F'] using hb
                  obtain ⟨regStart, cold, hregGe, htramp⟩ := htrampBlk
                  have hsuf := buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off htCutGe hftgt
                  have htrampLt : trampLbl < e.target + delta := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [trampLbl, ↓reduceIte, verSlowTrampBase, delta, verDelta]; omega
                    · simp only [trampLbl, hc0, ↓reduceIte, verFastTrampBase, verFastExitBase, verFastNodeBase, delta, verDelta]; omega
                  obtain ⟨ρ₂t, ρ₂', hbpt, hstepTramp, houter'⟩ := step_trampoline (q := q) (F' := F')
                    (fi := fi) (trampLbl := trampLbl) (x := e.target) (delta := delta)
                    (regStart := regStart) (nParams := tgtB.params.length)
                    (fr₂ := ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩)
                    (rest₂ := rest₂) (tgtBlk := tgtB) (cold := cold)
                    hqfi rfl htramp hsuf rfl rfl hregGe htrampLt hcopy.1 hbp
                  have hfwd1 : decide (trampLbl ≤ if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx) = false := by
                    by_cases hc0 : c = 0
                    · subst hc0; simp only [trampLbl, ↓reduceIte, verSlowTrampBase, decide_eq_false_iff_not]; omega
                    · simp only [trampLbl, hc0, ↓reduceIte, verFastTrampBase, verFastExitBase, verFastNodeBase, decide_eq_false_iff_not]; omega
                  refine ⟨0, { mem := mem, ctx := ctx, stack := ⟨fi, e.target + delta, 0, ρ₂', d₂⟩ :: rest₂ }, fun hst => ?_⟩
                  have hte1 : takeEdge F' { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ rest₂ ρ₂
                      { target := (if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits else verRemapFastTarget h nodes leafExits nonLeafExits) e.target,
                        args := e.args.map (loopMapArg clonedDefs off c) } =
                      .next { mem := mem, ctx := ctx, stack := ⟨fi, trampLbl, 0, ρ₂t, d₂⟩ :: rest₂ } false := by
                    rw [hrem, ← hfwd1]; exact takeEdge_ok hev2 htramp hbpt
                  have hstar : Sem.Star (semStep q)
                      { mem := mem, ctx := ctx, stack := ⟨fi, if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx, pos, ρ₂fr, d₂⟩ :: rest₂ }
                      0 { mem := mem, ctx := ctx, stack := ⟨fi, e.target + delta, 0, ρ₂', d₂⟩ :: rest₂ } :=
                    Sem.Star.free (by rw [semStep_next]; exact hst.trans hte1) (star_of_step hstepTramp)
                  have hremOrig : verRemapOrig h nodes leafExits nonLeafExits e.target = e.target + delta := by
                    have hnl : ¬ e.target < verCut h nodes := Nat.not_lt_of_ge htCutGe
                    simp [verRemapOrig, hnl, delta]
                  refine ⟨hstar, by simp [hbp0], ⟨rfl, rfl, .cons ?_ hrest⟩⟩
                  rw [← hremOrig]
                  exact .outside hftgt htnn htNotLeaf (Nat.zero_le _) (fun hc => by cases hc) houter'
  -- Construct `Sem.Forward`
  refine ⟨?_, ?_⟩
  · -- `next`
    intro s₁ s₁' s₂ b hrel hstep1
    have hpd' : ∀ fr ∈ s₁'.stack, frameParamsDef F fi fr :=
      step_preserves_frameParamsDef hpfi hrel.1 (semStep_next.1 hstep1)
    suffices hcore : (∃ c s₂', Sem.Star (semStep q) s₂ c s₂' ∧ b.toNat ≤ c ∧
          VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁' s₂') ∨
        Sem.Fails (semStep q) s₂ by
      rcases hcore with ⟨c, s₂', hstar, hle, hrc⟩ | hfail
      · exact .inl ⟨c, s₂', hstar, hle, ⟨hpd', hrc⟩⟩
      · exact .inr hfail
    rw [semStep_next] at hstep1
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨hpd, hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq
    obtain rfl : ctx₁ = ctx₂ := hctx_eq
    cases hstack with
    | nil => simp [step] at hstep1
    | @cons _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        cases hfr with
        | other hfn =>
            unfold step at hstep1; dsimp only at hstep1
            cases hG : p.funcs[fr₁.fn]? with
            | none => rw [hG] at hstep1; cases hstep1
            | some G =>
                have hqG : q.funcs[fr₁.fn]? = some G := by
                  rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hG]
                rw [hG] at hstep1; dsimp only at hstep1
                cases hB : G.blocks[fr₁.label]? with
                | none => rw [hB] at hstep1; cases hstep1
                | some B =>
                    rw [hB] at hstep1; dsimp only at hstep1
                    by_cases hltB : fr₁.pos < B.body.size
                    · simp only [hltB, ↓reduceDIte] at hstep1
                      cases hs : B.body[fr₁.pos]'hltB with
                      | call rs' g' as' =>
                          rw [hs] at hstep1; dsimp only at hstep1
                          cases hev : evalArgs fr₁.env as' with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g' vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                                  have hstep2 := step_call (p := q) (F := G) (B := B) (fr := fr₁) (rest := rest₂)
                                    (mem := mem₁) (ctx := ctx₁) hqG hB hltB hs hev hent2
                                  exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _,
                                    ⟨rfl, rfl, .cons hcalRel (.cons (.other hfn) hrest)⟩⟩
                      | assign _ _ | limb _ _ _ | store _ _ _ =>
                          rw [hs] at hstep1; dsimp only at hstep1
                          cases hx : (B.body[fr₁.pos]'hltB).exec fr₁.env mem₁ ctx₁ with
                          | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                          | some p' =>
                              rcases p' with ⟨ρ₁', mem₁'⟩
                              have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                              simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                              have hnc : (B.body[fr₁.pos]'hltB).isCall = false := by rw [hs]; rfl
                              have hstep2 := step_stmt (p := q) (F := G) (B := B) (fr := fr₁) (rest := rest₂)
                                (mem := mem₁) (ctx := ctx₁) hqG hB hltB rfl hnc hx'
                              exact .inl ⟨0, _, star_of_step hstep2, Nat.le_refl _, ⟨rfl, rfl, .cons (.other hfn) hrest⟩⟩
                    · simp only [hltB, ↓reduceDIte] at hstep1
                      have hstep2_unfold := step_term_ge (p := q) (F := G) (B := B) (mem := mem₁) (ctx := ctx₁) (fr := fr₁) (rest := rest₂) hqG hB hltB
                      have sameEdge : ∀ (ρ : Env) (e : Edge),
                          takeEdge G { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₁ } fr₁ rest₁ ρ e = .next s₁' b →
                          ∃ s₂', takeEdge G { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } fr₁ rest₂ ρ e = .next s₂' b ∧
                            VersionStateRelCore F fi h nodes leafExits nonLeafExits off availMap s₁' s₂' := by
                        intro ρ e hte
                        unfold takeEdge at hte
                        cases hev : evalArgs ρ e.args with
                        | none => rw [hev] at hte; cases hte
                        | some vs =>
                            cases htgt : G.blocks[e.target]? with
                            | none => rw [hev, htgt] at hte; cases hte
                            | some tb =>
                                rw [hev, htgt] at hte; dsimp only at hte
                                cases hbp : bindParams ρ tb.params vs with
                                | none => rw [hbp] at hte; cases hte
                                | some ρ' =>
                                    rw [hbp] at hte; simp only [Step.next.injEq] at hte; obtain ⟨rfl, rfl⟩ := hte
                                    exact ⟨_, takeEdge_ok hev htgt hbp, ⟨rfl, rfl, .cons (.other hfn) hrest⟩⟩
                      cases ht : B.term with
                      | jump e =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          obtain ⟨s₂', hte2, hrel'⟩ := sameEdge fr₁.env e hstep1
                          exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), Nat.le_refl _, hrel'⟩
                      | br c w a b' t f =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1 hstep2_unfold
                                  obtain ⟨s₂', hte2, hrel'⟩ := sameEdge fr₁.env (if c.holds w va vb then t else f) hstep1
                                  exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), Nat.le_refl _, hrel'⟩
                      | brOvf o x a b' ok ovf =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases ha : a.eval fr₁.env with
                          | none => rw [ha] at hstep1; cases hstep1
                          | some va =>
                              cases hb' : b'.eval fr₁.env with
                              | none => rw [ha, hb'] at hstep1; cases hstep1
                              | some vb =>
                                  rw [ha, hb'] at hstep1 hstep2_unfold
                                  obtain ⟨s₂', hte2, hrel'⟩ := sameEdge (fr₁.env.insert x (o.eval va vb).1)
                                    (if (o.eval va vb).2 then ovf else ok) hstep1
                                  exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hte2), Nat.le_refl _, hrel'⟩
                      | ret ras =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases hev : evalArgs fr₁.env ras with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1 hstep2_unfold; dsimp only at hstep2_unfold
                              obtain ⟨s₂', hret2, hrel'⟩ := matchRet mem₁ ctx₁ rest₁ rest₂ vs s₁' b hrest hstep1
                              exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), Nat.le_refl _, hrel'⟩
                      | tail g tas =>
                          rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                          cases hev : evalArgs fr₁.env tas with
                          | none => rw [hev] at hstep1; cases hstep1
                          | some vs =>
                              rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                              cases hent : enter p g vs with
                              | none => rw [hent] at hstep1; cases hstep1
                              | some calFr₁ =>
                                  rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                                  obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                                  simp only [hev, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                                  exact .inl ⟨1, _, star_of_step hstep2_unfold, Nat.le_refl _, ⟨rfl, rfl, .cons hcalRel hrest⟩⟩
                      | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @outside u pos ρ₁ ρ₂ d₁ d₂ blk hB hun hul hposLe _ houter =>
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hB).1
            obtain ⟨_, hstLt, htUsesLt, _, heUsesLt⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨hstNc, htNc, heNc⟩ := hf.outside_no_cloned u huLt hun hul blk hB
            have hB2 : F'.blocks[verRemapOrig h nodes leafExits nonLeafExits u]? =
                some { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) } := by
              unfold verRemapOrig
              by_cases hlt : u < verCut h nodes
              · simp only [hlt, ↓reduceIte]
                exact buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  hlt ((natSet_ofList_contains_false nodes u).2 hun) hB
              · simp only [hlt, ↓reduceIte]
                exact buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  (Nat.le_of_not_lt hlt) hB
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuNc : ∀ x ∈ (blk.body[pos]'hltB).uses, clonedDefs.contains x = false := hstNc _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuNc; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ as' = some vs := by
                            rw [outer_evalArgs houter (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          have hstep2 := step_call (p := q) (F := F')
                            (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                              { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) })
                            (fr := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩)
                            (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqfi hB2 hltB hs hev2 hent2
                          exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.outside hB hun hul (by omega) (fun _ => rfl) houter) hrest)⟩⟩
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, houter'⟩ := outer_stmt_exec houter hsuLt hsuNc hx'
                      have hnc : (blk.body[pos]'hltB).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F')
                        (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                          { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) })
                        (fr := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩)
                        (rest := rest₂) (mem := mem₁) (ctx := ctx₁) hqfi hB2 hltB rfl hnc hx2
                      exact .inl ⟨0, _, star_of_step hstep2, Nat.le_refl _,
                        ⟨rfl, rfl, .cons (.outside hB hun hul (by omega) (fun hc => by cases hc) houter') hrest⟩⟩
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hstep2_unfold := step_term_ge (p := q) (F := F')
                (B := { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) })
                (mem := mem₁) (ctx := ctx₁)
                (fr := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩) (rest := rest₂)
                hqfi hB2 hltB
              dsimp only at hstep2_unfold
              rw [term_setEdges_map] at hstep2_unfold
              have hEdgeOk : ∀ e ∈ blk.term.edges,
                  (∀ a ∈ e.args, listLt off a.uses = true) ∧
                  (∀ a ∈ e.args, ∀ x ∈ a.uses, clonedDefs.contains x = false) := fun e he =>
                ⟨fun a ha => by simp only [listLt, List.all_eq_true, decide_eq_true_eq]; intro x hx; exact listLt_mem' heUsesLt (edgeUses_mem he ha hx),
                 fun a ha x hx => heNc x (edgeUses_mem he ha hx)⟩
              have hpdTop : ∀ r ∈ F.params, ρ₁[r]?.isSome = true :=
                hpd ⟨fi, u, pos, ρ₁, d₁⟩ (by simp) rfl
              cases ht : blk.term with
              | jump e =>
                  rw [ht] at hstep1 hstep2_unfold; dsimp only at hstep1 hstep2_unfold
                  have he : e ∈ blk.term.edges := by simp [ht, Term.edges]
                  obtain ⟨h1, h2⟩ := hEdgeOk e he
                  obtain ⟨cStep, s₂', hgo⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ e s₁' b hB hun hul he houter hpdTop h1 h2 hrest hstep1
                  exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | br c w a b' t f =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 : a.eval ρ₂ = some va := by rw [outer_arg_eval houter htUsesLt.1 (fun x hx => htNc x (by simp [Term.uses, hx])), ha]
                          have hb2 : b'.eval ρ₂ = some vb := by rw [outer_arg_eval houter htUsesLt.2 (fun x hx => htNc x (by simp [Term.uses, hx])), hb']
                          rw [ha2, hb2] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hcond : c.holds w va vb <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : f ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk f he
                            obtain ⟨cStep, s₂', hgo⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ f s₁' b hB hun hul he houter hpdTop h1 h2 hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : t ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk t he
                            obtain ⟨cStep, s₂', hgo⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ t s₁' b hB hun hul he houter hpdTop h1 h2 hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | brOvf o x a b' ok ovf =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 : a.eval ρ₂ = some va := by rw [outer_arg_eval houter htUsesLt.1 (fun z hz => htNc z (by simp [Term.uses, hz])), ha]
                          have hb2 : b'.eval ρ₂ = some vb := by rw [outer_arg_eval houter htUsesLt.2 (fun z hz => htNc z (by simp [Term.uses, hz])), hb']
                          rw [ha2, hb2] at hstep2_unfold; dsimp only at hstep2_unfold
                          have hpdIns : ∀ r ∈ F.params, (ρ₁.insert x (o.eval va vb).1)[r]?.isSome = true :=
                            fun r hr => env_insert_isSome (hpdTop r hr)
                          cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : ok ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk ok he
                            obtain ⟨cStep, s₂', hgo⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert x (o.eval va vb).1) ρ₂ d₁ d₂ rest₁ rest₂ ok s₁' b
                              hB hun hul he (houter.insert_same x _) hpdIns h1 h2 hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : ovf ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨h1, h2⟩ := hEdgeOk ovf he
                            obtain ⟨cStep, s₂', hgo⟩ := outsideTakeEdge mem₁ ctx₁ u pos blk
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert x (o.eval va vb).1) ρ₂ d₁ d₂ rest₁ rest₂ ovf s₁' b
                              hB hun hul he (houter.insert_same x _) hpdIns h1 h2 hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | ret ras =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ ras = some vs := by
                        rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel'⟩ := matchRet mem₁ ctx₁ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), Nat.le_refl _, hrel'⟩
              | tail g tas =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htNc; dsimp only at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ tas = some vs := by
                            rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          simp only [hev2, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                          exact .inl ⟨1, _, star_of_step hstep2_unfold, Nat.le_refl _, ⟨rfl, rfl, .cons hcalRel hrest⟩⟩
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @loopNode u idx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hc2 hidx hB hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huMem : u ∈ nodes := List.mem_of_getElem? hidx
            have huCut : u < cut := hf.node_lt_cut huMem
            obtain ⟨_, hstLt, htUsesLt, _, heUsesLt⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨_, hbodyDefs, htDefs⟩ := collectBlocksDefs_mem (List.mem_append_left _ huMem) hB
            obtain ⟨av0', av1, hav0', hchk, htAv, heAv, havEdges⟩ := hf.avail_block u (List.mem_append_left _ huMem) blk hB
            rw [hav0] at hav0'; cases hav0'
            let qLbl := if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx
            let qRemap := if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                          else verRemapFastTarget h nodes leafExits nonLeafExits
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧
                ∃ (hsz : B2.body.size = blk.body.size),
                (∀ k (hk : k < blk.body.size), B2.body[k]'(hsz ▸ hk) = loopMapStmt clonedDefs off c (blk.body[k]'hk)) ∧
                B2.term = mapLoopTerm clonedDefs off c qRemap blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have hblk := buildVersioned_blocks_prefix_node F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  huCut ((natSet_ofList_contains nodes u).2 huMem) hB
                refine ⟨{ blk with term := mapLoopTerm clonedDefs off 0 qRemap blk.term, cold := true },
                  by simpa [qLbl, qRemap, clonedDefs, F'] using hblk, rfl, fun k hk => by simp [loopMapStmt_zero'], rfl⟩
              · have hc1 : c = 1 := by omega
                subst hc1
                have hblk := buildVersioned_blocks_fastNode F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hidx hB
                refine ⟨_, by simpa [qLbl] using hblk, by simp, fun k hk => by simp [clonedDefs], rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2body, hB2term⟩ := hB2
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hltB2 : pos < B2.body.size := hB2sz ▸ hltB
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuAv := checkStmtsAvail_at hchk hltB
              have hsdCl : ∀ d ∈ (blk.body[pos]'hltB).defs, clonedDefs.contains d = true := hbodyDefs _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuAv hsdCl; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (as'.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          have hs2 : B2.body[pos]'hltB2 = .call (rs'.map (loopMapReg clonedDefs off c)) g' (as'.map (loopMapArg clonedDefs off c)) := by
                            rw [hB2body pos hltB, hs]; rfl
                          have hstep2 := step_call (p := q) (F := F') (B := B2)
                            (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            hqfi hB2 hltB2 hs2 hev2 hent2
                          have hcallAt : blk.body[pos]? = some (.call rs' g' as') := by
                            rw [Array.getElem?_eq_getElem hltB, hs]
                          exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.loopNode hc2 hidx hB hav0 (by omega)
                              (fun _ => ⟨by omega, rfl, hsdCl, g', as', by simpa using hcallAt⟩)
                              (by simpa using hcopy)) hrest)⟩⟩
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, hcopy'⟩ := loopMapStmt_exec hcopy hsuLt hsuAv hsdCl hx'
                      have hnc : (loopMapStmt clonedDefs off c (blk.body[pos]'hltB)).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F') (B := B2)
                        (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                        hqfi hB2 hltB2 (hB2body pos hltB) hnc hx2
                      rw [← availAtPos_succ av0 blk.body hltB] at hcopy'
                      exact .inl ⟨0, _, star_of_step hstep2, Nat.le_refl _,
                        ⟨rfl, rfl, .cons (.loopNode hc2 hidx hB hav0 (by omega) (fun hc => by cases hc)
                          (by simpa using hcopy')) hrest⟩⟩
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hposEq : pos = blk.body.size := by omega
              subst hposEq
              rw [checkStmtsAvail_end hchk] at hcopy
              have hltB2 : ¬ blk.body.size < B2.body.size := by omega
              have hstep2_unfold := step_term_ge (p := q) (F := F') (B := B2) (mem := mem₁) (ctx := ctx₁)
                (fr := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩) (rest := rest₂) hqfi hB2 hltB2
              dsimp only at hstep2_unfold
              rw [hB2term] at hstep2_unfold
              have hEdgeLt : ∀ e ∈ blk.term.edges, ∀ a ∈ e.args, listLt off a.uses = true :=
                fun e he a ha => by
                  simp only [listLt, List.all_eq_true, decide_eq_true_eq]
                  intro x hx; exact listLt_mem' heUsesLt (edgeUses_mem he ha hx)
              have hEdgeAv : ∀ e ∈ blk.term.edges, ∀ a ∈ e.args, ∀ x ∈ a.uses,
                  clonedDefs.contains x = false ∨ (blk.term.defs.foldl (fun a x => a.insert x) av1).contains x = true :=
                fun e he a ha x hx => heAv x (edgeUses_mem he ha hx)
              have hpdTop : ∀ r ∈ F.params, ρ₁[r]?.isSome = true :=
                hpd ⟨fi, u, blk.body.size, ρ₁, d₁⟩ (by simp) rfl
              cases ht : blk.term with
              | jump e =>
                  rw [ht] at hstep1 hstep2_unfold; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  have he : e ∈ blk.term.edges := by simp [ht, Term.edges]
                  have hav2 : blk.term.defs.foldl (fun a x => a.insert x) av1 = av1 := by simp [ht, Term.defs]
                  obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                    (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ e s₁' b
                    hc2 hidx hB he havEdges (by rw [hav2]; exact hcopy) hpdTop (hEdgeLt e he) (hEdgeAv e he) hrest hstep1
                  exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | br cond w a b' t f =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  have hav2 : blk.term.defs.foldl (fun a x => a.insert x) av1 = av1 := by simp [ht, Term.defs]
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 := loopMapArg_eval hcopy htUsesLt.1 (fun x hx => htAv x (by simp [Term.uses, hx]))
                          have hb2 := loopMapArg_eval hcopy htUsesLt.2 (fun x hx => htAv x (by simp [Term.uses, hx]))
                          rw [ha2, hb2, ha, hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          cases hcond : cond.holds w va vb <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : f ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ f s₁' b
                              hc2 hidx hB he havEdges (by rw [hav2]; exact hcopy) hpdTop (hEdgeLt f he) (hEdgeAv f he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : t ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a x => a.insert x) av1) ρ₁ ρ₂ ρ₂ d₁ d₂ rest₁ rest₂ t s₁' b
                              hc2 hidx hB he havEdges (by rw [hav2]; exact hcopy) hpdTop (hEdgeLt t he) (hEdgeAv t he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | brOvf o x a b' ok ovf =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  simp only [Term.uses, listLt_append] at htUsesLt
                  have hxCl : clonedDefs.contains x = true := htDefs x (by simp [ht, Term.defs])
                  have hav2 : blk.term.defs.foldl (fun a z => a.insert z) av1 = av1.insert x := by simp [ht, Term.defs]
                  cases ha : a.eval ρ₁ with
                  | none => rw [ha] at hstep1; cases hstep1
                  | some va =>
                      cases hb' : b'.eval ρ₁ with
                      | none => rw [ha, hb'] at hstep1; cases hstep1
                      | some vb =>
                          rw [ha, hb'] at hstep1
                          have ha2 := loopMapArg_eval hcopy htUsesLt.1 (fun z hz => htAv z (by simp [Term.uses, hz]))
                          have hb2 := loopMapArg_eval hcopy htUsesLt.2 (fun z hz => htAv z (by simp [Term.uses, hz]))
                          rw [ha2, hb2, ha, hb'] at hstep2_unfold; dsimp only at hstep2_unfold
                          have hcopy' : LoopCopyRel clonedDefs off c (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) := by
                            rw [hav2]; exact hcopy.insert_def hxCl _
                          have hpdIns : ∀ r ∈ F.params, (ρ₁.insert x (o.eval va vb).1)[r]?.isSome = true :=
                            fun r hr => env_insert_isSome (hpdTop r hr)
                          cases hovf : (o.eval va vb).2 <;> simp only [hovf, Bool.false_eq_true, ↓reduceIte] at hstep1 hstep2_unfold
                          · have he : ok ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) ρ₂
                              d₁ d₂ rest₁ rest₂ ok s₁' b hc2 hidx hB he havEdges hcopy' hpdIns (hEdgeLt ok he) (hEdgeAv ok he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
                          · have he : ovf ∈ blk.term.edges := by simp [ht, Term.edges]
                            obtain ⟨cStep, s₂', hgo⟩ := loopNodeTakeEdge mem₁ ctx₁ u idx c blk.body.size blk
                              (blk.term.defs.foldl (fun a z => a.insert z) av1)
                              (ρ₁.insert x (o.eval va vb).1) (ρ₂.insert (loopMapReg clonedDefs off c x) (o.eval va vb).1) ρ₂
                              d₁ d₂ rest₁ rest₂ ovf s₁' b hc2 hidx hB he havEdges hcopy' hpdIns (hEdgeLt ovf he) (hEdgeAv ovf he) hrest hstep1
                            exact .inl ⟨cStep, s₂', hgo hstep2_unfold⟩
              | ret ras =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                        rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel'⟩ := matchRet mem₁ ctx₁ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), Nat.le_refl _, hrel'⟩
              | tail g tas =>
                  rw [ht] at hstep1 hstep2_unfold htUsesLt htAv; dsimp only [mapLoopTerm] at hstep1 hstep2_unfold
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (tas.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          simp only [hev2, Option.bind_eq_bind, Option.bind_some, hent2] at hstep2_unfold
                          exact .inl ⟨1, _, star_of_step hstep2_unfold, Nat.le_refl _, ⟨rfl, rfl, .cons hcalRel hrest⟩⟩
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
        | @leafExit u eidx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hc2 heidx hB hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            unfold step at hstep1; dsimp only at hstep1
            rw [hpfi] at hstep1; dsimp only at hstep1; rw [hB] at hstep1; dsimp only at hstep1
            have huMem : u ∈ leafExits := List.mem_of_getElem? heidx
            have hun : u ∉ nodes := (hf.leaf_ok u huMem).2.2
            have hnoEdges : blk.term.edges = [] := hf.leaf_no_edges u huMem blk hB
            obtain ⟨_, hstLt, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hB)
            obtain ⟨_, hbodyDefs, _⟩ := collectBlocksDefs_mem (List.mem_append_right _ huMem) hB
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_right _ huMem) blk hB
            rw [hav0] at hav0'; cases hav0'
            let qLbl := if c = 0 then verRemapOrig h nodes leafExits nonLeafExits u
                        else verFastExitBase h nodes nonLeafExits + eidx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧
                ∃ (hsz : B2.body.size = blk.body.size),
                (∀ k (hk : k < blk.body.size), B2.body[k]'(hsz ▸ hk) = loopMapStmt clonedDefs off c (blk.body[k]'hk)) ∧
                B2.term = mapLoopTerm clonedDefs off c (fun l => l) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have htermEq : blk.term.setEdges (blk.term.edges.map fun e =>
                    { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) =
                    mapLoopTerm clonedDefs off 0 (fun l => l) blk.term := by
                  cases ht' : blk.term <;> simp [ht', Term.edges] at hnoEdges ⊢ <;>
                    simp [Term.setEdges, mapLoopTerm, loopMapArg_zero_map]
                by_cases hlt : u < verCut h nodes
                · have hblk := buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                    hlt ((natSet_ofList_contains_false nodes u).2 hun) hB
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) },
                    by simpa [qLbl, verRemapOrig, hlt, F'] using hblk, rfl,
                    fun k hk => by simp [loopMapStmt_zero'], htermEq⟩
                · have hblk := buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                    (Nat.le_of_not_lt hlt) hB
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) },
                    by simpa [qLbl, verRemapOrig, hlt, F'] using hblk, rfl,
                    fun k hk => by simp [loopMapStmt_zero'], htermEq⟩
              · have hc1 : c = 1 := by omega
                subst hc1
                have hblk := buildVersioned_blocks_fastExit F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off heidx hB
                exact ⟨_, by simpa [qLbl] using hblk, by simp, fun k hk => by simp [clonedDefs], rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2body, hB2term⟩ := hB2
            by_cases hltB : pos < blk.body.size
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hltB2 : pos < B2.body.size := hB2sz ▸ hltB
              have hstMem : blk.body[pos]'hltB ∈ blk.body.toList := Array.mem_toList_iff.2 (Array.getElem_mem hltB)
              have hsuLt : listLt off (blk.body[pos]'hltB).uses = true := (hstLt _ hstMem).1
              have hsuAv := checkStmtsAvail_at hchk hltB
              have hsdCl : ∀ d ∈ (blk.body[pos]'hltB).defs, clonedDefs.contains d = true := hbodyDefs _ hstMem
              cases hs : blk.body[pos]'hltB with
              | call rs' g' as' =>
                  rw [hs] at hstep1 hsuLt hsuAv hsdCl; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ as' with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g' vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (as'.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses hsuLt)
                              (fun a ha x hx => hsuAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          have hs2 : B2.body[pos]'hltB2 = .call (rs'.map (loopMapReg clonedDefs off c)) g' (as'.map (loopMapArg clonedDefs off c)) := by
                            rw [hB2body pos hltB, hs]; rfl
                          have hstep2 := step_call (p := q) (F := F') (B := B2)
                            (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                            hqfi hB2 hltB2 hs2 hev2 hent2
                          have hcallAt : blk.body[pos]? = some (.call rs' g' as') := by
                            rw [Array.getElem?_eq_getElem hltB, hs]
                          exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _,
                            ⟨rfl, rfl, .cons hcalRel (.cons (.leafExit hc2 heidx hB hav0 (by omega)
                              (fun _ => ⟨by omega, rfl, hsdCl, g', as', by simpa using hcallAt⟩)
                              (by simpa using hcopy)) hrest)⟩⟩
              | assign _ _ | limb _ _ _ | store _ _ _ =>
                  rw [hs] at hstep1; dsimp only at hstep1
                  cases hx : (blk.body[pos]'hltB).exec ρ₁ mem₁ ctx₁ with
                  | none => rw [hs] at hx; rw [hx] at hstep1; cases hstep1
                  | some p' =>
                      rcases p' with ⟨ρ₁', mem₁'⟩
                      have hx' := hx; rw [hs] at hx; rw [hx] at hstep1
                      simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                      obtain ⟨ρ₂', hx2, hcopy'⟩ := loopMapStmt_exec hcopy hsuLt hsuAv hsdCl hx'
                      have hnc : (loopMapStmt clonedDefs off c (blk.body[pos]'hltB)).isCall = false := by rw [hs]; rfl
                      have hstep2 := step_stmt (p := q) (F := F') (B := B2)
                        (fr := ⟨fi, qLbl, pos, ρ₂, d₂⟩) (rest := rest₂) (mem := mem₁) (ctx := ctx₁)
                        hqfi hB2 hltB2 (hB2body pos hltB) hnc hx2
                      rw [← availAtPos_succ av0 blk.body hltB] at hcopy'
                      exact .inl ⟨0, _, star_of_step hstep2, Nat.le_refl _,
                        ⟨rfl, rfl, .cons (.leafExit hc2 heidx hB hav0 (by omega) (fun hc => by cases hc)
                          (by simpa using hcopy')) hrest⟩⟩
            · simp only [hltB, ↓reduceDIte] at hstep1
              have hposEq : pos = blk.body.size := by omega
              subst hposEq
              rw [checkStmtsAvail_end hchk] at hcopy
              have hltB2 : ¬ blk.body.size < B2.body.size := by omega
              cases ht : blk.term with
              | jump _ | br _ _ _ _ _ _ | brOvf _ _ _ _ _ _ => simp [ht, Term.edges] at hnoEdges
              | fail _ | trap => rw [ht] at hstep1; cases hstep1
              | ret ras =>
                  rw [ht] at hstep1 htUsesLt htAv; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ ras with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1
                      have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                        rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                          (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                      have hstep2_unfold := step_term_ge (p := q) (F := F') (B := B2) (mem := mem₁) (ctx := ctx₁)
                        (fr := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩) (rest := rest₂) hqfi hB2 hltB2
                      dsimp only at hstep2_unfold
                      rw [hB2term, ht] at hstep2_unfold; dsimp only [mapLoopTerm] at hstep2_unfold
                      rw [hev2] at hstep2_unfold; dsimp only at hstep2_unfold
                      obtain ⟨s₂', hret2, hrel'⟩ := matchRet mem₁ ctx₁ rest₁ rest₂ vs s₁' b hrest hstep1
                      exact .inl ⟨b.toNat, s₂', star_of_step (hstep2_unfold.trans hret2), Nat.le_refl _, hrel'⟩
              | tail g tas =>
                  rw [ht] at hstep1 htUsesLt htAv; dsimp only at hstep1
                  cases hev : evalArgs ρ₁ tas with
                  | none => rw [hev] at hstep1; cases hstep1
                  | some vs =>
                      rw [hev] at hstep1; simp only [Option.bind_eq_bind, Option.bind_some] at hstep1
                      cases hent : enter p g vs with
                      | none => rw [hent] at hstep1; cases hstep1
                      | some calFr₁ =>
                          rw [hent] at hstep1; simp only [Step.next.injEq] at hstep1; obtain ⟨rfl, rfl⟩ := hstep1
                          have hev2 : evalArgs ρ₂ (tas.map (loopMapArg clonedDefs off c)) = some vs := by
                            rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                              (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
                          obtain ⟨calFr₂, hent2, hcalRel⟩ := version_enter_rel hpfi hf hq hent
                          have hstep2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } =
                              .next { mem := mem₁, ctx := ctx₁, stack := calFr₂ :: rest₂ } true := by
                            unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]
                            simp [hltB2, mapLoopTerm, hev2, hent2]
                          exact .inl ⟨1, _, star_of_step hstep2, Nat.le_refl _, ⟨rfl, rfl, .cons hcalRel hrest⟩⟩
  · -- `final` (via `final_ne_stuck_elim`)
    intro s₁ s₂ r hrel hfin hne
    rcases s₁ with ⟨mem₁, ctx₁, st₁⟩
    rcases s₂ with ⟨mem₂, ctx₂, st₂⟩
    obtain ⟨_, hmem_eq, hctx_eq, hstack⟩ := hrel
    obtain rfl : mem₁ = mem₂ := hmem_eq
    obtain rfl : ctx₁ = ctx₂ := hctx_eq
    cases hstack with
    | nil =>
        have hst : step p { mem := mem₁, ctx := ctx₁, stack := [] } = .stuck := rfl
        rw [semStep, hst] at hfin; cases hfin; exact absurd rfl hne
    | @cons _ fr₁ fr₂ rest₁ rest₂ hfr hrest =>
        obtain ⟨G, B, hG, hB, hltB, hterm⟩ := final_ne_stuck_elim hfin hne
        cases hfr with
        | other hfn =>
            have hqG : q.funcs[fr₁.fn]? = some G := by
              rw [hq]; simp [Array.set!_eq_setIfInBounds, Ne.symm hfn, hG]
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := fr₁ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [fr₁] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqG]; dsimp only; rw [hB]; simp [hltB, ht, hev]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @outside u pos ρ₁ ρ₂ d₁ d₂ blk hBu hun hul _ _ houter =>
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have huLt : u < F.blocks.size := (Array.getElem?_eq_some_iff.1 hBu).1
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨_, htNc, _⟩ := hf.outside_no_cloned u huLt hun hul blk hBu
            have hB2 : F'.blocks[verRemapOrig h nodes leafExits nonLeafExits u]? =
                some { blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                  { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) } := by
              unfold verRemapOrig
              by_cases hlt : u < verCut h nodes
              · simp only [hlt, ↓reduceIte]
                exact buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  hlt ((natSet_ofList_contains_false nodes u).2 hun) hBu
              · simp only [hlt, ↓reduceIte]
                exact buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  (Nat.le_of_not_lt hlt) hBu
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htNc
              have hev2 : evalArgs ρ₂ ras = some vs := by
                rw [outer_evalArgs houter (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htNc x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, verRemapOrig h nodes leafExits nonLeafExits u, pos, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; simp [hltB, term_setEdges_map, ht, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @loopNode u idx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hc2 hidx hBu hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            dsimp only at hltB
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have hposEq : pos = blk.body.size := by omega
            subst hposEq
            have huMem : u ∈ nodes := List.mem_of_getElem? hidx
            have huCut : u < cut := hf.node_lt_cut huMem
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_left _ huMem) blk hBu
            rw [hav0] at hav0'; cases hav0'
            rw [checkStmtsAvail_end hchk] at hcopy
            let qLbl := if c = 0 then u else verFastNodeBase h nodes nonLeafExits + idx
            let qRemap := if c = 0 then verRemapSlowTarget h nodes leafExits nonLeafExits
                          else verRemapFastTarget h nodes leafExits nonLeafExits
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧ B2.body.size = blk.body.size ∧
                B2.term = mapLoopTerm clonedDefs off c qRemap blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have hblk := buildVersioned_blocks_prefix_node F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                  huCut ((natSet_ofList_contains nodes u).2 huMem) hBu
                exact ⟨{ blk with term := mapLoopTerm clonedDefs off 0 qRemap blk.term, cold := true },
                  by simpa [qLbl, qRemap, clonedDefs, F'] using hblk, rfl, rfl⟩
              · have hc1 : c = 1 := by omega
                subst hc1
                have hblk := buildVersioned_blocks_fastNode F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off hidx hBu
                exact ⟨_, by simpa [qLbl] using hblk, by simp, rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2term⟩ := hB2
            have hltB2 : ¬ blk.body.size < B2.body.size := by omega
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htAv
              have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩
        | @leafExit u eidx c pos ρ₁ ρ₂ d₁ d₂ blk av0 hc2 heidx hBu hav0 hposLe _ hcopy =>
            simp only [↓reduceIte] at hcopy
            dsimp only at hltB
            obtain rfl : F = G := Option.some.inj (hpfi.symm.trans hG)
            obtain rfl : blk = B := Option.some.inj (hBu.symm.trans hB)
            have hposEq : pos = blk.body.size := by omega
            subst hposEq
            have huMem : u ∈ leafExits := List.mem_of_getElem? heidx
            have hun : u ∉ nodes := (hf.leaf_ok u huMem).2.2
            have hnoEdges : blk.term.edges = [] := hf.leaf_no_edges u huMem blk hBu
            obtain ⟨_, _, htUsesLt, _, _⟩ := blockRegsLt_parts (blockRegsLt_of_func' hf.regs_lt hBu)
            obtain ⟨av0', av1, hav0', hchk, htAv, _, _⟩ := hf.avail_block u (List.mem_append_right _ huMem) blk hBu
            rw [hav0] at hav0'; cases hav0'
            rw [checkStmtsAvail_end hchk] at hcopy
            let qLbl := if c = 0 then verRemapOrig h nodes leafExits nonLeafExits u
                        else verFastExitBase h nodes nonLeafExits + eidx
            have hB2 : ∃ B2, F'.blocks[qLbl]? = some B2 ∧ B2.body.size = blk.body.size ∧
                B2.term = mapLoopTerm clonedDefs off c (fun l => l) blk.term := by
              by_cases hc0 : c = 0
              · subst hc0
                have htermEq : blk.term.setEdges (blk.term.edges.map fun e =>
                    { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) =
                    mapLoopTerm clonedDefs off 0 (fun l => l) blk.term := by
                  cases ht' : blk.term <;> simp [ht', Term.edges] at hnoEdges ⊢ <;>
                    simp [Term.setEdges, mapLoopTerm, loopMapArg_zero_map]
                by_cases hlt : u < verCut h nodes
                · have hblk := buildVersioned_blocks_prefix_other F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                    hlt ((natSet_ofList_contains_false nodes u).2 hun) hBu
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) },
                    by simpa [qLbl, verRemapOrig, hlt, F'] using hblk, rfl, htermEq⟩
                · have hblk := buildVersioned_blocks_suffix F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
                    (Nat.le_of_not_lt hlt) hBu
                  exact ⟨{ blk with term := blk.term.setEdges (blk.term.edges.map fun e =>
                      { e with target := verRemapOutside h nodes leafExits nonLeafExits e.target }) },
                    by simpa [qLbl, verRemapOrig, hlt, F'] using hblk, rfl, htermEq⟩
              · have hc1 : c = 1 := by omega
                subst hc1
                have hblk := buildVersioned_blocks_fastExit F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off heidx hBu
                exact ⟨_, by simpa [qLbl] using hblk, by simp, rfl⟩
            obtain ⟨B2, hB2, hB2sz, hB2term⟩ := hB2
            have hltB2 : ¬ blk.body.size < B2.body.size := by omega
            rcases hterm with ⟨res, ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ras, vs, ht, hev, hnil, rfl⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .fail res := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .resource res, .refl _, by rw [semStep, h2]; exact .fail, .resource res⟩
            · have h2 : step q { mem := mem₁, ctx := ctx₁, stack := ⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩ :: rest₂ } = .trap := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm]
              exact .inl ⟨0, _, .trap, .refl _, by rw [semStep, h2]; exact .trap, .trap⟩
            · subst hnil; cases hrest
              rw [ht] at htUsesLt htAv
              have hev2 : evalArgs ρ₂ (ras.map (loopMapArg clonedDefs off c)) = some vs := by
                rw [loopMapArgs_eval hcopy (listLt_flatMap_uses htUsesLt)
                  (fun a ha x hx => htAv x (List.mem_flatMap.2 ⟨a, ha, hx⟩)), hev]
              have h2 : step q { mem := mem₁, ctx := ctx₁, stack := [⟨fi, qLbl, blk.body.size, ρ₂, d₂⟩] } = .done vs mem₁ := by
                unfold step; dsimp only; rw [hqfi]; dsimp only; rw [hB2]; dsimp only; rw [hB2term, ht]; simp [hltB2, mapLoopTerm, hev2]
              exact .inl ⟨0, _, .ok (vs, mem₁), .refl _, by rw [semStep, h2]; exact .done, .ok rfl⟩

/-! ### Public `versionOddLoopSite` simulation & well-formedness theorems -/

/-- **Single-site odd-fixnum loop versioning simulation**:
`versionOddLoopSite p fi h testParamIdxs outerTestRegs = some q` simulates `p` with exact
value/memory equality and identity clock map `id`. -/
theorem versionOddLoopSite_sim {p q : Program} {fi h : Nat}
    {testParamIdxs : List Nat} {outerTestRegs : List VReg}
    (hver : versionOddLoopSite p fi h testParamIdxs outerTestRegs = some q)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx) (fun k => eval q k args mem ctx) := by
  unfold versionOddLoopSite at hver
  cases hpfi : p.funcs[fi]? with
  | none => rw [hpfi] at hver; cases hver
  | some F =>
      rw [hpfi] at hver; dsimp only at hver
      cases hcls : classifyLoopExits F h with
      | none => rw [hcls] at hver; cases hver
      | some triple =>
          rcases triple with ⟨nodes, leafExits, nonLeafExits⟩
          rw [hcls] at hver; dsimp only at hver
          split at hver
          · rename_i hok
            cases hver
            have hlok : loopCloneOk F h nodes leafExits nonLeafExits (nextFreshVReg F)
                (computeLoopAvail F h nodes leafExits) = true := by
              unfold versionOddLoopOk at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1.1
            have hf := loopCloneFacts_of_ok hlok
            have hfwd := versionOddLoopSite_forward hpfi hok rfl
            cases hinit1 : Lir.State.initial p args mem ctx with
            | none =>
                refine ⟨fun k _ => ⟨0, by simp [eval, hinit1]; exact .stuck⟩,
                  fun k hk => by simp [eval, hinit1] at hk⟩
            | some s₁ =>
                simp only [Lir.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff,
                  Option.some.injEq] at hinit1
                obtain ⟨fr₁, hent₁, rfl⟩ := hinit1
                obtain ⟨fr₂, hent₂, hfrRel⟩ := version_enter_rel hpfi hf rfl hent₁
                have hinit2 : Lir.State.initial
                    { funcs := p.funcs.set! fi (buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs (nextFreshVReg F)), main := p.main }
                    args mem ctx = some { mem := mem, ctx := ctx, stack := [fr₂] } := by
                  unfold Lir.State.initial; rw [hent₂]; rfl
                have hrel0 : VersionStateRel F fi h nodes leafExits nonLeafExits (nextFreshVReg F)
                    (computeLoopAvail F h nodes leafExits)
                    { mem := mem, ctx := ctx, stack := [fr₁] }
                    { mem := mem, ctx := ctx, stack := [fr₂] } :=
                  ⟨fun f hf => by simp only [List.mem_singleton] at hf; subst hf; exact enter_frameParamsDef hpfi hent₁,
                   ⟨rfl, rfl, .cons hfrRel .nil⟩⟩
                exact hfwd.sim hrel0
                  (runs_eval (by unfold Lir.State.initial; rw [hent₁]; rfl))
                  (runs_eval hinit2)
          · cases hver

theorem versionOddLoopSiteChecked_wellFormed {p : Program} {fi h : Nat}
    {testParamIdxs : List Nat} {outerTestRegs : List VReg}
    (hwf : p.wellFormed = true) :
    (versionOddLoopSiteChecked p fi h testParamIdxs outerTestRegs).1.wellFormed = true := by
  unfold versionOddLoopSiteChecked
  cases versionOddLoopSite p fi h testParamIdxs outerTestRegs with
  | none => exact hwf
  | some q =>
      dsimp only
      split
      · rename_i hok; simp [hwf] at hok; exact hok
      · exact hwf

theorem versionOddLoopSiteChecked_sim (p : Program) (fi h : Nat)
    (testParamIdxs : List Nat) (outerTestRegs : List VReg)
    (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.Sim Eq id
      (fun k => eval p k args mem ctx)
      (fun k => eval (versionOddLoopSiteChecked p fi h testParamIdxs outerTestRegs).1 k args mem ctx) := by
  unfold versionOddLoopSiteChecked
  cases hv : versionOddLoopSite p fi h testParamIdxs outerTestRegs with
  | none => exact Sem.Sim.refl (fun _ => rfl) _
  | some q =>
      dsimp only
      split
      · exact versionOddLoopSite_sim hv args mem ctx
      · exact Sem.Sim.refl (fun _ => rfl) _

end IxCC.Lir.Opt


