import Ix.Cert.ReaderUnits
import Ix.Cert.CtxAgree

/-! # Prelude entries through quotient Source's lowering

Proof-only bookkeeping for the actual collapse and lowering. The owner map
records the keys kept declarations claim; successful steps never release a
claim. The prefix theorem uses this to frame the reader's five semantic
maps, together with syntactic basis-freedom of the lowering's output.

`SourceAcceptsQ` is a reference acceptance. No argument here may infer the
executed checker's units check from that reference acceptance.
-/

namespace Ix.Cert.SourcePrelude

open Ix.Kernel
open Ix.Kernel.Reader
open Ix.LeanIngress

abbrev SKey := Key .source
abbrev Owners := Std.HashMap SKey Nat

def claimKeys (m : Owners) (ns : List SKey) (i : Nat) : Owners :=
  ns.foldl (fun m n => m.insert n i) m

theorem claimKeys_keep_same (ns : List SKey) (m : Owners) (i : Nat) (k : SKey)
    (h : m[k]? = some i) : (claimKeys m ns i)[k]? = some i := by
  induction ns generalizing m with
  | nil => exact h
  | cons n ns ih =>
    apply ih
    rw [Std.HashMap.getElem?_insert]
    split
    · rfl
    · exact h

theorem claimKeys_claimed (ns : List SKey) (m : Owners) (i : Nat) (k : SKey)
    (h : k ∈ ns) : (claimKeys m ns i)[k]? = some i := by
  induction ns generalizing m with
  | nil => simp at h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact claimKeys_keep_same ns (m.insert k i) i k (by simp)
    · exact ih (m.insert n i) h

theorem claimKeys_outside (ns : List SKey) (m : Owners) (i : Nat) (k : SKey)
    (h : k ∉ ns) : (claimKeys m ns i)[k]? = m[k]? := by
  induction ns generalizing m with
  | nil => rfl
  | cons n ns ih =>
    have hn : k ≠ n := fun e => h (by simp [e])
    have ht : k ∉ ns := fun hk => h (List.mem_cons_of_mem _ hk)
    change (claimKeys (m.insert n i) ns i)[k]? = m[k]?
    rw [ih _ ht, Std.HashMap.getElem?_insert]
    simp [Ne.symm hn]

theorem findSome_none {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), xs.findSome? f = none → ∀ x ∈ xs, f x = none := by
  intro xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro h x hx
    cases ha : f a with
    | none =>
      have ht : xs.findSome? f = none := by simpa [List.findSome?, ha] using h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih ht x hx
    | some b => simp [List.findSome?, ha] at h

/-- A successful collapse step preserves every existing owner lookup, claims
all of the declaration's names, and keeps the declaration only at fresh names. -/
theorem step_ownerFacts {s s' : CollapseState} {first : SKey}
    {d : Declaration .source} {kept : Bool} (h : s.step first d = (s', .ok kept)) :
    (∀ (k : SKey) (v : Nat), s.owner[k]? = some v → s'.owner[k]? = some v) ∧
    (∀ k ∈ d.names, (s'.owner[k]?).isSome = true) ∧
    (kept = true → ∀ k ∈ d.names, s.owner[k]? = none) := by
  obtain ⟨ds, owner⟩ := s
  unfold CollapseState.step at h
  dsimp only at h
  split at h
  · rename_i hnone
    cases h
    have fresh : ∀ k ∈ d.names, owner[k]? = none := findSome_none _ _ hnone
    refine ⟨?_, ?_, fun _ => fresh⟩
    · intro k v hk
      have hn : k ∉ d.names := by
        intro hm
        rw [fresh k hm] at hk
        cases hk
      exact (claimKeys_outside d.names owner ds.size k hn).trans hk
    · intro k hk
      change ((claimKeys owner d.names ds.size)[k]?).isSome = true
      rw [claimKeys_claimed d.names owner ds.size k hk]
      rfl
  · rename_i i hi
    split at h
    · rename_i heq
      cases h
      refine ⟨fun _ _ h => h, ?_, by simp⟩
      have ha : d.names.all (fun n => owner[n]? == some i) = true :=
        (Bool.and_eq_true_iff.mp heq).1
      intro k hk
      have hv : owner[k]? = some i := beq_iff_eq.mp ((List.all_eq_true.mp ha) k hk)
      simp [hv]
    · cases h

/-- An inductive block is lowered only if all of its declared keys are fresh.
The complete-alias branch skips lowering instead. -/
theorem alias_none_fresh {kb : KeptBlocks} {s : CollapseState} {first : SKey}
    {rb : BlockRead .source} (h : kb.alias s first rb = .ok none) :
    ∀ k ∈ Ix.LeanIngress.BlockRead.names rb, s.owner[k]? = none := by
  unfold KeptBlocks.alias at h
  dsimp only at h
  split at h
  · rename_i hfresh
    have hall : (Ix.LeanIngress.BlockRead.names rb).any s.owner.contains = false := by
      simpa using hfresh
    intro k hk
    have hc := (List.any_eq_false.mp hall) k hk
    cases hv : s.owner[k]? with
    | none => rfl
    | some v =>
      have ht : s.owner.contains k = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hv]
        rfl
      exact (hc ht).elim
  · split at h
    · split at h <;> cases h
    · cases h

theorem collapseGroup_inductive_fresh {st : State .source} {s s' : CollapseState}
    {kb kb' : KeptBlocks} {first : SKey} {position : Nat} {rb : BlockRead .source}
    {r : Read .source} {dropped : Array SKey}
    (h : collapseGroup st s kb first position (.ok (.inductive rb)) =
      .lowered s' kb' r dropped) :
    ∀ k ∈ Ix.LeanIngress.BlockRead.names rb, s.owner[k]? = none := by
  cases ha : kb.alias s first rb with
  | error e => simp [collapseGroup, ha] at h
  | ok a =>
    cases a with
    | some i => simp [collapseGroup, ha] at h
    | none => exact alias_none_fresh ha

/-- An `Id` loop either processes the whole input while preserving an
invariant, or stops in the explicitly classified failure state. -/
theorem forIn_id_inv_or {α σ : Type} (I : List α → σ → Prop) (Bad : σ → Prop)
    (body : α → σ → Id (ForInStep σ)) (full : List α)
    (step : ∀ pre x post s, pre ++ x :: post = full → I pre s →
      match body x s with
      | .yield s' => I (pre ++ [x]) s'
      | .done s' => Bad s') :
    ∀ post pre s, pre ++ post = full → I pre s →
      I full (forIn (m := Id) post s body) ∨ Bad (forIn (m := Id) post s body) := by
  intro post
  induction post with
  | nil =>
    intro pre s whole holds
    simp only [List.append_nil] at whole
    cases whole
    exact Or.inl holds
  | cons x post ih =>
    intro pre s whole holds
    have hs := step pre x post s whole holds
    rw [List.forIn_cons]
    cases hb : body x s with
    | done s' =>
      rw [hb] at hs
      exact Or.inr hs
    | yield s' =>
      rw [hb] at hs
      exact ih (pre ++ [x]) s' (by simpa [List.append_assoc] using whole) hs

theorem forIn_id_inv_or_array {α σ : Type} (I : List α → σ → Prop) (Bad : σ → Prop)
    (body : α → σ → Id (ForInStep σ)) (xs : Array α)
    (step : ∀ pre x post s, pre ++ x :: post = xs.toList → I pre s →
      match body x s with
      | .yield s' => I (pre ++ [x]) s'
      | .done s' => Bad s') (s : σ) (holds : I [] s) :
    I xs.toList (forIn (m := Id) xs s body) ∨ Bad (forIn (m := Id) xs s body) := by
  rw [← Array.forIn_toList]
  exact forIn_id_inv_or I Bad body xs.toList step xs.toList [] s rfl holds

abbrev ReadResult := CollapseState × Except CollapseError (Read .source × Array SKey)
abbrev ReadAcc := Option ReadResult × CollapseState × Array (Declaration .source) × Nat × Array SKey

/-- The elaborated body of `collapseRead`, named only in the proof module. -/
def readStep (first : SKey) (originalSize generated : Nat)
    (x : Declaration .source × Nat) (a : ReadAcc) : Id (ForInStep ReadAcc) :=
  match x with
  | (d, j) => match a.2.1.step first d with
    | (s', res) => match res with
      | .error e => pure <| .done
          (some (s'.restore originalSize, .error e),
            s', a.2.2.1, a.2.2.2.1, a.2.2.2.2)
      | .ok true =>
        if j < generated then
          pure <| .yield (none, s', a.2.2.1.push d, a.2.2.2.1 + 1, a.2.2.2.2)
        else
          pure <| .yield (none, s', a.2.2.1.push d, a.2.2.2.1, a.2.2.2.2)
      | .ok false =>
        pure <| .yield (none, s', a.2.2.1, a.2.2.2.1,
          a.2.2.2.2.push (Declaration.names d |>.head?.getD (.id .anonymous)))

def readLoop (s : CollapseState) (first : SKey) (r : Read .source) : ReadAcc :=
  forIn (m := Id) r.decls.zipIdx (none, s, #[], 0, #[])
    (readStep first s.kept.size r.generated)

def readFinish (r : Read .source) (a : ReadAcc) : ReadResult :=
  match a.1 with
  | some v => v
  | none => (a.2.1, .ok ({ r with decls := a.2.2.1, generated := a.2.2.2.1 }, a.2.2.2.2))

theorem collapseRead_eq (s : CollapseState) (first : SKey) (r : Read .source) :
    collapseRead s first r = readFinish r (readLoop s first r) := by
  simp +unfoldPartialApp only [collapseRead, readFinish, readLoop, readStep, Id.run, bind, pure]
  unfold Break.runK.match_1 collapseRead.match_1 readStep.match_1 readFinish.match_1
  rfl

def OwnerExt (s t : CollapseState) : Prop :=
  ∀ (k : SKey) (v : Nat), s.owner[k]? = some v → t.owner[k]? = some v

theorem OwnerExt.refl (s : CollapseState) : OwnerExt s s := fun _ _ h => h

theorem OwnerExt.trans {s t u : CollapseState} (h : OwnerExt s t) (h' : OwnerExt t u) :
    OwnerExt s u := fun k v hk => h' k v (h k v hk)

theorem OwnerExt.isSome {s t : CollapseState} (h : OwnerExt s t) {k : SKey}
    (hk : (s.owner[k]?).isSome = true) : (t.owner[k]?).isSome = true := by
  cases hv : s.owner[k]? with
  | none => simp [hv] at hk
  | some v => rw [h k v hv]; rfl

theorem OwnerExt.fresh {s t : CollapseState} (h : OwnerExt s t) {k : SKey}
    (hk : t.owner[k]? = none) : s.owner[k]? = none := by
  cases hv : s.owner[k]? with
  | none => rfl
  | some v => rw [h k v hv] at hk; cases hk

theorem step_kept {s s' : CollapseState} {first : SKey}
    {d : Declaration .source} {kept : Bool} (h : s.step first d = (s', .ok kept)) :
    s'.kept = if kept then s.kept.push d else s.kept := by
  obtain ⟨ds, owner⟩ := s
  unfold CollapseState.step at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

structure ReadInv (start : CollapseState) (pre : List (Declaration .source × Nat))
    (a : ReadAcc) : Prop where
  active : a.1 = none
  monotone : OwnerExt start a.2.1
  claims : ∀ x ∈ pre, ∀ k ∈ x.1.names, (a.2.1.owner[k]?).isSome = true
  fresh : ∀ d ∈ a.2.2.1.toList, ∀ k ∈ d.names, start.owner[k]? = none
  keptClaims : ∀ d ∈ a.2.2.1.toList, ∀ k ∈ d.names, (a.2.1.owner[k]?).isSome = true
  subset : ∀ d ∈ a.2.2.1.toList, ∃ j, (d, j) ∈ pre
  kept : a.2.1.kept = start.kept ++ a.2.2.1

def ReadBad (a : ReadAcc) : Prop := ∃ s e, a.1 = some (s, .error e)

theorem readStep_inv {start : CollapseState} {pre : List (Declaration .source × Nat)}
    {a : ReadAcc} (ha : ReadInv start pre a) (first : SKey) (originalSize generated : Nat)
    (x : Declaration .source × Nat) :
    match readStep first originalSize generated x a with
    | .yield a' => ReadInv start (pre ++ [x]) a'
    | .done a' => ReadBad a' := by
  rcases hs : a.2.1.step first x.1 with ⟨s', res⟩
  cases res with
  | error e =>
    simp only [readStep, hs, pure]
    exact ⟨s'.restore originalSize, e, rfl⟩
  | ok kept =>
    have hf := step_ownerFacts hs
    have he : OwnerExt a.2.1 s' := hf.1
    have hc : ∀ y ∈ pre ++ [x], ∀ k ∈ y.1.names, (s'.owner[k]?).isSome = true := by
      intro y hy k hk
      rcases List.mem_append.mp hy with hy | hy
      · exact he.isSome (ha.claims y hy k hk)
      · simp only [List.mem_singleton] at hy
        subst y
        exact hf.2.1 k hk
    have hm := step_kept hs
    cases kept with
    | false =>
      simp only [readStep, hs, pure]
      exact ⟨rfl, ha.monotone.trans he, hc, ha.fresh,
        fun d hd k hk => he.isSome (ha.keptClaims d hd k hk),
        fun d hd => by
          obtain ⟨j, hj⟩ := ha.subset d hd
          exact ⟨j, List.mem_append_left _ hj⟩,
        hm.trans ha.kept⟩
    | true =>
      have hi (gen : Nat) : ReadInv start (pre ++ [x])
          (none, s', a.2.2.1.push x.1, gen, a.2.2.2.2) := by
        refine ⟨rfl, ha.monotone.trans he, hc, ?_, ?_, ?_, ?_⟩
        · intro d hd k hk
          have hd : d ∈ a.2.2.1.toList ∨ d = x.1 := by simpa using hd
          rcases hd with hd | hd
          · exact ha.fresh d hd k hk
          · subst d
            exact ha.monotone.fresh (hf.2.2 rfl k hk)
        · intro d hd k hk
          have hd : d ∈ a.2.2.1.toList ∨ d = x.1 := by simpa using hd
          rcases hd with hd | hd
          · exact he.isSome (ha.keptClaims d hd k hk)
          · subst d
            exact hf.2.1 k hk
        · intro d hd
          have hd : d ∈ a.2.2.1.toList ∨ d = x.1 := by simpa using hd
          rcases hd with hd | hd
          · obtain ⟨j, hj⟩ := ha.subset d hd
            exact ⟨j, List.mem_append_left _ hj⟩
          · subst d
            exact ⟨x.2, List.mem_append_right _ (by simp)⟩
        · simpa [ha.kept] using hm
      by_cases hj : x.2 < generated
      · simpa only [readStep, hs, hj, ite_true, pure] using hi (a.2.2.2.1 + 1)
      · simpa only [readStep, hs, hj, ite_false, pure] using hi a.2.2.2.1

theorem collapseRead_facts {s s' : CollapseState} {first : SKey}
    {r r' : Read .source} {dropped : Array SKey}
    (h : collapseRead s first r = (s', .ok (r', dropped))) :
    OwnerExt s s' ∧
    (∀ d ∈ r.decls.toList, ∀ k ∈ d.names, (s'.owner[k]?).isSome = true) ∧
    (∀ d ∈ r'.decls.toList, ∀ k ∈ d.names, s.owner[k]? = none ∧
      (s'.owner[k]?).isSome = true) ∧
    (∀ d ∈ r'.decls.toList, d ∈ r.decls.toList) ∧
    s'.kept = s.kept ++ r'.decls ∧ r'.owners = r.owners ∧ r'.blocks = r.blocks := by
  have init : ReadInv s [] (none, s, #[], 0, #[]) :=
    ⟨rfl, .refl s, by simp, by simp, by simp, by simp, by simp⟩
  have inv := forIn_id_inv_or_array (ReadInv s) ReadBad
    (readStep first s.kept.size r.generated) r.decls.zipIdx
    (fun _ x _ a _ ha => by
      have hi := readStep_inv ha first s.kept.size r.generated x
      cases hb : readStep first s.kept.size r.generated x a <;>
        simpa only [hb] using hi) _ init
  change ReadInv s r.decls.zipIdx.toList (readLoop s first r) ∨
    ReadBad (readLoop s first r) at inv
  rw [collapseRead_eq] at h
  rcases inv with hi | hb
  · have hf : (readLoop s first r).1 = none := hi.active
    simp only [readFinish, hf, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨hst, hr, _⟩
    subst s'
    subst r'
    refine ⟨hi.monotone, ?_, ?_, ?_, hi.kept, rfl, rfl⟩
    · intro d hd k hk
      obtain ⟨j, hj⟩ := List.mem_map.mp (show d ∈ (r.decls.zipIdx.toList.map Prod.fst) by simpa using hd)
      exact hi.claims j hj.1 k (by simpa [hj.2] using hk)
    · intro d hd k hk
      exact ⟨hi.fresh d hd k hk, hi.keptClaims d hd k hk⟩
    · intro d hd
      obtain ⟨j, hj⟩ := hi.subset d hd
      have hm : d ∈ r.decls.zipIdx.toList.map Prod.fst := List.mem_map.mpr ⟨(d, j), hj, rfl⟩
      simpa using hm
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

/-- Every kept group retains both the raw lowering and its actual collapse. -/
theorem collapseGroup_lowered {st : State .source} {s s' : CollapseState}
    {kb kb' : KeptBlocks} {first : SKey} {pos : Nat} {c : Except ReadError Converted}
    {r : Read .source} {dropped : Array SKey}
    (h : collapseGroup st s kb first pos c = .lowered s' kb' r dropped) :
    ∃ conv raw, c = .ok conv ∧ lower st conv = .ok raw ∧
      collapseRead s first raw = (s', .ok (r, dropped)) := by
  cases c with
  | error e => simp [collapseGroup] at h
  | ok c =>
    unfold collapseGroup at h
    dsimp only at h
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · rename_i raw hl
        split at h
        · cases h
        · rename_i s'' r'' dropped' hc
          cases h
          exact ⟨c, raw, rfl, hl, hc⟩

theorem collapseGroup_alias_states {st : State .source} {s s' : CollapseState}
    {kb kb' : KeptBlocks} {first : SKey} {pos i : Nat} {c : Except ReadError Converted}
    (h : collapseGroup st s kb first pos c = .alias i s' kb') : s' = s ∧ kb' = kb := by
  cases c with
  | error e => simp [collapseGroup] at h
  | ok c =>
    unfold collapseGroup at h
    dsimp only at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
    · split at h
      · cases h
      · split at h <;> cases h

abbrev Scheduled := (Nat × Except ReadError Converted) × Nat

/-- A trace of the actual quotient Source loop. Aliases contribute no read;
each lowered step retains the raw reading, its lower equation, and its collapse
equation, as well as the kept reading the reader actually commits. -/
inductive Trace (g : Graph) (start : State .source) :
    List Scheduled → List (Read .source) → State .source → CollapseState → KeptBlocks → Prop
  | nil : Trace g start [] [] start {} {}
  | alias {xs rs st s kb x i} : Trace g start xs rs st s kb →
      collapseGroup st s kb g.groups[x.1.1]!.name x.2 x.1.2 = .alias i s kb →
      Trace g start (xs ++ [x]) rs st s kb
  | lowered {xs rs st s kb x s' kb' conv raw r dropped} :
      Trace g start xs rs st s kb → x.1.2 = .ok conv →
      lower st conv = .ok raw →
      collapseRead s g.groups[x.1.1]!.name raw = (s', .ok (r, dropped)) →
      collapseGroup st s kb g.groups[x.1.1]!.name x.2 x.1.2 = .lowered s' kb' r dropped →
      Trace g start (xs ++ [x]) (rs ++ [r]) (st.commit r) s' kb'

theorem Trace.fold {g : Graph} {start st : State .source} {xs rs s kb}
    (h : Trace g start xs rs st s kb) : st = rs.foldl State.commit start := by
  induction h with
  | nil => rfl
  | «alias» _ _ ih => exact ih
  | lowered _ _ _ _ _ ih => simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using congrArg (State.commit · _) ih

theorem Trace.decls {g : Graph} {start st : State .source} {xs rs s kb}
    (h : Trace g start xs rs st s kb) :
    s.kept.toList = rs.flatMap (·.decls.toList) := by
  induction h with
  | nil => rfl
  | «alias» _ _ ih => exact ih
  | lowered _ _ _ hr _ ih =>
    have hk := (collapseRead_facts hr).2.2.2.2.1
    simp [hk, ih]

/-- Successful production lowering has a trace with the exact kept-read fold
and declaration concatenation. This theorem assumes no checker acceptance. -/
theorem lowerAllCollapsed_trace {start fin : State .source} {g : Graph}
    {scheduled : Array (Nat × Except ReadError Converted)} {decls : Array (Declaration .source)}
    (h : lowerAllCollapsed start g scheduled = .ok (fin, decls)) :
    ∃ rs s kb, Trace g start scheduled.zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧ fin = rs.foldl State.commit start ∧
      decls.toList = rs.flatMap (·.decls.toList) := by
  unfold lowerAllCollapsed at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i res hr
    cases h
    have inv := Ix.CompileCert.Loop.forIn_inv_array
      (fun pre (a : State .source × CollapseState × KeptBlocks) =>
        ∃ rs, Trace g start pre rs a.1 a.2.1 a.2.2) _ scheduled.zipIdx
      (fun pre x _ a q _ hI hq => by
        obtain ⟨rs, ht⟩ := hI
        rcases x with ⟨⟨gi, c⟩, i⟩
        cases hg : collapseGroup a.1 a.2.1 a.2.2 g.groups[gi]!.name i c with
        | refused e s kb => simp [hg, throw] at hq
        | «alias» j s kb =>
          simp only [hg, Except.ok.injEq] at hq
          subst q
          obtain ⟨rfl, rfl⟩ := collapseGroup_alias_states hg
          exact ⟨_, rfl, rs, .alias ht hg⟩
        | lowered s kb r dropped =>
          simp only [hg, Except.ok.injEq] at hq
          subst q
          obtain ⟨conv, raw, hc, hl, hcol⟩ := collapseGroup_lowered hg
          exact ⟨_, rfl, rs ++ [r], .lowered ht hc hl hcol hg⟩)
      ⟨[], .nil⟩ hr
    obtain ⟨rs, ht⟩ := inv
    exact ⟨rs, res.2.1, res.2.2, ht, rfl, ht.fold, ht.decls⟩

theorem sameAt_refl (st : State .source) (k : SKey) : st.SameAt st k :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sameAt_trans {a b c : State .source} {k : SKey}
    (h : a.SameAt b k) (h' : b.SameAt c k) : a.SameAt c k :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

/-- The local frame obligation: only a previously unowned key claimed by this
group may change. The production prefix theorem discharges it from lowering
shape and successful collapse, without adding a checker or final premise. -/
def GroupFrame : Prop := ∀ (st : State .source) (s s' : CollapseState)
    (kb kb' : KeptBlocks) (first : SKey) (pos : Nat) (c : Except ReadError Converted)
    (r : Read .source) (dropped : Array SKey),
    collapseGroup st s kb first pos c = .lowered s' kb' r dropped →
    ∀ k, (s.owner[k]?).isSome = true ∨ s'.owner[k]? = none →
      (st.commit r).SameAt st k

/-- Once a group claims a key, later groups cannot change it. Before the key
is claimed its entries are the initial entries. Thus every boundary holds
either the initial or final entries, without an overwrite-and-restore gap. -/
theorem Trace.endpoints (frame : GroupFrame) {g : Graph} {start st : State .source}
    {xs rs s kb} (h : Trace g start xs rs st s kb) :
    (∀ k, s.owner[k]? = none → st.SameAt start k) ∧
    (∀ i k, ((rs.take i).foldl State.commit start).SameAt start k ∨
      ((rs.take i).foldl State.commit start).SameAt st k) := by
  induction h with
  | nil => exact ⟨fun k _ => sameAt_refl _ k,
      fun i k => .inl (by simpa only [List.take_nil, List.foldl_nil] using sameAt_refl start k)⟩
  | «alias» _ _ ih => exact ih
  | @lowered xs rs st s kb x s' kb' conv raw r dropped ht hc hl hr hg ih =>
    have ho := (collapseRead_facts hr).1
    have hf := frame st s s' kb kb' _ _ _ r dropped hg
    refine ⟨?_, ?_⟩
    · intro k hk
      exact sameAt_trans (hf k (.inr hk)) (ih.1 k (ho.fresh hk))
    · intro i k
      by_cases hi : i ≤ rs.length
      · rw [List.take_append_of_le_length hi]
        rcases ih.2 i k with hp | hp
        · exact .inl hp
        · cases hv : s.owner[k]? with
          | none => exact .inl (sameAt_trans hp (ih.1 k hv))
          | some v =>
            have he := hf k (.inl (by simp [hv]))
            have hs : st.SameAt (st.commit r) k :=
              ⟨he.1.symm, he.2.1.symm, he.2.2.1.symm, he.2.2.2.1.symm, he.2.2.2.2.symm⟩
            exact .inr (sameAt_trans hp hs)
      · have hi' : (rs ++ [r]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
        rw [List.take_of_length_le hi']
        right
        simpa [List.foldl_append, ← ht.fold] using sameAt_refl (st.commit r) k

theorem Trace.prefix_of_frame (frame : GroupFrame) {g : Graph} {pre fin : State .source}
    {xs rs s kb} (h : Trace g pre xs rs fin s kb)
    (keeps : State.keepsPrelude pre fin = true) :
    ∀ i k, k ∈ pre.keys → ((rs.take i).foldl State.commit pre).SameAt pre k := by
  intro i k hk
  rcases (h.endpoints frame).2 i k with hp | hp
  · exact hp
  · exact sameAt_trans hp (State.keepsPrelude_iff.mp keeps k hk)

theorem projRecOwners_keys {block : List (Ix.Kernel.ConstantInfo .source)}
    {types : List (SKey × List LevelParam × Ix.Kernel.Expr .source × Nat × Nat × List SKey × Bool)}
    {ctors : List (SKey × Nat × Ix.Kernel.Expr .source)}
    {recs : List (SKey × List LevelParam × Ix.Kernel.Expr .source × Nat × Nat)}
    {o : Frontend.ProjRecOwner .source} (ho : o ∈ Frontend.projRecOwners block types ctors recs) :
    o.T ∈ types.map Prod.fst := by
  unfold Frontend.projRecOwners at ho
  dsimp only at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · obtain ⟨t, ht, hf⟩ := List.mem_filterMap.mp ho
      have hk : o.T = t.1.1 := by
        obtain ⟨⟨T, lps, tty, nP, nI, cs, isRec⟩, j⟩ := t
        simp only [bind, Option.bind, guard, pure] at hf
        repeat' first | (dsimp only at hf) | (split at hf) | (cases hf)
        all_goals rfl
      rw [hk]
      have hm : t.1 ∈ types := by
        have hm : t.1 ∈ types.zipIdx.map Prod.fst := List.mem_map.mpr ⟨t, ht, rfl⟩
        simpa using hm
      exact List.mem_map.mpr ⟨t.1, hm, rfl⟩

theorem lowerInductive_sideNames {st : State .source} {rb : BlockRead .source}
    {r : Read .source} (h : lowerInductive st rb = .ok r) :
    (∀ o ∈ r.owners, o.T ∈ Ix.LeanIngress.BlockRead.names rb) ∧
    (∀ b ∈ r.blocks, b.1 ∈ Ix.LeanIngress.BlockRead.names rb) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  have keyMem (x : (CVal .source × Nat × Nat) × List SKey)
      (hx : x ∈ types.toList.zip ctorNames.toList) :
      x.1.1.name ∈ Ix.LeanIngress.BlockRead.names ⟨nPd, types, ctors, ctorNames, recs⟩ := by
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨x.1, (List.of_mem_zip hx).1, rfl⟩))
  unfold lowerInductive at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases ReaderUnits.ite_ok h with h | h
    all_goals first
      | (obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h)
      | skip
    all_goals
      rcases ReaderUnits.ite_ok h with h | h
      · split at h
        · simp [declined, throw, throwThe, MonadExceptOf.throw] at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst r
          constructor
          · intro o ho
            have hm := projRecOwners_keys ho
            simp only [List.map_map] at hm
            obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
            rw [← he]
            exact keyMem x hx
          · intro b hb
            have hm := (List.mem_map (f := Prod.fst)).mpr ⟨b, hb, rfl⟩
            simp only [List.map_map] at hm
            obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
            rw [← he]
            exact keyMem x hx
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst r
        constructor
        · intro o ho
          have hm := projRecOwners_keys ho
          simp only [List.map_map] at hm
          obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
          rw [← he]
          exact keyMem x hx
        · intro b hb
          have hm := (List.mem_map (f := Prod.fst)).mpr ⟨b, hb, rfl⟩
          simp only [List.map_map] at hm
          obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
          rw [← he]
          exact keyMem x hx

def NoBasis (d : Declaration .source) : Prop := ∀ k, d ≠ .basisDecl k

theorem noBasis_of_names {d : Declaration .source} {k : SKey} (h : d.names = [k]) : NoBasis d := by
  intro kind he
  subst d
  cases h

theorem lower_nonind {st : State .source} {c : Converted} {r : Read .source}
    (hc : ∀ rb, c ≠ .inductive rb) (h : lower st c = .ok r) :
    (∀ d ∈ r.decls.toList, NoBasis d) ∧ r.owners = [] ∧ r.blocks = [] := by
  cases c with
  | «inductive» rb => exact (hc rb rfl).elim
  | definitions ms =>
    unfold lower at h
    delta Ix.LeanIngress.lower.match_6 at h
    dsimp only at h
    split at h
    · rename_i hsz
      obtain ⟨l⟩ := ms
      obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
      · cases hsz
      · simp only at h
        obtain ⟨⟨decl, rw⟩, hd, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst r
        refine ⟨?_, rfl, rfl⟩
        intro d hd'
        simp at hd'
        subst d
        exact noBasis_of_names (ReaderUnits.lowerDefinition_names hd)
      · simp at hsz
    · obtain ⟨s, hs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst r
      have safe := ReaderUnits.forIn_pushes (fun s => s.2.1) NoBasis _ _
        (fun _ _ _ q hq => by
          obtain ⟨⟨decl, rw⟩, hd, hq⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hq
          have hn := noBasis_of_names (ReaderUnits.lowerDefinition_names hd)
          dsimp only at hq
          split at hq <;> split at hq <;>
          · simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst q
            refine ⟨_, rfl, fun e he => ?_⟩
            rcases Array.mem_push.mp he with he | rfl
            · exact .inl he
            · exact .inr hn)
        (by simp) hs
      exact ⟨fun d hd => safe d (Array.mem_def.mpr hd), rfl, rfl⟩
  | «axiom» cv =>
    cases h
    refine ⟨?_, rfl, rfl⟩
    intro d hd
    simp at hd
    subst d
    intro _ h
    cases h
  | quot kind cv =>
    cases h
    refine ⟨?_, rfl, rfl⟩
    intro d hd
    simp at hd
    subst d
    intro _ h
    cases h

/-- Filtering declarations does not filter side arrays. Their keys are fresh
because an inductive group is lowered only at fresh block names; the raw
closing declaration claims all of those names even if collapse drops it. -/
theorem collapseGroup_sideFresh {st : State .source} {s s' : CollapseState}
    {kb kb' : KeptBlocks} {first : SKey} {pos : Nat} {c : Except ReadError Converted}
    {r : Read .source} {dropped : Array SKey}
    (h : collapseGroup st s kb first pos c = .lowered s' kb' r dropped) :
    (∀ o ∈ r.owners, s.owner[o.T]? = none ∧ (s'.owner[o.T]?).isSome = true) ∧
    (∀ b ∈ r.blocks, s.owner[b.1]? = none ∧ (s'.owner[b.1]?).isSome = true) := by
  obtain ⟨conv, raw, rfl, hl, hr⟩ := collapseGroup_lowered h
  obtain ⟨_, claims, _, _, _, owners, blocks⟩ := collapseRead_facts hr
  by_cases hi : ∃ rb, conv = .inductive rb
  · obtain ⟨rb, rfl⟩ := hi
    have fresh := collapseGroup_inductive_fresh h
    have sides := lowerInductive_sideNames hl
    obtain ⟨gens, d, hd, _, hn⟩ := ReaderUnits.lowerInductive_decls hl
    have claim : ∀ k ∈ Ix.LeanIngress.BlockRead.names rb, (s'.owner[k]?).isSome = true := by
      intro k hk
      apply claims d (by rw [hd]; simp) k
      simpa only [hn, Ix.LeanIngress.BlockRead.names] using hk
    constructor
    · intro o ho
      rw [owners] at ho
      have hk := sides.1 o ho
      exact ⟨fresh _ hk, claim _ hk⟩
    · intro b hb
      rw [blocks] at hb
      have hk := sides.2 b hb
      exact ⟨fresh _ hk, claim _ hk⟩
  · have hn := lower_nonind (fun rb he => hi ⟨rb, he⟩) hl
    simp [owners, blocks, hn.2.1, hn.2.2]

theorem fold_ins_other {α β : Type} (g : α → Option (SKey × β)) (k : SKey) :
    ∀ (xs : List α) (m : Std.HashMap SKey β),
    (∀ x ∈ xs, ∀ p, g x = some p → p.1 ≠ k) →
    (xs.foldl (CtxAgree.insOpt g) m)[k]? = m[k]? := by
  intro xs
  induction xs with
  | nil => intro m _; rfl
  | cons x xs ih =>
    intro m hn
    rw [List.foldl_cons, ih _ (fun y hy => hn y (List.mem_cons_of_mem _ hy))]
    unfold CtxAgree.insOpt
    cases hg : g x with
    | none => rfl
    | some p =>
      rw [Std.HashMap.getElem?_insert]
      simp [hn x List.mem_cons_self p hg]

theorem noteEntries_names {d : Declaration .source} (hb : NoBasis d) :
    (CtxAgree.noteEntries d).map Prod.fst = d.names := by
  cases d with
  | basisDecl k => exact (hb k rfl).elim
  | indDecl block n => simp only [CtxAgree.noteEntries, Declaration.names, List.map_map]; rfl
  | _ => rfl

theorem note_aux (st : State .source) (d : Declaration .source) :
    (st.note d).projOwners = st.projOwners ∧ (st.note d).projLevels = st.projLevels := by
  cases d <;> constructor <;>
    exact CtxAgree.foldl_keep _ _ (fun s e => by obtain ⟨n, lps, ty, h⟩ := e; rfl) _ _

theorem note_other (st : State .source) (d : Declaration .source) (k : SKey)
    (hb : NoBasis d) (hk : k ∉ d.names) : (st.note d).SameAt st k := by
  have he : ∀ e ∈ CtxAgree.noteEntries d, e.1 ≠ k := by
    intro e hm heq
    apply hk
    rw [← noteEntries_names hb, ← heq]
    exact List.mem_map.mpr ⟨e, hm, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [CtxAgree.note_constTypes]
    apply fold_ins_other
    intro e hm p hp
    cases hp
    exact he e hm
  · rw [CtxAgree.note_heights]
    apply fold_ins_other
    intro e hm p hp
    unfold CtxAgree.htOf at hp
    cases hh : e.2.2.2 with
    | none => simp [hh] at hp
    | some v => simp only [hh, Option.map_some, Option.some.injEq] at hp; subst p; exact he e hm
  · rw [CtxAgree.note_indBlocks]
  · rw [(note_aux st d).1]
  · rw [(note_aux st d).2]

theorem noteGenerated_other (st : State .source) (d : Declaration .source) (k : SKey)
    (hb : NoBasis d) (hk : k ∉ d.names) : (st.noteGenerated d).SameAt st k := by
  cases d with
  | thmDecl cv value =>
    have hn : cv.name ≠ k := by simpa [Declaration.names, eq_comm] using hk
    unfold State.noteGenerated
    by_cases hp : cv.name.isProjIota = true
    · simp only [hp, ite_true]
      cases hl : Frontend.projIotaLevel cv.type with
      | none => exact note_other st (.thmDecl cv value) k hb hk
      | some l =>
        apply sameAt_trans (note_other _ (.thmDecl cv value) k hb hk)
        exact ⟨rfl, rfl, rfl, rfl, by simp [Std.HashMap.getElem?_insert, hn]⟩
    · simp only [hp]
      exact note_other st (.thmDecl cv value) k hb hk
  | _ => exact note_other st _ k hb hk

theorem sameAt_fold {α : Type} (f : State .source → α → State .source) (k : SKey) :
    ∀ (xs : List α) (st : State .source),
    (∀ x ∈ xs, ∀ s, (f s x).SameAt s k) → (xs.foldl f st).SameAt st k := by
  intro xs
  induction xs with
  | nil => intro st _; exact sameAt_refl st k
  | cons x xs ih =>
    intro st hf
    exact sameAt_trans (ih _ (fun y hy => hf y (List.mem_cons_of_mem _ hy)))
      (hf x List.mem_cons_self st)

theorem commit_other (st : State .source) (r : Read .source) (k : SKey)
    (hd : ∀ d ∈ r.decls.toList, NoBasis d ∧ k ∉ d.names)
    (ho : ∀ o ∈ r.owners, o.T ≠ k) (hb : ∀ b ∈ r.blocks, b.1 ≠ k) :
    (st.commit r).SameAt st k := by
  let s₁ := r.owners.foldl (fun s o => { s with projOwners := s.projOwners.insert o.T o }) st
  let s₂ := r.blocks.foldl (fun s b => { s with indBlocks := s.indBlocks.insert b.1 b.2 }) s₁
  let s₃ := r.decls.toList.zipIdx.foldl
    (fun s x => if x.2 < r.generated then s.noteGenerated x.1 else s.note x.1) s₂
  rw [CtxAgree.commit_eq]
  change s₃.SameAt st k
  have h₁ : s₁.SameAt st k := sameAt_fold _ k r.owners st (by
    intro o hm s
    exact ⟨rfl, rfl, rfl, by simp [Std.HashMap.getElem?_insert, ho o hm], rfl⟩)
  have h₂ : s₂.SameAt s₁ k := sameAt_fold _ k r.blocks s₁ (by
    intro b hm s
    exact ⟨rfl, rfl, by simp [Std.HashMap.getElem?_insert, hb b hm], rfl, rfl⟩)
  have h₃ : s₃.SameAt s₂ k := sameAt_fold _ k r.decls.toList.zipIdx s₂ (by
    intro x hx s
    have hm : x.1 ∈ r.decls.toList := by
      have hm := (List.mem_map (f := Prod.fst)).mpr ⟨x, hx, rfl⟩
      simpa using hm
    split
    · exact noteGenerated_other s x.1 k (hd x.1 hm).1 (hd x.1 hm).2
    · exact note_other s x.1 k (hd x.1 hm).1 (hd x.1 hm).2)
  exact sameAt_trans h₃ (sameAt_trans h₂ h₁)

def LowerNoBasis : Prop := ∀ (st : State .source) (c : Converted) (r : Read .source),
  lower st c = .ok r → ∀ d ∈ r.decls.toList, NoBasis d

/-- The producer's syntactic shape is the last ingredient of the local frame;
raw claims, retained declarations and unfiltered side arrays have separate
proofs, so filtering cannot hide a write to an already-owned key. -/
theorem groupFrame_of_lowerShape (basis : LowerNoBasis) : GroupFrame := by
  intro st s s' kb kb' first pos c r dropped h k hk
  obtain ⟨conv, raw, hc, hl, hr⟩ := collapseGroup_lowered h
  obtain ⟨_, _, fresh, subset, _, _, _⟩ := collapseRead_facts hr
  have side := collapseGroup_sideFresh h
  have outside : ∀ n, s.owner[n]? = none ∧ (s'.owner[n]?).isSome = true → n ≠ k := by
    intro n hn he
    subst n
    rcases hk with hk | hk
    · simp [hn.1] at hk
    · simp [hk] at hn
  apply commit_other
  · intro d hd
    refine ⟨basis st conv raw hl d (subset d hd), ?_⟩
    intro hm
    exact outside k (fresh d hd k hm) rfl
  · intro o ho
    exact outside _ (side.1 o ho)
  · intro b hb
    exact outside _ (side.2 b hb)

theorem lowerNoBasis_of_generate
    (hg : ∀ (ctx : Frontend.InModel.Ctx .source) (b : Frontend.InModel.BlockRec .source)
      (ds : List (Declaration .source)), Frontend.InModel.generate ctx b = .ok ds →
        ∀ d ∈ ds, NoBasis d) : LowerNoBasis := by
  intro st c r h
  by_cases hi : ∃ rb, c = .inductive rb
  · obtain ⟨rb, rfl⟩ := hi
    obtain ⟨gens, hd, _, _, hgen⟩ := CtxAgree.lowerInductive_ok h
    intro d hm
    have hm : d ∈ gens ∨ d = CtxAgree.indDeclOf rb := by simpa [hd] using hm
    rcases hm with hm | rfl
    · rcases hgen with ⟨_, hgen⟩ | ⟨_, rfl⟩
      · exact hg _ _ _ hgen d hm
      · cases hm
    · intro k he
      cases he
  · exact (lower_nonind (fun rb he => hi ⟨rb, he⟩) h).1

end Ix.Cert.SourcePrelude

/-! ## The modeller's output constructors -/

namespace Ix.Cert.SourcePrelude.Shape

open Ix.Kernel Ix.Kernel.Frontend.InModel

variable {α β σ ε : Type}

/-- The producer-shape proof tracks declaration tags through binds and loops.
Other data has a trivial invariant. The explicit `generate_noBasis` endpoint
is checked by the kernel, independently of the elaboration tactics below. -/
class Safe (α : Type) where
  holds : α → Prop

instance (priority := 10) safeAny (α : Type) : Safe α := ⟨fun _ => True⟩
instance safeDecl : Safe (Declaration md) := ⟨fun d => ∀ k, d ≠ .basisDecl k⟩
instance [Safe α] : Safe (Array α) := ⟨fun xs => ∀ x ∈ xs, Safe.holds x⟩
instance [Safe α] : Safe (List α) := ⟨fun xs => ∀ x ∈ xs, Safe.holds x⟩
instance [Safe α] [Safe β] : Safe (α × β) := ⟨fun x => Safe.holds x.1 ∧ Safe.holds x.2⟩
instance [Safe α] : Safe (ForInStep α) := ⟨fun x => match x with
  | .done a | .yield a => Safe.holds a⟩

theorem Safe.pair [Safe α] [Safe β] {a : α} {b : β}
    (ha : Safe.holds a) (hb : Safe.holds b) : Safe.holds (a, b) := ⟨ha, hb⟩
theorem Safe.fst [Safe α] [Safe β] {p : α × β} (h : Safe.holds p) : Safe.holds p.1 := h.1
theorem Safe.snd [Safe α] [Safe β] {p : α × β} (h : Safe.holds p) : Safe.holds p.2 := h.2
theorem Safe.yield [Safe α] {a : α} (ha : Safe.holds a) : Safe.holds (.yield a : ForInStep α) := ha
theorem Safe.push [Safe α] {xs : Array α} {a : α}
    (hx : Safe.holds xs) (ha : Safe.holds a) : Safe.holds (xs.push a) := by
  intro x h
  rcases Array.mem_push.mp h with h | rfl
  · exact hx x h
  · exact ha
theorem Safe.empty [Safe α] : Safe.holds (#[] : Array α) := by intro x h; simp at h
theorem Safe.toList [Safe α] {xs : Array α} (h : Safe.holds xs) : Safe.holds xs.toList := by
  intro x hx
  exact h x (Array.mem_toList_iff.mp hx)
theorem Safe.ind (block : List (Ix.Kernel.ConstantInfo md)) (n : Nat) : Safe.holds (.indDecl block n : Declaration md) := by
  intro k h; cases h
theorem Safe.defn (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) (hint : Ix.Kernel.ReducibilityHint) :
    Safe.holds (.defnDecl cv v hint : Declaration md) := by intro k h; cases h
theorem Safe.thm (cv : Ix.Kernel.ConstantVal md) (v : Ix.Kernel.Expr md) :
    Safe.holds (.thmDecl cv v : Declaration md) := by intro k h; cases h
theorem Safe.of_all [Safe α] {a : α} (h : ∀ x : α, Safe.holds x) : Safe.holds a := h a

def ExSafe [Safe α] (e : Except ε α) : Prop := ∀ a, e = .ok a → Safe.holds a

theorem ExSafe.of_all [Safe α] (e : Except ε α) (h : ∀ a : α, Safe.holds a) : ExSafe e :=
  fun a _ => h a

theorem ExSafe.pure [Safe α] {a : α} (h : Safe.holds a) : ExSafe (.ok a : Except ε α) := by
  intro a' he
  cases he
  exact h

theorem ExSafe.throw [Safe α] (e : ε) : ExSafe (.error e : Except ε α) := by
  intro a h
  cases h

theorem ExSafe.throw_bind [Safe β] (e : ε) (f : α → Except ε β) :
    ExSafe ((Except.error e : Except ε α) >>= f) := by
  intro b h
  cases h

theorem ExSafe.ite [Safe α] {c : Prop} [Decidable c] {x y : Except ε α}
    (ht : c → ExSafe x) (he : ¬c → ExSafe y) : ExSafe (if c then x else y) := by
  by_cases h : c
  · simpa only [h, ite_true] using ht h
  · simpa only [h, ite_false] using he h

theorem ExSafe.cond [Safe α] {c : Bool} {x y : Except ε α}
    (ht : c = true → ExSafe x) (he : c = false → ExSafe y) : ExSafe (cond c x y) := by
  cases c with
  | false => exact he rfl
  | true => exact ht rfl

theorem ExSafe.dite [Safe α] {c : Prop} [Decidable c]
    {x : c → Except ε α} {y : ¬c → Except ε α}
    (ht : ∀ h, ExSafe (x h)) (he : ∀ h, ExSafe (y h)) : ExSafe (dite c x y) := by
  by_cases h : c
  · simpa only [dite_eq_left h] using ht h
  · simpa only [dite_eq_right h] using he h

theorem ExSafe.bind [Safe α] [Safe β] {e : Except ε α} {f : α → Except ε β}
    (he : ExSafe e) (hf : ∀ a, Safe.holds a → ExSafe (f a)) : ExSafe (e >>= f) := by
  intro b h
  obtain ⟨a, ha, hb⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  exact hf a (he a ha) b hb

theorem ExSafe.forIn [Safe σ] (xs : List α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x s, Safe.holds s → ExSafe (body x s)) :
    ∀ s, Safe.holds s → ExSafe (forIn xs s body) := by
  induction xs with
  | nil => intro s hs; exact .pure hs
  | cons x xs ih =>
    intro s hs
    rw [List.forIn_cons]
    apply ExSafe.bind (hb x s hs)
    intro step hstep
    cases step with
    | done v => exact .pure hstep
    | yield v => exact ih v hstep

theorem ExSafe.forIn_array [Safe σ] (xs : Array α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x s, Safe.holds s → ExSafe (body x s))
    (s : σ) (hs : Safe.holds s) : ExSafe (ForIn.forIn xs s body) := by
  rw [← Array.forIn_toList]
  exact ExSafe.forIn _ _ hb s hs

open Lean Elab Tactic in
elab "shape_bind" : tactic => do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe do throwError "not a shape postcondition"
  let e := t.getAppArgs.back!.consumeMData
  unless e.isAppOf ``Bind.bind || e.isAppOf ``Except.bind do throwError "not a bind"
  let a := e.getAppArgs[e.getAppArgs.size - 2]!
  if a.isAppOf ``MonadExcept.throw || a.isAppOf ``MonadExceptOf.throw || a.isAppOf ``Except.error then
    evalTactic (← `(tactic| exact ExSafe.throw_bind _ _))
  else evalTactic (← `(tactic| apply ExSafe.bind))

open Lean Elab Tactic in
elab "shape_loop" : tactic => do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe do throwError "not a shape postcondition"
  let e := t.getAppArgs.back!.consumeMData
  unless e.isAppOf ``ForIn.forIn do throwError "not a loop"
  evalTactic (← `(tactic| first | apply ExSafe.forIn | apply ExSafe.forIn_array))

open Lean Elab Tactic in
elab "shape_intro" : tactic => do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isForall do throwError "not a binder"
  evalTactic (← `(tactic| intro))

open Lean Elab Tactic in
elab "shape_all" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe do throwError "not a shape postcondition"
  let ty ← Meta.inferType t.getAppArgs.back!
  if (ty.find? (·.isConstOf ``Ix.Kernel.Declaration)).isSome then
    throwError "declaration result needs a shape proof"
  evalTactic (← `(tactic| solve | apply ExSafe.of_all; intro a; simp [Safe.holds]))

open Lean Elab Tactic in
elab "shape_value" : tactic => do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe do throwError "not a shape postcondition"
  let e := t.getAppArgs.back!.consumeMData
  if e.isAppOf ``ite then
    evalTactic (← `(tactic| apply ExSafe.ite))
  else if e.isAppOf ``dite then
    evalTactic (← `(tactic| apply ExSafe.dite))
  else if e.isAppOf ``cond then
    evalTactic (← `(tactic| apply ExSafe.cond))
  else if e.isAppOf ``Except.ok || e.isAppOf ``Pure.pure then
    evalTactic (← `(tactic| apply ExSafe.pure))
  else if e.isAppOf ``Except.error || e.isAppOf ``MonadExceptOf.throw || e.isAppOf ``MonadExcept.throw then
    evalTactic (← `(tactic| exact ExSafe.throw _))
  else throwError "not a branch or value: {e.getAppFn.constName?}"

open Lean Elab Tactic in
elab "shape_safe" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``Safe.holds do throwError "not a safe value"
  let e := t.getAppArgs.back!.consumeMData
  let ty ← Meta.inferType e
  if (ty.find? (·.isConstOf ``Ix.Kernel.Declaration)).isNone then
    evalTactic (← `(tactic| solve | apply Safe.of_all; intro a; simp [Safe.holds]))
  else if e.isAppOf ``Prod.mk then evalTactic (← `(tactic| apply Safe.pair))
  else if e.isAppOf ``Prod.fst then evalTactic (← `(tactic| apply Safe.fst))
  else if e.isAppOf ``Prod.snd then evalTactic (← `(tactic| apply Safe.snd))
  else if e.isAppOf ``ForInStep.yield then evalTactic (← `(tactic| apply Safe.yield))
  else if e.isAppOf ``Array.push then evalTactic (← `(tactic| apply Safe.push))
  else if e.isAppOf ``Array.toList then evalTactic (← `(tactic| apply Safe.toList))
  else if e.isAppOf ``Ix.Kernel.Declaration.indDecl then evalTactic (← `(tactic| exact Safe.ind _ _))
  else if e.isAppOf ``Ix.Kernel.Declaration.defnDecl then evalTactic (← `(tactic| exact Safe.defn _ _ _))
  else if e.isAppOf ``Ix.Kernel.Declaration.thmDecl then evalTactic (← `(tactic| exact Safe.thm _ _))
  else evalTactic (← `(tactic| first | exact Safe.empty | exact True.intro))

open Lean Elab Tactic in
elab "shape_repeat " n:num tac:tacticSeq : tactic => do
  setGoals (← Meta.repeat' (evalTacticAtRaw tac) (← getGoals) n.getNat)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
theorem genMutual_safe (ctx : Ctx md) (b : BlockRec md) : ExSafe (genMutual ctx b) := by
  unfold genMutual
  simp only [← Bool.cond_eq_ite]
  shape_repeat 10000 first
    | shape_all
    | shape_bind
    | shape_loop
    | shape_value
    | shape_safe
    | shape_intro
    | assumption
    | solve | simp_all only [Safe.holds, forall_const, implies_true, and_true]
    | (split)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem genNested_safe (ctx : Ctx md) (b : BlockRec md) : ExSafe (genNested ctx b) := by
  unfold genNested
  simp only [← Bool.cond_eq_ite]
  shape_repeat 20000 first
    | shape_all
    | shape_bind
    | shape_loop
    | shape_value
    | shape_safe
    | shape_intro
    | assumption
    | solve | simp_all only [Safe.holds, forall_const, implies_true, and_true]
    | (dsimp only)
    | (split)

theorem generate_noBasis {ctx : Ctx md} {b : BlockRec md} {ds : List (Declaration md)}
    (h : generate ctx b = .ok ds) : ∀ d ∈ ds, ∀ k, d ≠ .basisDecl k := by
  unfold generate at h
  split at h
  · exact genNested_safe ctx b ds h
  · exact genMutual_safe ctx b ds h

end Ix.Cert.SourcePrelude.Shape

/-! ## The production prefix endpoint -/

namespace Ix.Cert.SourcePrelude

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress

/-- Source lowering cannot emit a basis declaration: the ordinary cases have
their declaration constructors, and both modeller rungs emit only inductives,
definitions and theorems. This is a producer fact, not checker acceptance. -/
theorem lower_noBasis : LowerNoBasis :=
  lowerNoBasis_of_generate fun _ _ _ h => Shape.generate_noBasis h

/-- Every successful lowered group changes only freshly claimed keys, in all
five reader maps, including the side arrays that declaration collapse retains. -/
theorem group_frame : GroupFrame := groupFrame_of_lowerShape lower_noBasis

/-- The actual retained-read trace of successful Source lowering preserves the
prelude at every group boundary whenever its final state passes the existing
prelude check. No claim is made about intermediate notes inside a group. -/
theorem lowerAllCollapsed_prefix {pre fin : State .source} {g : Graph}
    {scheduled : Array (Nat × Except ReadError Converted)} {decls : Array (Declaration .source)}
    (h : lowerAllCollapsed pre g scheduled = .ok (fin, decls))
    (keeps : State.keepsPrelude pre fin = true) :
    ∃ rs s kb, Trace g pre scheduled.zipIdx.toList rs fin s kb ∧ s.kept = decls ∧
      fin = rs.foldl State.commit pre ∧ decls.toList = rs.flatMap (·.decls.toList) ∧
      ∀ i k, k ∈ pre.keys → ((rs.take i).foldl State.commit pre).SameAt pre k := by
  obtain ⟨rs, s, kb, ht, hs, hfold, hflat⟩ := lowerAllCollapsed_trace h
  exact ⟨rs, s, kb, ht, hs, hfold, hflat, ht.prefix_of_frame group_frame keeps⟩

/-- Successful production preparation supplies its actual raw/kept trace and
preserves every prelude entry at every retained-read boundary. This discharges
the Source-side prefix obligation from the existing preparation function alone;
it adds neither a checker nor a final acceptance hypothesis. -/
theorem prepareSourceCollapsed_prefix {ρ : FiberMap}
    {hints : CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsed ρ hints pre env blocks = .ok ds) :
    ∃ rs fin decls s kb,
      lowerAllCollapsed pre.state (graphCollapsed ρ hints env blocks)
        (scheduleOf (graphCollapsed ρ hints env blocks)) = .ok (fin, decls) ∧
      Trace (graphCollapsed ρ hints env blocks) pre.state
        (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧ fin = rs.foldl State.commit pre.state ∧
      decls.toList = rs.flatMap (·.decls.toList) ∧
      ds = Frontend.preparePrelude pre.ix decls ∧
      ∀ i k, k ∈ pre.state.keys → ((rs.take i).foldl State.commit pre.state).SameAt pre.state k := by
  obtain ⟨fin, decls, hl, hk, hp⟩ := prepareSourceCollapsed_keepsPrelude h
  obtain ⟨rs, s, kb, ht, hs, hfold, hflat, hprefix⟩ := lowerAllCollapsed_prefix hl hk
  exact ⟨rs, fin, decls, s, kb, hl, ht, hs, hfold, hflat, hp, hprefix⟩

end Ix.Cert.SourcePrelude
