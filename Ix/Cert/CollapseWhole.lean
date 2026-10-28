import Ix.Cert.SourceTrace
import Ix.Cert.SourceOriginRead

/-! # Inductive reads are kept whole

Quotient Source's collapse (`collapseRead`) keeps or drops each declaration of a lowered group by
the names it declares: one none of whose names is kept yet is kept. A read whose names are all
fresh and pairwise distinct is therefore kept whole (`collapseRead_whole`).

An inductive group is lowered only when none of its block's names is kept yet
(`collapseGroup_inductive_fresh`), and `lowerInductive` declares the block's names and the
modeller's records' derived names over them, pairwise distinct
(`LowerDistinct.lowerInductive_names_nodup`). Along quotient Source's trace every name a read
keeps has its base kept too (`trace_baseClosed`): a derived name is kept only with the inductive
read that declares its base. So a derived name over a fresh block is fresh, and every inductive
read of the trace is kept whole (`lowered_inductive_whole`). -/

namespace Ix.Cert.CollapseWhole

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude

/-! ## A read with fresh, distinct names is kept whole -/

/-- What `collapseRead`'s loop has done after the prefix `pre` of a read whose declarations are
all kept: it is running, it kept exactly `pre`'s declarations, as many generated ones as `pre`
reaches into the generated prefix, and every name it owns was owned at the start or is declared
by `pre`. -/
structure WholeInv (s : CollapseState) (generated : Nat) (pre : List (Declaration .source × Nat))
    (a : ReadAcc) : Prop where
  active : a.1 = none
  kept : a.2.2.1.toList = pre.map Prod.fst
  gen : a.2.2.2.1 = min generated pre.length
  owned : ∀ k, (a.2.1.owner[k]?).isSome = true → (s.owner[k]?).isSome = true ∨ ∃ x ∈ pre, k ∈ x.1.names

/-- **A step at fresh names keeps the declaration**, and owns only its names besides. -/
theorem step_fresh {s : CollapseState} {first : SKey} {d : Declaration .source}
    (fresh : ∀ k ∈ d.names, s.owner[k]? = none) :
    ∃ s', s.step first d = (s', .ok true) ∧ s'.kept = s.kept.push d ∧
      ∀ k, (s'.owner[k]?).isSome = true → (s.owner[k]?).isSome = true ∨ k ∈ d.names := by
  obtain ⟨ds, owner⟩ := s
  have hnone : d.names.findSome? (owner[·]?) = none := List.findSome?_eq_none_iff.mpr fresh
  refine ⟨{ kept := ds.push d, owner := claimKeys owner d.names ds.size }, ?_, rfl, ?_⟩
  · unfold CollapseState.step
    simp only [hnone]
    rfl
  · intro k hk
    by_cases hm : k ∈ d.names
    · exact .inr hm
    · left
      have := claimKeys_outside d.names owner ds.size k hm
      change ((claimKeys owner d.names ds.size)[k]?).isSome = true at hk
      rwa [this] at hk

theorem readStep_whole {s : CollapseState} {first : SKey} {raw : Read .source}
    (fresh : ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names, s.owner[k]? = none)
    (distinct : (raw.decls.toList.flatMap Declaration.names).Nodup)
    (pre : List (Declaration .source × Nat)) (x : Declaration .source × Nat)
    (post : List (Declaration .source × Nat)) (a : ReadAcc)
    (split : pre ++ x :: post = raw.decls.zipIdx.toList) (ha : WholeInv s raw.generated pre a) :
    match readStep first s.kept.size raw.generated x a with
    | .yield a' => WholeInv s raw.generated (pre ++ [x]) a'
    | .done a' => ReadBad a' := by
  obtain ⟨d, j⟩ := x
  -- the read's declarations, split at `d`
  have hsplit : raw.decls.toList = pre.map Prod.fst ++ d :: post.map Prod.fst := by
    have := congrArg (List.map Prod.fst) split
    simp only [List.map_append, List.map_cons, Array.toList_zipIdx, List.zipIdx_map_fst] at this
    exact this.symm
  -- `d`'s position
  have hj : j = pre.length := by
    have := congrArg (·[pre.length]?) split
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Array.toList_zipIdx, List.getElem?_zipIdx] at this
    cases hg : raw.decls.toList[pre.length]? with
    | none => rw [hg] at this; cases this
    | some e =>
      rw [hg] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      omega
  have hd : d ∈ raw.decls.toList := by rw [hsplit]; simp
  -- `d`'s names are owned neither at the start nor by `pre`
  have hfree : ∀ k ∈ d.names, a.2.1.owner[k]? = none := by
    intro k hk
    cases hv : a.2.1.owner[k]? with
    | none => rfl
    | some v =>
      exfalso
      rcases ha.owned k (by simp [hv]) with hs | ⟨y, hy, hky⟩
      · rw [fresh d hd k hk] at hs
        cases hs
      · rw [hsplit, List.flatMap_append, List.flatMap_cons] at distinct
        have hpre : k ∈ (pre.map Prod.fst).flatMap Declaration.names :=
          List.mem_flatMap.mpr ⟨y.1, List.mem_map_of_mem hy, hky⟩
        have hpost : k ∈ d.names ++ (post.map Prod.fst).flatMap Declaration.names :=
          List.mem_append_left _ hk
        exact (List.nodup_append.mp distinct).2.2 k hpre k hpost rfl
  obtain ⟨s', hs, hkept, howned⟩ := step_fresh (first := first) hfree
  have owned' : ∀ k, (s'.owner[k]?).isSome = true →
      (s.owner[k]?).isSome = true ∨ ∃ x ∈ pre ++ [(d, j)], k ∈ x.1.names := by
    intro k hk
    rcases howned k hk with hk | hk
    · rcases ha.owned k hk with hk | ⟨y, hy, hky⟩
      · exact .inl hk
      · exact .inr ⟨y, List.mem_append_left _ hy, hky⟩
    · exact .inr ⟨(d, j), List.mem_append_right _ List.mem_cons_self, hk⟩
  have keptList : (a.2.2.1.push d).toList = (pre ++ [(d, j)]).map Prod.fst := by
    simp [ha.kept]
  by_cases hlt : j < raw.generated
  · simp only [readStep, hs, hlt, ↓reduceIte, pure]
    refine ⟨rfl, keptList, ?_, owned'⟩
    simp only [ha.gen, List.length_append, List.length_singleton]
    omega
  · simp only [readStep, hs, hlt, ↓reduceIte, pure]
    refine ⟨rfl, keptList, ?_, owned'⟩
    simp only [ha.gen, List.length_append, List.length_singleton]
    omega

/-- **A read whose names are fresh and pairwise distinct is kept whole** by the collapse. -/
theorem collapseRead_whole {s s' : CollapseState} {first : SKey} {raw r : Read .source}
    {dropped : Array SKey}
    (fresh : ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names, s.owner[k]? = none)
    (distinct : (raw.decls.toList.flatMap Declaration.names).Nodup)
    (hgen : raw.generated ≤ raw.decls.size)
    (h : collapseRead s first raw = (s', .ok (r, dropped))) : r = raw := by
  have inv := forIn_id_inv_or_array (WholeInv s raw.generated) ReadBad
    (readStep first s.kept.size raw.generated) raw.decls.zipIdx
    (fun pre x post a split ha => by
      have hi := readStep_whole (first := first) fresh distinct pre x post a split ha
      cases hb : readStep first s.kept.size raw.generated x a <;>
        simpa only [hb] using hi)
    (none, s, #[], 0, #[]) ⟨rfl, rfl, by simp, fun k hk => .inl hk⟩
  change WholeInv s raw.generated raw.decls.zipIdx.toList (readLoop s first raw) ∨
    ReadBad (readLoop s first raw) at inv
  rw [collapseRead_eq] at h
  rcases inv with hi | hb
  · simp only [readFinish, hi.active, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨-, hr, -⟩ := h
    rw [← hr]
    have hdecls : (readLoop s first raw).2.2.1 = raw.decls := by
      apply Array.toList_inj.mp
      rw [hi.kept, Array.toList_zipIdx, List.zipIdx_map_fst]
    have hg : (readLoop s first raw).2.2.2.1 = raw.generated := by
      rw [hi.gen, Array.toList_zipIdx, List.length_zipIdx, Array.length_toList]
      omega
    rw [hdecls, hg]
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

/-! ## Along the trace, kept names have kept bases -/

/-- The declarations the reads keep. -/
abbrev declsOf (rs : List (Read .source)) : List (Declaration .source) := rs.flatMap (·.decls.toList)

/-- **Every name the reads declare has its base declared by them too.** -/
def BaseClosed (rs : List (Read .source)) : Prop :=
  ∀ d ∈ declsOf rs, ∀ k ∈ d.names, ∃ d' ∈ declsOf rs, k.base ∈ d'.names

/-- **The trace's collapse owns exactly the names its reads declare.** -/
theorem owned_iff {g : Graph} {start st : State .source} {xs rs s kb}
    (ht : Trace g start xs rs st s kb) (k : SKey) :
    (s.owner[k]?).isSome = true ↔ ∃ d ∈ declsOf rs, k ∈ d.names := by
  have hex := SourceReplay.trace_ownerExact ht
  rw [declsOf, ← Trace.decls ht]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨d, hd, hk⟩ := (hex k i).mp hi
    exact ⟨d, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hd), hk⟩
  · rintro ⟨d, hd, hk⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    have : s.owner[k]? = some i := (hex k i).mpr ⟨d, by simpa using hi, hk⟩
    simp [this]

/-- A lowered inductive block's own declaration declares the block's names. -/
theorem indDecl_names (rb : BlockRead .source) :
    (CtxAgree.indDeclOf rb).names = CtxAgree.blockNames rb := by
  simp only [CtxAgree.blockNames, CtxAgree.noteEntries, CtxAgree.indDeclOf, Declaration.names,
    List.map_map]
  rfl

/-- A declaration's names are its noted entries' names. -/
theorem entry_of_name {d : Declaration .source} {k : SKey} (hk : k ∈ d.names) :
    ∃ e ∈ CtxAgree.noteEntries d, e.1 = k := by
  have hne : d.names ≠ [] := List.ne_nil_of_mem hk
  have eq : (CtxAgree.noteEntries d).map Prod.fst = d.names := by
    cases d with
    | basisDecl => exact (hne rfl).elim
    | indDecl block n => simp only [CtxAgree.noteEntries, Declaration.names, List.map_map]; rfl
    | _ => rfl
  rw [← eq] at hk
  exact List.mem_map.mp hk

/-- **A lowered inductive group of the trace is kept whole**, when the earlier reads' names have
their bases among them and the modeller's records' names have their bases among the block's. -/
theorem lowered_inductive_whole {g : Graph} {start st : State .source} {xs rs s kb}
    (ht : Trace g start xs rs st s kb) (closed : BaseClosed rs)
    {first : SKey} {pos : Nat} {rb : BlockRead .source} {raw r : Read .source} {s' : CollapseState}
    {kb' : KeptBlocks} {dropped : Array SKey}
    (hl : lower st (.inductive rb) = .ok raw)
    (hr : collapseRead s first raw = (s', .ok (r, dropped)))
    (hcol : collapseGroup st s kb first pos (.ok (.inductive rb)) = .lowered s' kb' r dropped)
    (bases : ∀ e ∈ CtxAgree.genEntries raw, e.1.base ∈ CtxAgree.blockNames rb) :
    r = raw := by
  have blockFresh : ∀ k ∈ CtxAgree.blockNames rb, s.owner[k]? = none := by
    intro k hk
    apply collapseGroup_inductive_fresh hcol
    rw [SourceOriginRead.blockNames_eq] at hk
    exact hk
  have hlow : lowerInductive st rb = .ok raw := hl
  obtain ⟨gens, hd, hgen, -, -⟩ := CtxAgree.lowerInductive_ok hlow
  have fresh : ∀ d ∈ raw.decls.toList, ∀ k ∈ d.names, s.owner[k]? = none := by
    intro d hd' k hk
    have hd'' : d ∈ gens ∨ d = CtxAgree.indDeclOf rb := by
      rw [hd] at hd'
      simpa using hd'
    rcases hd'' with hd'' | rfl
    · -- a derived name over the block: owned only with its base, a block name
      obtain ⟨e, he, rfl⟩ := entry_of_name hk
      have hgenE : e ∈ CtxAgree.genEntries raw := by
        simp only [CtxAgree.genEntries, hd, hgen, Array.toList_push, List.take_left]
        exact List.mem_flatMap.mpr ⟨d, hd'', he⟩
      have hbase := blockFresh _ (bases e hgenE)
      cases hv : s.owner[e.1]? with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨d0, hd0, hk0⟩ := (owned_iff ht e.1).mp (by simp [hv])
        obtain ⟨d', hd', hk'⟩ := closed d0 hd0 e.1 hk0
        have := (owned_iff ht e.1.base).mpr ⟨d', hd', hk'⟩
        rw [hbase] at this
        cases this
    · rw [indDecl_names] at hk
      exact blockFresh k hk
  have hle : raw.generated ≤ raw.decls.size := by
    rw [hgen, hd]
    simp
  exact collapseRead_whole fresh (LowerDistinct.lowerInductive_names_nodup hlow) hle hr

/-- An ordinary lowering generates nothing. -/
theorem lower_generated_zero {st : State .source} {c : Converted} {r : Read .source}
    (h : lower st c = .ok r) (hc : ∀ rb, c ≠ .inductive rb) : r.generated = 0 := by
  cases c with
  | «inductive» rb => exact absurd rfl (hc rb)
  | definitions ms =>
    unfold lower at h
    delta Ix.LeanIngress.lower.match_6 at h
    dsimp only at h
    split at h
    · rename_i hsz
      obtain ⟨l⟩ := ms
      obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
      · cases hsz
      · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        cases h; rfl
      · simp at hsz
    · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      cases h; rfl
  | «axiom» cv => cases h; rfl
  | quot kind cv => cases h; rfl

/-- **Along quotient Source's trace, every kept name has its base kept**, and every inductive read
is kept whole. -/
theorem trace_baseClosed {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {hints : CName .source → Option ReducibilityHint} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {start st : State .source} {xs : List Scheduled} {rs : List (Read .source)} {s : CollapseState}
    {kb : KeptBlocks}
    (ht : Trace (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) start xs rs st s kb) :
    (∀ x ∈ xs, x ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList) →
    BaseClosed rs := by
  induction ht with
  | nil => intro _ d hd; simp at hd
  | «alias» _ _ ih => exact fun inside => ih fun y hy => inside y (List.mem_append_left _ hy)
  | @lowered xs rs st s kb x s' kb' conv raw r dropped ht hc hl hr hcol ih =>
    intro inside
    have closed := ih fun y hy => inside y (List.mem_append_left _ hy)
    have hx1 : x.1 ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).toList :=
      List.fst_mem_of_mem_zipIdx (by
        simpa only [Array.toList_zipIdx] using inside x (List.mem_append_right _ List.mem_cons_self))
    obtain ⟨gr, c, -, hconv, heq⟩ := SourceTrace.graph_conversion (ReaderUnits.scheduleOf_ok hx1 hc)
    have ordinary := SourceNames.quotient_lower_ordinary hconv hints (st := st) (r := raw)
      (by rw [← heq]; exact hl)
    have facts := collapseRead_facts hr
    intro d hd k hk
    simp only [declsOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨d', hd', hk'⟩ := closed d hd k hk
      exact ⟨d', by simp only [declsOf, List.flatMap_append, List.mem_append]; exact .inl hd', hk'⟩
    · have hraw : d ∈ raw.decls.toList := facts.2.2.2.1 d hd
      cases hka : k.isAux with
      | false =>
        exact ⟨d, by simp only [declsOf, List.flatMap_append, List.mem_append]; simp [hd],
          by rw [SourceOriginRead.base_of_not_aux hka]; exact hk⟩
      | true =>
        -- a derived name: declared in the generated prefix of an inductive read
        have hgenPart : d ∈ raw.decls.toList.take raw.generated := by
          have hsplit := List.take_append_drop raw.generated raw.decls.toList
          rw [← hsplit] at hraw
          rcases List.mem_append.mp hraw with h | h
          · exact h
          · rw [ordinary d h k hk] at hka
            cases hka
        by_cases hind : ∃ rb, conv = .inductive rb
        · obtain ⟨rb, rfl⟩ := hind
          rw [hc] at hcol
          have bases := SourceOriginRead.quotient_lowerInductive_bases hconv hints heq.symm
            (show lowerInductive st rb = .ok raw from hl)
          have whole : r = raw := lowered_inductive_whole ht closed hl hr hcol bases
          obtain ⟨e, he, rfl⟩ := entry_of_name hk
          have hgenE : e ∈ CtxAgree.genEntries raw := List.mem_flatMap.mpr ⟨d, hgenPart, he⟩
          obtain ⟨gens, hdecls, -, -, -⟩ :=
            CtxAgree.lowerInductive_ok (show lowerInductive st rb = .ok raw from hl)
          refine ⟨CtxAgree.indDeclOf rb, ?_, by rw [indDecl_names]; exact bases e hgenE⟩
          simp only [declsOf, List.flatMap_append, List.mem_append]
          right
          simp [whole, hdecls]
        · rw [lower_generated_zero hl (fun rb h => hind ⟨rb, h⟩)] at hgenPart
          simp at hgenPart

/-- **Every inductive read of quotient Source's trace is kept whole**: its kept part is its raw
lowering. -/
theorem trace_inductive_whole {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {hints : CName .source → Option ReducibilityHint} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {start st : State .source} {xs : List Scheduled} {rs : List (Read .source)} {s : CollapseState}
    {kb : KeptBlocks}
    (ht : Trace (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) start xs rs st s kb)
    (inside : ∀ x ∈ xs, x ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList)
    {x : Scheduled} {rb : BlockRead .source} {raw r : Read .source} {s' : CollapseState} {kb' : KeptBlocks}
    {dropped : Array SKey} (hx : x ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList)
    (hc : x.1.2 = .ok (.inductive rb)) (hl : lower st (.inductive rb) = .ok raw)
    (hr : collapseRead s (graphCollapsed (fiberAliasAt ixe roles) hints env blocks).groups[x.1.1]!.name raw =
      (s', .ok (r, dropped)))
    (hcol : collapseGroup st s kb (graphCollapsed (fiberAliasAt ixe roles) hints env blocks).groups[x.1.1]!.name x.2
      x.1.2 = .lowered s' kb' r dropped) :
    r = raw := by
  have hx1 : x.1 ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).toList :=
    List.fst_mem_of_mem_zipIdx (by simpa only [Array.toList_zipIdx] using hx)
  obtain ⟨gr, c, -, hconv, heq⟩ := SourceTrace.graph_conversion (ReaderUnits.scheduleOf_ok hx1 hc)
  rw [hc] at hcol
  exact lowered_inductive_whole ht (trace_baseClosed ht inside) hl hr hcol
    (SourceOriginRead.quotient_lowerInductive_bases hconv hints heq.symm
      (show lowerInductive st rb = .ok raw from hl))

/-! ## Index by index -/

/-- **Each read of a trace over the items `xs`, with the trace before it**: for the lowered items
`ls` and their reads `rs`, read `ℓ` follows a trace of earlier items of `xs` whose reads are the
`ℓ` earlier ones, and is item `ℓ`'s lowering at that trace's state, collapsed at its collapse
state. -/
def TraceAt (g : Graph) (start : State .source) (xs ls : List Scheduled) (rs : List (Read .source)) :
    Prop :=
  ∀ ℓ y r, ls[ℓ]? = some y → rs[ℓ]? = some r →
    ∃ (xs' : List Scheduled) (s : CollapseState) (kb : KeptBlocks) (conv : Converted) (raw : Read .source)
      (s' : CollapseState) (kb' : KeptBlocks) (dropped : Array SKey),
      Trace g start xs' (rs.take ℓ) ((rs.take ℓ).foldl State.commit start) s kb ∧
      (∀ x ∈ xs', x ∈ xs) ∧ y ∈ xs ∧ y.1.2 = .ok conv ∧
      lower ((rs.take ℓ).foldl State.commit start) conv = .ok raw ∧
      collapseRead s g.groups[y.1.1]!.name raw = (s', .ok (r, dropped)) ∧
      collapseGroup ((rs.take ℓ).foldl State.commit start) s kb g.groups[y.1.1]!.name y.2 y.1.2 =
        .lowered s' kb' r dropped

/-- **The inductive reads are kept whole**: read `ℓ` of an inductive item is its lowering at the
state of the reads before it. -/
def InductiveWhole (start : State .source) (ls : List Scheduled) (rs : List (Read .source)) :
    Prop :=
  ∀ ℓ y r conv raw, ls[ℓ]? = some y → rs[ℓ]? = some r → y.1.2 = .ok conv →
    (∃ rb, conv = .inductive rb) → lower ((rs.take ℓ).foldl State.commit start) conv = .ok raw → r = raw

/-- **Quotient Source's inductive reads are kept whole**, read by read. -/
theorem inductiveWhole_of_traceAt {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {hints : CName .source → Option ReducibilityHint} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {start : State .source} {xs ls : List Scheduled} {rs : List (Read .source)}
    (traceAt : TraceAt (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) start xs ls rs)
    (inside : ∀ x ∈ xs, x ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList) :
    InductiveWhole start ls rs := by
  intro ℓ y r conv raw hy hr hc hind hl
  obtain ⟨rb, rfl⟩ := hind
  obtain ⟨xs', s, kb, conv', raw', s', kb', dropped, ht, hsub, hyx, hc', hl', hcr, hcol⟩ :=
    traceAt ℓ y r hy hr
  obtain rfl : conv' = .inductive rb := by
    rw [hc] at hc'
    exact (Except.ok.inj hc').symm
  obtain rfl : raw' = raw := by
    rw [hl] at hl'
    exact (Except.ok.inj hl').symm
  exact trace_inductive_whole ht (fun x hx => inside x (hsub x hx)) (inside y hyx) hc hl hcr hcol

/--
info: 'Ix.Cert.CollapseWhole.inductiveWhole_of_traceAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductiveWhole_of_traceAt

end Ix.Cert.CollapseWhole
