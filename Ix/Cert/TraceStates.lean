import Ix.Cert.TraceSegments
import Ix.Cert.CtxAgreeProjFields
import Ix.Cert.TraceGood

/-! # The states of quotient Source's trace lie in the scope

`TraceSegments.TraceNeeds.states` asks that every state the trace's reads are read from have
its owners, constant types and inductive blocks, at keys of the scope of representatives, in
that scope (`TraceSegments.StateGood`). This module proves it by induction over the reads
(`states_good`):

* **The start**: the prelude's state names no input at all (`PreludeAgree.preludeAgreeB`'s
  decided check), so its entries lie in every scope (`prelude_good`).
* **A commit keeps the states good** when the read's owners, blocks and noted types are good
  (`commit_good`), and a read the collapse keeps from a lowering has the lowering's
  (`collapse_good`).
* **A lowering of a group whose terms lie in the scope lies in the scope** (`lower_good`): a
  definition's, axiom's or quotient constant's declared type is its converted one. An inductive
  group's owners and block are its block's, and its declarations, the modeller's generated ones
  included, are fixed by a renaming that fixes the scope's ids and moves every other id
  (`lowerInductive_mapKeys` at a state that is its own renaming, `StateGood`'s own consequence):
  a term such a renaming fixes names only the scope's ids (`expr_good_of_fix`). -/

namespace Ix.Cert.TraceStates

open Ix.Kernel Ix.Kernel.Reader
open Ix.Kernel.Frontend (ProjRecOwner)
open Ix.Kernel.Frontend.InModel (BlockRec IndTypeRec IndCtorRec IndRecRec)
open Ix.Cert.TraceSegments (StateGood ConvGood scope)
open Ix.Cert.ClosureLayout (Steps quotientGraph)
open Ix.LeanIngress (Converted Group)

/-! ## Renamings that fix the scope -/

section Fix

variable {md : Mode} {P : KeyScope md} {f : md.Id → md.Id}

theorem key_fix (hf : ∀ i, P i → f i = i) {k : Key md} (h : k.Good P) : k.map f = k := by
  rw [PreludeAgree.key_map_congr (g := fun i => i) hf h, Key.map_id]

theorem expr_fix (hf : ∀ i, P i → f i = i) {e : Ix.Kernel.Expr md} (h : e.Good P) : e.mapKeys f = e := by
  rw [PreludeAgree.expr_mapKeys_congr (g := fun i => i) hf e h, Expr.mapKeys_id]

theorem map_fix {α : Type} {g : α → α} {l : List α} (h : ∀ x ∈ l, g x = x) : l.map g = l := by
  rw [List.map_congr_left h]
  exact List.map_id _

theorem arr_map_fix {α : Type} {g : α → α} {a : Array α} (h : ∀ x ∈ a.toList, g x = x) : a.map g = a := by
  apply Array.toList_inj.mp
  rw [Array.toList_map]
  exact map_fix h

theorem blockRec_mapKeys_id (b : BlockRec md) : b.mapKeys (fun i => i) = b := by
  obtain ⟨ts, cs, rs⟩ := b
  simp only [BlockRec.mapKeys, BlockRec.mk.injEq]
  refine ⟨map_fix fun t _ => ?_, map_fix fun c _ => ?_, map_fix fun r _ => ?_⟩
  · obtain ⟨cv, nP, nIdx, ctors, isRec, isRefl, nn⟩ := t
    simp [IndTypeRec.mapKeys, show (Key.map (md := md) (md' := md) fun i => i) = id from funext Key.map_id]
  · obtain ⟨cv, nP, nF⟩ := c
    simp [IndCtorRec.mapKeys]
  · obtain ⟨cv, nP, nM, nm, nI, rules⟩ := r
    simp [IndRecRec.mapKeys, RecRule.mapKeys_id_fun]

theorem block_fix (hf : ∀ i, P i → f i = i) {b : BlockRec md} (h : b.Good P) : b.mapKeys f = b := by
  rw [PreludeAgree.block_mapKeys_congr (g := fun i => i) hf h, blockRec_mapKeys_id]

theorem cval_fix (hf : ∀ i, P i → f i = i) {cv : Ix.Kernel.ConstantVal md} (h : cv.Good P) : cv.mapKeys f = cv := by
  rw [PreludeAgree.cval_mapKeys_congr (g := fun i => i) hf h, ConstantVal.mapKeys_id]

theorem blockRead_fix (hf : ∀ i, P i → f i = i) {rb : BlockRead md} (h : rb.Good P) : rb.mapKeys f = rb := by
  obtain ⟨hT, hC, hN, hR⟩ := h
  obtain ⟨nP, ts, cs, ns, rs⟩ := rb
  simp only [BlockRead.mapKeys, BlockRead.mk.injEq, true_and]
  refine ⟨arr_map_fix fun x hx => ?_, arr_map_fix fun x hx => ?_, arr_map_fix fun ks hks => ?_,
    arr_map_fix fun x hx => ?_⟩
  · obtain ⟨cv, p, i⟩ := x
    simp only [cval_fix hf (hT _ hx)]
  · obtain ⟨cv, p, n⟩ := x
    simp only [cval_fix hf (hC _ hx)]
  · exact map_fix fun k hk => key_fix hf (hN ks hks k hk)
  · obtain ⟨cv, cnt, rules⟩ := x
    obtain ⟨hcv, hrs⟩ := hR _ hx
    simp only [cval_fix hf hcv, PreludeAgree.rules_map_congr (g := fun i => i) hf hrs, RecRule.mapKeys_id_fun,
      List.map_id]

/-- A key a renaming fixes names only ids it fixes. -/
theorem key_good_of_fix {Q : md.Id → Prop} (hQ : ∀ i, f i = i → Q i) :
    ∀ {k : Key md}, k.map f = k → k.Good (KeyScope.ofId Q)
  | .id i, h => hQ i (Key.id.inj h)
  | .role _, _ => trivial
  | .aux k _, h => key_good_of_fix (k := k) hQ (Key.aux.inj h).1

/-- **A term a renaming fixes names only ids it fixes.** -/
theorem expr_good_of_fix {Q : md.Id → Prop} (hQ : ∀ i, f i = i → Q i) :
    ∀ {e : Ix.Kernel.Expr md}, e.mapKeys f = e → e.Good (KeyScope.ofId Q)
  | .bvar _, _ => trivial
  | .fvar _ t, h => expr_good_of_fix (e := t) hQ (Ix.Kernel.Expr.fvar.inj h).2
  | .sort _, _ => trivial
  | .const n _, h => key_good_of_fix (k := n) hQ (Ix.Kernel.Expr.const.inj h).1
  | .app a b, h => ⟨expr_good_of_fix (e := a) hQ (Ix.Kernel.Expr.app.inj h).1,
      expr_good_of_fix (e := b) hQ (Ix.Kernel.Expr.app.inj h).2⟩
  | .lam t b _, h => ⟨expr_good_of_fix (e := t) hQ (Ix.Kernel.Expr.lam.inj h).1,
      expr_good_of_fix (e := b) hQ (Ix.Kernel.Expr.lam.inj h).2.1⟩
  | .forallE t b _, h => ⟨expr_good_of_fix (e := t) hQ (Ix.Kernel.Expr.forallE.inj h).1,
      expr_good_of_fix (e := b) hQ (Ix.Kernel.Expr.forallE.inj h).2.1⟩
  | .letE t v b _, h => ⟨expr_good_of_fix (e := t) hQ (Ix.Kernel.Expr.letE.inj h).1,
      expr_good_of_fix (e := v) hQ (Ix.Kernel.Expr.letE.inj h).2.1,
      expr_good_of_fix (e := b) hQ (Ix.Kernel.Expr.letE.inj h).2.2.1⟩
  | .lit (.natVal _), _ => trivial
  | .lit (.strVal _), _ => fun _ _ => trivial
  | .proj s _ e, h => ⟨key_good_of_fix (k := s) hQ (Ix.Kernel.Expr.proj.inj h).1,
      expr_good_of_fix (e := e) hQ (Ix.Kernel.Expr.proj.inj h).2.2⟩

/-- A list a map fixes has each element fixed. -/
theorem fixed_of_map {α : Type} {g : α → α} : ∀ {l : List α}, l.map g = l → ∀ x ∈ l, g x = x
  | [], _, _, hx => by cases hx
  | y :: l, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact fixed_of_map h.2 x hx

/-- **A declaration a renaming fixes notes types naming only ids it fixes**, unless it is a
basis block. -/
theorem noted_good_of_fix {Q : md.Id → Prop} (hQ : ∀ i, f i = i → Q i) {d : Declaration md}
    (h : d.mapKeys f = d) (basis : ∀ k, d ≠ .basisDecl k) :
    ∀ e ∈ CtxAgree.noteEntries d, e.2.2.1.Good (KeyScope.ofId Q) := by
  have cv_fix : ∀ {cv : Ix.Kernel.ConstantVal md}, cv.mapKeys f = cv → cv.type.mapKeys f = cv.type := fun h => by
    rw [← ConstantVal.mapKeys_type, h]
  cases d with
  | axiomDecl v =>
    simp only [Declaration.mapKeys, Declaration.axiomDecl.injEq] at h
    simp only [CtxAgree.noteEntries, List.mem_singleton]
    rintro e rfl
    exact expr_good_of_fix hQ (cv_fix h)
  | defnDecl v e₀ h₀ =>
    simp only [Declaration.mapKeys, Declaration.defnDecl.injEq] at h
    simp only [CtxAgree.noteEntries, List.mem_singleton]
    rintro e rfl
    exact expr_good_of_fix hQ (cv_fix h.1)
  | thmDecl v e₀ =>
    simp only [Declaration.mapKeys, Declaration.thmDecl.injEq] at h
    simp only [CtxAgree.noteEntries, List.mem_singleton]
    rintro e rfl
    exact expr_good_of_fix hQ (cv_fix h.1)
  | opaqueDecl v e₀ =>
    simp only [Declaration.mapKeys, Declaration.opaqueDecl.injEq] at h
    simp only [CtxAgree.noteEntries, List.mem_singleton]
    rintro e rfl
    exact expr_good_of_fix hQ (cv_fix h.1)
  | basisDecl k => exact absurd rfl (basis k)
  | quotDecl k v =>
    simp only [Declaration.mapKeys, Declaration.quotDecl.injEq, true_and] at h
    simp only [CtxAgree.noteEntries, List.mem_singleton]
    rintro e rfl
    exact expr_good_of_fix hQ (cv_fix h)
  | indDecl block nP =>
    simp only [Declaration.mapKeys, Declaration.indDecl.injEq, and_true] at h
    simp only [CtxAgree.noteEntries, List.mem_map]
    rintro e ⟨ci, hci, rfl⟩
    have hc := fixed_of_map h ci hci
    have := congrArg ConstantInfo.toConstantVal hc
    rw [ConstantInfo.mapKeys_toConstantVal] at this
    exact expr_good_of_fix hQ (cv_fix this)

end Fix

/-! ## Commits keep the states good -/

/-- **What a read records lies in a scope**: its projection owners, its blocks and the types
its declarations note. -/
structure ReadGood (Q : KeyScope .source) (r : Read .source) : Prop where
  owners : ∀ o ∈ r.owners, o.Good Q
  blocks : ∀ x ∈ r.blocks, x.2.Good Q
  types : ∀ d ∈ r.decls.toList, ∀ e ∈ CtxAgree.noteEntries d, e.2.2.1.Good Q

theorem foldl_insOpt_val {α β γ : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (g : γ → Option (α × β)) (V : β → Prop) :
    ∀ (l : List γ) (m : Std.HashMap α β), (∀ e ∈ l, ∀ a b, g e = some (a, b) → V b) →
      ∀ (k : α) (v : β), (l.foldl (CtxAgree.insOpt g) m)[k]? = some v → m[k]? = some v ∨ V v
  | [], m, _, k, v, h => .inl h
  | e :: l, m, hl, k, v, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insOpt_val g V l _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) k v h with h | h
    · unfold CtxAgree.insOpt at h
      split at h
      · rename_i a b hab
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · exact .inr (Option.some.inj h ▸ hl e List.mem_cons_self a b hab)
        · exact .inl h
      · exact .inl h
    · exact .inr h

/-- **A commit of a good read keeps a state good.** -/
theorem commit_good {Q : KeyScope .source} {st : State .source} {r : Read .source} (hst : StateGood Q st)
    (hr : ReadGood Q r) : StateGood Q (st.commit r) := by
  refine ⟨fun k hk o ho => ?_, fun k hk p hp => ?_, fun k hk b hb => ?_⟩
  · rw [CtxAgree.commit_projOwners] at ho
    rcases foldl_insOpt_val some (fun o : ProjRecOwner .source => o.Good Q) _ _
      (fun e he a b hab => by
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp he
        simp only [Option.some.injEq, Prod.mk.injEq] at hab
        rw [← hab.2]
        exact hr.owners o' ho') k o ho with h | h
    · exact hst.owners k hk o h
    · exact h
  · rw [CtxAgree.commit_constTypes] at hp
    rcases foldl_insOpt_val CtxAgree.tyOf (fun p : List LevelParam × Ix.Kernel.Expr .source => p.2.Good Q) _ _
      (fun e he a b hab => by
        obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
        simp only [CtxAgree.tyOf, Option.some.injEq, Prod.mk.injEq] at hab
        rw [← hab.2]
        exact hr.types d hd e he) k p hp with h | h
    · exact hst.types k hk p h
    · exact h
  · rw [CtxAgree.commit_indBlocks] at hb
    rcases foldl_insOpt_val some (fun b : BlockRec .source => b.Good Q) _ _
      (fun e he a b hab => by
        simp only [Option.some.injEq] at hab
        subst hab
        exact hr.blocks _ he) k b hb with h | h
    · exact hst.blocks k hk b h
    · exact h

/-- **A read the collapse keeps from a good lowering is good.** -/
theorem collapse_good {Q : KeyScope .source} {s s' : Ix.LeanIngress.CollapseState} {first : SourcePrelude.SKey}
    {raw r : Read .source} {dropped : Array SourcePrelude.SKey}
    (h : Ix.LeanIngress.collapseRead s first raw = (s', .ok (r, dropped))) (hraw : ReadGood Q raw) :
    ReadGood Q r := by
  obtain ⟨-, -, -, sub, -, howners, hblocks⟩ := SourcePrelude.collapseRead_facts h
  exact ⟨howners ▸ hraw.owners, hblocks ▸ hraw.blocks, fun d hd => hraw.types d (sub d hd)⟩

/-! ## Lowerings lie in the scope -/

section Lower

variable {P : Ix.Kernel.Name → Prop}

/-- A renaming of Source names that fixes `P`'s and moves every other. -/
theorem moveOff : ∃ f : Ix.Kernel.Name → Ix.Kernel.Name, (∀ i, P i → f i = i) ∧ ∀ i, f i = i → P i := by
  classical
  refine ⟨fun i => if P i then i else .num i 0, fun i hi => by simp [hi], fun i h => ?_⟩
  by_contra hi
  have h2 : Ix.Kernel.Name.num i 0 = i := by simpa [hi] using h
  have h' := congrArg sizeOf h2
  simp only [Ix.Kernel.Name.num.sizeOf_spec] at h'
  omega

/-- **A state good in a scope is its own renaming** under a renaming that fixes the scope. -/
theorem stateAgree_self {f : Ix.Kernel.Name → Ix.Kernel.Name} (hf : ∀ i, P i → f i = i) {st : State .source}
    (hst : StateGood (KeyScope.ofId P) st) : CtxAgree.StateAgree f (KeyScope.ofId P) st st := by
  have hf' : ∀ i, (KeyScope.ofId (md := .source) P) i → f i = i := hf
  refine ⟨fun k hk => ?_, fun k hk p hp => hst.types k hk p hp,
    fun k hk => by rw [key_fix hf' hk],
    fun k hk => ?_, fun k hk b hb => hst.blocks k hk b hb⟩
  · rw [key_fix hf' hk]
    cases hp : st.constTypes[k]? with
    | none => rfl
    | some p => simp only [Option.map_some, expr_fix hf' (hst.types k hk p hp)]
  · rw [key_fix hf' hk]
    cases hb : st.indBlocks[k]? with
    | none => rfl
    | some b => simp only [Option.map_some, block_fix hf' (hst.blocks k hk b hb)]

/-- A definition's lowering keeps its header. -/
theorem lowerDefinition_cv {hint : Option ReducibilityHint} {st : State .source}
    {heights : CName .source → Nat} {cv : CVal .source} {value : CExpr .source} {kind : Ix.DefKind}
    {safety : Ix.DefinitionSafety} {decl : CDecl .source} {rw : Bool}
    (h : lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    ∀ e ∈ CtxAgree.noteEntries decl, e.2.2.1 = cv.type := by
  unfold lowerDefinition at h
  dsimp only at h
  split at h
  · simp [declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    cases kind <;> simp [CtxAgree.noteEntries]

/-- **A lowering of a group whose terms lie in the scope lies in the scope**, from a state good
there. -/
theorem lower_good {st : State .source} (hst : StateGood (KeyScope.ofId P) st) {c : Converted}
    (hc : ConvGood (KeyScope.ofId P) c) {raw : Read .source} (hl : Ix.LeanIngress.lower st c = .ok raw) :
    ReadGood (KeyScope.ofId P) raw := by
  cases c with
  | definitions ms =>
    obtain ⟨ds, hds, plain, hF⟩ := DefinitionBlockReads.lower_defs hl
    refine ⟨by simp [plain.owners], by simp [plain.blocks], fun d hd e he => ?_⟩
    rw [hds, List.toList_toArray] at hd
    obtain ⟨m, hm, b, hlow⟩ := ReaderUnits.forall₂_mem_right hF d hd
    rw [lowerDefinition_cv hlow e he]
    exact (hc m (by simpa using hm)).1
  | «axiom» cv =>
    simp only [Ix.LeanIngress.lower, pure, Except.pure, Except.ok.injEq] at hl
    subst hl
    refine ⟨by simp, by simp, fun d hd e he => ?_⟩
    simp only [List.mem_singleton] at hd
    subst hd
    simp only [CtxAgree.noteEntries, List.mem_singleton] at he
    subst he
    exact hc
  | quot k cv =>
    simp only [Ix.LeanIngress.lower, pure, Except.pure, Except.ok.injEq] at hl
    subst hl
    refine ⟨by simp, by simp, fun d hd e he => ?_⟩
    simp only [List.mem_singleton] at hd
    subst hd
    simp only [CtxAgree.noteEntries, List.mem_singleton] at he
    subst he
    exact hc
  | «inductive» rb =>
    have hl' : lowerInductive st rb = .ok raw := hl
    obtain ⟨gens, -, -, hblocks, -⟩ := CtxAgree.lowerInductiveDecls_ok (LowerDistinct.lowerInductiveDecls_of_ok hl')
    refine ⟨CtxAgree.lowerInductive_owners_good (P := KeyScope.ofId (md := .source) P) hc hl',
      fun x hx => ?_, fun d hd => ?_⟩
    · rw [hblocks] at hx
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      exact CtxAgree.blockRecOf_good (P := KeyScope.ofId (md := .source) P) hc
    · -- a renaming fixing the scope fixes the lowering
      obtain ⟨f, hfix, hmove⟩ := moveOff (P := P)
      have hfix' : ∀ i, (KeyScope.ofId (md := .source) P) i → f i = i := hfix
      have hrb : rb.Good (KeyScope.ofId P) := hc
      have hA : lowerInductive st (rb.mapKeys f) = .ok raw := by rw [blockRead_fix hfix' hrb]; exact hl'
      obtain ⟨hdecls, -, -⟩ := CtxAgree.lowerInductive_mapKeys (P := KeyScope.ofId P) (fun _ _ => trivial)
        (by intro a b ha hb e; rw [hfix a ha, hfix b hb] at e; exact e) (stateAgree_self hfix hst) hrb hl' hA
      have hd' := fixed_of_map (by rw [← Array.toList_map, ← hdecls]) d hd
      exact noted_good_of_fix hmove hd' (SourcePrelude.lower_noBasis st _ raw hl d hd)

end Lower

/-! ## The prelude's state -/

theorem fieldAgree_ok {α β : Type} [BEq β] {mS : Std.HashMap (Key .source) α} {mA : Std.HashMap (Key .anon) β}
    {ok : α → Bool} {erase : α → β} (h : PreludeAgree.fieldAgreeB mS mA ok erase = true) :
    ∀ (k : Key .source) (v : α), mS[k]? = some v → ok v = true := by
  intro k v hv
  unfold PreludeAgree.fieldAgreeB at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have := List.all_eq_true.mp h1 (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv)
  simp only [Bool.and_eq_true] at this
  exact this.1.2

/-- **The prelude's state lies in every scope of ids**: the decided prelude check makes every
entry name no input. -/
theorem prelude_good {P : Ix.Kernel.Name → Prop} {pre : Prelude .source} {preA : Prelude .anon}
    (h : PreludeAgree.preludeAgreeB pre preA = true) : StateGood (KeyScope.ofId P) pre.state := by
  simp only [PreludeAgree.preludeAgreeB, PreludeAgree.stateAgreeB, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨⟨hT, -⟩, hB⟩, hO⟩, -⟩⟩ := h
  have none : ∀ i, PreludeAgree.NoIds i → (KeyScope.ofId P) i := fun i hi => by
    simp [PreludeAgree.NoIds, PreludeAgree.noId] at hi
  have expr : ∀ {e : Ix.Kernel.Expr .source}, e.Good PreludeAgree.NoIds → e.Good (KeyScope.ofId P) :=
    fun he => Expr.Good.mono none (fun _ _ => trivial) he
  have key : ∀ {k : Key .source}, k.Good PreludeAgree.NoIds → k.Good (KeyScope.ofId P) :=
    fun hk => Key.Good.mono none (fun _ _ => trivial) hk
  have le : PreludeAgree.NoIds.Le (KeyScope.ofId P) := ⟨none, fun _ _ => trivial⟩
  refine ⟨fun k _ o ho => ?_, fun k _ p hp => expr (PreludeAgree.exprOk_good (fieldAgree_ok hT k p hp)),
    fun k _ b hb => ?_⟩
  · obtain ⟨hT', hc, hr, ht⟩ := PreludeAgree.ownerOk_good (fieldAgree_ok hO k o ho)
    exact ⟨key hT', key hc, key hr, expr ht⟩
  · obtain ⟨ht, hc, hr⟩ := PreludeAgree.blockOk_good (fieldAgree_ok hB k b hb)
    refine ⟨fun x hx => ?_, fun x hx => ConstantVal.Good.mono le (hc x hx), fun x hx => ?_⟩
    · obtain ⟨hcv, hks⟩ := ht x hx
      exact ⟨ConstantVal.Good.mono le hcv, fun k hk => key (hks k hk)⟩
    · obtain ⟨hcv, hrs⟩ := hr x hx
      exact ⟨ConstantVal.Good.mono le hcv, fun r hr => RecRule.Good.mono le (hrs r hr)⟩

/-! ## Every state of the trace -/

variable {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
  {failures : Failures} {t : RoleTable} {envQ : Env .source}

/-- **Every state quotient Source's trace reads from lies in the scope**
(`TraceSegments.TraceNeeds.states`), for the trace's lowered items (`Steps`) from the prelude's
state, when every group's quotient terms lie in the scope (`TraceNeeds.good`). -/
theorem states_good {hints : CName .source → Option ReducibilityHint} {pre : Prelude .source}
    {preA : Prelude .anon} (agree : PreludeAgree.preludeAgreeB pre preA = true)
    {ls : List SourcePrelude.Scheduled} {rs : List (Read .source)}
    (steps : Steps (quotientGraph ixe t hints sub) pre.state ls rs)
    (inTrace : ∀ y ∈ ls, y ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList)
    (good : ∀ (i : Nat) (gr : Group) (c : Converted), (quotientGraph ixe t hints sub).groups[i]? = some gr →
      Ix.LeanIngress.convert gr = .ok c →
        ConvGood (scope ixe t) ((c.withHints hints).quotient (TraceSegments.fibers ixe t))) :
    ∀ ℓ, StateGood (scope ixe t) ((rs.take ℓ).foldl State.commit pre.state) := by
  obtain ⟨hlen, stepsAt⟩ := steps
  intro ℓ
  induction ℓ with
  | zero => exact prelude_good agree
  | succ ℓ ih =>
    by_cases hℓ : ℓ < rs.length
    · rw [List.take_add_one, List.getElem?_eq_getElem hℓ, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      obtain ⟨y, hy⟩ : ∃ y, ls[ℓ]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨conv, raw, s, s', _, _, dropped, hc, hl, hcol, -, -, -⟩ :=
        stepsAt ℓ y rs[ℓ] hy (List.getElem?_eq_getElem hℓ)
      obtain ⟨gr, c, hgr, hconv, rfl⟩ := ClosureLayout.scheduled_conversion (inTrace y (List.mem_of_getElem? hy)) hc
      exact commit_good ih (collapse_good hcol (lower_good ih (good _ gr c hgr hconv) hl))
    · rw [List.take_of_length_le (by omega), ← List.take_of_length_le (l := rs) (Nat.le_of_not_lt hℓ)]
      exact ih

/--
info: 'Ix.Cert.TraceStates.states_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms states_good

/-- **Every state quotient Source's trace reads from lies in the scope**, for the trace over the
schedule from the prelude's state (`TraceNeeds.states` in the form G takes it): its lowered items
(`ClosureLayout.trace_lowered`) and every group's good terms (`TraceGood.converted_good`). -/
theorem trace_states_good (P : Premises env roots sub ixe failures t envQ)
    {hints : CName .source → Option ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {pre : Prelude .source} {preA : Prelude .anon} (agree : PreludeAgree.preludeAgreeB pre preA = true) :
    ∀ rs fin s kb, SourcePrelude.Trace (quotientGraph ixe t hints sub) pre.state
      (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList rs fin s kb →
      ∀ ℓ, StateGood (scope ixe t) ((rs.take ℓ).foldl State.commit pre.state) := by
  intro rs fin s kb htrace
  have hxs : ((Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList).map (·.2) =
      List.range (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList.length := by
    rw [Array.toList_zipIdx, List.zipIdx_map_snd, List.length_zipIdx, List.range_eq_range']
  obtain ⟨ls, low, steps, -⟩ := ClosureLayout.trace_lowered htrace (fun _ h => h) hxs
  exact states_good agree steps (fun y hy => low.sub.subset hy)
    (fun i gr c hgr hconv => TraceGood.converted_good P scheduled hgr hconv)

/--
info: 'Ix.Cert.TraceStates.trace_states_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_states_good

end Ix.Cert.TraceStates
