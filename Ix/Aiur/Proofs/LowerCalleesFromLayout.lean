module
public import Ix.Aiur.Proofs.LowerShared
public import Ix.Aiur.Proofs.DedupSound

public section

namespace Aiur

open Concrete

/-! Core predicates. -/

/-- `callee` is the index of some `.function` entry in `layout`. -/
@[reducible]
def CalleeFromLayout (layout : LayoutMap) (callee : Bytecode.FunIdx) : Prop :=
  ∃ (g : Global) (fl : FunctionLayout),
    layout[g]? = some (.function fl) ∧ callee = fl.index

/-- Every `.call` op whose idx appears as a callee in `ops` comes from a
`.function` layout entry. -/
@[expose, reducible]
def AllCallsFromLayout (layout : LayoutMap) (ops : Array Bytecode.Op) : Prop :=
  ∀ op ∈ ops, ∀ idx args outSz uc,
    op = Bytecode.Op.call idx args outSz uc → CalleeFromLayout layout idx

/-- Every callee collected from a `.ctrl` tree comes from a layout entry. -/
@[expose, reducible]
def CtrlCalleesFromLayout (layout : LayoutMap) (c : Bytecode.Ctrl) : Prop :=
  ∀ callee, callee ∈ Bytecode.Ctrl.collectAllCallees c → CalleeFromLayout layout callee

/-- Every callee of a full `Block` (ops + ctrl) comes from a layout entry. -/
@[expose, reducible]
def BlockCalleesFromLayout (layout : LayoutMap) (b : Bytecode.Block) : Prop :=
  ∀ callee, callee ∈ Bytecode.Block.collectAllCallees b → CalleeFromLayout layout callee

/-! Basic helpers. -/

/-- `foldl`-based callee collector, extracted so we can reason about it. -/
private abbrev opCollector (acc : Array Bytecode.FunIdx) (op : Bytecode.Op) :
    Array Bytecode.FunIdx :=
  match op with | .call idx _ _ _ => acc.push idx | _ => acc

/-- Op-collector step: the new accumulator is either unchanged (non-`.call` op)
or has `idx` pushed (for a `.call idx _ _ _` op). -/
private theorem opCollector_push_cases
    (acc : Array Bytecode.FunIdx) (op : Bytecode.Op) :
    opCollector acc op = acc ∨
    ∃ idx args outSz uc, op = Bytecode.Op.call idx args outSz uc ∧
      opCollector acc op = acc.push idx := by
  cases op
  case call idx args outSz uc =>
    right; exact ⟨idx, args, outSz, uc, rfl, rfl⟩
  all_goals
    left
    rfl

/-- List-level version of the op-callee fold: members in the result are either
in `acc` or `.call`-op-indices from `ops`. -/
private theorem mem_list_foldl_opCollector
    (ops : List Bytecode.Op) (acc : Array Bytecode.FunIdx) (x : Bytecode.FunIdx) :
    x ∈ List.foldl opCollector acc ops →
    x ∈ acc ∨ ∃ op ∈ ops, ∃ args outSz uc, op = Bytecode.Op.call x args outSz uc := by
  induction ops generalizing acc with
  | nil => intro h; left; simpa [List.foldl] using h
  | cons op rest ih =>
    intro h
    simp only [List.foldl_cons] at h
    rcases opCollector_push_cases acc op with heq | ⟨idx, args, outSz, uc, hcall, hpush⟩
    · rw [heq] at h
      rcases ih _ h with hacc | ⟨op', hop', args', outSz', uc', heq'⟩
      · left; exact hacc
      · right
        exact ⟨op', List.mem_cons.mpr (Or.inr hop'), args', outSz', uc', heq'⟩
    · rw [hpush] at h
      rcases ih _ h with hacc | ⟨op', hop', args', outSz', uc', heq'⟩
      · rcases Array.mem_push.mp hacc with h1 | h1
        · left; exact h1
        · right
          refine ⟨Bytecode.Op.call idx args outSz uc,
                  List.mem_cons.mpr (Or.inl hcall.symm),
                   args, outSz, uc, ?_⟩
          rw [h1]
      · right
        exact ⟨op', List.mem_cons.mpr (Or.inr hop'), args', outSz', uc', heq'⟩

/-- Array form: a callee produced by the op-level fold over `ops` (with empty
initial accumulator) came from some `.call` op in `ops`. -/
private theorem mem_foldl_opCollector_empty
    (ops : Array Bytecode.Op) (x : Bytecode.FunIdx)
    (h : x ∈ ops.foldl (init := #[]) opCollector) :
    ∃ op ∈ ops, ∃ args outSz uc, op = Bytecode.Op.call x args outSz uc := by
  rw [← Array.foldl_toList] at h
  rcases mem_list_foldl_opCollector ops.toList #[] x h with h' | h'
  · exact absurd h' (Array.not_mem_empty _)
  · obtain ⟨op, hop, args, outSz, uc, heq⟩ := h'
    exact ⟨op, Array.mem_toList_iff.mp hop, args, outSz, uc, heq⟩

/-- Strengthened form: a callee in `Block.collectAllCallees b` came from either
a `.call` op in `b.ops` or from `b.ctrl`. -/
private theorem mem_block_collectAllCallees
    (b : Bytecode.Block) (x : Bytecode.FunIdx) :
    x ∈ Bytecode.Block.collectAllCallees b →
    (∃ op ∈ b.ops, ∃ args outSz uc, op = Bytecode.Op.call x args outSz uc) ∨
    x ∈ Bytecode.Ctrl.collectAllCallees b.ctrl := by
  intro h
  unfold Bytecode.Block.collectAllCallees at h
  simp only at h
  rw [Array.mem_append] at h
  cases h with
  | inl hop => left; exact mem_foldl_opCollector_empty b.ops x hop
  | inr hctrl => right; exact hctrl

/-- If `BlockCalleesFromLayout layout b` holds, then so does
`CtrlCalleesFromLayout layout b.ctrl`. -/
private theorem block_callees_implies_ctrl
    {layout : LayoutMap} {b : Bytecode.Block}
    (h : BlockCalleesFromLayout layout b) :
    CtrlCalleesFromLayout layout b.ctrl := by
  intro callee hmem
  apply h
  unfold Bytecode.Block.collectAllCallees
  simp only
  exact Array.mem_append.mpr (Or.inr hmem)

/-- A block built from ops + ctrl with both sides layout-derived is itself
layout-derived. -/
private theorem block_callees_of_parts
    {layout : LayoutMap} {ops : Array Bytecode.Op} {ctrl : Bytecode.Ctrl}
    (hops : AllCallsFromLayout layout ops)
    (hctrl : CtrlCalleesFromLayout layout ctrl) :
    BlockCalleesFromLayout layout ({ ops, ctrl } : Bytecode.Block) := by
  intro callee hmem
  unfold Bytecode.Block.collectAllCallees at hmem
  simp only at hmem
  rw [Array.mem_append] at hmem
  cases hmem with
  | inl hop =>
    obtain ⟨op, hop, args, outSz, uc, heq⟩ :=
      mem_foldl_opCollector_empty ops callee hop
    exact hops op hop callee args outSz uc heq
  | inr hc => exact hctrl callee hc

/-! ## Main decomposed sub-lemmas.

Strategy (all sorried — closure is multi-round work):

1. `toIndex_delta` — `toIndex` extends the `ops` array only with calls whose idx
   comes from a layout function entry, so `AllCallsFromLayout` is preserved.
2. `term_compile_delta` — `Term.compile` produces a block whose callees are all
   layout-derived, assuming the initial `ops` are all layout-derived.
3. `addCase_delta` — `addCase` preserves the layout-derived invariant across
   both the ops it leaves behind and the cases it produces.
4. `buildArgs_delta` — `buildArgs` only recurses through `toIndex`, so it
   preserves `AllCallsFromLayout`.

Then `Function.compile` starts with empty ops (trivially layout-derived), so
the output block is fully layout-derived.
-/

/-- `AllCallsFromLayout` is preserved when pushing a non-`.call` op. -/
private theorem allCalls_push_non_call
    {layout : LayoutMap} {ops : Array Bytecode.Op} {op : Bytecode.Op}
    (hnc : ∀ idx args outSz uc, op ≠ Bytecode.Op.call idx args outSz uc)
    (hops : AllCallsFromLayout layout ops) :
    AllCallsFromLayout layout (ops.push op) := by
  intro op' hop' idx args outSz uc hcall
  rcases Array.mem_push.mp hop' with h | h
  · exact hops op' h idx args outSz uc hcall
  · subst h; exact absurd hcall (hnc idx args outSz uc)

/-- `AllCallsFromLayout` is preserved when pushing a `.call` with a layout-derived
callee. -/
private theorem allCalls_push_call
    {layout : LayoutMap} {ops : Array Bytecode.Op}
    {idx : Bytecode.FunIdx} {args : Array Bytecode.ValIdx}
    {outSz : Nat} {uc : Bool}
    (hcallee : CalleeFromLayout layout idx)
    (hops : AllCallsFromLayout layout ops) :
    AllCallsFromLayout layout (ops.push (Bytecode.Op.call idx args outSz uc)) := by
  intro op' hop' idx' args' outSz' uc' hcall
  rcases Array.mem_push.mp hop' with h | h
  · exact hops op' h idx' args' outSz' uc' hcall
  · subst h
    have : idx' = idx := by cases hcall; rfl
    subst this
    exact hcallee

mutual

/-- `toIndex` preserves `AllCallsFromLayout` on the `ops` array. -/
private theorem toIndex_delta
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Term)
    (s s' : CompilerState) (idxs : Array Bytecode.ValIdx)
    (hrun : (toIndex layoutMap bindings term).run s =
      .ok idxs s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    AllCallsFromLayout layoutMap s'.ops := by
  match term with
  | .unit t e =>
    -- `toIndex ... (.unit t e) = pure #[]` — state is unchanged.
    unfold toIndex at hrun
    simp only [pure] at hrun
    cases hrun; exact hops
  | .ret .. =>
    -- Error arm.
    unfold toIndex at hrun
    simp only [throw, throwThe, MonadExceptOf.throw] at hrun
    cases hrun
  | .match .. =>
    unfold toIndex at hrun
    simp only [throw, throwThe, MonadExceptOf.throw] at hrun
    cases hrun
  | .var t e name =>
    unfold toIndex at hrun
    simp only [pure] at hrun
    cases hrun; exact hops
  | .field t e g =>
    -- pushOp (.const g)
    unfold toIndex at hrun
    change pushOp _ _ s = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    refine allCalls_push_non_call ?_ hops
    intros; intro hc; cases hc
  | .ref t e name =>
    unfold toIndex at hrun
    -- Three arms: .function, .constructor, other (throws).
    split at hrun
    · -- .function: pushOp (.const (.ofNat layout.index))
      change pushOp _ _ s = .ok idxs s' at hrun
      rw [pushOp_run] at hrun
      cases hrun
      exact allCalls_push_non_call (by intros; intro hc; cases hc) hops
    · -- .constructor: do { index ← pushOp paddingOp; if ... then ... else ... }
      rename_i layout _
      simp only [bind, EStateM.bind, EStateM.run] at hrun
      rw [pushOp_run] at hrun
      -- Now hrun has the form: match (pushOp_run output) ... ; but pushOp_run
      -- rewrites in the outer, not inside the match. Let's normalize.
      simp only at hrun
      have hmid : AllCallsFromLayout layoutMap
        (s.ops.push (Bytecode.Op.const (.ofNat layout.index))) :=
        allCalls_push_non_call (by intros; intro hc; cases hc) hops
      -- Now either the if-branch is taken (another pushOp + pure) or else pure.
      split at hrun
      · -- if branch: pushOp (const 0) then pure (index ++ ...)
        simp only [EStateM.bind] at hrun
        rw [pushOp_run] at hrun
        simp only at hrun
        simp only [pure, EStateM.pure] at hrun
        cases hrun
        exact allCalls_push_non_call (by intros; intro hc; cases hc) hmid
      · -- else branch: pure index
        simp only [pure, EStateM.pure] at hrun
        cases hrun; exact hmid
    · -- throws
      simp only [throw, throwThe, MonadExceptOf.throw] at hrun; cases hrun
  | .letLoad t e dst dstTyp src bod =>
    unfold toIndex at hrun
    -- First: match typSize; either .error (throw) or .ok n (pure n)
    cases hts : typSize layoutMap dstTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok size =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      rw [pushOp_run] at hrun
      simp only at hrun
      exact toIndex_delta layoutMap _ bod _ s' idxs hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
  | .tuple typ escapes terms =>
    unfold toIndex at hrun
    rw [← Array.foldlM_toList] at hrun
    -- Size bound for elements; pack as sized pairs.
    have hmem_size : ∀ t, t ∈ terms.toList → sizeOf t <
        sizeOf (Term.tuple typ escapes terms) := by
      intro t ht
      have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ht)
      simp only [Term.tuple.sizeOf_spec]; omega
    -- Induction on the list of sized pairs.
    have hgen :
        ∀ (l : List Term)
          (hsz : ∀ t ∈ l, sizeOf t < sizeOf (Term.tuple typ escapes terms))
          (acc : Array Bytecode.ValIdx) (sStart sEnd : CompilerState)
          (r : Array Bytecode.ValIdx),
          (l.foldlM (m := CompileM) (fun acc arg => do
              pure (acc ++ (← toIndex layoutMap bindings arg))) acc).run sStart =
            .ok r sEnd →
          AllCallsFromLayout layoutMap sStart.ops →
          AllCallsFromLayout layoutMap sEnd.ops := by
      intro l
      induction l with
      | nil =>
        intro _ acc sStart sEnd r hfold hops'
        simp only [List.foldlM_nil, pure] at hfold
        cases hfold; exact hops'
      | cons head tail ih =>
        intro hsz acc sStart sEnd r hfold hops'
        simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hfold
        split at hfold
        rotate_left
        · cases hfold
        rename_i stepRes sStep hstep
        simp only [pure, EStateM.pure] at hstep
        split at hstep
        rotate_left
        · cases hstep
        rename_i tiRes sTi hti
        have hheadsz : sizeOf head < sizeOf (Term.tuple typ escapes terms) :=
          hsz head (List.Mem.head _)
        have htoI : AllCallsFromLayout layoutMap sTi.ops :=
          toIndex_delta layoutMap bindings head sStart sTi tiRes hti hops'
        cases hstep
        exact ih (fun t ht => hsz t (List.Mem.tail _ ht)) (acc ++ tiRes) _ _ _
          hfold htoI
    exact hgen terms.toList hmem_size #[] s s' idxs hrun hops
  | .array typ escapes terms =>
    unfold toIndex at hrun
    rw [← Array.foldlM_toList] at hrun
    have hmem_size : ∀ t, t ∈ terms.toList → sizeOf t <
        sizeOf (Term.array typ escapes terms) := by
      intro t ht
      have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ht)
      simp only [Term.array.sizeOf_spec]; omega
    have hgen :
        ∀ (l : List Term)
          (hsz : ∀ t ∈ l, sizeOf t < sizeOf (Term.array typ escapes terms))
          (acc : Array Bytecode.ValIdx) (sStart sEnd : CompilerState)
          (r : Array Bytecode.ValIdx),
          (l.foldlM (m := CompileM) (fun acc arg => do
              pure (acc ++ (← toIndex layoutMap bindings arg))) acc).run sStart =
            .ok r sEnd →
          AllCallsFromLayout layoutMap sStart.ops →
          AllCallsFromLayout layoutMap sEnd.ops := by
      intro l
      induction l with
      | nil =>
        intro _ acc sStart sEnd r hfold hops'
        simp only [List.foldlM_nil, pure] at hfold
        cases hfold; exact hops'
      | cons head tail ih =>
        intro hsz acc sStart sEnd r hfold hops'
        simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hfold
        split at hfold
        rotate_left
        · cases hfold
        rename_i stepRes sStep hstep
        simp only [pure, EStateM.pure] at hstep
        split at hstep
        rotate_left
        · cases hstep
        rename_i tiRes sTi hti
        have hheadsz : sizeOf head < sizeOf (Term.array typ escapes terms) :=
          hsz head (List.Mem.head _)
        have htoI : AllCallsFromLayout layoutMap sTi.ops :=
          toIndex_delta layoutMap bindings head sStart sTi tiRes hti hops'
        cases hstep
        exact ih (fun t ht => hsz t (List.Mem.tail _ ht)) (acc ++ tiRes) _ _ _
          hfold htoI
    exact hgen terms.toList hmem_size #[] s s' idxs hrun hops
  | .letVar _ _ var val bod =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i valRes sMid htoi
    have hmid : AllCallsFromLayout layoutMap sMid.ops :=
      toIndex_delta layoutMap bindings val s sMid valRes htoi hops
    exact toIndex_delta layoutMap _ bod sMid s' idxs hrun hmid
  | .letWild _ _ val bod =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i valRes sMid htoi
    have hmid : AllCallsFromLayout layoutMap sMid.ops :=
      toIndex_delta layoutMap bindings val s sMid valRes htoi hops
    exact toIndex_delta layoutMap bindings bod sMid s' idxs hrun hmid
  | .add _ _ a b =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aIdx s1 hea
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings a s s1 aIdx hea hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i bIdx s2 heb
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings b s1 s2 bIdx heb h1
    -- pushOp (.add aIdx bIdx)
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .sub _ _ a b =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aIdx s1 hea
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings a s s1 aIdx hea hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i bIdx s2 heb
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings b s1 s2 bIdx heb h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .mul _ _ a b =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aIdx s1 hea
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings a s s1 aIdx hea hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i bIdx s2 heb
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings b s1 s2 bIdx heb h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .eqZero _ _ a =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aIdx s1 hea
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings a s s1 aIdx hea hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .app _ _ name args unconstrained =>
    unfold toIndex at hrun
    split at hrun
    · -- .function layout: buildArgs, then pushOp (.call layout.index args layout.outputSize unconstrained)
      rename_i layout hlookup
      simp only [bind, EStateM.bind, EStateM.run] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i argIdxs s1 hba
      have h1 : AllCallsFromLayout layoutMap s1.ops :=
        buildArgs_delta layoutMap bindings args #[] s s1 argIdxs hba hops
      change pushOp _ _ s1 = .ok idxs s' at hrun
      rw [pushOp_run] at hrun
      cases hrun
      refine allCalls_push_call ?_ h1
      exact ⟨name, layout, hlookup, rfl⟩
    · -- .constructor layout: pushOp (.const), buildArgs, optional pushOp (.const), pure
      rename_i layout _
      simp only [bind, EStateM.bind, EStateM.run] at hrun
      rw [pushOp_run] at hrun
      simp only at hrun
      have h0 : AllCallsFromLayout layoutMap
          (s.ops.push (.const (.ofNat layout.index))) :=
        allCalls_push_non_call (by intros; intro hc; cases hc) hops
      split at hrun
      rotate_left
      · cases hrun
      rename_i argIdxs s1 hba
      have h1 : AllCallsFromLayout layoutMap s1.ops :=
        buildArgs_delta layoutMap bindings args _ _ s1 argIdxs hba h0
      split at hrun
      · -- if-branch: pushOp (.const 0), pure
        simp only [EStateM.bind] at hrun
        rw [pushOp_run] at hrun
        simp only at hrun
        simp only [pure, EStateM.pure] at hrun
        cases hrun
        exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
      · -- else-branch: pure
        simp only [pure, EStateM.pure] at hrun
        cases hrun; exact h1
    · -- throws
      simp only [throw, throwThe, MonadExceptOf.throw] at hrun; cases hrun
  | .proj _ _ arg i =>
    unfold toIndex at hrun
    cases hat : arg.typ with
    | tuple typs =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      -- Inner: (typs.extract 0 i).foldlM body that only throws or pure's
      -- via typSize; state-preserving on success.
      have hfoldPreserves : ∀ (l : List Concrete.Typ) (sStart sEnd : CompilerState)
          (initAcc outAcc : Nat),
          (l.foldlM (m := CompileM) (fun acc typ => do
              let typLen ← match typSize layoutMap typ with
                | .error e => throw e
                | .ok len => pure len
              pure (typLen + acc)) initAcc).run sStart = .ok outAcc sEnd →
          sEnd = sStart := by
        intro l
        induction l with
        | nil =>
          intro sStart sEnd initAcc outAcc hf
          simp only [List.foldlM_nil, pure] at hf
          cases hf; rfl
        | cons t rest ih =>
          intro sStart sEnd initAcc outAcc hf
          simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hf
          -- Step: `match typSize layoutMap t with | .error => throw e | .ok => pure len; pure ...`
          cases hts : typSize layoutMap t with
          | error e =>
            -- throws → hf = Result.error
            rw [hts] at hf
            simp only [throw, throwThe, MonadExceptOf.throw] at hf
            cases hf
          | ok v =>
            rw [hts] at hf
            simp only [pure] at hf
            exact ih _ _ _ _ hf
      rw [← Array.foldlM_toList] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i offset sF hfold
      have hsF := hfoldPreserves (typs.extract 0 i).toList s sF 0 offset hfold
      rw [hsF] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i argRes s1 hti
      have h1 : AllCallsFromLayout layoutMap s1.ops :=
        toIndex_delta layoutMap bindings arg s s1 argRes hti hops
      cases hts : typSize layoutMap (typs[i]?.getD .unit) with
      | error e =>
        rw [hts] at hrun
        simp only [throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      | ok iLen =>
        rw [hts] at hrun
        simp only [] at hrun
        cases hrun; exact h1
    | unit | field | array _ _ | pointer _ | ref _ | function _ _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
  | .get _ _ arr i =>
    unfold toIndex at hrun
    cases hat : arr.typ with
    | array eltTyp _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      cases hts : typSize layoutMap eltTyp with
      | error e =>
        rw [hts] at hrun
        simp only [throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      | ok eltSize =>
        rw [hts] at hrun
        simp only [EStateM.pure, EStateM.bind] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i arrRes s1 hti
        have h1 : AllCallsFromLayout layoutMap s1.ops :=
          toIndex_delta layoutMap bindings arr s s1 arrRes hti hops
        cases hrun; exact h1
    | unit | field | tuple _ | pointer _ | ref _ | function _ _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
  | .slice _ _ arr i j =>
    unfold toIndex at hrun
    cases hat : arr.typ with
    | array eltTyp _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      cases hts : typSize layoutMap eltTyp with
      | error e =>
        rw [hts] at hrun
        simp only [throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      | ok eltSize =>
        rw [hts] at hrun
        simp only [EStateM.pure, EStateM.bind] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i arrRes s1 hti
        have h1 : AllCallsFromLayout layoutMap s1.ops :=
          toIndex_delta layoutMap bindings arr s s1 arrRes hti hops
        cases hrun; exact h1
    | unit | field | tuple _ | pointer _ | ref _ | function _ _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
  | .set _ _ arr i val =>
    unfold toIndex at hrun
    cases hat : arr.typ with
    | array eltTyp _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      cases hts : typSize layoutMap eltTyp with
      | error e =>
        rw [hts] at hrun
        simp only [throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      | ok eltSize =>
        rw [hts] at hrun
        simp only [EStateM.pure, EStateM.bind] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i arrRes s1 hti_arr
        have h1 : AllCallsFromLayout layoutMap s1.ops :=
          toIndex_delta layoutMap bindings arr s s1 arrRes hti_arr hops
        split at hrun
        rotate_left
        · cases hrun
        rename_i valRes s2 hti_val
        have h2 : AllCallsFromLayout layoutMap s2.ops :=
          toIndex_delta layoutMap bindings val s1 s2 valRes hti_val h1
        cases hrun; exact h2
    | unit | field | tuple _ | pointer _ | ref _ | function _ _ =>
      rw [hat] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
  | .store _ _ arg =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i argIdxs s1 hti
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings arg s s1 argIdxs hti hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .load _ _ ptr =>
    unfold toIndex at hrun
    cases hptyp : ptr.typ with
    | pointer typ =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.run] at hrun
      cases hts : typSize layoutMap typ with
      | error e =>
        rw [hts] at hrun
        simp only [throw, throwThe, MonadExceptOf.throw] at hrun
        cases hrun
      | ok len =>
        rw [hts] at hrun
        simp only [pure, EStateM.pure, EStateM.bind] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i ptrIdx s1 he
        have h1 : AllCallsFromLayout layoutMap s1.ops :=
          expectIdx_delta layoutMap bindings ptr s s1 ptrIdx he hops
        change pushOp _ _ s1 = .ok idxs s' at hrun
        rw [pushOp_run] at hrun
        cases hrun
        exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
    | unit =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | field =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | tuple _ =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | array _ _ =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ref _ =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | function _ _ =>
      rw [hptyp] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
  | .ptrVal _ _ ptr =>
    unfold toIndex at hrun
    exact toIndex_delta layoutMap bindings ptr s s' idxs hrun hops
  | .assertEq _ _ a b ret =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aIdx s1 hta
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings a s s1 aIdx hta hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i bIdx s2 htb
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      toIndex_delta layoutMap bindings b s1 s2 bIdx htb h1
    -- `modify (fun stt => {stt with ops := stt.ops.push (.assertEq a b)})`
    -- followed by `toIndex ret`. `modify` in EStateM returns `.ok () (f s2)`.
    simp only [modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet] at hrun
    exact toIndex_delta layoutMap bindings ret _ s' idxs hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h2)
  | .ioGetInfo _ _ key =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i keyIdxs s1 hk
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings key s s1 keyIdxs hk hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .ioSetInfo _ _ key idx len ret =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i keyIdxs s1 hk
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings key s s1 keyIdxs hk hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i idxIdx s2 hi
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings idx s1 s2 idxIdx hi h1
    split at hrun
    rotate_left
    · cases hrun
    rename_i lenIdx s3 hl
    have h3 : AllCallsFromLayout layoutMap s3.ops :=
      expectIdx_delta layoutMap bindings len s2 s3 lenIdx hl h2
    simp only [modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet] at hrun
    exact toIndex_delta layoutMap bindings ret _ s' idxs hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h3)
  | .ioRead _ _ idx len =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idxIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings idx s s1 idxIdx hi hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .ioWrite _ _ data ret =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i dataIdxs s1 hd
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings data s s1 dataIdxs hd hops
    simp only [modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet] at hrun
    exact toIndex_delta layoutMap bindings ret _ s' idxs hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h1)
  | .u8BitDecomposition _ _ byte =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i byteIdx s1 hb
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings byte s s1 byteIdx hb hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .u8ShiftLeft _ _ byte =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i byteIdx s1 hb
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings byte s s1 byteIdx hb hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .u8ShiftRight _ _ byte =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i byteIdx s1 hb
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings byte s s1 byteIdx hb hops
    change pushOp _ _ s1 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h1
  | .u8Xor _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u8Add _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u8Sub _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u8And _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u8Or _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u8LessThan _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .u32LessThan _ _ i j =>
    unfold toIndex at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i iIdx s1 hi
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      expectIdx_delta layoutMap bindings i s s1 iIdx hi hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i jIdx s2 hj
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      expectIdx_delta layoutMap bindings j s1 s2 jIdx hj h1
    change pushOp _ _ s2 = .ok idxs s' at hrun
    rw [pushOp_run] at hrun
    cases hrun
    exact allCalls_push_non_call (by intros; intro hc; cases hc) h2
  | .debug _ _ label t_opt ret =>
    unfold toIndex at hrun
    -- First: match t_opt → CompileM (Option (Array ValIdx))
    -- If none: pure none (state unchanged)
    -- If some sub: do let x ← toIndex sub; pure (some x) (state after toIndex)
    -- Then: modify ops; toIndex ret.
    cases t_opt with
    | none =>
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet] at hrun
      exact toIndex_delta layoutMap bindings ret _ s' idxs hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
    | some sub =>
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i subRes s1 hti
      have h1 : AllCallsFromLayout layoutMap s1.ops :=
        toIndex_delta layoutMap bindings sub s s1 subRes hti hops
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet] at hrun
      exact toIndex_delta layoutMap bindings ret _ s' idxs hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) h1)
termination_by (sizeOf term, 0)
decreasing_by
  all_goals first
    | assumption
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

/-- `buildArgs` preserves `AllCallsFromLayout`.
We bridge `.attach.foldlM` to a structural induction on the `args` list. -/
private theorem buildArgs_delta
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (args : List Term) (init : Array Bytecode.ValIdx)
    (s s' : CompilerState) (res : Array Bytecode.ValIdx)
    (hrun : (buildArgs layoutMap bindings args init).run s = .ok res s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    AllCallsFromLayout layoutMap s'.ops := by
  unfold buildArgs at hrun
  -- Helper: for a list `sub` whose elements are all "smaller than args"
  -- (enforced via a sizeOf-bounded predicate, matching the termination
  -- measure), the foldlM preserves the invariant.
  have hgen :
      ∀ (sub : List {x : Term // sizeOf x < sizeOf args})
        (acc : Array Bytecode.ValIdx) (sStart sEnd : CompilerState)
        (r : Array Bytecode.ValIdx),
        (sub.foldlM (m := CompileM) (fun acc ⟨arg, _⟩ => do
            pure (acc.append (← toIndex layoutMap bindings arg))) acc).run sStart =
          .ok r sEnd →
        AllCallsFromLayout layoutMap sStart.ops →
        AllCallsFromLayout layoutMap sEnd.ops := by
    intro sub
    induction sub with
    | nil =>
      intro acc sStart sEnd r hfold hops'
      simp only [List.foldlM_nil, pure] at hfold
      cases hfold; exact hops'
    | cons head tail ih =>
      intro acc sStart sEnd r hfold hops'
      simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hfold
      split at hfold
      rotate_left
      · cases hfold
      rename_i stepRes sStep hstep
      simp only [pure, EStateM.pure] at hstep
      split at hstep
      rotate_left
      · cases hstep
      rename_i tiRes sTi hti
      have htoI : AllCallsFromLayout layoutMap sTi.ops :=
        toIndex_delta layoutMap bindings head.val sStart sTi tiRes hti hops'
      cases hstep
      exact ih (acc.append tiRes) _ _ _ hfold htoI
  -- Map args.attach to the sized variant.
  have hargs_sub : args.attach.map
      (fun ⟨x, hx⟩ => (⟨x, List.sizeOf_lt_of_mem hx⟩ :
        {x : Term // sizeOf x < sizeOf args})) = _ := rfl
  -- Apply hgen with the sized version; foldlM over the map is the same
  -- because the body only reads `.val`.
  have hrun' :
      ((args.attach.map
          (fun ⟨x, hx⟩ => (⟨x, List.sizeOf_lt_of_mem hx⟩ :
            {x : Term // sizeOf x < sizeOf args}))).foldlM (m := CompileM)
        (fun acc ⟨arg, _⟩ => do
          pure (acc.append (← toIndex layoutMap bindings arg))) init).run s =
      .ok res s' := by
    rw [List.foldlM_map]
    exact hrun
  exact hgen _ init s s' res hrun' hops
termination_by (sizeOf args, 1)
decreasing_by
  all_goals first
    | assumption
    | decreasing_tactic
    | (have := head.2; omega)
    | grind

/-- `expectIdx` preserves `AllCallsFromLayout` (delegates to `toIndex`). -/
private theorem expectIdx_delta
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (term : Term)
    (s s' : CompilerState) (i : Bytecode.ValIdx)
    (hrun : (expectIdx layoutMap bindings term).run s = .ok i s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    AllCallsFromLayout layoutMap s'.ops := by
  unfold expectIdx at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun  -- error arm
  rename_i idxs sMid hti
  by_cases hsz : idxs.size = 1
  · rw [dif_pos hsz] at hrun
    simp only [pure, EStateM.pure] at hrun
    have : sMid = s' := by cases hrun; rfl
    subst this
    exact toIndex_delta layoutMap bindings term s sMid idxs hti hops
  · rw [dif_neg hsz] at hrun
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hrun
    cases hrun
termination_by (sizeOf term, 1)

end

/-! ### Hoisted per-arm sub-goals for `addCase_delta`.

Each `addCase` pattern arm dispatches through `Concrete.Term.compile` once,
then massages the `CompilerState`. We hoist each as a top-level theorem that
takes `term_compile_delta` as an explicit hypothesis (so the stub sits outside
the mutual block that would otherwise make it recursive). -/

@[simp]
private theorem compileM_get_apply (s : CompilerState) :
    (get : CompileM CompilerState) s = .ok s s := rfl

@[simp]
private theorem compileM_set_apply (v s : CompilerState) :
    (set v : CompileM PUnit) s = .ok () v := rfl

/-- `.field g` arm of `addCase`. -/
private theorem addCase_delta_field_arm
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (cases : Array (G × Bytecode.Block)) (defOpt : Option Bytecode.Block)
    (g : G) (term : Concrete.Term)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (_termCompileDelta : ∀ (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (_hrun : (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl
      (cases, defOpt) (.field g, term)).run s = .ok (cases', defOpt') s')
    (_hops : AllCallsFromLayout layoutMap s.ops)
    (_hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (_hdef : ∀ d, defOpt = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  unfold Concrete.addCase at _hrun
  simp only [bind, EStateM.bind, EStateM.run,
             compileM_get_apply, compileM_set_apply,
             pure, EStateM.pure] at _hrun
  split at _hrun
  rotate_left
  · cases _hrun
  rename_i body sMid hcompile
  cases _hrun
  refine ⟨?_, ?_, ?_⟩
  · exact _hops
  · intro p hmem
    rcases Array.mem_push.mp hmem with h | h
    · exact _hcases p h
    · subst h
      exact _termCompileDelta bindings s sMid body hcompile _hops
  · exact _hdef

/-- `.ref global pats` arm of `addCase`. -/
private theorem addCase_delta_ref_arm
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (cases : Array (G × Bytecode.Block)) (defOpt : Option Bytecode.Block)
    (global : Global) (pats : Array Local) (term : Concrete.Term)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (_termCompileDelta : ∀ (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (_hrun : (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl
      (cases, defOpt) (.ref global pats, term)).run s = .ok (cases', defOpt') s')
    (_hops : AllCallsFromLayout layoutMap s.ops)
    (_hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (_hdef : ∀ d, defOpt = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  cases hlookup : layoutMap[global]? with
  | none =>
    unfold Concrete.addCase at _hrun
    simp only [hlookup, bind, EStateM.bind, EStateM.run,
               throw, throwThe, MonadExceptOf.throw] at _hrun
    contradiction
  | some entry =>
    cases entry with
    | dataType _ =>
      unfold Concrete.addCase at _hrun
      simp only [hlookup, bind, EStateM.bind, EStateM.run,
                 throw, throwThe, MonadExceptOf.throw] at _hrun
      contradiction
    | function layout =>
      unfold Concrete.addCase at _hrun
      simp only [hlookup, bind, EStateM.bind, EStateM.run,
                 compileM_get_apply, compileM_set_apply,
                 pure, EStateM.pure] at _hrun
      split at _hrun
      · rename_i body sMid hcompile_
        first
        | (cases _hrun
           refine ⟨_hops, ?_, _hdef⟩
           intro p hmem
           rcases Array.mem_push.mp hmem with hp | hp
           · exact _hcases p hp
           · subst hp
             exact _termCompileDelta _ s sMid body hcompile_ _hops)
        | (symm at _hrun
           cases _hrun
           refine ⟨_hops, ?_, _hdef⟩
           intro p hmem
           rcases Array.mem_push.mp hmem with hp | hp
           · exact _hcases p hp
           · subst hp
             exact _termCompileDelta _ s sMid body hcompile_ _hops)
      · first | cases _hrun | (symm at _hrun; cases _hrun) | contradiction
    | constructor layout =>
      unfold Concrete.addCase at _hrun
      simp only [hlookup, bind, EStateM.bind, EStateM.run,
                 compileM_get_apply, compileM_set_apply,
                 pure, EStateM.pure] at _hrun
      split at _hrun
      · rename_i body sMid hcompile_
        first
        | (cases _hrun
           refine ⟨_hops, ?_, _hdef⟩
           intro p hmem
           rcases Array.mem_push.mp hmem with hp | hp
           · exact _hcases p hp
           · subst hp
             exact _termCompileDelta _ s sMid body hcompile_ _hops)
        | (symm at _hrun
           cases _hrun
           refine ⟨_hops, ?_, _hdef⟩
           intro p hmem
           rcases Array.mem_push.mp hmem with hp | hp
           · exact _hcases p hp
           · subst hp
             exact _termCompileDelta _ s sMid body hcompile_ _hops)
      · first | cases _hrun | (symm at _hrun; cases _hrun) | contradiction

/-- `.wildcard` arm of `addCase`. -/
private theorem addCase_delta_wildcard_arm
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (cases : Array (G × Bytecode.Block)) (defOpt : Option Bytecode.Block)
    (term : Concrete.Term)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (_termCompileDelta : ∀ (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (_hrun : (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl
      (cases, defOpt) (.wildcard, term)).run s = .ok (cases', defOpt') s')
    (_hops : AllCallsFromLayout layoutMap s.ops)
    (_hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (_hdef : ∀ d, defOpt = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  unfold Concrete.addCase at _hrun
  simp only [bind, EStateM.bind, EStateM.run,
             compileM_get_apply, compileM_set_apply,
             pure, EStateM.pure] at _hrun
  split at _hrun
  rotate_left
  · cases _hrun
  rename_i body sMid hcompile
  cases _hrun
  refine ⟨_hops, _hcases, ?_⟩
  intro d hd
  cases hd
  exact _termCompileDelta bindings s sMid body hcompile _hops

/-! ### Callee-traversal helpers for `.match` / `.matchContinue` control flow. -/

/-- `cases.attach.foldl (fun acc ⟨(_, block), _⟩ => acc ++ block.collectAllCallees) #[]`
membership implies membership in some case's `collectAllCallees`. -/
private theorem mem_attach_foldl_cases
    (cases : Array (G × Bytecode.Block))
    (x : Bytecode.FunIdx)
    (h : x ∈ cases.attach.foldl (init := (#[] : Array Bytecode.FunIdx))
      (fun acc ⟨(_, block), _⟩ => acc ++ Bytecode.Block.collectAllCallees block)) :
    ∃ p ∈ cases, x ∈ Bytecode.Block.collectAllCallees p.2 := by
  have hinv :
      ∀ (acc : Array Bytecode.FunIdx)
        (_hacc : ∀ y ∈ acc,
            ∃ p ∈ cases, y ∈ Bytecode.Block.collectAllCallees p.2),
      ∀ y ∈ cases.attach.foldl (init := acc)
        (fun acc ⟨(_, block), _⟩ => acc ++ Bytecode.Block.collectAllCallees block),
      ∃ p ∈ cases, y ∈ Bytecode.Block.collectAllCallees p.2 := by
    intro acc hacc
    refine Array.foldl_induction
      (motive := fun _ s =>
        ∀ y ∈ s, ∃ p ∈ cases, y ∈ Bytecode.Block.collectAllCallees p.2)
      hacc ?_
    intro i acc' ih y hy
    rcases Array.mem_append.mp hy with h1 | h1
    · exact ih y h1
    · exact ⟨(cases.attach[i]).val, (cases.attach[i]).property, h1⟩
  have hempty : ∀ y ∈ (#[] : Array Bytecode.FunIdx),
      ∃ p ∈ cases, y ∈ Bytecode.Block.collectAllCallees p.2 :=
    fun y hy => absurd hy (Array.not_mem_empty _)
  exact hinv #[] hempty x h

/-- `Bytecode.Ctrl.collectAllCallees (.match sel cases default)` is layout-derived
if all cases and the default (when present) are. -/
private theorem ctrlCallees_match
    {layoutMap : LayoutMap} (sel : Nat)
    (cases : Array (G × Bytecode.Block))
    (defaultBlock : Option Bytecode.Block)
    (hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (hdef : ∀ d, defaultBlock = some d → BlockCalleesFromLayout layoutMap d) :
    CtrlCalleesFromLayout layoutMap (.match sel cases defaultBlock) := by
  intro callee hmem
  unfold Bytecode.Ctrl.collectAllCallees at hmem
  simp only at hmem
  cases defaultBlock with
  | none =>
    obtain ⟨p, hp, hpc⟩ := mem_attach_foldl_cases cases callee hmem
    exact hcases p hp callee hpc
  | some blk =>
    rcases Array.mem_append.mp hmem with h | h
    · obtain ⟨p, hp, hpc⟩ := mem_attach_foldl_cases cases callee h
      exact hcases p hp callee hpc
    · exact hdef blk rfl callee h

/-- `Bytecode.Ctrl.collectAllCallees (.matchContinue sel cases default _ _ _ cont)` is
layout-derived if all cases, the default (when present), and the continuation are. -/
private theorem ctrlCallees_matchContinue
    {layoutMap : LayoutMap} (sel : Nat)
    (cases : Array (G × Bytecode.Block))
    (defaultBlock : Option Bytecode.Block)
    (outputSize sharedAux sharedLookups : Nat)
    (cont : Bytecode.Block)
    (hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (hdef : ∀ d, defaultBlock = some d → BlockCalleesFromLayout layoutMap d)
    (hcont : BlockCalleesFromLayout layoutMap cont) :
    CtrlCalleesFromLayout layoutMap
      (.matchContinue sel cases defaultBlock outputSize sharedAux sharedLookups cont) := by
  intro callee hmem
  unfold Bytecode.Ctrl.collectAllCallees at hmem
  simp only at hmem
  rcases Array.mem_append.mp hmem with hbranch | hcont_mem
  · cases defaultBlock with
    | none =>
      obtain ⟨p, hp, hpc⟩ := mem_attach_foldl_cases cases callee hbranch
      exact hcases p hp callee hpc
    | some blk =>
      rcases Array.mem_append.mp hbranch with h | h
      · obtain ⟨p, hp, hpc⟩ := mem_attach_foldl_cases cases callee h
        exact hcases p hp callee hpc
      · exact hdef blk rfl callee h
  · -- cont contributes directly as a Block.collectAllCallees witness.
    exact hcont callee hcont_mem

/-- Folding `Concrete.addCase` over `patTerms` preserves all three invariants:
`AllCallsFromLayout` on `ops`, case-blocks layout-derived, default-block
layout-derived. Takes `term_compile_delta` as explicit callback. -/
private theorem addCase_foldlM_delta
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (patTerms : Array (Concrete.Pattern × Concrete.Term))
    (cases0 : Array (G × Bytecode.Block)) (defOpt0 : Option Bytecode.Block)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (patTerms.foldlM (init := (cases0, defOpt0))
      (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl)).run s =
      .ok (cases', defOpt') s')
    (hops : AllCallsFromLayout layoutMap s.ops)
    (hcases : ∀ p ∈ cases0, BlockCalleesFromLayout layoutMap p.2)
    (hdef : ∀ d, defOpt0 = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  rw [← Array.foldlM_toList] at hrun
  have hgen :
      ∀ (l : List (Concrete.Pattern × Concrete.Term))
        (cs₀ : Array (G × Bytecode.Block)) (dOpt₀ : Option Bytecode.Block)
        (cs' : Array (G × Bytecode.Block)) (dOpt' : Option Bytecode.Block)
        (sStart sEnd : CompilerState),
      (l.foldlM (init := (cs₀, dOpt₀))
        (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl)).run sStart =
        .ok (cs', dOpt') sEnd →
      AllCallsFromLayout layoutMap sStart.ops →
      (∀ p ∈ cs₀, BlockCalleesFromLayout layoutMap p.2) →
      (∀ d, dOpt₀ = some d → BlockCalleesFromLayout layoutMap d) →
      AllCallsFromLayout layoutMap sEnd.ops ∧
      (∀ p ∈ cs', BlockCalleesFromLayout layoutMap p.2) ∧
      (∀ d, dOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
    intro l
    induction l with
    | nil =>
      intro cs₀ dOpt₀ cs' dOpt' sStart sEnd hfold hops0 hcs0 hd0
      simp only [List.foldlM_nil, pure, EStateM.pure] at hfold
      obtain ⟨hprod, hend⟩ := EStateM.Result.ok.inj hfold
      obtain ⟨hcs_eq, hd_eq⟩ := Prod.mk.inj hprod
      subst hcs_eq; subst hd_eq; subst hend
      exact ⟨hops0, hcs0, hd0⟩
    | cons head tail ih =>
      intro cs₀ dOpt₀ cs' dOpt' sStart sEnd hfold hops0 hcs0 hd0
      simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hfold
      split at hfold
      rotate_left
      · cases hfold
      rename_i midPair sMid hstep
      obtain ⟨midCases, midDef⟩ := midPair
      -- Single addCase step via the three arms.
      have hmid :
          AllCallsFromLayout layoutMap sMid.ops ∧
          (∀ p ∈ midCases, BlockCalleesFromLayout layoutMap p.2) ∧
          (∀ d, midDef = some d → BlockCalleesFromLayout layoutMap d) := by
        obtain ⟨pat, term⟩ := head
        cases pat with
        | field g =>
          exact addCase_delta_field_arm layoutMap bindings returnTyp idxs yieldCtrl
            cs₀ dOpt₀ g term midCases midDef sStart sMid
            (fun bindings' s₁ s₂ body' => termCompileDelta term bindings' s₁ s₂ body')
            hstep hops0 hcs0 hd0
        | ref global pats =>
          exact addCase_delta_ref_arm layoutMap bindings returnTyp idxs yieldCtrl
            cs₀ dOpt₀ global pats term midCases midDef sStart sMid
            (fun bindings' s₁ s₂ body' => termCompileDelta term bindings' s₁ s₂ body')
            hstep hops0 hcs0 hd0
        | wildcard =>
          exact addCase_delta_wildcard_arm layoutMap bindings returnTyp idxs yieldCtrl
            cs₀ dOpt₀ term midCases midDef sStart sMid
            (fun bindings' s₁ s₂ body' => termCompileDelta term bindings' s₁ s₂ body')
            hstep hops0 hcs0 hd0
        | tuple _ | array _ =>
          unfold Concrete.addCase at hstep
          simp only [throw, throwThe, MonadExceptOf.throw] at hstep; cases hstep
      obtain ⟨hops_mid, hcases_mid, hdef_mid⟩ := hmid
      exact ih midCases midDef cs' dOpt' sMid sEnd hfold hops_mid hcases_mid hdef_mid
  exact hgen patTerms.toList cases0 defOpt0 cases' defOpt' s s' hrun hops hcases hdef

/-! ### Hoisted per-arm sub-goals for `term_compile_delta`.

Each arm of `Concrete.Term.compile` dispatches via one of these hoisted
helpers, all of which take `term_compile_delta` as an explicit callback so
they live outside the mutual block. -/

/-- `Concrete.computeSharedLayout` does not touch state: it reads `degrees`
via `get` and returns a `pure` value. Therefore the final state equals the
input state. -/
private theorem computeSharedLayout_preserves_state
    (matchCases : Array (G × Bytecode.Block))
    (defaultBlock : Option Bytecode.Block)
    (s s' : CompilerState) (r : Nat × Nat)
    (hrun : (Concrete.computeSharedLayout matchCases defaultBlock).run s =
      .ok r s') :
    s = s' := by
  unfold Concrete.computeSharedLayout at hrun
  simp only [bind, EStateM.bind, EStateM.run, get, getThe, MonadStateOf.get,
    EStateM.get, pure, EStateM.pure] at hrun
  cases hrun
  rfl

/-- Non-tail `.letVar _ _ _ (.match ... valEscapes=true) bod` — reduces to
`(Concrete.Term.match ...).compile`. -/
private theorem term_compile_delta_letVar_match_escape
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (var : Local) (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letVar typ escapes var
          (.match matchTyp true scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [if_true] at hrun
  exact termCompileDelta
    (.match matchTyp true scrut cases defaultOpt) bindings s s' body hrun hops

/-- Non-tail `.letWild _ _ (.match ... valEscapes=true) bod`. -/
private theorem term_compile_delta_letWild_match_escape
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letWild typ escapes
          (.match matchTyp true scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [if_true] at hrun
  exact termCompileDelta
    (.match matchTyp true scrut cases defaultOpt) bindings s s' body hrun hops

/-- `.letVar _ _ _ val bod` where `val` is not a `.match`. -/
private theorem term_compile_delta_letVar_non_match
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (var : Local) (val bod : Concrete.Term)
    (hnm : ∀ mt me scr cs deOpt, val ≠ .match mt me scr cs deOpt)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.letVar typ escapes var val bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  have goal : ∀ (idxs : Array Bytecode.ValIdx) (sMid : CompilerState),
      (toIndex layoutMap bindings val).run s = .ok idxs sMid →
      (Concrete.Term.compile bod returnTyp layoutMap
          (bindings.insert var idxs) yieldCtrl).run sMid = .ok body s' →
      BlockCalleesFromLayout layoutMap body := by
    intro idxs sMid htoi hbod
    have hmid : AllCallsFromLayout layoutMap sMid.ops :=
      toIndex_delta layoutMap bindings val s sMid idxs htoi hops
    exact termCompileDelta bod (bindings.insert var idxs) sMid s' body hbod hmid
  match val, hnm with
  | .match mt me scr cs deOpt, h => exact absurd rfl (h mt me scr cs deOpt)
  | .unit .., _ | .var .., _ | .ref .., _ | .field .., _ | .tuple .., _
  | .array .., _ | .ret .., _ | .letVar .., _ | .letWild .., _
  | .letLoad .., _ | .app .., _ | .add .., _ | .sub .., _ | .mul .., _
  | .eqZero .., _ | .proj .., _ | .get .., _ | .slice .., _ | .set .., _
  | .store .., _ | .load .., _ | .ptrVal .., _ | .assertEq .., _
  | .ioGetInfo .., _ | .ioSetInfo .., _ | .ioRead .., _ | .ioWrite .., _
  | .u8BitDecomposition .., _ | .u8ShiftLeft .., _ | .u8ShiftRight .., _
  | .u8Xor .., _ | .u8Add .., _ | .u8Sub .., _ | .u8And .., _ | .u8Or .., _
  | .u8LessThan .., _ | .u32LessThan .., _ | .debug .., _ =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idx sMid htoi
    exact goal idx sMid htoi hrun

/-- `.letWild _ _ val bod` where `val` is not a `.match`. -/
private theorem term_compile_delta_letWild_non_match
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (val bod : Concrete.Term)
    (hnm : ∀ mt me scr cs deOpt, val ≠ .match mt me scr cs deOpt)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.letWild typ escapes val bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  have goal : ∀ (idxs : Array Bytecode.ValIdx) (sMid : CompilerState),
      (toIndex layoutMap bindings val).run s = .ok idxs sMid →
      (Concrete.Term.compile bod returnTyp layoutMap bindings yieldCtrl).run sMid =
        .ok body s' →
      BlockCalleesFromLayout layoutMap body := by
    intro idxs sMid htoi hbod
    have hmid : AllCallsFromLayout layoutMap sMid.ops :=
      toIndex_delta layoutMap bindings val s sMid idxs htoi hops
    exact termCompileDelta bod bindings sMid s' body hbod hmid
  match val, hnm with
  | .match mt me scr cs deOpt, h => exact absurd rfl (h mt me scr cs deOpt)
  | .unit .., _ | .var .., _ | .ref .., _ | .field .., _ | .tuple .., _
  | .array .., _ | .ret .., _ | .letVar .., _ | .letWild .., _
  | .letLoad .., _ | .app .., _ | .add .., _ | .sub .., _ | .mul .., _
  | .eqZero .., _ | .proj .., _ | .get .., _ | .slice .., _ | .set .., _
  | .store .., _ | .load .., _ | .ptrVal .., _ | .assertEq .., _
  | .ioGetInfo .., _ | .ioSetInfo .., _ | .ioRead .., _ | .ioWrite .., _
  | .u8BitDecomposition .., _ | .u8ShiftLeft .., _ | .u8ShiftRight .., _
  | .u8Xor .., _ | .u8Add .., _ | .u8Sub .., _ | .u8And .., _ | .u8Or .., _
  | .u8LessThan .., _ | .u32LessThan .., _ | .debug .., _ =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idx sMid htoi
    exact goal idx sMid htoi hrun

/-- `.letLoad _ _ dst dstTyp src bod`. -/
private theorem term_compile_delta_letLoad
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (dst : Local) (dstTyp : Concrete.Typ) (src : Local) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.letLoad ty es dst dstTyp src bod)
        returnTyp layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  cases hts : typSize layoutMap dstTyp with
  | error e =>
    rw [hts] at hrun
    simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
      MonadExceptOf.throw] at hrun
    cases hrun
  | ok size =>
    rw [hts] at hrun
    simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
    rw [pushOp_run] at hrun
    simp only at hrun
    exact termCompileDelta bod _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) hops)

/-- `.debug _ _ label term ret`. -/
private theorem term_compile_delta_debug
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (label : String) (t_opt : Option Concrete.Term) (ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.debug ty es label t_opt ret)
        returnTyp layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  cases t_opt with
  | none =>
    simp only [Option.mapM, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    exact termCompileDelta ret _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
  | some sub =>
    simp only [Option.mapM_some, Functor.map, EStateM.map,
      bind, EStateM.bind, EStateM.run] at hrun
    cases hti_eq : toIndex layoutMap bindings sub s with
    | error eErr sErr =>
      rw [hti_eq] at hrun
      simp only at hrun
      cases hrun
    | ok subRes sMid =>
      rw [hti_eq] at hrun
      simp only at hrun
      have hti_run : (toIndex layoutMap bindings sub).run s =
          .ok subRes sMid := hti_eq
      have h1 : AllCallsFromLayout layoutMap sMid.ops :=
        toIndex_delta layoutMap bindings sub s sMid subRes hti_run hops
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet] at hrun
      exact termCompileDelta ret _ _ _ _ hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) h1)

/-- `.assertEq _ _ a b ret`. -/
private theorem term_compile_delta_assertEq
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (a b ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.assertEq ty es a b ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i aRes s1 hta
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings a s s1 aRes hta hops
  split at hrun
  rotate_left
  · cases hrun
  rename_i bRes s2 htb
  have h2 : AllCallsFromLayout layoutMap s2.ops :=
    toIndex_delta layoutMap bindings b s1 s2 bRes htb h1
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h2)

/-- `.ioSetInfo _ _ key idx len ret`. -/
private theorem term_compile_delta_ioSetInfo
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (key idx len ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.ioSetInfo ty es key idx len ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i keyRes s1 hk
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings key s s1 keyRes hk hops
  split at hrun
  rotate_left
  · cases hrun
  rename_i idxRes s2 hi
  have h2 : AllCallsFromLayout layoutMap s2.ops :=
    toIndex_delta layoutMap bindings idx s1 s2 idxRes hi h1
  split at hrun
  rotate_left
  · cases hrun
  rename_i lenRes s3 hl
  have h3 : AllCallsFromLayout layoutMap s3.ops :=
    toIndex_delta layoutMap bindings len s2 s3 lenRes hl h2
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h3)

/-- `.ioWrite _ _ data ret`. -/
private theorem term_compile_delta_ioWrite
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (data ret : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.ioWrite ty es data ret) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i dataRes s1 hd
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings data s s1 dataRes hd hops
  simp only [modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  exact termCompileDelta ret _ _ _ _ hrun
    (allCalls_push_non_call (by intros; intro hc; cases hc) h1)

/-- `.ret _ _ sub`. -/
private theorem term_compile_delta_ret
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool) (sub : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (hrun : (Concrete.Term.compile (.ret ty es sub) returnTyp layoutMap
        bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  split at hrun
  rotate_left
  · cases hrun
  rename_i idxs s1 hti
  have h1 : AllCallsFromLayout layoutMap s1.ops :=
    toIndex_delta layoutMap bindings sub s s1 idxs hti hops
  simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
    EStateM.set, pure, EStateM.pure] at hrun
  cases hrun
  exact block_callees_of_parts h1 (by
    intro callee hmem
    unfold Bytecode.Ctrl.collectAllCallees at hmem
    exact absurd hmem (Array.not_mem_empty _))

/-- `.match _ _ scrut cases defaultOpt` — tail match. -/
private theorem term_compile_delta_match
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (ty : Concrete.Typ) (es : Bool)
    (scrut : Local) (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yieldCtrl).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile (.match ty es scrut cases defaultOpt) returnTyp
        layoutMap bindings yieldCtrl).run s = .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  have hpost : AllCallsFromLayout layoutMap
      ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
         degrees := s.degrees } : CompilerState).ops := by
    intro op hop; exact absurd hop (Array.not_mem_empty _)
  split at hrun
  rotate_left
  · cases hrun
  rename_i pair s1 hfold
  obtain ⟨bcCases, defBlk⟩ := pair
  have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
      BlockCalleesFromLayout layoutMap p.2 := by
    intro p hmem
    exact absurd hmem (Array.not_mem_empty _)
  have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
      BlockCalleesFromLayout layoutMap d := by
    intro d heq; cases heq
  have hstep :
      AllCallsFromLayout layoutMap s1.ops ∧
      (∀ p ∈ bcCases, BlockCalleesFromLayout layoutMap p.2) ∧
      (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
    addCase_foldlM_delta layoutMap bindings returnTyp _ yieldCtrl cases
      #[] none bcCases defBlk _ s1 termCompileDelta hfold hpost hInitCases hInitDef
  obtain ⟨hs1_ops, hbcCases, hdefBlk⟩ := hstep
  cases defaultOpt with
  | none =>
    simp only [pure, EStateM.pure] at hrun
    cases hrun
    refine block_callees_of_parts hops ?_
    exact ctrlCallees_match _ _ _ hbcCases hdefBlk
  | some t =>
    simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i tBlock s2 htcomp
    have htBlock : BlockCalleesFromLayout layoutMap tBlock :=
      termCompileDelta t bindings _ _ _ htcomp hs1_ops
    cases hrun
    refine block_callees_of_parts hops ?_
    refine ctrlCallees_match _ _ _ hbcCases ?_
    intro d hd
    have : d = tBlock := by cases hd; rfl
    subst this
    exact htBlock

-- matchContinue helpers (valEscapes=false for letVar/letWild) kept in a
-- block comment pending a state-preservation strengthening of
-- `term_compile_delta` (needed to derive `AllCallsFromLayout` on the state
-- AFTER `t.compile ... true`, which the current signature does not yield).
/-
private theorem term_compile_delta_letVar_match_continue
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (var : Local) (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (yc : Bool)
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yc).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letVar typ escapes var
          (.match matchTyp false scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [Bool.false_eq_true, ite_false, if_false,
    ↓reduceIte] at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  have hpost : AllCallsFromLayout layoutMap
      ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
         degrees := s.degrees } : CompilerState).ops := by
    intro op hop; exact absurd hop (Array.not_mem_empty _)
  split at hrun
  rotate_left
  · cases hrun
  rename_i pair s1 hfold
  obtain ⟨matchCases, defBlk⟩ := pair
  have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
      BlockCalleesFromLayout layoutMap p.2 := fun p hmem =>
    absurd hmem (Array.not_mem_empty _)
  have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
      BlockCalleesFromLayout layoutMap d := fun d heq => by cases heq
  have hstep :
      AllCallsFromLayout layoutMap s1.ops ∧
      (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
      (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
    addCase_foldlM_delta (yieldCtrl := true) layoutMap bindings returnTyp _ cases
      #[] none matchCases defBlk _ s1
      (fun term' bindings' s₁ s₂ body' hr' hops' =>
        termCompileDelta term' bindings' true s₁ s₂ body' hr' hops')
      hfold hpost hInitCases hInitDef
  obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
  -- Next: default block (possibly compiled from `t`).
  cases hdo : defaultOpt with
  | none =>
    rw [hdo] at hrun
    simp only [pure, EStateM.pure] at hrun
    -- Continue: typSize lookup, shared-layout, modify, bod.compile.
    cases hts : typSize layoutMap matchTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok outputSize =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      -- computeSharedLayout
      split at hrun
      rotate_left
      · cases hrun
      rename_i sharedPair s2 hcsl
      obtain ⟨sharedAux, sharedLookups⟩ := sharedPair
      -- get (returns current state)
      simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
      -- modify: state becomes { s2 with valIdx := ..., degrees := ... }
      simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      -- bod.compile
      split at hrun
      rotate_left
      · cases hrun
      rename_i contBlock s3 hcont
      cases hrun
      have hs1_s2 : s1 = s2 :=
        computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
      have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
        rw [← hs1_s2]; exact hs1_ops
      -- bod.compile runs with modified state; modify only touches valIdx/degrees.
      have hcontBlock : BlockCalleesFromLayout layoutMap contBlock :=
        termCompileDelta bod _ yieldCtrl _ _ _ hcont hs2_ops
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
  | some t =>
    rw [hdo] at hrun
    simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i tBlock s2' htcomp
    have htBlock : BlockCalleesFromLayout layoutMap tBlock :=
      termCompileDelta t bindings true _ _ _ htcomp hs1_ops
    have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
      intro d heq
      cases heq; exact htBlock
    -- typSize lookup
    cases hts : typSize layoutMap matchTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok outputSize =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i sharedPair s3' hcsl
      obtain ⟨sharedAux, sharedLookups⟩ := sharedPair
      simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
      simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i contBlock s4' hcont
      cases hrun
      have hs2_s3 : s2' = s3' :=
        computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
      have hs2_ops : AllCallsFromLayout layoutMap s2'.ops := by
        -- BLOCKED: `term_compile_delta` gives block-callees, but we need
        -- AllCallsFromLayout on s2'.ops (state after `t.compile` with
        -- yieldCtrl := true). This requires strengthening `term_compile_delta`
        -- to also assert the final state's ops are layout-derived. Out of
        -- scope for this pass.
        sorry
      have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
        rw [← hs2_s3]; exact hs2_ops
      have hcontBlock : BlockCalleesFromLayout layoutMap contBlock :=
        termCompileDelta bod _ yieldCtrl _ _ _ hcont hs3_ops
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock

/-- `.letWild _ _ (.match ... valEscapes=false) bod` — produces `.matchContinue` ctrl.
Symmetric to the `letVar` version (no `var` binding on the continuation). -/
private theorem term_compile_delta_letWild_match_continue
    (returnTyp : Concrete.Typ) (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (typ : Concrete.Typ) (escapes : Bool)
    (matchTyp : Concrete.Typ) (scrut : Local)
    (cases : Array (Concrete.Pattern × Concrete.Term))
    (defaultOpt : Option Concrete.Term) (bod : Concrete.Term)
    (s s' : CompilerState) (body : Bytecode.Block)
    (termCompileDelta : ∀ (term' : Concrete.Term)
        (bindings' : Std.HashMap Local (Array Bytecode.ValIdx))
        (yc : Bool)
        (s₁ s₂ : CompilerState) (body' : Bytecode.Block),
      (Concrete.Term.compile term' returnTyp layoutMap bindings' yc).run s₁ =
        .ok body' s₂ →
      AllCallsFromLayout layoutMap s₁.ops →
      BlockCalleesFromLayout layoutMap body')
    (hrun : (Concrete.Term.compile
        (.letWild typ escapes
          (.match matchTyp false scrut cases defaultOpt) bod)
        returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    BlockCalleesFromLayout layoutMap body := by
  unfold Concrete.Term.compile at hrun
  simp only [Bool.false_eq_true, ite_false, if_false,
    ↓reduceIte] at hrun
  simp only [bind, EStateM.bind, EStateM.run] at hrun
  simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at hrun
  have hpost : AllCallsFromLayout layoutMap
      ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
         degrees := s.degrees } : CompilerState).ops := by
    intro op hop; exact absurd hop (Array.not_mem_empty _)
  split at hrun
  rotate_left
  · cases hrun
  rename_i pair s1 hfold
  obtain ⟨matchCases, defBlk⟩ := pair
  have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
      BlockCalleesFromLayout layoutMap p.2 := fun p hmem =>
    absurd hmem (Array.not_mem_empty _)
  have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
      BlockCalleesFromLayout layoutMap d := fun d heq => by cases heq
  have hstep :
      AllCallsFromLayout layoutMap s1.ops ∧
      (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
      (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
    addCase_foldlM_delta (yieldCtrl := true) layoutMap bindings returnTyp _ cases
      #[] none matchCases defBlk _ s1
      (fun term' bindings' s₁ s₂ body' hr' hops' =>
        termCompileDelta term' bindings' true s₁ s₂ body' hr' hops')
      hfold hpost hInitCases hInitDef
  obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
  cases hdo : defaultOpt with
  | none =>
    rw [hdo] at hrun
    simp only [pure, EStateM.pure] at hrun
    cases hts : typSize layoutMap matchTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok outputSize =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i sharedPair s2 hcsl
      simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i contBlock s3 hcont
      cases hrun
      have hs1_s2 : s1 = s2 :=
        computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
      have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
        rw [← hs1_s2]; exact hs1_ops
      have hcontBlock : BlockCalleesFromLayout layoutMap contBlock :=
        termCompileDelta bod _ yieldCtrl _ _ _ hcont hs2_ops
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
  | some t =>
    rw [hdo] at hrun
    simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i tBlock s2' htcomp
    have htBlock : BlockCalleesFromLayout layoutMap tBlock :=
      termCompileDelta t bindings true _ _ _ htcomp hs1_ops
    have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
      intro d heq
      cases heq; exact htBlock
    cases hts : typSize layoutMap matchTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok outputSize =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i sharedPair s3' hcsl
      simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i contBlock s4' hcont
      cases hrun
      have hs2_s3 : s2' = s3' :=
        computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
      have hs2_ops : AllCallsFromLayout layoutMap s2'.ops := by
        -- BLOCKED: `term_compile_delta` gives block-callees, but we need
        -- AllCallsFromLayout on s2'.ops (state after `t.compile` with
        -- yieldCtrl := true). This requires strengthening `term_compile_delta`
        -- to also assert the final state's ops are layout-derived. Out of
        -- scope for this pass.
        sorry
      have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
        rw [← hs2_s3]; exact hs2_ops
      have hcontBlock : BlockCalleesFromLayout layoutMap contBlock :=
        termCompileDelta bod _ yieldCtrl _ _ _ hcont hs3_ops
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock
-/
-- end matchContinue placeholder

/-! ### The mutual block: three-way mutual for `term_compile_delta` +
`addCase_delta_inlined` + `addCases_fold_delta_inlined`. The signature is
STRENGTHENED to a conjunction
`AllCallsFromLayout layoutMap s'.ops ∧ BlockCalleesFromLayout layoutMap body`
so state preservation carries through the mutual. -/

mutual

private theorem addCases_fold_delta_inlined
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (patTerms : List (Concrete.Pattern × Concrete.Term))
    (cases0 : Array (G × Bytecode.Block)) (defOpt0 : Option Bytecode.Block)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (hrun : (patTerms.foldlM (init := (cases0, defOpt0))
      (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl)).run s =
      .ok (cases', defOpt') s')
    (hops : AllCallsFromLayout layoutMap s.ops)
    (hcases : ∀ p ∈ cases0, BlockCalleesFromLayout layoutMap p.2)
    (hdef : ∀ d, defOpt0 = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  match patTerms with
  | [] =>
    simp only [List.foldlM_nil, pure, EStateM.pure] at hrun
    obtain ⟨hprod, hend⟩ := EStateM.Result.ok.inj hrun
    obtain ⟨hcs_eq, hd_eq⟩ := Prod.mk.inj hprod
    subst hcs_eq; subst hd_eq; subst hend
    exact ⟨hops, hcases, hdef⟩
  | head :: tail =>
    simp only [List.foldlM_cons, bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i midPair sMid hstep
    obtain ⟨midCases, midDef⟩ := midPair
    have hmid :
        AllCallsFromLayout layoutMap sMid.ops ∧
        (∀ p ∈ midCases, BlockCalleesFromLayout layoutMap p.2) ∧
        (∀ d, midDef = some d → BlockCalleesFromLayout layoutMap d) :=
      addCase_delta_inlined layoutMap bindings returnTyp idxs yieldCtrl
        cases0 defOpt0 head midCases midDef s sMid hstep hops hcases hdef
    obtain ⟨hops_mid, hcases_mid, hdef_mid⟩ := hmid
    exact addCases_fold_delta_inlined layoutMap bindings returnTyp idxs yieldCtrl
      tail midCases midDef cases' defOpt' sMid s' hrun hops_mid hcases_mid hdef_mid

private theorem addCase_delta_inlined
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (returnTyp : Concrete.Typ)
    (idxs : Array Bytecode.ValIdx) (yieldCtrl : Bool)
    (cases : Array (G × Bytecode.Block)) (defOpt : Option Bytecode.Block)
    (patTerm : Concrete.Pattern × Concrete.Term)
    (cases' : Array (G × Bytecode.Block)) (defOpt' : Option Bytecode.Block)
    (s s' : CompilerState)
    (hrun : (Concrete.addCase layoutMap bindings returnTyp idxs yieldCtrl
      (cases, defOpt) patTerm).run s = .ok (cases', defOpt') s')
    (hops : AllCallsFromLayout layoutMap s.ops)
    (hcases : ∀ p ∈ cases, BlockCalleesFromLayout layoutMap p.2)
    (hdef : ∀ d, defOpt = some d → BlockCalleesFromLayout layoutMap d) :
    AllCallsFromLayout layoutMap s'.ops ∧
    (∀ p ∈ cases', BlockCalleesFromLayout layoutMap p.2) ∧
    (∀ d, defOpt' = some d → BlockCalleesFromLayout layoutMap d) := by
  obtain ⟨pat, term⟩ := patTerm
  cases pat with
  | field g =>
    exact addCase_delta_field_arm layoutMap bindings returnTyp idxs yieldCtrl
      cases defOpt g term cases' defOpt' s s'
      (fun bindings' s₁ s₂ body' hr' hops' =>
        (term_compile_delta term returnTyp layoutMap bindings' yieldCtrl s₁ s₂ body'
          hr' hops').2)
      hrun hops hcases hdef
  | ref global pats =>
    exact addCase_delta_ref_arm layoutMap bindings returnTyp idxs yieldCtrl
      cases defOpt global pats term cases' defOpt' s s'
      (fun bindings' s₁ s₂ body' hr' hops' =>
        (term_compile_delta term returnTyp layoutMap bindings' yieldCtrl s₁ s₂ body'
          hr' hops').2)
      hrun hops hcases hdef
  | wildcard =>
    exact addCase_delta_wildcard_arm layoutMap bindings returnTyp idxs yieldCtrl
      cases defOpt term cases' defOpt' s s'
      (fun bindings' s₁ s₂ body' hr' hops' =>
        (term_compile_delta term returnTyp layoutMap bindings' yieldCtrl s₁ s₂ body'
          hr' hops').2)
      hrun hops hcases hdef
  | tuple _ | array _ =>
    unfold Concrete.addCase at hrun
    simp only [throw, throwThe, MonadExceptOf.throw] at hrun
    cases hrun

/-- Main theorem: `Term.compile` produces a layout-derived block AND
preserves `AllCallsFromLayout` on the final compiler state. -/
private theorem term_compile_delta
    (term : Concrete.Term) (returnTyp : Concrete.Typ)
    (layoutMap : LayoutMap)
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (yieldCtrl : Bool)
    (s s' : CompilerState) (body : Bytecode.Block)
    (hrun : (Concrete.Term.compile term returnTyp layoutMap bindings yieldCtrl).run s =
      .ok body s')
    (hops : AllCallsFromLayout layoutMap s.ops) :
    AllCallsFromLayout layoutMap s'.ops ∧ BlockCalleesFromLayout layoutMap body := by
  match term with
  -- Arm 1+2: .letVar/letWild (.match _ true _ _ _) bod → inlined .match-compile.
  | .letVar _ _ _ (.match _ true _ cases defaultOpt) _
  | .letWild _ _ (.match _ true _ cases defaultOpt) _ =>
    unfold Concrete.Term.compile at hrun
    simp only [if_true] at hrun
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    simp only [extractOps, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    have hpost : AllCallsFromLayout layoutMap
        ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
           degrees := s.degrees } : CompilerState).ops := by
      intro op hop; exact absurd hop (Array.not_mem_empty _)
    split at hrun
    rotate_left
    · cases hrun
    rename_i pair s1 hfold
    obtain ⟨bcCases, defBlk⟩ := pair
    have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
        BlockCalleesFromLayout layoutMap p.2 :=
      fun p hmem => absurd hmem (Array.not_mem_empty _)
    have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
        BlockCalleesFromLayout layoutMap d :=
      fun d heq => by cases heq
    rw [← Array.foldlM_toList] at hfold
    have hstep :
        AllCallsFromLayout layoutMap s1.ops ∧
        (∀ p ∈ bcCases, BlockCalleesFromLayout layoutMap p.2) ∧
        (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
      addCases_fold_delta_inlined layoutMap bindings returnTyp _ yieldCtrl
        cases.toList #[] none bcCases defBlk _ s1 hfold hpost hInitCases hInitDef
    obtain ⟨hs1_ops, hbcCases, hdefBlk⟩ := hstep
    cases defaultOpt with
    | none =>
      simp only [pure, EStateM.pure] at hrun
      cases hrun
      refine ⟨hs1_ops, ?_⟩
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_match _ _ _ hbcCases hdefBlk
    | some t =>
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i tBlock s2 htcomp
      have htRes :
          AllCallsFromLayout layoutMap s2.ops ∧
          BlockCalleesFromLayout layoutMap tBlock :=
        term_compile_delta t returnTyp layoutMap bindings yieldCtrl _ _ _ htcomp hs1_ops
      obtain ⟨hs2_ops, htBlock⟩ := htRes
      cases hrun
      refine ⟨hs2_ops, ?_⟩
      refine block_callees_of_parts hops ?_
      refine ctrlCallees_match _ _ _ hbcCases ?_
      intro d hd
      have : d = tBlock := by cases hd; rfl
      subst this
      exact htBlock
  -- Arm 3: .letVar _ _ var (.match _ false _ _ _) bod → matchContinue.
  | .letVar _ _ var (.match matchTyp false _ cases defaultOpt) bod =>
    unfold Concrete.Term.compile at hrun
    simp only [Bool.false_eq_true, if_false, ↓reduceIte] at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    simp only [extractOps, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    have hpost : AllCallsFromLayout layoutMap
        ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
           degrees := s.degrees } : CompilerState).ops := by
      intro op hop; exact absurd hop (Array.not_mem_empty _)
    split at hrun
    rotate_left
    · cases hrun
    rename_i pair s1 hfold
    obtain ⟨matchCases, defBlk⟩ := pair
    have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
        BlockCalleesFromLayout layoutMap p.2 :=
      fun p hmem => absurd hmem (Array.not_mem_empty _)
    have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
        BlockCalleesFromLayout layoutMap d :=
      fun d heq => by cases heq
    rw [← Array.foldlM_toList] at hfold
    have hstep :
        AllCallsFromLayout layoutMap s1.ops ∧
        (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
        (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
      addCases_fold_delta_inlined layoutMap bindings returnTyp _ true
        cases.toList #[] none matchCases defBlk _ s1
        hfold hpost hInitCases hInitDef
    obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
    cases hdo : defaultOpt with
    | none =>
      rw [hdo] at hrun
      simp only [EStateM.pure] at hrun
      cases hts : typSize layoutMap matchTyp with
      | error e =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
          MonadExceptOf.throw] at hrun
        cases hrun
      | ok outputSize =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i sharedPair s2 hcsl
        simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i contBlock s3 hcont
        have hs1_s2 : s1 = s2 :=
          computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
        have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
          rw [← hs1_s2]; exact hs1_ops
        have hcontRes :
            AllCallsFromLayout layoutMap s3.ops ∧
            BlockCalleesFromLayout layoutMap contBlock :=
          term_compile_delta bod returnTyp layoutMap
            (bindings.insert var (Array.range' _ outputSize)) yieldCtrl _ _ _ hcont hs2_ops
        obtain ⟨hs3_ops, hcontBlock⟩ := hcontRes
        cases hrun
        refine ⟨hs3_ops, ?_⟩
        refine block_callees_of_parts hops ?_
        exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
    | some t =>
      rw [hdo] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i tBlock s2' htcomp
      have htRes :
          AllCallsFromLayout layoutMap s2'.ops ∧
          BlockCalleesFromLayout layoutMap tBlock :=
        term_compile_delta t returnTyp layoutMap bindings true _ _ _ htcomp hs1_ops
      obtain ⟨hs2'_ops, htBlock⟩ := htRes
      have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
        intro d heq; cases heq; exact htBlock
      cases hts : typSize layoutMap matchTyp with
      | error e =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
          MonadExceptOf.throw] at hrun
        cases hrun
      | ok outputSize =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i sharedPair s3' hcsl
        simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i contBlock s4' hcont
        have hs2_s3 : s2' = s3' :=
          computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
        have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
          rw [← hs2_s3]; exact hs2'_ops
        have hcontRes :
            AllCallsFromLayout layoutMap s4'.ops ∧
            BlockCalleesFromLayout layoutMap contBlock :=
          term_compile_delta bod returnTyp layoutMap
            (bindings.insert var (Array.range' _ outputSize)) yieldCtrl _ _ _ hcont hs3_ops
        obtain ⟨hs4_ops, hcontBlock⟩ := hcontRes
        cases hrun
        refine ⟨hs4_ops, ?_⟩
        refine block_callees_of_parts hops ?_
        exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock
  -- Arm 4: .letWild _ _ (.match _ false _ _ _) bod → matchContinue (no var).
  | .letWild _ _ (.match matchTyp false _ cases defaultOpt) bod =>
    unfold Concrete.Term.compile at hrun
    simp only [Bool.false_eq_true, if_false, ↓reduceIte] at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    simp only [extractOps, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    have hpost : AllCallsFromLayout layoutMap
        ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
           degrees := s.degrees } : CompilerState).ops := by
      intro op hop; exact absurd hop (Array.not_mem_empty _)
    split at hrun
    rotate_left
    · cases hrun
    rename_i pair s1 hfold
    obtain ⟨matchCases, defBlk⟩ := pair
    have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
        BlockCalleesFromLayout layoutMap p.2 :=
      fun p hmem => absurd hmem (Array.not_mem_empty _)
    have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
        BlockCalleesFromLayout layoutMap d :=
      fun d heq => by cases heq
    rw [← Array.foldlM_toList] at hfold
    have hstep :
        AllCallsFromLayout layoutMap s1.ops ∧
        (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
        (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
      addCases_fold_delta_inlined layoutMap bindings returnTyp _ true
        cases.toList #[] none matchCases defBlk _ s1
        hfold hpost hInitCases hInitDef
    obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
    cases hdo : defaultOpt with
    | none =>
      rw [hdo] at hrun
      simp only [EStateM.pure] at hrun
      cases hts : typSize layoutMap matchTyp with
      | error e =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
          MonadExceptOf.throw] at hrun
        cases hrun
      | ok outputSize =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i sharedPair s2 hcsl
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i contBlock s3 hcont
        have hs1_s2 : s1 = s2 :=
          computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
        have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
          rw [← hs1_s2]; exact hs1_ops
        have hcontRes :
            AllCallsFromLayout layoutMap s3.ops ∧
            BlockCalleesFromLayout layoutMap contBlock :=
          term_compile_delta bod returnTyp layoutMap bindings yieldCtrl _ _ _ hcont hs2_ops
        obtain ⟨hs3_ops, hcontBlock⟩ := hcontRes
        cases hrun
        refine ⟨hs3_ops, ?_⟩
        refine block_callees_of_parts hops ?_
        exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
    | some t =>
      rw [hdo] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i tBlock s2' htcomp
      have htRes :
          AllCallsFromLayout layoutMap s2'.ops ∧
          BlockCalleesFromLayout layoutMap tBlock :=
        term_compile_delta t returnTyp layoutMap bindings true _ _ _ htcomp hs1_ops
      obtain ⟨hs2'_ops, htBlock⟩ := htRes
      have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
        intro d heq; cases heq; exact htBlock
      cases hts : typSize layoutMap matchTyp with
      | error e =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
          MonadExceptOf.throw] at hrun
        cases hrun
      | ok outputSize =>
        rw [hts] at hrun
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i sharedPair s3' hcsl
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
        split at hrun
        rotate_left
        · cases hrun
        rename_i contBlock s4' hcont
        have hs2_s3 : s2' = s3' :=
          computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
        have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
          rw [← hs2_s3]; exact hs2'_ops
        have hcontRes :
            AllCallsFromLayout layoutMap s4'.ops ∧
            BlockCalleesFromLayout layoutMap contBlock :=
          term_compile_delta bod returnTyp layoutMap bindings yieldCtrl _ _ _
            hcont hs3_ops
        obtain ⟨hs4_ops, hcontBlock⟩ := hcontRes
        cases hrun
        refine ⟨hs4_ops, ?_⟩
        refine block_callees_of_parts hops ?_
        exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock
  -- Arm 5: .letVar _ _ var val bod (val non-match) → toIndex val + bod.compile.
  | .letVar _ _ var val bod =>
    unfold Concrete.Term.compile at hrun
    match val, bod, hrun with
    | .match matchTyp ve _ cases defaultOpt, bod, hrun =>
      -- Outer arms 1/3 handle .letVar + .match but Lean's pattern-match
      -- compiler doesn't propagate that — the branch is REACHABLE at
      -- elaboration even if runtime-dead. Inline arm 1 (ve=true) or
      -- arm 3 (ve=false) body.
      cases ve with
      | true =>
        -- Replicates arm 1 body.
        simp only [if_true] at hrun
        unfold Concrete.Term.compile at hrun
        simp only [bind, EStateM.bind, EStateM.run] at hrun
        simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hrun
        have hpost : AllCallsFromLayout layoutMap
            ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
               degrees := s.degrees } : CompilerState).ops := by
          intro op hop; exact absurd hop (Array.not_mem_empty _)
        split at hrun
        rotate_left
        · cases hrun
        rename_i pair s1 hfold
        obtain ⟨bcCases, defBlk⟩ := pair
        have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
            BlockCalleesFromLayout layoutMap p.2 :=
          fun p hmem => absurd hmem (Array.not_mem_empty _)
        have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
            BlockCalleesFromLayout layoutMap d :=
          fun d heq => by cases heq
        rw [← Array.foldlM_toList] at hfold
        have hstep :
            AllCallsFromLayout layoutMap s1.ops ∧
            (∀ p ∈ bcCases, BlockCalleesFromLayout layoutMap p.2) ∧
            (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
          addCases_fold_delta_inlined layoutMap bindings returnTyp _ yieldCtrl
            cases.toList #[] none bcCases defBlk _ s1 hfold hpost hInitCases hInitDef
        obtain ⟨hs1_ops, hbcCases, hdefBlk⟩ := hstep
        cases defaultOpt with
        | none =>
          simp only [pure, EStateM.pure] at hrun
          cases hrun
          refine ⟨hs1_ops, ?_⟩
          refine block_callees_of_parts hops ?_
          exact ctrlCallees_match _ _ _ hbcCases hdefBlk
        | some t =>
          simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
          split at hrun
          rotate_left
          · cases hrun
          rename_i tBlock s2 htcomp
          have htRes :
              AllCallsFromLayout layoutMap s2.ops ∧
              BlockCalleesFromLayout layoutMap tBlock :=
            term_compile_delta t returnTyp layoutMap bindings yieldCtrl _ _ _ htcomp hs1_ops
          obtain ⟨hs2_ops, htBlock⟩ := htRes
          cases hrun
          refine ⟨hs2_ops, ?_⟩
          refine block_callees_of_parts hops ?_
          refine ctrlCallees_match _ _ _ hbcCases ?_
          intro d hd
          have : d = tBlock := by cases hd; rfl
          subst this
          exact htBlock
      | false =>
        -- Replicates arm 3 body.
        simp only [Bool.false_eq_true, if_false, ↓reduceIte] at hrun
        simp only [bind, EStateM.bind, EStateM.run] at hrun
        simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hrun
        have hpost : AllCallsFromLayout layoutMap
            ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
               degrees := s.degrees } : CompilerState).ops := by
          intro op hop; exact absurd hop (Array.not_mem_empty _)
        split at hrun
        rotate_left
        · cases hrun
        rename_i pair s1 hfold
        obtain ⟨matchCases, defBlk⟩ := pair
        have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
            BlockCalleesFromLayout layoutMap p.2 :=
          fun p hmem => absurd hmem (Array.not_mem_empty _)
        have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
            BlockCalleesFromLayout layoutMap d :=
          fun d heq => by cases heq
        rw [← Array.foldlM_toList] at hfold
        have hstep :
            AllCallsFromLayout layoutMap s1.ops ∧
            (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
            (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
          addCases_fold_delta_inlined layoutMap bindings returnTyp _ true
            cases.toList #[] none matchCases defBlk _ s1
            hfold hpost hInitCases hInitDef
        obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
        cases hdo : defaultOpt with
        | none =>
          rw [hdo] at hrun
          simp only [EStateM.pure] at hrun
          cases hts : typSize layoutMap matchTyp with
          | error e =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
              MonadExceptOf.throw] at hrun
            cases hrun
          | ok outputSize =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i sharedPair s2 hcsl
            simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
            simp only [modify, modifyGet, MonadStateOf.modifyGet,
              EStateM.modifyGet] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i contBlock s3 hcont
            have hs1_s2 : s1 = s2 :=
              computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
            have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
              rw [← hs1_s2]; exact hs1_ops
            have hcontRes :
                AllCallsFromLayout layoutMap s3.ops ∧
                BlockCalleesFromLayout layoutMap contBlock :=
              term_compile_delta bod returnTyp layoutMap
                (bindings.insert var (Array.range' _ outputSize)) yieldCtrl _ _ _
                hcont hs2_ops
            obtain ⟨hs3_ops, hcontBlock⟩ := hcontRes
            cases hrun
            refine ⟨hs3_ops, ?_⟩
            refine block_callees_of_parts hops ?_
            exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
        | some t =>
          rw [hdo] at hrun
          simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
          split at hrun
          rotate_left
          · cases hrun
          rename_i tBlock s2' htcomp
          have htRes :
              AllCallsFromLayout layoutMap s2'.ops ∧
              BlockCalleesFromLayout layoutMap tBlock :=
            term_compile_delta t returnTyp layoutMap bindings true _ _ _ htcomp hs1_ops
          obtain ⟨hs2'_ops, htBlock⟩ := htRes
          have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
            intro d heq; cases heq; exact htBlock
          cases hts : typSize layoutMap matchTyp with
          | error e =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
              MonadExceptOf.throw] at hrun
            cases hrun
          | ok outputSize =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i sharedPair s3' hcsl
            simp only [get, getThe, MonadStateOf.get, EStateM.get] at hrun
            simp only [modify, modifyGet, MonadStateOf.modifyGet,
              EStateM.modifyGet] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i contBlock s4' hcont
            have hs2_s3 : s2' = s3' :=
              computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
            have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
              rw [← hs2_s3]; exact hs2'_ops
            have hcontRes :
                AllCallsFromLayout layoutMap s4'.ops ∧
                BlockCalleesFromLayout layoutMap contBlock :=
              term_compile_delta bod returnTyp layoutMap
                (bindings.insert var (Array.range' _ outputSize)) yieldCtrl _ _ _
                hcont hs3_ops
            obtain ⟨hs4_ops, hcontBlock⟩ := hcontRes
            cases hrun
            refine ⟨hs4_ops, ?_⟩
            refine block_callees_of_parts hops ?_
            exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock
    | .unit .., bod, hrun | .var .., bod, hrun | .ref .., bod, hrun | .field .., bod, hrun
    | .tuple .., bod, hrun | .array .., bod, hrun | .ret .., bod, hrun
    | .letVar .., bod, hrun | .letWild .., bod, hrun | .letLoad .., bod, hrun
    | .app .., bod, hrun | .add .., bod, hrun | .sub .., bod, hrun | .mul .., bod, hrun
    | .eqZero .., bod, hrun | .proj .., bod, hrun | .get .., bod, hrun
    | .slice .., bod, hrun | .set .., bod, hrun | .store .., bod, hrun
    | .load .., bod, hrun | .ptrVal .., bod, hrun | .assertEq .., bod, hrun
    | .ioGetInfo .., bod, hrun | .ioSetInfo .., bod, hrun | .ioRead .., bod, hrun
    | .ioWrite .., bod, hrun | .u8BitDecomposition .., bod, hrun
    | .u8ShiftLeft .., bod, hrun | .u8ShiftRight .., bod, hrun
    | .u8Xor .., bod, hrun | .u8Add .., bod, hrun | .u8Sub .., bod, hrun
    | .u8And .., bod, hrun | .u8Or .., bod, hrun | .u8LessThan .., bod, hrun
    | .u32LessThan .., bod, hrun | .debug .., bod, hrun =>
      simp only [bind, EStateM.bind, EStateM.run] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i idx sMid htoi
      have hmid : AllCallsFromLayout layoutMap sMid.ops :=
        toIndex_delta layoutMap bindings _ s sMid idx htoi hops
      exact term_compile_delta bod returnTyp layoutMap
        (bindings.insert var idx) yieldCtrl sMid s' body hrun hmid
  -- Arm 6: .letWild _ _ val bod (val non-match).
  | .letWild _ _ val bod =>
    unfold Concrete.Term.compile at hrun
    match val, bod, hrun with
    | .match matchTyp ve _ cases defaultOpt, bod, hrun =>
      cases ve with
      | true =>
        -- Replicates arm 2 body (same as arm 1 but .letWild).
        simp only [if_true] at hrun
        unfold Concrete.Term.compile at hrun
        simp only [bind, EStateM.bind, EStateM.run] at hrun
        simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hrun
        have hpost : AllCallsFromLayout layoutMap
            ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
               degrees := s.degrees } : CompilerState).ops := by
          intro op hop; exact absurd hop (Array.not_mem_empty _)
        split at hrun
        rotate_left
        · cases hrun
        rename_i pair s1 hfold
        obtain ⟨bcCases, defBlk⟩ := pair
        have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
            BlockCalleesFromLayout layoutMap p.2 :=
          fun p hmem => absurd hmem (Array.not_mem_empty _)
        have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
            BlockCalleesFromLayout layoutMap d :=
          fun d heq => by cases heq
        rw [← Array.foldlM_toList] at hfold
        have hstep :
            AllCallsFromLayout layoutMap s1.ops ∧
            (∀ p ∈ bcCases, BlockCalleesFromLayout layoutMap p.2) ∧
            (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
          addCases_fold_delta_inlined layoutMap bindings returnTyp _ yieldCtrl
            cases.toList #[] none bcCases defBlk _ s1 hfold hpost hInitCases hInitDef
        obtain ⟨hs1_ops, hbcCases, hdefBlk⟩ := hstep
        cases defaultOpt with
        | none =>
          simp only [pure, EStateM.pure] at hrun
          cases hrun
          refine ⟨hs1_ops, ?_⟩
          refine block_callees_of_parts hops ?_
          exact ctrlCallees_match _ _ _ hbcCases hdefBlk
        | some t =>
          simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
          split at hrun
          rotate_left
          · cases hrun
          rename_i tBlock s2 htcomp
          have htRes :
              AllCallsFromLayout layoutMap s2.ops ∧
              BlockCalleesFromLayout layoutMap tBlock :=
            term_compile_delta t returnTyp layoutMap bindings yieldCtrl _ _ _ htcomp hs1_ops
          obtain ⟨hs2_ops, htBlock⟩ := htRes
          cases hrun
          refine ⟨hs2_ops, ?_⟩
          refine block_callees_of_parts hops ?_
          refine ctrlCallees_match _ _ _ hbcCases ?_
          intro d hd
          have : d = tBlock := by cases hd; rfl
          subst this
          exact htBlock
      | false =>
        -- Replicates arm 4 body.
        simp only [Bool.false_eq_true, if_false, ↓reduceIte] at hrun
        simp only [bind, EStateM.bind, EStateM.run] at hrun
        simp only [extractOps, modifyGet, MonadStateOf.modifyGet,
          EStateM.modifyGet] at hrun
        have hpost : AllCallsFromLayout layoutMap
            ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
               degrees := s.degrees } : CompilerState).ops := by
          intro op hop; exact absurd hop (Array.not_mem_empty _)
        split at hrun
        rotate_left
        · cases hrun
        rename_i pair s1 hfold
        obtain ⟨matchCases, defBlk⟩ := pair
        have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
            BlockCalleesFromLayout layoutMap p.2 :=
          fun p hmem => absurd hmem (Array.not_mem_empty _)
        have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
            BlockCalleesFromLayout layoutMap d :=
          fun d heq => by cases heq
        rw [← Array.foldlM_toList] at hfold
        have hstep :
            AllCallsFromLayout layoutMap s1.ops ∧
            (∀ p ∈ matchCases, BlockCalleesFromLayout layoutMap p.2) ∧
            (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
          addCases_fold_delta_inlined layoutMap bindings returnTyp _ true
            cases.toList #[] none matchCases defBlk _ s1
            hfold hpost hInitCases hInitDef
        obtain ⟨hs1_ops, hMC, hDB⟩ := hstep
        cases hdo : defaultOpt with
        | none =>
          rw [hdo] at hrun
          simp only [EStateM.pure] at hrun
          cases hts : typSize layoutMap matchTyp with
          | error e =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
              MonadExceptOf.throw] at hrun
            cases hrun
          | ok outputSize =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i sharedPair s2 hcsl
            simp only [modify, modifyGet, MonadStateOf.modifyGet,
              EStateM.modifyGet] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i contBlock s3 hcont
            have hs1_s2 : s1 = s2 :=
              computeSharedLayout_preserves_state matchCases defBlk s1 s2 _ hcsl
            have hs2_ops : AllCallsFromLayout layoutMap s2.ops := by
              rw [← hs1_s2]; exact hs1_ops
            have hcontRes :
                AllCallsFromLayout layoutMap s3.ops ∧
                BlockCalleesFromLayout layoutMap contBlock :=
              term_compile_delta bod returnTyp layoutMap bindings yieldCtrl _ _ _
                hcont hs2_ops
            obtain ⟨hs3_ops, hcontBlock⟩ := hcontRes
            cases hrun
            refine ⟨hs3_ops, ?_⟩
            refine block_callees_of_parts hops ?_
            exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB hcontBlock
        | some t =>
          rw [hdo] at hrun
          simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
          split at hrun
          rotate_left
          · cases hrun
          rename_i tBlock s2' htcomp
          have htRes :
              AllCallsFromLayout layoutMap s2'.ops ∧
              BlockCalleesFromLayout layoutMap tBlock :=
            term_compile_delta t returnTyp layoutMap bindings true _ _ _ htcomp hs1_ops
          obtain ⟨hs2'_ops, htBlock⟩ := htRes
          have hDB' : ∀ d, some tBlock = some d → BlockCalleesFromLayout layoutMap d := by
            intro d heq; cases heq; exact htBlock
          cases hts : typSize layoutMap matchTyp with
          | error e =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
              MonadExceptOf.throw] at hrun
            cases hrun
          | ok outputSize =>
            rw [hts] at hrun
            simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i sharedPair s3' hcsl
            simp only [modify, modifyGet, MonadStateOf.modifyGet,
              EStateM.modifyGet] at hrun
            split at hrun
            rotate_left
            · cases hrun
            rename_i contBlock s4' hcont
            have hs2_s3 : s2' = s3' :=
              computeSharedLayout_preserves_state matchCases (some tBlock) s2' s3' _ hcsl
            have hs3_ops : AllCallsFromLayout layoutMap s3'.ops := by
              rw [← hs2_s3]; exact hs2'_ops
            have hcontRes :
                AllCallsFromLayout layoutMap s4'.ops ∧
                BlockCalleesFromLayout layoutMap contBlock :=
              term_compile_delta bod returnTyp layoutMap bindings yieldCtrl _ _ _
                hcont hs3_ops
            obtain ⟨hs4_ops, hcontBlock⟩ := hcontRes
            cases hrun
            refine ⟨hs4_ops, ?_⟩
            refine block_callees_of_parts hops ?_
            exact ctrlCallees_matchContinue _ _ _ _ _ _ _ hMC hDB' hcontBlock
    | .unit .., bod, hrun | .var .., bod, hrun | .ref .., bod, hrun | .field .., bod, hrun
    | .tuple .., bod, hrun | .array .., bod, hrun | .ret .., bod, hrun
    | .letVar .., bod, hrun | .letWild .., bod, hrun | .letLoad .., bod, hrun
    | .app .., bod, hrun | .add .., bod, hrun | .sub .., bod, hrun | .mul .., bod, hrun
    | .eqZero .., bod, hrun | .proj .., bod, hrun | .get .., bod, hrun
    | .slice .., bod, hrun | .set .., bod, hrun | .store .., bod, hrun
    | .load .., bod, hrun | .ptrVal .., bod, hrun | .assertEq .., bod, hrun
    | .ioGetInfo .., bod, hrun | .ioSetInfo .., bod, hrun | .ioRead .., bod, hrun
    | .ioWrite .., bod, hrun | .u8BitDecomposition .., bod, hrun
    | .u8ShiftLeft .., bod, hrun | .u8ShiftRight .., bod, hrun
    | .u8Xor .., bod, hrun | .u8Add .., bod, hrun | .u8Sub .., bod, hrun
    | .u8And .., bod, hrun | .u8Or .., bod, hrun | .u8LessThan .., bod, hrun
    | .u32LessThan .., bod, hrun | .debug .., bod, hrun =>
      simp only [bind, EStateM.bind, EStateM.run] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i idx sMid htoi
      have hmid : AllCallsFromLayout layoutMap sMid.ops :=
        toIndex_delta layoutMap bindings _ s sMid idx htoi hops
      exact term_compile_delta bod returnTyp layoutMap bindings yieldCtrl
        sMid s' body hrun hmid
  -- Arm 7: .letLoad _ _ dst dstTyp src bod.
  | .letLoad _ _ _ dstTyp _ bod =>
    unfold Concrete.Term.compile at hrun
    cases hts : typSize layoutMap dstTyp with
    | error e =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, throw, throwThe,
        MonadExceptOf.throw] at hrun
      cases hrun
    | ok size =>
      rw [hts] at hrun
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      rw [pushOp_run] at hrun
      simp only at hrun
      exact term_compile_delta bod returnTyp layoutMap _ _ _ _ _ hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
  -- Arm 8: .debug _ _ label t_opt ret.
  | .debug _ _ _ t_opt ret =>
    unfold Concrete.Term.compile at hrun
    cases t_opt with
    | none =>
      simp only [Option.mapM, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
      exact term_compile_delta ret returnTyp layoutMap _ _ _ _ _ hrun
        (allCalls_push_non_call (by intros; intro hc; cases hc) hops)
    | some sub =>
      simp only [Option.mapM_some, Functor.map, EStateM.map,
        bind, EStateM.bind, EStateM.run] at hrun
      cases hti_eq : toIndex layoutMap bindings sub s with
      | error eErr sErr =>
        rw [hti_eq] at hrun
        simp only at hrun
        cases hrun
      | ok subRes sMid =>
        rw [hti_eq] at hrun
        simp only at hrun
        have hti_run : (toIndex layoutMap bindings sub).run s = .ok subRes sMid := hti_eq
        have h1 : AllCallsFromLayout layoutMap sMid.ops :=
          toIndex_delta layoutMap bindings sub s sMid subRes hti_run hops
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
        exact term_compile_delta ret returnTyp layoutMap _ _ _ _ _ hrun
          (allCalls_push_non_call (by intros; intro hc; cases hc) h1)
  -- Arm 9: .assertEq _ _ a b ret.
  | .assertEq _ _ a b ret =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i aRes s1 hta
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings a s s1 aRes hta hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i bRes s2 htb
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      toIndex_delta layoutMap bindings b s1 s2 bRes htb h1
    simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    exact term_compile_delta ret returnTyp layoutMap _ _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h2)
  -- Arm 10: .ioSetInfo _ _ key idx len ret.
  | .ioSetInfo _ _ key idxTm len ret =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i keyRes s1 hk
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings key s s1 keyRes hk hops
    split at hrun
    rotate_left
    · cases hrun
    rename_i idxRes s2 hi
    have h2 : AllCallsFromLayout layoutMap s2.ops :=
      toIndex_delta layoutMap bindings idxTm s1 s2 idxRes hi h1
    split at hrun
    rotate_left
    · cases hrun
    rename_i lenRes s3 hl
    have h3 : AllCallsFromLayout layoutMap s3.ops :=
      toIndex_delta layoutMap bindings len s2 s3 lenRes hl h2
    simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    exact term_compile_delta ret returnTyp layoutMap _ _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h3)
  -- Arm 11: .ioWrite _ _ data ret.
  | .ioWrite _ _ data ret =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i dataRes s1 hd
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings data s s1 dataRes hd hops
    simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    exact term_compile_delta ret returnTyp layoutMap _ _ _ _ _ hrun
      (allCalls_push_non_call (by intros; intro hc; cases hc) h1)
  -- Arm 12: .match _ _ scrut cases defaultOpt (tail match).
  | .match _ _ _ cases defaultOpt =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    simp only [extractOps, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hrun
    have hpost : AllCallsFromLayout layoutMap
        ({ valIdx := s.valIdx, ops := #[], selIdx := s.selIdx,
           degrees := s.degrees } : CompilerState).ops := by
      intro op hop; exact absurd hop (Array.not_mem_empty _)
    split at hrun
    rotate_left
    · cases hrun
    rename_i pair s1 hfold
    obtain ⟨bcCases, defBlk⟩ := pair
    have hInitCases : ∀ p ∈ (#[] : Array (G × Bytecode.Block)),
        BlockCalleesFromLayout layoutMap p.2 :=
      fun p hmem => absurd hmem (Array.not_mem_empty _)
    have hInitDef : ∀ d, (none : Option Bytecode.Block) = some d →
        BlockCalleesFromLayout layoutMap d :=
      fun d heq => by cases heq
    rw [← Array.foldlM_toList] at hfold
    have hstep :
        AllCallsFromLayout layoutMap s1.ops ∧
        (∀ p ∈ bcCases, BlockCalleesFromLayout layoutMap p.2) ∧
        (∀ d, defBlk = some d → BlockCalleesFromLayout layoutMap d) :=
      addCases_fold_delta_inlined layoutMap bindings returnTyp _ yieldCtrl
        cases.toList #[] none bcCases defBlk _ s1 hfold hpost hInitCases hInitDef
    obtain ⟨hs1_ops, hbcCases, hdefBlk⟩ := hstep
    cases defaultOpt with
    | none =>
      simp only [pure, EStateM.pure] at hrun
      cases hrun
      refine ⟨hs1_ops, ?_⟩
      refine block_callees_of_parts hops ?_
      exact ctrlCallees_match _ _ _ hbcCases hdefBlk
    | some t =>
      simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure] at hrun
      split at hrun
      rotate_left
      · cases hrun
      rename_i tBlock s2 htcomp
      have htRes :
          AllCallsFromLayout layoutMap s2.ops ∧
          BlockCalleesFromLayout layoutMap tBlock :=
        term_compile_delta t returnTyp layoutMap bindings yieldCtrl _ _ _ htcomp hs1_ops
      obtain ⟨hs2_ops, htBlock⟩ := htRes
      cases hrun
      refine ⟨hs2_ops, ?_⟩
      refine block_callees_of_parts hops ?_
      refine ctrlCallees_match _ _ _ hbcCases ?_
      intro d hd
      have : d = tBlock := by cases hd; rfl
      subst this
      exact htBlock
  -- Arm 13: .ret _ _ sub.
  | .ret _ _ _ =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idxs s1 hti
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings _ s s1 idxs hti hops
    simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      EStateM.set, pure, EStateM.pure] at hrun
    cases hrun
    refine ⟨h1, ?_⟩
    exact block_callees_of_parts h1 (by
      intro callee hmem
      unfold Bytecode.Ctrl.collectAllCallees at hmem
      exact absurd hmem (Array.not_mem_empty _))
  -- Arm 14: fallthrough — leaf-ish constructors. Go through
  -- Concrete.Term.compile's `_ =>` default arm: toIndex + get + set +
  -- .return/.yield ctrl. Enumerate each explicitly for the unfold to fire.
  | .unit _ _ | .var _ _ _ | .ref _ _ _ | .field _ _ _
  | .tuple _ _ _ | .array _ _ _ | .app _ _ _ _ _
  | .add _ _ _ _ | .sub _ _ _ _ | .mul _ _ _ _ | .eqZero _ _ _
  | .proj _ _ _ _ | .get _ _ _ _ | .slice _ _ _ _ _ | .set _ _ _ _ _
  | .store _ _ _ | .load _ _ _ | .ptrVal _ _ _
  | .ioGetInfo _ _ _ | .ioRead _ _ _ _
  | .u8BitDecomposition _ _ _ | .u8ShiftLeft _ _ _ | .u8ShiftRight _ _ _
  | .u8Xor _ _ _ _ | .u8Add _ _ _ _ | .u8Sub _ _ _ _
  | .u8And _ _ _ _ | .u8Or _ _ _ _ | .u8LessThan _ _ _ _ | .u32LessThan _ _ _ _ =>
    unfold Concrete.Term.compile at hrun
    simp only [bind, EStateM.bind, EStateM.run] at hrun
    split at hrun
    rotate_left
    · cases hrun
    rename_i idxs s1 hti
    have h1 : AllCallsFromLayout layoutMap s1.ops :=
      toIndex_delta layoutMap bindings _ s s1 idxs hti hops
    simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      EStateM.set, pure, EStateM.pure] at hrun
    cases hrun
    refine ⟨h1, ?_⟩
    refine block_callees_of_parts h1 ?_
    intro callee hmem
    -- ctrl is .return or .yield depending on if-condition. Both yield #[].
    split at hmem <;>
    (unfold Bytecode.Ctrl.collectAllCallees at hmem
     exact absurd hmem (Array.not_mem_empty _))

end

/-! ## Top-level composition. -/

/-- The target theorem (matches the signature in `LowerShared.lean`). -/
private theorem compile_callees_from_layout
    {layout : LayoutMap} {f : Concrete.Function}
    {targetBody : Bytecode.Block} {mst : _}
    (_hcomp : Concrete.Function.compile layout f = .ok (targetBody, mst))
    (callee : Bytecode.FunIdx)
    (_hcallee : callee ∈ Bytecode.Block.collectAllCallees targetBody) :
    ∃ (g : Global) (fl : FunctionLayout),
      layout[g]? = some (.function fl) ∧ callee = fl.index := by
  -- Derive `BlockCalleesFromLayout layout targetBody` from `term_compile_delta`,
  -- then apply it to `callee`.
  suffices hblock : BlockCalleesFromLayout layout targetBody by
    exact hblock callee _hcallee
  -- Unfold `Function.compile` to extract the `Term.compile` call and its
  -- initial state (which has `ops := #[]`, trivially layout-derived).
  unfold Concrete.Function.compile at _hcomp
  simp only [bind, Except.bind, pure, Except.pure] at _hcomp
  -- First `match` on the layout lookup.
  split at _hcomp
  rotate_left
  · exact absurd _hcomp (by intro heq; cases heq)
  rename_i fl _hlookup
  -- Now do a `split` on the foldlM.
  split at _hcomp
  · exact absurd _hcomp (by intro heq; cases heq)
  rename_i v _hfold
  -- Now there remains a match on `EStateM.run ...`.
  split at _hcomp
  · exact absurd _hcomp (by intro heq; cases heq)
  rename_i cbody _finalS hrun
  have hBody : cbody = targetBody := (Prod.mk.inj (Except.ok.inj _hcomp)).1
  have hinit :
      AllCallsFromLayout layout
        ({ valIdx := v.fst, selIdx := 0, ops := #[],
           degrees := Array.replicate v.fst 1 } : CompilerState).ops := by
    intro op hop; simp at hop
  rw [← hBody]
  exact (term_compile_delta f.body f.output layout v.snd false _ _ cbody hrun hinit).2

/-! ### Downstream consequences — moved from `LowerShared.lean`. -/

/-- Every callee produced by `Concrete.Function.compile layoutMap f` is
strictly below the final `bytecodeRaw.functions.size`. Composed from
`compile_callees_from_layout` + `layout_funcIdx_lt_bytecode_size`. -/
private theorem function_compile_callees_lt_final_size
    {decls : Concrete.Decls} {layout : LayoutMap}
    {f : Concrete.Function} {body : Bytecode.Block}
    {mst : _}
    {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (_hlayout : decls.layoutMap = .ok layout)
    (_hbc : decls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (_hcomp : Concrete.Function.compile layout f = .ok (body, mst))
    (callee : Bytecode.FunIdx)
    (_hcallee : callee ∈ Bytecode.Block.collectAllCallees body) :
    callee < bytecodeRaw.functions.size := by
  obtain ⟨g, fl, hfl, hcallee_eq⟩ :=
    compile_callees_from_layout _hcomp callee _hcallee
  rw [hcallee_eq]
  exact layout_funcIdx_lt_bytecode_size _hlayout _hbc g fl hfl

/-- Consolidated fold-invariant of `Concrete.Decls.toBytecode`. -/
theorem toBytecode_fold_invariant
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    (∀ (name : Global) (i : Bytecode.FunIdx),
        preNameMap[name]? = some i → i < bytecodeRaw.functions.size) ∧
    (∀ fi (_hfi : fi < bytecodeRaw.functions.size),
       ∀ callee,
         callee ∈ (Bytecode.Block.collectAllCallees bytecodeRaw.functions[fi].body) →
         callee < bytecodeRaw.functions.size) := by
  have horig := h
  rw [Concrete.Decls.toBytecode_unfold] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by intro heq; cases heq)
  rename_i layout hlayout
  simp only [IndexMap.foldlM] at h
  split at h
  · exact absurd h (by intro heq; cases heq)
  rename_i triple htriple
  obtain ⟨functions, memSizes, nameMap⟩ := triple
  simp only at h
  have hEq : (⟨functions, memSizes.toArray⟩ : Bytecode.Toplevel) = bytecodeRaw ∧
             nameMap = preNameMap := by
    have := Except.ok.inj h
    exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
  obtain ⟨hBC, hNM⟩ := hEq
  rw [← Array.foldlM_toList] at htriple
  let P :
      (Array Bytecode.Function × Lean.RBTree Nat compare ×
        Std.HashMap Global Bytecode.FunIdx) → Prop :=
    fun acc =>
      (∀ (name : Global) (i : Bytecode.FunIdx),
          (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[name]? = some i →
          i < acc.1.size) ∧
      (∀ fi (_ : fi < acc.1.size), ∀ callee,
          callee ∈ Bytecode.Block.collectAllCallees acc.1[fi].body →
          callee < bytecodeRaw.functions.size)
  have hP_init : P (#[], (Lean.RBTree.empty : Lean.RBTree Nat compare), {}) := by
    refine ⟨?_, ?_⟩
    · intro name i hget; simp at hget
    · intro fi hfi; simp at hfi
  have hP_step : ∀ acc x acc',
      x ∈ concDecls.pairs.toList →
      (match x.2 with
        | .function function => do
          let (body, layoutMState) ← Concrete.Function.compile layout function
          let nameMap := acc.2.2.insert function.name acc.1.size
          let function' : Bytecode.Function :=
            ⟨body, layoutMState.functionLayout, function.entry, false⟩
          let memSizes := layoutMState.memSizes.fold (·.insert ·) acc.2.1
          pure (acc.1.push function', memSizes, nameMap)
        | _ => pure acc : Except String _) = .ok acc' →
      P acc → P acc' := by
    rintro ⟨accF, accM, accN⟩ ⟨name, decl⟩ ⟨accF', accM', accN'⟩ _hmem hok ⟨hmap, hcal⟩
    match decl with
    | .function function =>
      simp only [bind, Except.bind] at hok
      split at hok
      · exact absurd hok (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, layoutMState⟩ := res
      simp only [pure, Except.pure] at hok
      have hprod := Prod.mk.inj (Except.ok.inj hok)
      have hF : accF' = accF.push
          ⟨body, layoutMState.functionLayout, function.entry, false⟩ := hprod.1.symm
      have hinner := Prod.mk.inj hprod.2
      have hN' : accN' = accN.insert function.name accF.size := hinner.2.symm
      subst hF; subst hN'
      refine ⟨?_, ?_⟩
      · intro nm i hget
        simp only at hget
        by_cases hname : (function.name == nm) = true
        · rw [Std.HashMap.getElem?_insert] at hget
          simp only [hname, if_true] at hget
          have hi : i = accF.size := (Option.some.inj hget).symm
          subst hi
          have hsize : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩).size = accF.size + 1 := Array.size_push _
          show accF.size < (accF.push _).size
          rw [hsize]; exact Nat.lt_succ_self _
        · have hname' : (function.name == nm) = false :=
            Bool.not_eq_true _ |>.mp hname
          rw [Std.HashMap.getElem?_insert] at hget
          simp only [hname'] at hget
          have hi : i < accF.size := hmap nm i hget
          have hsize : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩).size = accF.size + 1 := Array.size_push _
          show i < (accF.push _).size
          rw [hsize]; exact Nat.lt_succ_of_lt hi
      · intro fi hfi callee hc
        simp only at hfi hc
        by_cases hfiN : fi < accF.size
        · have hget : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[fi]'hfi = accF[fi] :=
            Array.getElem_push_lt (h := hfiN)
          rw [hget] at hc
          exact hcal fi hfiN callee hc
        · have hfieq : fi = accF.size := by
            have : fi < accF.size + 1 := by
              rw [Array.size_push] at hfi; exact hfi
            omega
          subst hfieq
          have hget : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[accF.size]'hfi =
            ⟨body, layoutMState.functionLayout, function.entry, false⟩ :=
            Array.getElem_push_eq
          rw [hget] at hc
          exact function_compile_callees_lt_final_size (decls := concDecls)
            hlayout horig hcomp callee hc
    | .dataType dt =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact ⟨hmap, hcal⟩
    | .constructor _ _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact ⟨hmap, hcal⟩
  have hP_final : P (functions, memSizes, nameMap) :=
    List.foldlM_except_invariant concDecls.pairs.toList _ _ hP_init hP_step htriple
  obtain ⟨hmap_final, hcal_final⟩ := hP_final
  refine ⟨?_, ?_⟩
  · intro name i hget
    rw [← hNM] at hget
    have := hmap_final name i hget
    show i < bytecodeRaw.functions.size
    rw [← hBC]; exact this
  · intro fi hfi callee hc
    have hfi' : fi < functions.size := by
      have : bytecodeRaw.functions = functions := by rw [← hBC]
      rw [this] at hfi; exact hfi
    have hc' : callee ∈ Bytecode.Block.collectAllCallees functions[fi].body := by
      have hfunEq : bytecodeRaw.functions = functions := by rw [← hBC]
      have : functions[fi] = bytecodeRaw.functions[fi]'(by rw [hfunEq]; exact hfi') := by
        congr 1 <;> rw [hfunEq]
      rw [this]; exact hc
    exact hcal_final fi hfi' callee hc'

private theorem IndexMap.getByKey_of_indices_eq
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) (j : Nat) (hj : j < m.pairs.size)
    (hidx : m.indices[m.pairs[j].1]? = some j) :
    m.getByKey m.pairs[j].1 = some m.pairs[j].2 := by
  unfold IndexMap.getByKey
  simp only [hidx, bind, Option.bind]
  have hget : m.pairs[j]? = some m.pairs[j] := Array.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
  rw [hget]
  rfl

/-- Every `name → funIdx` binding in `preNameMap` pairs with a specific
compiled function body in the bytecode. Requires the structural invariant
`hNameAgrees`: for every `.function f` pair in `cd.pairs`, the stored key
equals `f.name`. This holds for concretize-output decls where the iteration
key is always the function's declared name, but is not enforced structurally
by `Concrete.Decls` / `IndexMap` so must be supplied. -/
theorem toBytecode_function_extract
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {lm : LayoutMap}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (_hlm : cd.layoutMap = .ok lm)
    (_hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (name : Global) (funIdx : Bytecode.FunIdx)
    (_hfi : preNameMap[name]? = some funIdx) :
    ∃ (f : Concrete.Function) (body : Bytecode.Block)
      (lms : Bytecode.LayoutMState),
      funIdx < bytecode.functions.size ∧
      cd.getByKey name = some (.function f) ∧
      Concrete.Function.compile lm f = .ok (body, lms) ∧
      bytecode.functions[funIdx]?.map (·.body) = some body := by
  have _hlt : funIdx < bytecode.functions.size :=
    (toBytecode_fold_invariant _hbc).1 name funIdx _hfi
  have hbc_orig := _hbc
  rw [Concrete.Decls.toBytecode_unfold] at _hbc
  simp only [bind, Except.bind, pure, Except.pure] at _hbc
  split at _hbc
  · exact absurd _hbc (by intro heq; cases heq)
  rename_i layout hlayout
  have hlm_eq : layout = lm := by
    have := Except.ok.inj (hlayout ▸ _hlm); exact this
  simp only [IndexMap.foldlM] at _hbc
  split at _hbc
  · exact absurd _hbc (by intro heq; cases heq)
  rename_i triple htriple
  obtain ⟨functions, memSizes, nameMap⟩ := triple
  simp only at _hbc
  have hEq := Prod.mk.inj (Except.ok.inj _hbc)
  have hBC : (⟨functions, memSizes.toArray⟩ : Bytecode.Toplevel) = bytecode := hEq.1
  have hNM : nameMap = preNameMap := hEq.2
  rw [← Array.foldlM_toList] at htriple
  rw [hlm_eq] at htriple
  let P : (Array Bytecode.Function × Lean.RBTree Nat compare ×
      Std.HashMap Global Bytecode.FunIdx) → Prop :=
    fun acc =>
      ∀ nm idx, (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some idx →
        idx < acc.1.size ∧
        ∃ (f : Concrete.Function) (body : Bytecode.Block) (lms : Bytecode.LayoutMState),
          cd.getByKey nm = some (Declaration.function f) ∧
          Concrete.Function.compile lm f = .ok (body, lms) ∧
          acc.1[idx]?.map (·.body) = some body
  have hP_init : P (#[], (Lean.RBTree.empty : Lean.RBTree Nat compare), {}) := by
    intro nm idx hget; simp at hget
  have hP_step : ∀ acc x acc',
      x ∈ cd.pairs.toList →
      (match x.2 with
        | Declaration.function function => do
          let (body, layoutMState) ← Concrete.Function.compile lm function
          let nameMap := acc.2.2.insert function.name acc.1.size
          let function' : Bytecode.Function :=
            ⟨body, layoutMState.functionLayout, function.entry, false⟩
          let memSizes := layoutMState.memSizes.fold (·.insert ·) acc.2.1
          pure (acc.1.push function', memSizes, nameMap)
        | _ => pure acc : Except String _) = .ok acc' →
      P acc → P acc' := by
    rintro ⟨accF, accM, accN⟩ ⟨xname, decl⟩ ⟨accF', accM', accN'⟩ hmem hok hP
    match decl with
    | .function function =>
      simp only [bind, Except.bind] at hok
      split at hok
      · exact absurd hok (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, layoutMState⟩ := res
      simp only [pure, Except.pure] at hok
      have hprod := Prod.mk.inj (Except.ok.inj hok)
      have hF : accF' = accF.push
          ⟨body, layoutMState.functionLayout, function.entry, false⟩ := hprod.1.symm
      have hinner := Prod.mk.inj hprod.2
      have hN' : accN' = accN.insert function.name accF.size := hinner.2.symm
      subst hF; subst hN'
      intro nm idx hget
      by_cases hname : (function.name == nm) = true
      · rw [Std.HashMap.getElem?_insert] at hget
        simp only [hname, ↓reduceIte] at hget
        have hi : idx = accF.size := (Option.some.inj hget).symm
        subst hi
        constructor
        · rw [Array.size_push]; exact Nat.lt_succ_self _
        · refine ⟨function, body, layoutMState, ?_, hcomp, ?_⟩
          · -- From hmem + hNameAgrees we get xname = function.name.
            -- Combined with hname (function.name == nm), xname == nm.
            -- Applying IndexMap.getByKey_of_mem_pairs (which uses pairsIndexed)
            -- gives cd.getByKey xname = some (.function function), and congr
            -- under `==` finishes.
            have hxname : xname = function.name := _hNameAgrees xname function hmem
            have hgbk : cd.getByKey xname = some (Declaration.function function) :=
              IndexMap.getByKey_of_mem_pairs cd xname _ hmem
            -- `function.name == nm` with xname = function.name gives xname == nm.
            have hxn : (xname == nm) = true := by
              rw [hxname]; exact hname
            -- HashMap.getElem?_congr transfers getByKey across `==`-equivalent keys.
            unfold IndexMap.getByKey at hgbk ⊢
            rw [Std.HashMap.getElem?_congr (hab := hxn)] at hgbk
            exact hgbk
          · simp
      · have hname' : (function.name == nm) = false :=
            Bool.not_eq_true _ |>.mp hname
        rw [Std.HashMap.getElem?_insert] at hget
        simp only [hname'] at hget
        have ⟨hidx, f', body', lms', hgbk, hcmp, hbody⟩ := hP nm idx hget
        have hidx' : idx < accF.size := hidx
        constructor
        · rw [Array.size_push]; exact Nat.lt_succ_of_lt hidx'
        · refine ⟨f', body', lms', hgbk, hcmp, ?_⟩
          have h1 : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[idx]? = some accF[idx] :=
            Array.getElem?_push_lt (h := hidx')
          rw [h1]
          have h2 : (accF[idx]? : Option Bytecode.Function) = some accF[idx] := by
            simp [getElem?_pos, hidx']
          rw [h2] at hbody
          exact hbody
    | .dataType _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
    | .constructor _ _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
  have hP_final : P (functions, memSizes, nameMap) :=
    List.foldlM_except_invariant cd.pairs.toList _ _ hP_init hP_step htriple
  rw [← hNM] at _hfi
  obtain ⟨hidx, f, body, lms, hgbk, hcmp, hbody⟩ := hP_final name funIdx _hfi
  refine ⟨f, body, lms, _hlt, hgbk, hcmp, ?_⟩
  have hfun_eq : bytecode.functions = functions := by cases hBC; rfl
  rw [hfun_eq]; exact hbody

/-- Every index inserted by `toBytecode` into `preNameMap` is strictly less
than the final `functions.size`. -/
theorem preNameMap_in_range
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∀ (name : Global) (i : Bytecode.FunIdx),
      preNameMap[name]? = some i → i < bytecodeRaw.functions.size :=
  (toBytecode_fold_invariant h).1

/-- Every callee emitted by `toBytecode` is a valid `FunIdx` — strictly less
than `bytecodeRaw.functions.size`. -/
theorem toBytecode_callees_in_range
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∀ fi (_h : fi < bytecodeRaw.functions.size),
      ∀ callee,
        callee ∈ (Bytecode.Block.collectAllCallees bytecodeRaw.functions[fi].body) →
        callee < bytecodeRaw.functions.size :=
  (toBytecode_fold_invariant h).2

/-! ### Bridge between `Bytecode.Block.collectAllCallees` and
`Bytecode.collectCalleesBlock`.

Two definitions over `Block` give the same callee multiset; one lives in
`Semantics/Compatible.lean`, the other in `Compiler/Dedup.lean`.
`WellFormedCallees` uses the dedup-side form; the existing exported
`toBytecode_callees_in_range` uses the compatible-side form. We bridge them
via pointwise-membership iffs, then package the `WellFormedCallees` form. -/

/-- Op-level fold membership bridge (pointwise ∀ y). -/
private theorem ops_fold_mem_iff
    (ops : List Bytecode.Op) :
    ∀ (acc1 acc2 : Array Bytecode.FunIdx),
      (∀ y, y ∈ acc1 ↔ y ∈ acc2) →
      ∀ y,
        (y ∈ List.foldl (fun acc op => acc ++ Bytecode.collectCalleesOp op) acc1 ops ↔
          y ∈ List.foldl (fun acc op =>
            match op with | .call idx _ _ _ => acc.push idx | _ => acc) acc2 ops) := by
  induction ops with
  | nil =>
    intro acc1 acc2 hacc y
    simp only [List.foldl_nil]
    exact hacc y
  | cons op rest ih =>
    intro acc1 acc2 hacc y
    simp only [List.foldl_cons]
    apply ih
    intro z
    cases op <;>
      first
      | (simp only [Bytecode.collectCalleesOp]
         rw [Array.mem_append, Array.mem_push]
         constructor
         · rintro (h | h)
           · exact Or.inl ((hacc z).mp h)
           · rw [Array.mem_singleton] at h; exact Or.inr h
         · rintro (h | h)
           · exact Or.inl ((hacc z).mpr h)
           · exact Or.inr (Array.mem_singleton.mpr h))
      | (simp only [Bytecode.collectCalleesOp]
         rw [Array.append_empty]
         exact hacc z)

mutual
  theorem collectCalleesCtrl_mem_iff (c : Bytecode.Ctrl) :
      ∀ y, y ∈ Bytecode.collectCalleesCtrl c ↔ y ∈ Bytecode.Ctrl.collectAllCallees c := by
    cases c with
    | «return» s vs =>
      intro y
      unfold Bytecode.collectCalleesCtrl Bytecode.Ctrl.collectAllCallees
      simp
    | yield s vs =>
      intro y
      unfold Bytecode.collectCalleesCtrl Bytecode.Ctrl.collectAllCallees
      simp
    | «match» v branches def_ =>
      intro y
      unfold Bytecode.collectCalleesCtrl Bytecode.Ctrl.collectAllCallees
      simp only []
      have hbranches :
          ∀ (ps : List ({p : G × Bytecode.Block // p ∈ branches}))
            (acc1 acc2 : Array Bytecode.FunIdx),
            (∀ z, z ∈ acc1 ↔ z ∈ acc2) →
            (∀ q ∈ ps, ∀ z,
              z ∈ Bytecode.collectCalleesBlock q.1.2 ↔
                z ∈ Bytecode.Block.collectAllCallees q.1.2) →
            ∀ z,
              (z ∈ List.foldl (fun acc ⟨(_, b), _⟩ => acc ++ Bytecode.collectCalleesBlock b)
                        acc1 ps ↔
                z ∈ List.foldl
                        (fun acc ⟨(_, b), _⟩ => acc ++ Bytecode.Block.collectAllCallees b)
                        acc2 ps) := by
        intro ps
        induction ps with
        | nil =>
          intro acc1 acc2 hacc _ z
          simp only [List.foldl_nil]
          exact hacc z
        | cons p rest ih =>
          intro acc1 acc2 hacc hIH z
          simp only [List.foldl_cons]
          apply ih
          · intro w
            rw [Array.mem_append, Array.mem_append]
            have hIHp := hIH p (List.mem_cons_self ..) w
            constructor
            · rintro (h | h)
              · exact Or.inl ((hacc w).mp h)
              · exact Or.inr (hIHp.mp h)
            · rintro (h | h)
              · exact Or.inl ((hacc w).mpr h)
              · exact Or.inr (hIHp.mpr h)
          · intro q hq; exact hIH q (List.mem_cons_of_mem _ hq)
      have hIH_branch :
          ∀ q ∈ branches.attach.toList, ∀ z,
            z ∈ Bytecode.collectCalleesBlock q.1.2 ↔
              z ∈ Bytecode.Block.collectAllCallees q.1.2 := by
        intro q _ z
        exact collectCalleesBlock_mem_iff q.1.2 z
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      cases def_ with
      | none =>
        exact hbranches branches.attach.toList #[] #[] (fun _ => Iff.rfl) hIH_branch y
      | some b =>
        have hbr_iff := hbranches branches.attach.toList #[] #[] (fun _ => Iff.rfl) hIH_branch
        have hb_iff := collectCalleesBlock_mem_iff b
        rw [Array.mem_append, Array.mem_append]
        constructor
        · rintro (h | h)
          · exact Or.inl ((hbr_iff y).mp h)
          · exact Or.inr ((hb_iff y).mp h)
        · rintro (h | h)
          · exact Or.inl ((hbr_iff y).mpr h)
          · exact Or.inr ((hb_iff y).mpr h)
    | matchContinue v branches def_ outputSize sharedAux sharedLookups cont =>
      intro y
      unfold Bytecode.collectCalleesCtrl Bytecode.Ctrl.collectAllCallees
      simp only []
      have hbranches :
          ∀ (ps : List ({p : G × Bytecode.Block // p ∈ branches}))
            (acc1 acc2 : Array Bytecode.FunIdx),
            (∀ z, z ∈ acc1 ↔ z ∈ acc2) →
            (∀ q ∈ ps, ∀ z,
              z ∈ Bytecode.collectCalleesBlock q.1.2 ↔
                z ∈ Bytecode.Block.collectAllCallees q.1.2) →
            ∀ z,
              (z ∈ List.foldl (fun acc ⟨(_, b), _⟩ => acc ++ Bytecode.collectCalleesBlock b)
                        acc1 ps ↔
                z ∈ List.foldl
                        (fun acc ⟨(_, b), _⟩ => acc ++ Bytecode.Block.collectAllCallees b)
                        acc2 ps) := by
        intro ps
        induction ps with
        | nil =>
          intro acc1 acc2 hacc _ z
          simp only [List.foldl_nil]
          exact hacc z
        | cons p rest ih =>
          intro acc1 acc2 hacc hIH z
          simp only [List.foldl_cons]
          apply ih
          · intro w
            rw [Array.mem_append, Array.mem_append]
            have hIHp := hIH p (List.mem_cons_self ..) w
            constructor
            · rintro (h | h)
              · exact Or.inl ((hacc w).mp h)
              · exact Or.inr (hIHp.mp h)
            · rintro (h | h)
              · exact Or.inl ((hacc w).mpr h)
              · exact Or.inr (hIHp.mpr h)
          · intro q hq; exact hIH q (List.mem_cons_of_mem _ hq)
      have hIH_branch :
          ∀ q ∈ branches.attach.toList, ∀ z,
            z ∈ Bytecode.collectCalleesBlock q.1.2 ↔
              z ∈ Bytecode.Block.collectAllCallees q.1.2 := by
        intro q _ z
        exact collectCalleesBlock_mem_iff q.1.2 z
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      have hbr_iff := hbranches branches.attach.toList #[] #[] (fun _ => Iff.rfl) hIH_branch
      have hcont_iff := collectCalleesBlock_mem_iff cont
      cases def_ with
      | none =>
        rw [Array.mem_append, Array.mem_append]
        constructor
        · rintro (h | h)
          · exact Or.inl ((hbr_iff y).mp h)
          · exact Or.inr ((hcont_iff y).mp h)
        · rintro (h | h)
          · exact Or.inl ((hbr_iff y).mpr h)
          · exact Or.inr ((hcont_iff y).mpr h)
      | some b =>
        have hb_iff := collectCalleesBlock_mem_iff b
        show y ∈ (_ ++ Bytecode.collectCalleesBlock b) ++ Bytecode.collectCalleesBlock cont ↔
              y ∈ (_ ++ b.collectAllCallees) ++ cont.collectAllCallees
        rw [Array.mem_append, Array.mem_append, Array.mem_append, Array.mem_append]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl ((hbr_iff y).mp h))
          · exact Or.inl (Or.inr ((hb_iff y).mp h))
          · exact Or.inr ((hcont_iff y).mp h)
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl ((hbr_iff y).mpr h))
          · exact Or.inl (Or.inr ((hb_iff y).mpr h))
          · exact Or.inr ((hcont_iff y).mpr h)
  termination_by (sizeOf c, 0)
  decreasing_by
    all_goals try decreasing_tactic
    all_goals (
      apply Prod.Lex.left
      have hmem : q.val ∈ branches := q.2
      have h1 : sizeOf q.val < sizeOf branches := Array.sizeOf_lt_of_mem hmem
      have h2 : sizeOf q.val.2 < sizeOf q.val := by
        rcases q with ⟨⟨g, b⟩, _⟩
        simp
        omega
      first
        | (show sizeOf q.val.2 < sizeOf (Bytecode.Ctrl.match _ branches _)
           simp
           omega)
        | (show sizeOf q.val.2 < sizeOf (Bytecode.Ctrl.matchContinue _ branches _ _ _ _ _)
           simp
           omega))

  theorem collectCalleesBlock_mem_iff (b : Bytecode.Block) :
      ∀ y, y ∈ Bytecode.collectCalleesBlock b ↔ y ∈ Bytecode.Block.collectAllCallees b := by
    intro y
    unfold Bytecode.collectCalleesBlock Bytecode.Block.collectAllCallees
    simp only []
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    rw [Array.mem_append, Array.mem_append]
    have hop := ops_fold_mem_iff b.ops.toList #[] #[] (fun _ => Iff.rfl) y
    have hctrl := collectCalleesCtrl_mem_iff b.ctrl y
    constructor
    · rintro (h | h)
      · exact Or.inl (hop.mp h)
      · exact Or.inr (hctrl.mp h)
    · rintro (h | h)
      · exact Or.inl (hop.mpr h)
      · exact Or.inr (hctrl.mpr h)
  termination_by (sizeOf b, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left
         rcases b with ⟨ops, ctrl⟩
         show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
         omega)
end

/-- **Dedup cascade bridge**: `WellFormedCallees bytecodeRaw` holds for any
`bytecodeRaw` produced by `Concrete.Decls.toBytecode`. Proven by composing
`toBytecode_callees_in_range` with `collectCalleesBlock_mem_iff`. -/
theorem toBytecode_produces_WellFormedCallees
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    WellFormedCallees bytecodeRaw := by
  intro fi hfi c hc
  have h' := toBytecode_callees_in_range h fi hfi c
  apply h'
  exact (collectCalleesBlock_mem_iff _ c).mp hc

end Aiur

end
