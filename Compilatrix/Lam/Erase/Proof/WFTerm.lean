import Compilatrix.Lam.Erase.Proof.WFBase
import Compilatrix.Lam.Erase.Proof.RegBuild

/-! # Erased terms are well formed

Every term the specification `TR` describes is well formed (`Term.WF`) at
its context's depth, given what the finished program provides (`WFEnv`):
the globals `G` names are in range, and every constructor key registered
in the final table has its table arity, of its constructor's shape. The
table part comes from `erase_reg`: `RegT` says every key of the term has a
row (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels)

/-- What the well-formedness proof reads from the finished program. -/
structure WFEnv (I : Input) (G : Key.GKey → GlobalId → Prop) (S : Sig) (T : CTab) : Prop where
  wf : ProgWF I
  glob : ∀ key g, G key g → g < S.size
  arity : ∀ k n, T k n → S.arity? k = some n
  shape : ∀ k n, T k n → ∃ c, k = .src c ∧ RowShape I c n

section

variable {I : Input} {G : Key.GKey → GlobalId → Prop} {S : Sig} {T : CTab} (E : WFEnv I G S T)
include E

/-- A registered key of a constructor has the constructor's kept-field count
as its arity. -/
theorem WFEnv.ctor_arity {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat}
    {ty : Src.Term} (hd : I.decl? c = some (.ctor sf lv ind cidx np nf ty)) {n : Nat}
    (hT : T (I.ctorKey c) n) (q : Profile) :
    S.arity? (I.ctorKey c) = some (I.keptCount c q nf) := by
  obtain ⟨c', hk, c₀, sf₀, lv₀, ind₀, cidx₀, np₀, nf₀, ty₀, hd₀, ha₀, hn⟩ := E.shape _ _ hT
  have ha : I.alias c₀ = I.alias c := by
    rw [ha₀]
    unfold Input.ctorKey at hk
    injection hk with hk
    exact hk.symm
  rw [E.arity _ _ hT, hn, keptCount_alias_eq E.wf hd₀ hd ha, Input.keptCount_prof I c q nf]

end

theorem prim_arity (op : Src.PrimOp) : (Prim.ofSrc op).arity = op.arity := by
  cases op <;> rfl

theorem mem_of_getD_lvl {refs : List Ref} {k l : Nat} (h : refs.getD k .box = .lvl l) :
    Ref.lvl l ∈ refs := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hk : refs[k]? with
  | none => rw [hk] at h; cases h
  | some x =>
    rw [hk] at h
    cases h
    exact List.mem_of_getElem? hk

/-- What `BindR` produces: its lets well formed at their depths, a context
under them with the same map, and levels below the new depth. -/
structure BindOk (S : Sig) (cx : Cx) (lets : List Term) (refs : List Ref) (cx' : Cx) : Prop where
  wfLets : ∀ (i : Nat) v, lets[i]? = some v → Term.WF S (cx.depth + i) v
  depth : cx'.depth = cx.depth + lets.length
  ctx : cx'.ctx = cx.ctx
  refsLt : ∀ l, Ref.lvl l ∈ refs → l < cx'.depth

theorem BindOk.cxOk {S : Sig} {cx cx' : Cx} {lets : List Term} {refs : List Ref}
    (h : BindOk S cx lets refs cx') (hcx : CxOk cx) : CxOk cx' := fun i l hi => by
  rw [h.ctx] at hi
  rw [h.depth]
  exact Nat.lt_of_lt_of_le (hcx i l hi) (Nat.le_add_right _ _)

theorem BindOk.wrap {S : Sig} {cx cx' : Cx} {lets : List Term} {refs : List Ref} {b : Term}
    (h : BindOk S cx lets refs cx') (hb : Term.WF S cx'.depth b) :
    Term.WF S cx.depth (Erase.wrapLets lets b) :=
  wf_wrapLets h.wfLets (by rw [← h.depth]; exact hb)

theorem fieldArgs_wf {S : Sig} {cx : Cx} {fields : List (Option Nat)}
    (h : ∀ l, some l ∈ fields → l < cx.depth) :
    ∀ a ∈ fieldArgs cx fields, Term.WF S cx.depth a.1 := by
  intro a ha
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
  cases o with
  | some l => exact wf_lvl (h l ho)
  | none => trivial

/-- Keys of alternatives built from rules from index `j`: constructors of
the inductive at indices from `j`. -/
def KeysFrom (I : Input) (ind : CId) (j : Nat) (keys : List Key.CtorKey) : Prop :=
  ∀ k ∈ keys, ∃ c sf lv cidx np nf ty, k = I.ctorKey c ∧
    I.decl? c = some (.ctor sf lv ind cidx np nf ty) ∧ j ≤ cidx

section Mutual

set_option linter.unusedSectionVars false

variable {I : Input} {G : Key.GKey → GlobalId → Prop} {S : Sig} {T : CTab} (E : WFEnv I G S T)
include E

/-- One alternative from `RuleAltR`: its arity is the key's table arity,
and its fields' levels lie below the alternative's depth. -/
theorem ruleAlt_wf {r : CId} {q : Profile} {base : Nat} {ind : CId} {j : Nat} {rule : Src.Rule}
    {key : Key.CtorKey} {arity : Nat} {fields : List (Option Nat)}
    (h : RuleAltR I r q base ind j rule key arity fields) (hk : ∃ n, T key n) :
    S.arity? key = some arity ∧ (∀ l, some l ∈ fields → l < base + arity) ∧
      ∃ c sf lv np nf ty, key = I.ctorKey c ∧ I.decl? c = some (.ctor sf lv ind j np nf ty) := by
  obtain ⟨s, lv, cidx, np, nf, ty, hd, rfl, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨n, hn⟩ := hk
  refine ⟨E.ctor_arity hd hn _, fun l hl => ?_, rule.ctor, s, lv, np, rule.fields, ty, rfl, hd⟩
  obtain ⟨i, hi, hs⟩ := List.mem_map.1 hl
  split at hs
  · next hk =>
    cases hs
    exact Nat.add_lt_add_left (rank_lt I hk (List.mem_range.1 hi)) _
  · cases hs

mutual

theorem tr_wf : ∀ {cx : Cx} {t : Src.Term} {t' : Term}, TR I G cx t t' → CxOk cx → RegT T t' →
    Term.WF S cx.depth t'
  | _, _, _, .varSome hl, hcx, _ => wf_lvl (hcx _ _ hl)
  | _, _, _, .varNone _, _, _ => trivial
  | _, _, _, .sort, _, _ => trivial
  | _, _, _, .pi, _, _ => trivial
  | _, _, _, .natLit, _, _ => trivial
  | _, _, _, .lam _ hb, hcx, hr => by
    cases hr with
    | lam hr => exact (tr_wf hb hcx.bind hr :)
  | _, _, _, .letIrr _ hb, hcx, hr => by
    cases hr with
    | letE _ hr => exact ⟨trivial, tr_wf hb hcx.bind hr⟩
  | _, _, _, .letRel _ hv hb, hcx, hr => by
    cases hr with
    | letE hrv hrb => exact ⟨tr_wf hv hcx hrv, tr_wf hb hcx.bind hrb⟩
  | _, _, _, .projDrop he _ _ _ _, hcx, hr => by
    cases hr with
    | letE hre _ => exact ⟨tr_wf he hcx hre, trivial⟩
  | _, _, _, .projUnbox he _ _ _ _ _, hcx, hr => tr_wf he hcx hr
  | _, _, _, .projKey (i := i) (k := k) he _ hf hcls hdrop _ hd, hcx, hr => by
    cases hr with
    | proj hk hre =>
      obtain ⟨n, hn⟩ := hk
      refine ⟨⟨_, E.ctor_arity hd hn [], ?_⟩, tr_wf he hcx hre⟩
      have hkept : I.kept k [] i = true := by
        unfold Input.kept
        rw [hf]
        dsimp only
        rw [hcls]
        simp [hdrop]
      have hlen := E.wf.ctorFields hd hf
      exact rank_lt I hkept (hlen ▸ (List.getElem?_eq_some_iff.1 hcls).1)
  | _, _, _, .app _ _ hh ha, hcx, hr => by
    obtain ⟨hrh, hra⟩ := RegT.apps_inv hr
    exact wf_apps (tr_wf hh hcx hrh) (argsR_wf ha hcx hra).1
  | _, _, _, .plain _ _ _ hg ha, hcx, hr => by
    obtain ⟨_, hra⟩ := RegT.apps_inv hr
    exact wf_apps (E.glob _ _ hg) (argsR_wf ha hcx hra).1
  | _, _, _, .variant _ _ _ _ _ hg hl hrest, hcx, hr => by
    obtain ⟨_, hra⟩ := RegT.apps_inv hr
    refine wf_apps (E.glob _ _ hg) fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · exact lazyArgsR_wf hl hcx (fun b hb => hra b (List.mem_append_left _ hb)) a ha
    · exact (argsR_wf hrest hcx (fun b hb => hra b (List.mem_append_right _ hb))).1 a ha
  | _, _, _, .wrap _ _ _ hg ha, hcx, hr => by
    obtain ⟨_, hra⟩ := RegT.apps_inv hr
    exact wf_apps (E.glob _ _ hg) (argsR_wf ha hcx hra).1
  | _, _, _, .sat _ _ hle hs ha, hcx, hr => by
    obtain ⟨hrh, hra⟩ := RegT.apps_inv hr
    exact wf_apps (satR_wf hs hcx (by simp [List.length_take, Nat.min_eq_left hle]) hrh)
      (argsR_wf ha hcx hra).1

theorem argsR_wf : ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
    ArgsR I G cx args args' → CxOk cx → (∀ a ∈ args', RegT T a.1) →
    (∀ a ∈ args', Term.WF S cx.depth a.1) ∧ args'.length = args.length
  | _, _, _, .nil, _, _ => ⟨fun _ h => (by cases h), rfl⟩
  | _, _, _, .irr _ hrest, hcx, hr => by
    obtain ⟨h₁, h₂⟩ := argsR_wf hrest hcx fun b hb => hr b (List.mem_cons_of_mem _ hb)
    refine ⟨fun a ha => ?_, by simp [h₂]⟩
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; trivial
    · exact h₁ a ha
  | _, _, _, .strict _ ht hrest, hcx, hr => by
    obtain ⟨h₁, h₂⟩ := argsR_wf hrest hcx fun b hb => hr b (List.mem_cons_of_mem _ hb)
    refine ⟨fun a ha => ?_, by simp [h₂]⟩
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact tr_wf ht hcx (hr _ List.mem_cons_self)
    · exact h₁ a ha

theorem lazyArgsR_wf : ∀ {cx : Cx} {ms : List Mode} {args : List Src.Term.Arg}
    {args' : List (Term × Mode)}, LazyArgsR I G cx ms args args' → CxOk cx →
    (∀ a ∈ args', RegT T a.1) → ∀ a ∈ args', Term.WF S cx.depth a.1
  | _, _, _, _, .nil, _, _ => fun _ h => by cases h
  | _, _, _, _, .irr _ _ hrest, hcx, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; trivial
    · exact lazyArgsR_wf hrest hcx (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, .name _ _ ht hrest, hcx, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact tr_wf ht hcx (hr _ List.mem_cons_self)
    · exact lazyArgsR_wf hrest hcx (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha

theorem bindR_wf : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' → CxOk cx →
    (∀ v ∈ lets, RegT T v) → BindOk S cx lets refs cx'
  | _, _, _, _, _, .nil, _, _ => ⟨fun _ _ h => (by simp at h), rfl, rfl, fun _ h => (by cases h)⟩
  | _, _, _, _, _, .irr _ hrest, hcx, hr => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := bindR_wf hrest hcx hr
    exact ⟨h₁, h₂, h₃, fun l hl => by
      rcases List.mem_cons.1 hl with e | hl
      · cases e
      · exact h₄ l hl⟩
  | _, _, _, _, _, .name _ hrest, hcx, hr => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := bindR_wf hrest hcx hr
    exact ⟨h₁, h₂, h₃, fun l hl => by
      rcases List.mem_cons.1 hl with e | hl
      · cases e
      · exact h₄ l hl⟩
  | cx, _, _, _, _, .strict _ hv hrest, hcx, hr => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      bindR_wf hrest (hcx.extra 1) fun w hw => hr w (List.mem_cons_of_mem _ hw)
    refine ⟨fun i v hi => ?_, by rw [h₂]; simp [Cx.extra]; omega, h₃, fun l hl => ?_⟩
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact tr_wf hv hcx (hr _ List.mem_cons_self)
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        have := h₁ i v hi
        simp only [Cx.extra] at this
        rwa [Nat.add_assoc, Nat.add_comm 1 i] at this
    · rcases List.mem_cons.1 hl with e | hl
      · cases e
        rw [h₂]
        simp [Cx.extra]
        omega
      · exact h₄ l hl

theorem refR_wf : ∀ {cx : Cx} {ref : Ref} {t : Term}, RefR I G cx ref t → CxOk cx →
    (∀ l, ref = .lvl l → l < cx.depth) → RegT T t → Term.WF S cx.depth t
  | _, _, _, .box, _, _, _ => trivial
  | _, _, _, .lvl, _, hl, _ => wf_lvl (hl _ rfl)
  | _, _, _, .name ht, hcx, _, hr => tr_wf ht hcx hr

theorem satR_wf : ∀ {cx : Cx} {h : Head} {q : Profile} {args : List Src.Term.Arg} {t : Term},
    SatR I G cx h q args t → CxOk cx → args.length = headArity I h → RegT T t →
    Term.WF S cx.depth t
  | _, _, _, _, _, .prim ha, hcx, hlen, hr => by
    cases hr with
    | prim hra =>
      obtain ⟨h₁, h₂⟩ := argsR_wf ha hcx fun a ha' => hra _ (List.mem_map.2 ⟨a, ha', rfl⟩)
      refine ⟨by simp [h₂, hlen, headArity, prim_arity], (wfList_iff).2 fun a ha' => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha'
      exact h₁ b hb
  | _, _, _, _, _, .natZero _ _, _, _, _ => trivial
  | _, _, _, _, _, .natSucc hd _ hs hb hf, hcx, hlen, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    refine hB.wrap ?_
    cases hrb with
    | prim hra =>
      obtain ⟨h₁, h₂⟩ := argsR_wf hf (hB.cxOk hcx) fun a ha' => hra _
        (List.mem_append_left _ (List.mem_map.2 ⟨a, ha', rfl⟩))
      obtain ⟨sf, lv, N, cidx, ty, hS⟩ := E.wf.succPin hs
      rw [hd] at hS
      cases hS
      simp only [headArity, hd] at hlen
      refine ⟨by simp [h₂, hlen, Prim.arity], (wfList_iff).2 fun a ha' => ?_⟩
      rcases List.mem_append.1 ha' with ha' | ha'
      · obtain ⟨b, hb', rfl⟩ := List.mem_map.1 ha'
        exact h₁ b hb'
      · simp only [List.mem_singleton] at ha'
        subst ha'
        trivial
  | _, _, _, _, _, .ctorUnbox _ _ _ hb hF _, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    exact hB.wrap ((fieldsR_wf hF (hB.cxOk hcx) fun f hf => by
      cases hf with
      | head => exact hrb
      | tail _ h => cases h).1 _ List.mem_cons_self)
  | _, _, q, args, _, .ctorBox (c := c) (np := np) (nf := nf) hd _ _ hb hF _, hcx, hlen, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    refine hB.wrap ?_
    cases hrb with
    | con hk hfs =>
      obtain ⟨n, hn⟩ := hk
      obtain ⟨h₁, h₂⟩ := fieldsR_wf hF (hB.cxOk hcx) hfs
      refine ⟨?_, (wfList_iff).2 h₁⟩
      rw [E.ctor_arity hd hn q]
      simp only [headArity, hd] at hlen
      have hdrop : (args.drop np).length = nf := by simp [hlen]
      rw [hdrop, Nat.zero_add] at h₂
      have h0 : I.rank c q 0 = 0 := rfl
      rw [h0, Nat.add_zero] at h₂
      exact congrArg some h₂.symm
  | _, _, _, _, _, .quotMk hb he, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    exact hB.wrap (refR_wf he (hB.cxOk hcx) (fun l hl => hB.refsLt l (mem_of_getD_lvl hl)) hrb)
  | _, _, _, _, _, .quotLift hb hf hx, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    refine hB.wrap ?_
    cases hrb with
    | tick hrb =>
      cases hrb with
      | app hrf hrx =>
        exact ⟨refR_wf hf (hB.cxOk hcx) (fun l hl => hB.refsLt l (mem_of_getD_lvl hl)) hrf,
          refR_wf hx (hB.cxOk hcx) (fun l hl => hB.refsLt l (mem_of_getD_lvl hl)) hrx⟩
  | _, _, _, _, _, .casesEmpty _ _ hb _, hcx, _, hr => by
    obtain ⟨hrl, _⟩ := RegT.wrapLets_inv hr
    exact (bindR_wf hb hcx hrl).wrap trivial
  | _, _, _, _, _, .casesSub _ _ hb _ hm, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    refine hB.wrap ?_
    cases hrb with
    | tick hrb =>
      simp only [Term.WF]
      refine minorR_wf hm (hB.cxOk hcx) (fun l hl => hB.refsLt l (mem_of_getD_lvl hl))
        (fun l hl => ?_) hrb
      obtain ⟨src, _, hs⟩ := List.mem_map.1 hl
      cases src with
      | index i =>
        simp only at hs
        cases hg : ((_ : List Ref).getD _ Ref.box) with
        | lvl l' =>
          rw [hg] at hs
          cases hs
          exact hB.refsLt _ (mem_of_getD_lvl hg)
        | box => rw [hg] at hs; cases hs
        | name _ => rw [hg] at hs; cases hs
      | proof => cases hs
  | _, _, _, _, _, .casesOrd _ _ hb _ hmaj _ halts, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    refine hB.wrap ?_
    cases hrb with
    | tick hrb =>
      cases hrb with
      | case _ hk hbodies _ =>
        obtain ⟨h₁, h₂, _⟩ := altsR_wf halts (hB.cxOk hcx) hB.refsLt fun a ha => by
          cases a with
          | mk k n b => exact ⟨k, n, b, rfl, hk k n b ha, hbodies k n b ha⟩
        exact ⟨wf_lvl (hB.refsLt _ (mem_of_getD_lvl hmaj)), h₁, h₂, trivial⟩
  | _, _, _, _, _, .recr _ hb _ hargs hg, hcx, _, hr => by
    obtain ⟨hrl, hrb⟩ := RegT.wrapLets_inv hr
    have hB := bindR_wf hb hcx hrl
    obtain ⟨_, hra⟩ := RegT.apps_inv hrb
    exact hB.wrap (wf_apps (E.glob _ _ hg) (recArgsR_wf hargs (hB.cxOk hcx) hB.refsLt hra))

theorem fieldsR_wf : ∀ {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} {args : List Src.Term.Arg}
    {fs : List Term}, FieldsR I G cx cx' c q j args fs → CxOk cx' → (∀ f ∈ fs, RegT T f) →
    (∀ f ∈ fs, Term.WF S cx'.depth f) ∧ fs.length + I.rank c q j = I.rank c q (j + args.length)
  | _, _, _, _, _, _, _, .nil, _, _ => ⟨fun _ h => (by cases h), by simp⟩
  | _, _, c, q, j, _, _, .keptIrr (rest := rest) hk _ hrest, hcx, hr => by
    obtain ⟨h₁, h₂⟩ := fieldsR_wf hrest hcx fun f hf => hr f (List.mem_cons_of_mem _ hf)
    refine ⟨fun f hf => ?_, ?_⟩
    · rcases List.mem_cons.1 hf with e | hf
      · rw [e]; trivial
      · exact h₁ f hf
    · rw [rank_succ, hk] at h₂
      simp only [↓reduceIte, List.length_cons] at h₂ ⊢
      rw [show j + (rest.length + 1) = j + 1 + rest.length by omega]
      omega
  | _, _, c, q, j, _, _, .keptRel (rest := rest) hk _ ht hrest, hcx, hr => by
    obtain ⟨h₁, h₂⟩ := fieldsR_wf hrest hcx fun f hf => hr f (List.mem_cons_of_mem _ hf)
    refine ⟨fun f hf => ?_, ?_⟩
    · rcases List.mem_cons.1 hf with e | hf
      · rw [e]; exact tr_wf ht hcx (hr _ List.mem_cons_self)
      · exact h₁ f hf
    · rw [rank_succ, hk] at h₂
      simp only [↓reduceIte, List.length_cons] at h₂ ⊢
      rw [show j + (rest.length + 1) = j + 1 + rest.length by omega]
      omega
  | _, _, c, q, j, _, _, .drop (rest := rest) hk _ hrest, hcx, hr => by
    obtain ⟨h₁, h₂⟩ := fieldsR_wf hrest hcx hr
    refine ⟨h₁, ?_⟩
    rw [rank_succ, hk] at h₂
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.length_cons] at h₂ ⊢
    rw [show j + (rest.length + 1) = j + 1 + rest.length by omega]
    omega

theorem minorR_wf : ∀ {cx : Cx} {ref : Ref} {fields : List (Option Nat)} {t : Term},
    MinorR I G cx ref fields t → CxOk cx → (∀ l, ref = .lvl l → l < cx.depth) →
    (∀ l, some l ∈ fields → l < cx.depth) → RegT T t → Term.WF S cx.depth t
  | _, _, _, _, .box, _, _, hf, _ => wf_apps trivial (fieldArgs_wf hf)
  | _, _, _, _, .lvl, _, hl, hf, _ => wf_apps (wf_lvl (hl _ rfl)) (fieldArgs_wf hf)
  | cx, _, fields, _, .name _ ht, hcx, _, hf, hr => by
    obtain ⟨hrh, _⟩ := RegT.apps_inv hr
    cases hrh with
    | tick hrb =>
      refine wf_apps (tr_wf ht (hcx.under fun l hl => hf l (List.mem_of_mem_take hl)) hrb :)
        fun a ha => fieldArgs_wf hf a (List.mem_of_mem_drop ha)

theorem altsR_wf : ∀ {cx : Cx} {r : CId} {q : Profile} {ind : CId} {refs : List Ref}
    {mbase j : Nat} {rules : List Src.Rule} {alts : List Alt},
    AltsR I G cx r q ind refs mbase j rules alts → CxOk cx →
    (∀ l, Ref.lvl l ∈ refs → l < cx.depth) → (∀ a ∈ alts, AltReg T a) →
    Term.WFAlts S cx.depth alts ∧ (Term.altKeys alts).Nodup ∧ KeysFrom I ind j (Term.altKeys alts)
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _ =>
    ⟨trivial, List.nodup_nil, fun _ h => by cases h⟩
  | cx, _, _, ind, refs, mbase, j, _, _, .cons hra hm hrest, hcx, hrefs, hr => by
    obtain ⟨k, n, b, e, hk, hrb⟩ := hr _ List.mem_cons_self
    cases e
    obtain ⟨ha, hfl, c, sf, lv, np, nf, ty, rfl, hd⟩ := ruleAlt_wf E hra hk
    obtain ⟨h₁, h₂, h₃⟩ := altsR_wf hrest hcx hrefs fun a ha => hr a (List.mem_cons_of_mem _ ha)
    refine ⟨⟨ha, minorR_wf hm (hcx.extra _)
        (fun l hl => Nat.lt_of_lt_of_le (hrefs l (hl ▸ mem_of_getD_lvl hl))
          (Nat.le_add_right _ _))
        (fun l hl => hfl l hl) hrb, h₁⟩, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hmem => ?_, h₂⟩
      obtain ⟨c', sf', lv', cidx', np', nf', ty', hk', hd', hle⟩ := h₃ _ hmem
      have := ctorKey_cidx E.wf hd hd' hk'
      omega
    · intro k' hk'
      rcases List.mem_cons.1 hk' with e | hk'
      · rw [e]; exact ⟨c, sf, lv, j, np, nf, ty, rfl, hd, Nat.le_refl _⟩
      · obtain ⟨c', sf', lv', cidx', np', nf', ty', e, hd', hle⟩ := h₃ k' hk'
        exact ⟨c', sf', lv', cidx', np', nf', ty', e, hd', by omega⟩

theorem recArgsR_wf : ∀ {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} {refs : List Ref}
    {ts : List (Term × Mode)}, RecArgsR I G cx r q np nmot nmin i refs ts → CxOk cx →
    (∀ l, Ref.lvl l ∈ refs → l < cx.depth) → (∀ a ∈ ts, RegT T a.1) →
    ∀ a ∈ ts, Term.WF S cx.depth a.1
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _ => fun _ h => by cases h
  | _, _, _, _, _, _, _, _, _, .other _ href hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact refR_wf href hcx (fun l e => hrefs l (e ▸ List.mem_cons_self))
        (hr _ List.mem_cons_self)
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, _, _, _, _, _, .minorBox _ _ hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; trivial
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, _, _, _, _, _, .minorLvl _ _ _ hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact wf_lvl (hrefs _ List.mem_cons_self)
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, _, _, _, _, _, .minorName _ _ _ ht hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact tr_wf ht hcx (hr _ List.mem_cons_self)
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, _, _, _, _, _, .minorFwd _ _ _ hv _ hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact wf_lvl (hcx _ _ hv)
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, _, _, _, _, _, _, .minorTele _ _ _ _ _ ht hs hrest, hcx, hrefs, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact wf_setModes hs (tr_wf ht hcx (RegT.setModes_inv hs (hr _ List.mem_cons_self)))
    · exact recArgsR_wf hrest hcx (fun l hl => hrefs l (List.mem_cons_of_mem _ hl))
        (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha

end

end Mutual

end Compilatrix.Lam.Erase.Proof
