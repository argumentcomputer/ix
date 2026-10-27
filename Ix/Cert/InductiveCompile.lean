import Ix.Cert.BlockEmission
import Ix.Cert.InductiveUnits
import Ix.CompileCert.Canon.Ctx

/-! # Inductive and recursor blocks compiled in Lean's order, read in a closure

`BlockEmission.mutualBlock_correct` reads a block compiled one member per class back as its
members' sources, in the compile environment's reading context. This module splits that
reading member by member and moves it to the closure's context (`RecordTransfer.read_le`):

* `inductiveBlock_reads`: an inductive block in Lean's order is a record of inductives keeping
  the members' safety and headers (`IndFacts`), whose member reader in the closure's context
  reads every type and constructor as a term related to its Lean type. The block's self
  references are its members' keys in the closure's context; no constructor of the block
  occurs in its members' types, so none needs a self reference (`scopes_of_noCtor`).
* `recursorBlock_reads`: a recursor family in family order is a lone recursor's record or a
  block of several (`RecPayload`), whose recursor reader reads every recursor's type and
  rules' right-hand sides as terms related to their Lean ones.
* `compiled_inductive_unit_reads`: with the closure's keys, block shape and recursor index,
  these are the reader's facts of `InductiveUnits.inductive_unit_reads` (`typeFacts_of`,
  `recFacts_of`), so an inductive group compiled in Lean's order reads as quotient Source's
  unit renamed. -/

namespace Ix.Cert.InductiveCompile

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam ConstRef)
open Ix.Kernel.Reader
open Ix.LeanIngress (FiberMap Numbering)
open Ix.Cert.RecordReadings (sourceNames)
open Ix.Cert.BlockEmission (PayloadOf memberSources memberLps mutContext blockInfo)
open Ix.Cert.InductiveUnits (srcKey blockReader)

/-! ## Lists -/

theorem forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, l₁.length = m₁.length → List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) →
      List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | _ :: _, _, _ :: _, _, hl, .cons hab rest =>
    let ⟨h₁, h₂⟩ := forall₂_append_split (by simpa using hl) rest
    ⟨.cons hab h₁, h₂⟩
  | [], _, _ :: _, _, hl, _ => absurd hl (by simp)
  | _ :: _, _, [], _, hl, _ => absurd hl (by simp)

theorem forall₂_and {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ S l m → List.Forall₂ (fun a b => R a b ∧ S a b) l m
  | [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, .cons h₁ r₁, .cons h₂ r₂ => .cons ⟨h₁, h₂⟩ (forall₂_and r₁ r₂)

theorem forall₂_trans {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} {T : α → γ → Prop}
    (h : ∀ a b c, R a b → S c b → T a c) :
    ∀ {l : List α} {m : List β} {n : List γ}, List.Forall₂ R l m → List.Forall₂ S n m → List.Forall₂ T l n
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ r₁, .cons h₂ r₂ => .cons (h _ _ _ h₁ h₂) (forall₂_trans h r₁ r₂)

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h₁ r₁ => .cons (h _ _ h₁) (forall₂_imp h r₁)

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → l.length = m.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest => by simp [forall₂_length rest]

/-- **A block's members' roots read, member by member.** -/
theorem members_read {reader : MemberReader .anon} {rel : Ix.Expr → CExpr .anon → Prop} :
    ∀ {ms : List MutConst} {qs : List Ixon.MutConst},
      List.Forall₂ (fun m q => (memberSources m).length = (mutConstRootExprs q).length) ms qs →
      SharingRoots.RootsRead reader rel (ms.flatMap memberSources) (qs.flatMap mutConstRootExprs) →
      List.Forall₂ (fun m q => SharingRoots.RootsRead reader rel (memberSources m) (mutConstRootExprs q)) ms qs
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons hl rest, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := forall₂_append_split hl h
    exact .cons h₁ (members_read rest h₂)

/-! ## The record's inductives -/

/-- **What a compiled inductive keeps of its source**: its safety, its header and its
constructors' headers and safety. -/
def IndFacts (i : Ix.Ind) (t : Ixon.Inductive) : Prop :=
  t.isUnsafe = i.isUnsafe ∧ ProjectionLayout.IndHeader i t ∧
    List.Forall₂ (fun c ct => ProjectionLayout.CtorHeader c ct ∧ ct.isUnsafe = c.isUnsafe) i.ctors.toList
      t.ctors.toList

theorem indFacts_payload {i : Ix.Ind} {p : Ixon.MutConst} (h : PayloadOf (.indc i) p) :
    ∃ t, p = .indc t ∧ IndFacts i t := by
  obtain ⟨t, rfl, ht, hctors, header, ctorHeaders⟩ := h
  refine ⟨t, rfl, by rw [ht]; rfl, header, forall₂_and ctorHeaders ?_⟩
  exact forall₂_imp (fun c ct hct => by rw [hct]; rfl) hctors

theorem indFacts_erase {i : Ix.Ind} {t t' : Ixon.Inductive} (h : IndFacts i t)
    (e : SharingRoots.eraseMut (.indc t') = SharingRoots.eraseMut (.indc t)) : IndFacts i t' := by
  simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Ixon.MutConst.indc.injEq,
    Ixon.Inductive.mk.injEq] at e
  obtain ⟨hu, hl, hp, hi, -, hc⟩ := e
  obtain ⟨unsafeEq, ⟨lvls, params, indices, size⟩, ctors⟩ := h
  have hc' : t'.ctors.toList.map (fun ct => { ct with typ := Ixon.Expr.sort 0 }) =
      t.ctors.toList.map (fun ct => { ct with typ := Ixon.Expr.sort 0 }) := by
    simpa using congrArg Array.toList hc
  have hsize : t'.ctors.size = t.ctors.size := by simpa using congrArg List.length hc'
  refine ⟨hu.trans unsafeEq, ⟨hl ▸ lvls, hp ▸ params, hi ▸ indices, hsize ▸ size⟩, ?_⟩
  clear hc hsize size
  generalize t'.ctors.toList = ts' at hc'
  generalize t.ctors.toList = ts at hc' ctors
  generalize i.ctors.toList = cs at ctors
  induction ctors generalizing ts' with
  | nil => cases ts' with
    | nil => exact .nil
    | cons _ _ => simp at hc'
  | cons hh _ ih =>
    cases ts' with
    | nil => simp at hc'
    | cons ct' rest =>
      simp only [List.map_cons, List.cons.injEq, Ixon.Constructor.mk.injEq] at hc'
      obtain ⟨⟨u, l, ci, p, fl, -⟩, rest'⟩ := hc'
      obtain ⟨⟨hl', hci, hp', hf⟩, hu'⟩ := hh
      exact .cons ⟨⟨l ▸ hl', ci ▸ hci, p ▸ hp', fl ▸ hf⟩, u ▸ hu'⟩ (ih _ rest')

theorem indcs_of_erase : ∀ (ms : List Ixon.MutConst) (ts : List Ixon.Inductive),
    ms.map SharingRoots.eraseMut = ts.map (fun t => SharingRoots.eraseMut (.indc t)) →
    ∃ ts' : List Ixon.Inductive, ms = ts'.map .indc ∧
      List.Forall₂ (fun t' t => SharingRoots.eraseMut (.indc t') = SharingRoots.eraseMut (.indc t)) ts' ts
  | [], [], _ => ⟨[], rfl, .nil⟩
  | m :: ms, t :: ts, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨ts', rfl, hr⟩ := indcs_of_erase ms ts h₂
    cases m with
    | indc t' => exact ⟨t' :: ts', rfl, .cons h₁ hr⟩
    | defn d => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
    | recr r => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem blockInfo_indcs (ts : List Ixon.Inductive) : blockInfo (ts.map .indc) = .muts (ts.map .indc).toArray := by
  rcases ts with _ | ⟨t, _ | ⟨t₂, rest⟩⟩ <;> rfl

/-- **A block of inductives, as its record**: the record's inductives keep the payloads'
skeletons. -/
theorem erase_indcs {info : Ixon.ConstantInfo} {ts : List Ixon.Inductive}
    (same : SharingRoots.erase info = SharingRoots.erase (blockInfo (ts.map .indc))) :
    ∃ ts' : List Ixon.Inductive, info = .muts (ts'.map .indc).toArray ∧
      List.Forall₂ (fun t' t => SharingRoots.eraseMut (.indc t') = SharingRoots.eraseMut (.indc t)) ts' ts := by
  rw [blockInfo_indcs] at same
  cases info with
  | muts ms =>
    simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ixon.ConstantInfo.muts.injEq] at same
    have hl : ms.toList.map SharingRoots.eraseMut = ts.map (fun t => SharingRoots.eraseMut (.indc t)) := by
      have := congrArg Array.toList same
      simp only [Array.toList_map, List.map_map, Function.comp_def] at this
      exact this
    obtain ⟨ts', hms, hr⟩ := indcs_of_erase ms.toList ts hl
    exact ⟨ts', by rw [← hms], hr⟩
  | _ => simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same

theorem forall₂_map_map {α β γ δ : Type} {R : γ → δ → Prop} {g : α → γ} {k : β → δ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R (l.map g) (m.map k) ↔ List.Forall₂ (fun a b => R (g a) (k b)) l m
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | _ :: _, [] => ⟨(fun hh => by cases hh), (fun hh => by cases hh)⟩
  | [], _ :: _ => ⟨(fun hh => by cases hh), (fun hh => by cases hh)⟩
  | _ :: _, _ :: _ => by
    simp only [List.map_cons, List.forall₂_cons]
    exact and_congr Iff.rfl forall₂_map_map

theorem flatten_singletons {α : Type} : ∀ l : List α, (l.map ([·])).flatten = l
  | [] => rfl
  | a :: l => by simp [flatten_singletons l]

/-! ## The inductive block -/

/-- The self references of a block of `n` members in the closure's context. -/
def selfOf (cx : Ctx .anon) (owner : Address) (n : Nat) : Nat → Option (ReadM (CName .anon)) :=
  fun k => if k < n then some (cx.memberKey (.member owner k)) else none

theorem blockSelf_eq (cx : Ctx .anon) (owner : Address) (ts : List Ixon.Inductive) :
    InductiveReading.blockSelf cx owner (ts.map .indc).toArray = selfOf cx owner ts.length := by
  funext k
  simp [InductiveReading.blockSelf, selfOf]

variable (ρ : FiberMap) (f : Mode.Id .source → Mode.Id .anon)

/-- **The block's self references**: a member's name is its key in the closure's context; no
constructor of the block occurs. -/
theorem scopes_of_noCtor (context : CompileEnv × BlockEnv) (cx : Ctx .anon) (owner : Address) (inds : List Ix.Ind)
    (keys : ∀ k (h : k < inds.length), cx.memberKey (.member owner k) = .ok (srcKey ρ f inds[k].name))
    (distinct : Canon.KeysDistinct (inds.map MutConst.indc))
    (noCtor : ∀ i ∈ inds, ∀ e ∈ memberSources (.indc i),
      ConstsSatisfy (fun n => ∀ i' ∈ inds, ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) e) :
    ∀ m ∈ inds.map MutConst.indc, ∀ e ∈ memberSources m,
      ConstsSatisfy (SelfName (mutContext ((inds.map MutConst.indc).map ([·])) context).2
        (selfOf cx owner inds.length) (sourceNames ρ f)) e := by
  intro m hm e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  refine constsSatisfy_mono (fun n hn index found => ?_) e (noCtor i hi e he)
  have hk : Canon.KeysDistinct ((inds.map MutConst.indc).map ([·])).flatten := by
    rw [flatten_singletons]
    exact distinct
  simp only [mutContext] at found
  rw [Std.TreeMap.get?_eq_getElem?] at found
  obtain ⟨j, C, m', hC, hm', hcase⟩ := Canon.ctx_val hk found
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨m0, ⟨x, hx, rfl⟩, rfl⟩ := hC
  rw [List.mem_singleton] at hm'
  subst hm'
  have hj : j < inds.length := (List.getElem?_eq_some_iff.mp hx).1
  have hxj : inds[j] = x := (List.getElem?_eq_some_iff.mp hx).2
  rcases hcase with ⟨hname, rfl⟩ | ⟨k, c, hc, hcn, -⟩
  · refine ⟨srcKey ρ f inds[index].name, by simp [selfOf, hj, keys index hj], ?_⟩
    show srcKey ρ f inds[index].name = (Ix.LeanIngress.Key.subst ρ (Ix.LeanIngress.ingressKey n)).map f
    rw [hxj, ← hname]
    rfl
  · exfalso
    have hcm : c ∈ x.ctors.toList := by
      have hc' : x.ctors[k]? = some c := hc
      exact List.mem_of_getElem? (show x.ctors.toList[k]? = some c by simpa using hc')
    exact hn x (List.mem_of_getElem? hx) c hcm hcn.symm

/-- The relation a block's terms are read in: related to their Lean terms, at quotient
Source's names renamed and the block's level parameters. -/
abbrev blockRel (lps : Array Ix.Name) : Ix.Expr → CExpr .anon → Prop :=
  Related (sourceNames ρ f) (LevelMeaning lps.toList (Numbering.mk lps false).pos id)

/-- **An inductive block compiled in Lean's order, read in a closure**: the record is a block
of inductives keeping their sources' headers, and in the closure's context its member reader
reads every type and every constructor's type as a term related to its Lean type, given the
compile run, the members' keys in the closure's context, distinct names, no constructor of
the block in its members' types, and the closure's context reading the record's references
as the compile environment's does. -/
theorem inductiveBlock_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a) {bindings : Bindings}
    (external : BindingsCorrect context.1 bindings cx₁ (sourceNames ρ f)) (inds : List Ix.Ind)
    (lps : Array Ix.Name) (hlps : ∀ i ∈ inds, i.levelParams = lps) (owner : Address)
    (keys : ∀ k (h : k < inds.length), cx.memberKey (.member owner k) = .ok (srcKey ρ f inds[k].name))
    (distinct : Canon.KeysDistinct (inds.map MutConst.indc))
    (noCtor : ∀ i ∈ inds, ∀ e ∈ memberSources (.indc i),
      ConstsSatisfy (fun n => ∀ i' ∈ inds, ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) e)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock ((inds.map MutConst.indc).map ([·]))) context before = (.ok output, after))
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx) :
    ∃ targets : List Ixon.Inductive, output.block.info = .muts (targets.map Ixon.MutConst.indc).toArray ∧
      List.Forall₂ (fun i t => IndFacts i t ∧
        (∃ type, (blockReader cx owner output.block targets).read t.typ = .ok type ∧
          blockRel ρ f lps i.type type) ∧
        List.Forall₂ (fun c (ct : Ixon.Constructor) =>
          ∃ type, (blockReader cx owner output.block targets).read ct.typ = .ok type ∧
            blockRel ρ f lps c.cnst.type type) i.ctors.toList t.ctors.toList) inds targets := by
  obtain ⟨ps, payloads, erased, roots⟩ := BlockEmission.mutualBlock_correct cx₁ id (selfOf cx owner inds.length)
    (sourceNames ρ f) (Numbering.mk lps false).pos bindings context free aligned external (inds.map MutConst.indc)
    lps.toList (by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      simp [memberLps, hlps i hi])
    (scopes_of_noCtor ρ f context cx owner inds keys distinct noCtor) clean ran
  -- the payloads are inductives keeping their sources' headers
  have hps : ∀ {is : List Ix.Ind} {qs : List Ixon.MutConst}, List.Forall₂ PayloadOf (is.map MutConst.indc) qs →
      ∃ ts : List Ixon.Inductive, qs = ts.map Ixon.MutConst.indc ∧ List.Forall₂ IndFacts is ts := by
    intro is
    induction is with
    | nil => intro qs h; cases h; exact ⟨[], rfl, .nil⟩
    | cons i is ih =>
      intro qs h
      cases h with
      | cons hq rest =>
        obtain ⟨t, rfl, ht⟩ := indFacts_payload hq
        obtain ⟨ts, rfl, hts⟩ := ih rest
        exact ⟨t :: ts, rfl, .cons ht hts⟩
  obtain ⟨ts, rfl, hts⟩ := hps payloads
  obtain ⟨ts', hinfo, hsame⟩ := erase_indcs erased
  have facts : List.Forall₂ IndFacts inds ts' :=
    forall₂_trans (R := IndFacts) (T := IndFacts) (fun _ _ _ h e => indFacts_erase h e) hts hsame
  rw [hinfo, show (constantInfoRootExprs (.muts (ts'.map Ixon.MutConst.indc).toArray)).toList =
    (ts'.map Ixon.MutConst.indc).flatMap mutConstRootExprs by simp [constantInfoRootExprs]] at roots
  have lengths : List.Forall₂ (fun m q => (memberSources m).length = (mutConstRootExprs q).length)
      (inds.map MutConst.indc) (ts'.map Ixon.MutConst.indc) := by
    refine forall₂_map_map.mpr (forall₂_imp (fun i t h => ?_) facts)
    simp [memberSources, mutConstRootExprs, forall₂_length h.2.2]
  have members := forall₂_map_map.mp (members_read lengths roots)
  have reader : blockReader cx owner output.block ts' = MemberReader.mk' cx output.block id (selfOf cx owner inds.length) := by
    unfold blockReader
    rw [blockSelf_eq, ← forall₂_length facts]
  refine ⟨ts', hinfo, forall₂_imp (fun i t h => ?_) (forall₂_and facts members)⟩
  obtain ⟨hf, hr⟩ := h
  simp only [memberSources, mutConstRootExprs] at hr
  obtain ⟨⟨type, rel, read⟩, rest⟩ := InductiveReading.rootsRead_cons hr
  rw [reader]
  refine ⟨hf, ⟨type, RecordTransfer.read_le refs id _ _ read, rel⟩, ?_⟩
  refine forall₂_imp (fun c ct hc => ?_) (forall₂_map_map.mp rest)
  obtain ⟨type, rel, read⟩ := hc
  exact ⟨type, RecordTransfer.read_le refs id _ _ read, rel⟩

/--
info: 'Ix.Cert.InductiveCompile.inductiveBlock_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductiveBlock_reads

/-! ## Recursor families -/

/-- **What a compiled recursor keeps of its source**: its safety, its `k`, its header and its
rules' field counts. -/
def RecPayload (r : Ix.RecursorVal) (t : Ixon.Recursor) : Prop :=
  t.isUnsafe = r.isUnsafe ∧ t.k = r.k ∧ BlockEmission.RecHeader r t ∧
    t.rules.toList.map (·.fields) = r.rules.toList.map (fun rule => rule.nfields.toUInt64)

theorem recPayload_of {r : Ix.RecursorVal} {p : Ixon.MutConst} (h : PayloadOf (.recr r) p) :
    ∃ t, p = .recr t ∧ RecPayload r t := by
  obtain ⟨t, rfl, ht, fields, header⟩ := h
  exact ⟨t, rfl, by rw [ht]; rfl, by rw [ht]; rfl, header, fields⟩

theorem recPayload_erase {r : Ix.RecursorVal} {t t' : Ixon.Recursor} (h : RecPayload r t)
    (e : SharingRoots.eraseMut (.recr t') = SharingRoots.eraseMut (.recr t)) : RecPayload r t' := by
  simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Ixon.MutConst.recr.injEq,
    Ixon.Recursor.mk.injEq] at e
  obtain ⟨hk, hu, hl, hp, hi, hm, hn, -, hr⟩ := e
  obtain ⟨unsafeEq, kEq, ⟨lvls, params, indices, motives, minors, bounded⟩, fields⟩ := h
  have hr' : t'.rules.toList.map (fun rl => { rl with rhs := Ixon.Expr.sort 0 }) =
      t.rules.toList.map (fun rl => { rl with rhs := Ixon.Expr.sort 0 }) := by
    simpa using congrArg Array.toList hr
  have hf : t'.rules.toList.map (·.fields) = t.rules.toList.map (·.fields) := by
    have := congrArg (List.map (·.fields)) hr'
    simpa [Function.comp_def] using this
  exact ⟨hu.trans unsafeEq, hk.trans kEq, ⟨hl ▸ lvls, hp ▸ params, hi ▸ indices, hm ▸ motives, hn ▸ minors,
    bounded⟩, hf.trans fields⟩

theorem recrs_of_erase : ∀ (ms : List Ixon.MutConst) (ts : List Ixon.Recursor),
    ms.map SharingRoots.eraseMut = ts.map (fun t => SharingRoots.eraseMut (.recr t)) →
    ∃ ts' : List Ixon.Recursor, ms = ts'.map .recr ∧
      List.Forall₂ (fun t' t => SharingRoots.eraseMut (.recr t') = SharingRoots.eraseMut (.recr t)) ts' ts
  | [], [], _ => ⟨[], rfl, .nil⟩
  | m :: ms, t :: ts, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨ts', rfl, hr⟩ := recrs_of_erase ms ts h₂
    cases m with
    | recr t' => exact ⟨t' :: ts', rfl, .cons h₁ hr⟩
    | defn d => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
    | indc i => simp [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots] at h₁
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **A recursor family, as its record**: a lone recursor's or several's, keeping the
payloads' skeletons. -/
theorem erase_recrs {info : Ixon.ConstantInfo} {ts : List Ixon.Recursor}
    (same : SharingRoots.erase info = SharingRoots.erase (blockInfo (ts.map .recr))) :
    ∃ ts' : List Ixon.Recursor, info = blockInfo (ts'.map .recr) ∧
      List.Forall₂ (fun t' t => SharingRoots.eraseMut (.recr t') = SharingRoots.eraseMut (.recr t)) ts' ts := by
  rcases ts with _ | ⟨t, _ | ⟨t₂, rest⟩⟩
  · have hb : blockInfo (([] : List Ixon.Recursor).map Ixon.MutConst.recr) = .muts #[] := rfl
    rw [hb] at same
    cases info with
    | muts ms =>
      simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ixon.ConstantInfo.muts.injEq] at same
      have : ms = #[] := by simpa using congrArg Array.size same
      exact ⟨[], by rw [this]; rfl, .nil⟩
    | _ => simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same
  · have hb : blockInfo [Ixon.MutConst.recr t] = .recr t := rfl
    rw [List.map_singleton, hb] at same
    cases info with
    | recr t' =>
      refine ⟨[t'], rfl, .cons ?_ .nil⟩
      simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ixon.ConstantInfo.recr.injEq] at same
      simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, same]
    | _ => simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same
  · have hb : blockInfo ((t :: t₂ :: rest).map Ixon.MutConst.recr) =
        .muts ((t :: t₂ :: rest).map Ixon.MutConst.recr).toArray := rfl
    rw [hb] at same
    cases info with
    | muts ms =>
      simp only [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, Ixon.ConstantInfo.muts.injEq] at same
      have hl : ms.toList.map SharingRoots.eraseMut =
          (t :: t₂ :: rest).map (fun t => SharingRoots.eraseMut (.recr t)) := by
        have := congrArg Array.toList same
        simp only [Array.toList_map, List.map_map, Function.comp_def] at this
        exact this
      obtain ⟨ts', hms, hr⟩ := recrs_of_erase ms.toList _ hl
      have hlen : ts'.length = rest.length + 2 := by simpa using forall₂_length hr
      obtain ⟨u, u₂, rest', rfl⟩ : ∃ u u₂ rest', ts' = u :: u₂ :: rest' := by
        rcases ts' with _ | ⟨u, _ | ⟨u₂, rest'⟩⟩ <;> simp at hlen
        exact ⟨u, u₂, rest', rfl⟩
      refine ⟨u :: u₂ :: rest', ?_, hr⟩
      rw [show blockInfo ((u :: u₂ :: rest').map Ixon.MutConst.recr) =
        .muts ((u :: u₂ :: rest').map Ixon.MutConst.recr).toArray from rfl, ← hms]
    | _ => simp [SharingRoots.erase, Ix.Sharing.Exact.mapRoots] at same

/-- The self references of a recursor family of `n` members in the closure's context, as the
reader reads them (`RecursorReads.recSelf`): a lone recursor is its key, a member of a family of
several its member key. -/
def recSelfOf (cx : Ctx .anon) (owner : Address) (key : CName .anon) (n : Nat) : Nat → Option (ReadM (CName .anon)) :=
  if n = 1 then fun i => if (i == 0) = true then some (pure key) else none
  else fun i => if i < n then some (cx.memberKey (.member owner i)) else none

theorem recSelf_eq (cx : Ctx .anon) (owner : Address) (key : CName .anon) {rc : Ixon.Constant}
    {ts : List Ixon.Recursor} (hne : ts ≠ []) (hinfo : rc.info = blockInfo (ts.map .recr)) :
    RecursorReads.recSelf cx rc owner key = recSelfOf cx owner key ts.length := by
  funext i
  rcases ts with _ | ⟨t, _ | ⟨t₂, rest⟩⟩
  · exact absurd rfl hne
  · have hb : blockInfo [Ixon.MutConst.recr t] = .recr t := rfl
    rw [List.map_singleton, hb] at hinfo
    simp [RecursorReads.recSelf, recSelfOf, hinfo]
  · have hb : blockInfo ((t :: t₂ :: rest).map Ixon.MutConst.recr) =
        .muts ((t :: t₂ :: rest).map Ixon.MutConst.recr).toArray := rfl
    rw [hb] at hinfo
    simp [RecursorReads.recSelf, recSelfOf, hinfo]

/-- **A recursor family's self references**: a member's name is read as its key. -/
theorem rec_scopes (context : CompileEnv × BlockEnv) (cx : Ctx .anon) (owner : Address) (key : CName .anon)
    (recs : List Ix.RecursorVal)
    (selfKeys : ∀ k (h : k < recs.length),
      recSelfOf cx owner key recs.length k = some (.ok (srcKey ρ f recs[k].cnst.name)))
    (distinct : Canon.KeysDistinct (recs.map MutConst.recr)) :
    ∀ m ∈ recs.map MutConst.recr, ∀ e ∈ memberSources m,
      ConstsSatisfy (SelfName (mutContext ((recs.map MutConst.recr).map ([·])) context).2
        (recSelfOf cx owner key recs.length) (sourceNames ρ f)) e := by
  intro m _ e _
  refine constsSatisfy_of_forall (fun n index found => ?_) e
  have hk : Canon.KeysDistinct ((recs.map MutConst.recr).map ([·])).flatten := by
    rw [flatten_singletons]
    exact distinct
  simp only [mutContext] at found
  rw [Std.TreeMap.get?_eq_getElem?] at found
  obtain ⟨j, C, m', hC, hm', hcase⟩ := Canon.ctx_val hk found
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨m0, ⟨x, hx, rfl⟩, rfl⟩ := hC
  rw [List.mem_singleton] at hm'
  subst hm'
  have hj : j < recs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hxj : recs[j] = x := (List.getElem?_eq_some_iff.mp hx).2
  rcases hcase with ⟨hname, rfl⟩ | ⟨k, c, hc, -, -⟩
  · refine ⟨srcKey ρ f recs[index].cnst.name, selfKeys index hj, ?_⟩
    show srcKey ρ f recs[index].cnst.name = (Ix.LeanIngress.Key.subst ρ (Ix.LeanIngress.ingressKey n)).map f
    rw [hxj, ← hname]
    rfl
  · exact absurd hc (by simp [MutConst.ctors])

/-- The relation a recursor family's terms are read in: related to their Lean terms, at
quotient Source's names renamed and the family's numbering of its level parameters. -/
abbrev recRel (lps : Array Ix.Name) (large : Bool) : Ix.Expr → CExpr .anon → Prop :=
  Related (sourceNames ρ f) (LevelMeaning lps.toList (Numbering.mk lps large).pos
    (recParam (Numbering.mk lps large).params))

/-- **A recursor family compiled in family order, read in a closure**: the record is the
family's, keeping its recursors' safety, `k`, headers and rules' field counts, and in the
closure's context the reader reads every recursor's type and rules' right-hand sides as
terms related to their Lean ones, given the compile run, the members' keys in the closure's
context, distinct names, and the closure's context reading the record's references as the
compile environment's does. -/
theorem recursorBlock_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    {cx₁ cx : Ctx .anon} (aligned : ∀ a, cx₁.blob a = context.1.blobs.get? a) {bindings : Bindings}
    (external : BindingsCorrect context.1 bindings cx₁ (sourceNames ρ f)) (recs : List Ix.RecursorVal)
    (hne : recs ≠ []) (lps : Array Ix.Name) (hlps : ∀ r ∈ recs, r.cnst.levelParams = lps) (large : Bool)
    (owner : Address) (key : CName .anon)
    (selfKeys : ∀ k (h : k < recs.length),
      recSelfOf cx owner key recs.length k = some (.ok (srcKey ρ f recs[k].cnst.name)))
    (distinct : Canon.KeysDistinct (recs.map MutConst.recr))
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock ((recs.map MutConst.recr).map ([·]))) context before = (.ok output, after))
    (refs : RecordTransfer.RefsLe output.block (ExpressionRead.withBlockBlobs cx₁ after) cx) :
    ∃ rIs : List Ixon.Recursor, output.block.info = blockInfo (rIs.map Ixon.MutConst.recr) ∧
      List.Forall₂ (fun r rI => RecPayload r rI ∧
        (∃ type, (RecursorReads.recReader cx output.block owner key (Numbering.mk lps large).params).read rI.typ =
            .ok type ∧ recRel ρ f lps large r.cnst.type type) ∧
        List.Forall₂ (fun (rule : Ix.RecursorRule) (rr : Ixon.RecursorRule) =>
          ∃ rhs, (RecursorReads.recReader cx output.block owner key (Numbering.mk lps large).params).read rr.rhs =
            .ok rhs ∧ recRel ρ f lps large rule.rhs rhs) r.rules.toList rI.rules.toList) recs rIs := by
  obtain ⟨ps, payloads, erased, roots⟩ := BlockEmission.mutualBlock_correct cx₁
    (recParam (Numbering.mk lps large).params) (recSelfOf cx owner key recs.length)
    (sourceNames ρ f) (Numbering.mk lps large).pos bindings context free aligned external (recs.map MutConst.recr)
    lps.toList (by
      intro m hm
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
      simp [memberLps, hlps r hr])
    (rec_scopes ρ f context cx owner key recs selfKeys distinct) clean ran
  have hps : ∀ {rs : List Ix.RecursorVal} {qs : List Ixon.MutConst},
      List.Forall₂ PayloadOf (rs.map MutConst.recr) qs →
      ∃ ts : List Ixon.Recursor, qs = ts.map Ixon.MutConst.recr ∧ List.Forall₂ RecPayload rs ts := by
    intro rs
    induction rs with
    | nil => intro qs h; cases h; exact ⟨[], rfl, .nil⟩
    | cons r rs ih =>
      intro qs h
      cases h with
      | cons hq rest =>
        obtain ⟨t, rfl, ht⟩ := recPayload_of hq
        obtain ⟨ts, rfl, hts⟩ := ih rest
        exact ⟨t :: ts, rfl, .cons ht hts⟩
  obtain ⟨ts, rfl, hts⟩ := hps payloads
  obtain ⟨ts', hinfo, hsame⟩ := erase_recrs erased
  have facts : List.Forall₂ RecPayload recs ts' :=
    forall₂_trans (R := RecPayload) (T := RecPayload) (fun _ _ _ h e => recPayload_erase h e) hts hsame
  rw [hinfo, BlockEmission.blockInfo_roots] at roots
  have lengths : List.Forall₂ (fun m q => (memberSources m).length = (mutConstRootExprs q).length)
      (recs.map MutConst.recr) (ts'.map Ixon.MutConst.recr) := by
    refine forall₂_map_map.mpr (forall₂_imp (fun r t h => ?_) facts)
    have := congrArg List.length h.2.2.2
    simp only [List.length_map, Array.length_toList] at this
    simp [memberSources, mutConstRootExprs, this]
  have members := forall₂_map_map.mp (members_read lengths roots)
  have hlen : ts'.length = recs.length := (forall₂_length facts).symm
  have hne' : ts' ≠ [] := by
    intro h
    rw [h] at hlen
    exact hne (List.length_eq_zero_iff.mp hlen.symm)
  have reader : RecursorReads.recReader cx output.block owner key (Numbering.mk lps large).params =
      MemberReader.mk' cx output.block (recParam (Numbering.mk lps large).params)
        (recSelfOf cx owner key recs.length) := by
    unfold RecursorReads.recReader
    rw [recSelf_eq cx owner key hne' hinfo, hlen]
  refine ⟨ts', hinfo, forall₂_imp (fun r t h => ?_) (forall₂_and facts members)⟩
  obtain ⟨hf, hr⟩ := h
  simp only [memberSources, mutConstRootExprs] at hr
  obtain ⟨⟨type, rel, read⟩, rest⟩ := InductiveReading.rootsRead_cons hr
  rw [reader]
  refine ⟨hf, ⟨type, RecordTransfer.read_le refs _ _ _ read, rel⟩, ?_⟩
  refine forall₂_imp (fun rule rr hc => ?_) (forall₂_map_map.mp rest)
  obtain ⟨rhs, rel, read⟩ := hc
  exact ⟨rhs, RecordTransfer.read_le refs _ _ _ read, rel⟩

/--
info: 'Ix.Cert.InductiveCompile.recursorBlock_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recursorBlock_reads

/-! ## The closure's lookups of the records -/

theorem inductiveAt_block {cx : Ctx .anon} {owner : Address} {c : Ixon.Constant} {targets : List Ixon.Inductive}
    (hstore : cx.store owner = some c) (hinfo : c.info = .muts (targets.map Ixon.MutConst.indc).toArray)
    {mi : Nat} (hmi : mi < targets.length) : inductiveAt cx.store (.member owner mi) = some targets[mi] := by
  simp [inductiveAt, hstore, hinfo, hmi]

theorem find_swap {α : Type} : ∀ (l : List α) (k j : Nat) (h : j < l.length),
    ((l.zipIdx k).map fun p => (p.2, p.1)).find? (·.1 == k + j) = some (k + j, l[j])
  | [], _, _, h => absurd h (by simp)
  | a :: l, k, 0, _ => by simp
  | a :: l, k, j + 1, h => by
    have hne : (k == k + (j + 1)) = false := by simp
    rw [List.zipIdx_cons, List.map_cons, List.find?_cons]
    simp only [hne]
    have := find_swap l (k + 1) j (by simpa using h)
    rw [show k + 1 + j = k + (j + 1) by omega] at this
    simpa using this

theorem recursorMembers_find {c : Ixon.Constant} {rIs : List Ixon.Recursor}
    (hinfo : c.info = blockInfo (rIs.map Ixon.MutConst.recr)) {j : Nat} (hj : j < rIs.length) :
    (recursorMembers c).find? (·.1 == j) = some (j, rIs[j]) := by
  rcases rIs with _ | ⟨r, _ | ⟨r₂, rest⟩⟩
  · exact absurd hj (by simp)
  · have hb : blockInfo [Ixon.MutConst.recr r] = .recr r := rfl
    rw [List.map_singleton, hb] at hinfo
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp [recursorMembers, hinfo]
  · have hb : blockInfo ((r :: r₂ :: rest).map Ixon.MutConst.recr) =
        .muts ((r :: r₂ :: rest).map Ixon.MutConst.recr).toArray := rfl
    rw [hb] at hinfo
    have hm : recursorMembers c = (((r :: r₂ :: rest).zipIdx 0).map fun p => (p.2, p.1)).toArray := by
      simp only [recursorMembers, hinfo]
      apply Array.ext'
      simp only [Array.toList_filterMap, Array.toList_zipIdx]
      rw [List.zipIdx_map]
      simp only [List.filterMap_map]
      apply InductiveBlocks.filterMap_eq_map
      intro x _
      rfl
    rw [hm, List.find?_toArray]
    simpa using find_swap (r :: r₂ :: rest) 0 j hj

/-- Quotient Source's conversion of an inductive group refuses unsafe recursors. -/
theorem convertInductive_recs_safe {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Ix.LeanIngress.Converted}
    (ran : Ix.LeanIngress.convertInductive types ctors recs = .ok conv) : ∀ r ∈ recs.toList, r.isUnsafe = false := by
  unfold Ix.LeanIngress.convertInductive at ran
  split at ran
  · simp only at ran
    split at ran
    · cases ran
    · rename_i safe
      intro r hr
      cases hu : r.isUnsafe
      · rfl
      · refine absurd ?_ safe
        rw [Bool.or_eq_true]
        exact .inr (Array.any_eq_true'.mpr ⟨r, Array.mem_def.mpr hr, hu⟩)
  · cases ran

/-- An inductive group's member, as the compiler takes it (`MutConst.fromInductiveVal`). -/
def indOf (v : Ix.InductiveVal) (cs : Array Ix.ConstructorVal) : Ix.Ind :=
  ⟨v.cnst.name, v.cnst.levelParams, v.cnst.type, v.numParams, v.numIndices, v.all, cs, v.numNested, v.isRec,
   v.isReflexive, v.isUnsafe⟩

theorem fromInductiveVal_eq (v : Ix.InductiveVal) (cs : Array Ix.ConstructorVal) :
    MutConst.fromInductiveVal v cs = .indc (indOf v cs) := rfl

/-- An inductive group's members, as the compiler takes them, in Lean's order. -/
def indsOf (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal)) : List Ix.Ind :=
  List.zipWith indOf types.toList ctors.toList

theorem indsOf_getElem {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    (hcsize : ctors.size = types.size) {i : Nat} (hi : i < (indsOf types ctors).length) :
    (indsOf types ctors)[i] = indOf (types[i]'(by simp [indsOf, hcsize] at hi; exact hi))
      (ctors[i]'(by simp [indsOf, hcsize] at hi; omega)) := by
  simp [indsOf]

theorem indsOf_length {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    (hcsize : ctors.size = types.size) : (indsOf types ctors).length = types.size := by
  simp [indsOf, hcsize]

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ i (h₁ : i < l.length) (h₂ : i < m.length), R l[i] m[i]
  | [], [], .nil, _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, .cons hab _, 0, _, _ => hab
  | _ :: _, _ :: _, .cons _ rest, i + 1, h₁, h₂ =>
    forall₂_getElem rest i (by simpa using h₁) (by simpa using h₂)

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, l.length = m.length → (∀ i (h₁ : i < l.length) (h₂ : i < m.length), R l[i] m[i]) →
      List.Forall₂ R l m
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (h 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using hl) fun i h₁ h₂ => h (i + 1) (by simpa using h₁) (by simpa using h₂))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-! ## An inductive group's unit, from its compile runs -/

open Ix.Cert.InductiveUnits (TypeFacts CtorFacts RecFacts srcBlock)
open Ix.Cert.SourceConversion (ownNum recNum motiveOf)
open Ix.Cert.CtxAgree (numNestedOf)
open Ix.Kernel (KeyScope InjOn Key)

theorem ctorFacts_of {cx : Ctx .anon} {owner : Address} {mr : MemberReader .anon} {i j : Nat}
    {c : Ix.ConstructorVal} {ct : Ixon.Constructor} {lps : Array Ix.Name} (hc : c.cnst.levelParams = lps)
    (nodup : lps.toList.Nodup) (cidx : ct.cidx.toNat = j) (safe : ct.isUnsafe = false)
    (key : cx.memberKey (.ctor owner i j) = .ok (srcKey ρ f c.cnst.name))
    (hdr : ProjectionLayout.CtorHeader c ct)
    (read : ∃ type, mr.read ct.typ = .ok type ∧ blockRel ρ f lps c.cnst.type type) :
    CtorFacts ρ f cx owner mr i j c ct := by
  obtain ⟨clvls, -, cparams, cfields⟩ := hdr
  obtain ⟨type, read, rel⟩ := read
  refine ⟨cidx, safe, key, ⟨type, read, ?_⟩, clvls, cparams, cfields, by rw [hc]; exact nodup⟩
  show Related _ (LevelMeaning c.cnst.levelParams.toList (Numbering.mk c.cnst.levelParams false).pos id) _ _
  rw [hc]
  exact rel

/-- **The reader's facts of a compiled type**, from the compile-side reading and the closure's
keys. -/
theorem typeFacts_of {cx : Ctx .anon} {owner : Address} {mr : MemberReader .anon} {i : Nat}
    {v : Ix.InductiveVal} {cs : Array Ix.ConstructorVal} {t : Ixon.Inductive} {lps : Array Ix.Name}
    (hv : v.cnst.levelParams = lps) (hcs : ∀ c ∈ cs.toList, c.cnst.levelParams = lps) (nodup : lps.toList.Nodup)
    (safe : v.isUnsafe = false) (ctorSafe : ∀ c ∈ cs.toList, c.isUnsafe = false)
    (positions : ∀ j (hj : j < cs.size), cs[j].cidx = j)
    (key : cx.memberKey (.member owner i) = .ok (srcKey ρ f v.cnst.name))
    (ctorKeys : ∀ j (hj : j < cs.size), cx.memberKey (.ctor owner i j) = .ok (srcKey ρ f cs[j].cnst.name))
    (h : IndFacts (indOf v cs) t ∧ (∃ type, mr.read t.typ = .ok type ∧ blockRel ρ f lps (indOf v cs).type type) ∧
      List.Forall₂ (fun c (ct : Ixon.Constructor) => ∃ type, mr.read ct.typ = .ok type ∧
        blockRel ρ f lps c.cnst.type type) (indOf v cs).ctors.toList t.ctors.toList) :
    TypeFacts ρ f cx owner mr i v cs t := by
  obtain ⟨⟨unsafeEq, ⟨lvls, params, indices, -⟩, ctorFacts⟩, ⟨type, read, rel⟩, ctorReads⟩ := h
  have hlen : t.ctors.size = cs.size := by
    have := forall₂_length ctorFacts
    simpa [indOf] using this.symm
  refine ⟨key, ⟨type, read, ?_⟩, unsafeEq.trans safe, params, lvls, indices,
    by rw [hv]; exact nodup, hlen, fun j hj hj' => ?_⟩
  · show Related _ (LevelMeaning v.cnst.levelParams.toList (Numbering.mk v.cnst.levelParams false).pos id) _ _
    rw [hv]
    exact rel
  have hj₁ : j < (indOf v cs).ctors.toList.length := by simpa [indOf] using hj
  have hj₂ : j < t.ctors.toList.length := by simpa using hj'
  obtain ⟨hdr, cunsafe⟩ := forall₂_getElem ctorFacts j hj₁ hj₂
  have creads := forall₂_getElem ctorReads j hj₁ hj₂
  have hmem : cs[j] ∈ cs.toList := Array.getElem_mem_toList hj
  exact ctorFacts_of ρ f (hcs _ hmem) nodup (hdr.2.1.trans (positions j hj))
    (cunsafe.trans (ctorSafe _ hmem)) (ctorKeys j hj) hdr creads

theorem recReader_key (cx : Ctx .anon) (owner : Address) {rc : Ixon.Constant} {ts : List Ixon.Recursor}
    (hne : ts ≠ []) (hinfo : rc.info = blockInfo (ts.map .recr)) (hn : ts.length ≠ 1) (k k' : CName .anon)
    (lps : List LevelParam) : RecursorReads.recReader cx rc owner k lps = RecursorReads.recReader cx rc owner k' lps := by
  unfold RecursorReads.recReader
  rw [recSelf_eq cx owner k hne hinfo, recSelf_eq cx owner k' hne hinfo]
  simp [recSelfOf, hn]

/-- **The reader's facts of a compiled recursor**, from the compile-side reading, the
closure's keys and the recursor index. -/
theorem recFacts_of {cx : Ctx .anon} {blockLps : List LevelParam} {types : Array Ix.InductiveVal}
    {first : Ix.InductiveVal} {nested : Prop} {rOwner : Address} {rc : Ixon.Constant} {rIs : List Ixon.Recursor}
    {recs : List Ix.RecursorVal} (hlen : rIs.length = recs.length) (hstore : cx.store rOwner = some rc)
    (hinfo : rc.info = blockInfo (rIs.map .recr)) {rlps : Array Ix.Name} {large : Bool} {key₀ : CName .anon}
    (hkey₀ : ∀ r ∈ recs.head?, key₀ = srcKey ρ f r.cnst.name) {j : Nat} (hj : j < recs.length)
    (hr : RecPayload recs[j] (rIs[j]'(hlen ▸ hj)) ∧
      (∃ type, (RecursorReads.recReader cx rc rOwner key₀ (Numbering.mk rlps large).params).read
        (rIs[j]'(hlen ▸ hj)).typ = .ok type ∧ recRel ρ f rlps large recs[j].cnst.type type) ∧
      List.Forall₂ (fun (rule : Ix.RecursorRule) (rr : Ixon.RecursorRule) =>
        ∃ rhs, (RecursorReads.recReader cx rc rOwner key₀ (Numbering.mk rlps large).params).read rr.rhs = .ok rhs ∧
          recRel ρ f rlps large rule.rhs rhs) recs[j].rules.toList (rIs[j]'(hlen ▸ hj)).rules.toList)
    (hnum : recNum first recs[j] = Numbering.mk rlps large) (safe : recs[j].isUnsafe = false)
    (nodup : recs[j].cnst.levelParams.toList.Nodup)
    (key : cx.memberKey (.member rOwner j) = .ok (srcKey ρ f recs[j].cnst.name))
    {entry : RecEntry} (hentry : cx.index.recs[ConstRef.member rOwner j]? = some entry)
    (hlpsE : recLps entry.large blockLps = (recNum first recs[j]).params) {major : Ixon.Inductive}
    {mb : Address} {mi : Nat} (hmajor : inductiveAt cx.store entry.major = some major)
    (hmb : entry.major = .member mb mi) (hmsize : major.ctors.size = recs[j].rules.size)
    (ruleKeys : ∀ k (hk : k < recs[j].rules.size),
      cx.memberKey (.ctor mb mi k) = .ok (srcKey ρ f recs[j].rules[k].ctor))
    (motive : nested → some entry.motive = motiveOf types recs[j]) :
    RecFacts ρ f cx blockLps types first nested (.member rOwner j) recs[j] := by
  obtain ⟨⟨unsafeEq, kEq, ⟨-, params, indices, motives, minors, bounded⟩, fields⟩, ⟨type, read, rel⟩, rules⟩ := hr
  have hjI : j < rIs.length := hlen ▸ hj
  have hne : rIs ≠ [] := by
    intro h
    rw [h] at hjI
    exact absurd hjI (by simp)
  have hrlps : recs[j].cnst.levelParams = rlps := congrArg Numbering.names hnum
  -- the reader at the recursor's own key
  have hreader : RecursorReads.recReader cx rc rOwner (srcKey ρ f recs[j].cnst.name) (recNum first recs[j]).params =
      RecursorReads.recReader cx rc rOwner key₀ (Numbering.mk rlps large).params := by
    rw [hnum]
    by_cases h1 : rIs.length = 1
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [hkey₀ recs[0] (by cases recs with
        | nil => exact absurd hj (by simp)
        | cons r rs => simp)]
    · exact recReader_key cx rOwner hne hinfo h1 _ _ _
  have hrel : ∀ {s : Ix.Expr} {t : CExpr .anon}, recRel ρ f rlps large s t →
      Related (sourceNames ρ f) (LevelMeaning recs[j].cnst.levelParams.toList (recNum first recs[j]).pos
        (recParam (recNum first recs[j]).params)) s t := by
    intro s t h
    rw [hnum, hrlps]
    exact h
  have hsize : (rIs[j]'hjI).rules.size = recs[j].rules.size := by
    simpa using congrArg List.length fields
  refine ⟨entry, rOwner, j, rc, j, rIs[j]'hjI, major, mb, mi, hentry, rfl, hstore,
    recursorMembers_find hinfo hjI, unsafeEq.trans safe, key, hlpsE,
    ⟨type, by rw [hreader]; exact read, hrel rel⟩, hmajor, hmsize.trans hsize.symm, hmb, hsize,
    fun k hk hk' => ?_, params, motives, minors, indices, kEq, nodup, motive⟩
  have hk₁ : k < recs[j].rules.toList.length := by simpa using hk'
  have hk₂ : k < (rIs[j]'hjI).rules.toList.length := by simpa using hk
  obtain ⟨rhs, rread, rrel⟩ := forall₂_getElem rules k hk₁ hk₂
  have hf : (rIs[j]'hjI).rules[k].fields = recs[j].rules[k].nfields.toUInt64 := by
    have := congrArg (·[k]?) fields
    simpa [hk, hk'] using this
  simp only [Array.getElem_toList] at rread rrel
  refine ⟨ruleKeys k hk', ?_, ⟨rhs, by rw [hreader]; exact rread, hrel rrel⟩⟩
  rw [hf]
  exact Emission.exact_header _ (bounded _ (Array.getElem_mem_toList hk'))

/-- **An inductive group compiled in Lean's order reads as quotient Source's unit renamed**,
from every state related to the unit's (the `reads` of `StreamUnits.Units.record`).

Premises: quotient Source's conversion and lowering of the group, with good keys; the group's
Lean facts (shared level parameters, distinct, constructors at their positions, distinct
names, no constructor in the members' types); the compile runs of the inductive block, in
Lean's order, and of its recursor family, in family order, each from a clean state in a
reading context aligned with its compile environment; and the closure's context: the two
records in its store, reading their references as the compile environments do, the members',
constructors' and recursors' keys, the block shape in Lean's order with the family's
recursors, and each recursor's index entry. -/
theorem compiled_inductive_unit_reads {P : KeyScope .source} (hP : P.Pre) (hf : InjOn f P)
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    {conv : Ix.LeanIngress.Converted} (src : Ix.LeanIngress.convertInductive types ctors recs = .ok conv)
    {first : Ix.InductiveVal} (hfirst : types[0]? = some first) (hcsize : ctors.size = types.size)
    (lpsEq : ∀ v ∈ types.toList, v.cnst.levelParams = first.cnst.levelParams)
    (ctorLps : ∀ cs ∈ ctors.toList, ∀ c ∈ cs.toList, c.cnst.levelParams = first.cnst.levelParams)
    (nodup : first.cnst.levelParams.toList.Nodup)
    (positions : ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size), ctors[i][j].cidx = j)
    {rlps : Array Ix.Name} (recLpsEq : ∀ r ∈ recs.toList, r.cnst.levelParams = rlps)
    (recNodup : rlps.toList.Nodup) (hrne : recs.toList ≠ [])
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc))
    (noCtor : ∀ i ∈ indsOf types ctors, ∀ e ∈ memberSources (.indc i),
      ConstsSatisfy (fun n => ∀ i' ∈ indsOf types ctors, ∀ c ∈ i'.ctors.toList, n ≠ c.cnst.name) e)
    (recDistinct : Canon.KeysDistinct (recs.toList.map MutConst.recr))
    (context₁ : CompileEnv × BlockEnv) (free₁ : context₁.1.surgeryFree = true) {cx₁ : Ctx .anon}
    (aligned₁ : ∀ a, cx₁.blob a = context₁.1.blobs.get? a) {bindings₁ : Bindings}
    (external₁ : BindingsCorrect context₁.1 bindings₁ cx₁ (sourceNames ρ f))
    {before₁ after₁ : BlockState} {out₁ : BlockResult} (clean₁ : Emission.Clean bindings₁ before₁)
    (ran₁ : rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·]))) context₁ before₁ =
      (.ok out₁, after₁))
    (context₂ : CompileEnv × BlockEnv) (free₂ : context₂.1.surgeryFree = true) {cx₂ : Ctx .anon}
    (aligned₂ : ∀ a, cx₂.blob a = context₂.1.blobs.get? a) {bindings₂ : Bindings}
    (external₂ : BindingsCorrect context₂.1 bindings₂ cx₂ (sourceNames ρ f))
    {before₂ after₂ : BlockState} {out₂ : BlockResult} (clean₂ : Emission.Clean bindings₂ before₂)
    (ran₂ : rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·]))) context₂ before₂ =
      (.ok out₂, after₂))
    (cx : Ctx .anon) (owner rOwner : Address) (hstore₁ : cx.store owner = some out₁.block)
    (hstore₂ : cx.store rOwner = some out₂.block)
    (refs₁ : RecordTransfer.RefsLe out₁.block (ExpressionRead.withBlockBlobs cx₁ after₁) cx)
    (refs₂ : RecordTransfer.RefsLe out₂.block (ExpressionRead.withBlockBlobs cx₂ after₂) cx)
    (keys : ∀ i (hi : i < types.size), cx.memberKey (.member owner i) = .ok (srcKey ρ f types[i].cnst.name))
    (ctorKeys : ∀ i (hi : i < ctors.size) j (hj : j < ctors[i].size),
      cx.memberKey (.ctor owner i j) = .ok (srcKey ρ f ctors[i][j].cnst.name))
    (recKeys : ∀ j (hj : j < recs.size), cx.memberKey (.member rOwner j) = .ok (srcKey ρ f recs[j].cnst.name))
    {shape : BlockShape} (hindexed : cx.index.blocks[owner]? = some shape)
    (order : shape.order = (List.range types.size).toArray)
    (hrecs : shape.recs.toList = (List.range recs.size).map fun j => ConstRef.member rOwner j)
    (entries : ∀ j (hj : j < recs.size), ∃ entry mi, ∃ hmi : mi < types.size,
      cx.index.recs[ConstRef.member rOwner j]? = some entry ∧
      recLps entry.large (List.range first.cnst.levelParams.size) = (recNum first recs[j]).params ∧
      entry.major = .member owner mi ∧ recs[j].rules.size = (ctors[mi]'(hcsize ▸ hmi)).size ∧
      (∀ k (hk : k < recs[j].rules.size),
        cx.memberKey (.ctor owner mi k) = .ok (srcKey ρ f recs[j].rules[k].ctor)) ∧
      (numNestedOf (srcBlock types ctors recs first) = 0 → some entry.motive = motiveOf types recs[j]))
    (good : ∀ rb, conv.quotient ρ = .inductive rb → rb.Good P) {stS : State .source}
    (typesGood : ∀ k : Key .source, k.Good P → ∀ p, stS.constTypes[k]? = some p → p.2.Good P)
    (blocksGood : ∀ k : Key .source, k.Good P → ∀ b, stS.indBlocks[k]? = some b → b.Good P)
    {rS : Read .source} (lowered : Ix.LeanIngress.lower stS (conv.quotient ρ) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA owner out₁.block = .ok rA ∧ StreamUnits.ReadRen f rS rA := by
  obtain ⟨-, -, typeSafe, ctorSafe, -, -⟩ :=
    Ix.CompileCert.SourceConstructorPositions.convertInductive_spec types ctors recs conv src
  have recSafe := convertInductive_recs_safe src
  have hlenI := indsOf_length hcsize
  -- the inductive block
  obtain ⟨targets, hinfo, hT⟩ := inductiveBlock_reads ρ f context₁ free₁ aligned₁ external₁ (indsOf types ctors)
    first.cnst.levelParams (by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
      rw [indsOf_getElem hcsize hk]
      exact lpsEq _ (Array.getElem_mem_toList _))
    owner (by
      intro k hk
      rw [indsOf_getElem hcsize hk]
      exact keys k _)
    distinct noCtor clean₁ ran₁ refs₁
  have hlenT : targets.length = types.size := (forall₂_length hT).symm.trans hlenI
  -- the recursor family
  have hrsize : 0 < recs.size := by
    rcases h : recs.toList with _ | ⟨r, rs⟩
    · exact absurd h hrne
    · have := congrArg List.length h
      simp only [Array.length_toList, List.length_cons] at this
      omega
  obtain ⟨rIs, hrinfo, hR⟩ := recursorBlock_reads ρ f context₂ free₂ aligned₂ external₂ recs.toList hrne rlps
    recLpsEq (rlps.size == first.cnst.levelParams.size + 1) rOwner (srcKey ρ f (recs[0]'hrsize).cnst.name)
    (by
      intro k hk
      by_cases h1 : recs.toList.length = 1
      · have hk0 : k = 0 := by omega
        subst hk0
        simp [recSelfOf, h1]
        rfl
      · simp only [recSelfOf, h1, ↓reduceIte, hk]
        rw [recKeys k (by simpa using hk)]
        simp)
    recDistinct clean₂ ran₂ refs₂
  have hlenR : rIs.length = recs.toList.length := (forall₂_length hR).symm
  -- the unit's reading
  refine InductiveUnits.inductive_unit_reads ρ f hP hf src hfirst cx owner out₁.block targets
    (by
      intro h
      have hpos : 0 < types.size := (Array.getElem?_eq_some_iff.mp hfirst).1
      rw [h] at hlenT
      simp at hlenT
      omega)
    hinfo hindexed (by rw [order, hlenT]) hlenT hcsize ?typeFacts ?recFacts good typesGood blocksGood lowered
  case typeFacts =>
    intro i hi hi' hc
    have hiI : i < (indsOf types ctors).length := hlenI ▸ hi
    have h := forall₂_getElem hT i hiI hi'
    rw [indsOf_getElem hcsize hiI] at h
    exact typeFacts_of ρ f (lpsEq _ (Array.getElem_mem_toList hi))
      (ctorLps _ (Array.getElem_mem_toList hc)) nodup (typeSafe _ (Array.getElem_mem_toList hi))
      (ctorSafe _ (Array.getElem_mem_toList hc)) (positions i hc) (keys i hi) (ctorKeys i hc) h
  case recFacts =>
    rw [hrecs]
    refine forall₂_of_getElem (by simp) fun j h₁ h₂ => ?_
    have hj : j < recs.size := by simpa using h₂
    obtain ⟨entry, mi, hmi, hentry, hlpsE, hmb, hrules, ruleKeys, motive⟩ := entries j hj
    have hmiT : mi < targets.length := hlenT ▸ hmi
    have hmajor := inductiveAt_block hstore₁ hinfo hmiT
    have hTmi := forall₂_getElem hT mi (hlenI ▸ hmi) hmiT
    rw [indsOf_getElem hcsize (hlenI ▸ hmi)] at hTmi
    have hmsize : targets[mi].ctors.size = (ctors[mi]'(hcsize ▸ hmi)).size := by
      have := forall₂_length hTmi.1.2.2
      simpa [indOf] using this.symm
    have hjl : j < recs.toList.length := by simpa using hj
    have hRj := forall₂_getElem hR j hjl (hlenR ▸ hjl)
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList] at hRj ⊢
    have hmem : recs[j] ∈ recs.toList := Array.getElem_mem_toList hj
    have hnum : recNum first recs[j] = Numbering.mk rlps (rlps.size == first.cnst.levelParams.size + 1) := by
      simp [recNum, recLpsEq _ hmem]
    exact recFacts_of ρ f hlenR hstore₂ hrinfo (by
        intro r hr
        rcases h : recs.toList with _ | ⟨r₀, rs⟩
        · exact absurd h hrne
        · rw [h] at hr
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
          subst hr
          have : recs[0]'hrsize = r₀ := by
            have := congrArg (·[0]?) h
            simp only [Array.getElem?_toList, List.getElem?_cons_zero] at this
            exact Option.some.inj ((Array.getElem?_eq_getElem hrsize).symm.trans this)
          rw [this])
      hjl hRj hnum (recSafe _ hmem) (by simp only [Array.getElem_toList]; rw [recLpsEq _ hmem]; exact recNodup) (recKeys j hj) hentry hlpsE
      (by rw [hmb]; exact hmajor) hmb (hmsize.trans hrules.symm) ruleKeys motive

/--
info: 'Ix.Cert.InductiveCompile.compiled_inductive_unit_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms compiled_inductive_unit_reads

end Ix.Cert.InductiveCompile
