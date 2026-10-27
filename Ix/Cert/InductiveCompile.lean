import Ix.Cert.BlockEmission
import Ix.Cert.InductiveUnits
import Ix.CompileCert.Canon.Ctx

/-! # Inductive and recursor blocks compiled in Lean's order, read in a closure

`BlockEmission.mutualBlock_correct` reads a block compiled one member per class back as its
members' sources, in the compile environment's reading context. This module splits that
reading member by member and moves it to the closure's context (`RecordTransfer.read_le`), for
an inductive block in Lean's order (`inductiveBlock_reads`): the record is a block of
inductives keeping the members' headers, whose member reader in the closure's context reads
every type and constructor as a term related to its Lean type. The block's self references
are its members' keys in the closure's context; the constructors of the block occur in no
member's types (`NoCtorIn`), so they need no self reference. -/

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

end Ix.Cert.InductiveCompile
