import IxC.Kernel.Verify.Frontend.InModelGenNested
import IxC.Kernel.Ixon.ReaderSpec
import Ix.CompileCert.Loop
import Ix.Cert.LowerDistinct

/-! # The generator's context on both streams (the statements half of `CtxAgree`)

For a mutual or nested inductive block, `Reader.lowerInductive` prepends the
in-process modeller's records (`InModel.generate`) on both streams: quotient
Source's (`Ix.LeanIngress.lowerAllCollapsed`) and the Ixon reader's
(`Reader.readRecords`). IxC proves the generator parametric
(`InModel.generate_mapKeys`): at contexts that agree on a scope under a
renaming `f` injective there (`InModel.CtxAgree`), a good block's generation
and its renaming's give renamed records, or both fail. This file is the other
half: the contexts the two streams build do agree, so a mutual or nested block's
generated records agree on the two sides (S1's `UnitsAgree` for those units).

* **The block** (`blockRecOf`): the modeller's block `lowerInductive` builds
  from a block as read, renamed with it (`blockRecOf_mapKeys`, through
  `occursConstFast` = `occursConst` and the renaming of `occursConst` and
  `headIs`).
* **One block** (`lowerInductive_ok`, `ctxAgree_genCtx`,
  `lowerInductive_mapKeys`): at reader states that agree on the block's scope
  (`StateAgree`), the block and its renaming lower to renamed records, the
  generated ones included.
* **The states** (`fold_fields`, `foldl_insOpt_some`/`_none`): what a reader
  state holds at a key after a stream prefix comes from an entry the prefix
  noted there, or from the start.
* **The per-key relation** (`ReadsAgreeAt`, named; `NonAuxAgree`, what it gives
  of the states): at every key but the derived ones the two prefixes read
  renamed-equal declarations. It is discharged by the reading chain (N5b stage B
  and the recursor pieces), outside this file.
* **The cone induction** (`Streams.units`): a derived key's entries are an
  earlier block's generated records on both sides, so every block unit agrees
  with its partner, by induction over the Source stream.
* **Hints** (`Ix.Cert.CtxAgreeHints`, `hints_agree`): quotient Source and the reader
  run one hint per published definition (point (2)).

Both streams read canonical levels and keep `generate`'s output as it is
(quotient Source canonicalizes each renamed group's levels before lowering,
option (α)), so the two contexts are compared by renaming alone. The scope of a
block is the caller's: it must hold the block, be good for what the Source
state holds there (`NonAuxAgree.typesGood`, derived keys included: the block's
reference closure in the Source stream is), allow the prelude's roles
(`KeyScope.Pre`), and lie inside a scope `f` is injective on.
-/

namespace Ix.Cert.CtxAgree

open Ix.Kernel
open Ix.Kernel.Frontend (occursConst occursConstB occursConstGo occursConstFast headIs stripPisAll
  stripPisAll_mapKeys stripPisAll_good headIs_mapKeys)
open Ix.Kernel.Frontend.InModel
open Ix.Kernel.Reader (BlockRead RecCounts State Read CDecl CName CVal CExpr)

variable {md md' : Mode}

/-! ## `occursConst`, memoised, is `occursConst` -/

section Occurs

variable (n : Key md)

/-- `occursConstB`'s answer, when it gives one, is `occursConst`'s. -/
theorem occursConstB_sound : ∀ (e : Expr md) (fuel : Nat) {b : Bool} {fuel' : Nat},
    occursConstB n fuel e = (some b, fuel') → occursConst n e = b := by
  intro e
  induction e with
  | const m _ =>
    intro fuel b fuel' h
    cases fuel <;> simp only [occursConstB, Prod.mk.injEq, Option.some.injEq] at h <;>
      simp [occursConst, h.1]
  | bvar _ | sort _ | lit _ =>
    intro fuel b fuel' h
    cases fuel <;> simp only [occursConstB, Prod.mk.injEq, Option.some.injEq] at h <;>
      simp [occursConst, ← h.1]
  | fvar _ _ _ =>
    intro fuel b fuel' h
    cases fuel <;> simp only [occursConstB, Prod.mk.injEq, Option.some.injEq] at h <;>
      simp [occursConst, ← h.1]
  | app g a ihg iha =>
    intro fuel b fuel' h
    cases fuel with
    | zero => simp [occursConstB] at h
    | succ fuel =>
      simp only [occursConstB] at h
      rcases hg : occursConstB n fuel g with ⟨o, k⟩
      rw [hg] at h
      cases o with
      | none => simp at h
      | some c =>
        cases c with
        | false => simp only at h; simp only [occursConst, ihg _ hg, iha _ h, Bool.false_or]
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          simp only [occursConst, ihg _ hg, ← h.1, Bool.true_or]
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    intro fuel c fuel' h
    cases fuel with
    | zero => simp [occursConstB] at h
    | succ fuel =>
      simp only [occursConstB] at h
      rcases ht : occursConstB n fuel t with ⟨o, k⟩
      rw [ht] at h
      cases o with
      | none => simp at h
      | some c' =>
        cases c' with
        | false => simp only at h; simp only [occursConst, iht _ ht, ihb _ h, Bool.false_or]
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          simp only [occursConst, iht _ ht, ← h.1, Bool.true_or]
  | letE t v b _ iht ihv ihb =>
    intro fuel c fuel' h
    cases fuel with
    | zero => simp [occursConstB] at h
    | succ fuel =>
      simp only [occursConstB] at h
      rcases ht : occursConstB n fuel t with ⟨o, k⟩
      rw [ht] at h
      cases o with
      | none => simp at h
      | some c' =>
        cases c' with
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          simp only [occursConst, iht _ ht, ← h.1, Bool.true_or]
        | false =>
          simp only at h
          rcases hv : occursConstB n k v with ⟨o, k'⟩
          rw [hv] at h
          cases o with
          | none => simp at h
          | some c'' =>
            cases c'' with
            | false =>
              simp only at h
              simp only [occursConst, iht _ ht, ihv _ hv, ihb _ h, Bool.false_or]
            | true =>
              simp only [Prod.mk.injEq, Option.some.injEq] at h
              simp only [occursConst, iht _ ht, ihv _ hv, ← h.1, Bool.false_or, Bool.true_or]
  | proj _ _ e ih =>
    intro fuel b fuel' h
    cases fuel with
    | zero => simp [occursConstB] at h
    | succ fuel => simp only [occursConstB] at h; simp only [occursConst, ih _ h]

/-- **The memoised descent is `occursConst`**, from a memo holding only terms
that do not mention `n`, and it leaves only such terms there. -/
theorem occursConstGo_spec : ∀ (e : Expr md) (seen : Std.HashSet (Expr md)),
    (∀ x, seen.contains x = true → occursConst n x = false) →
    (occursConstGo n seen e).1 = occursConst n e ∧
      ∀ x, (occursConstGo n seen e).2.contains x = true → occursConst n x = false := by
  intro e
  induction e with
  | const m _ => intro seen hs; exact ⟨by simp [occursConstGo, occursConst], hs⟩
  | bvar _ | sort _ | lit _ => intro seen hs; exact ⟨by simp [occursConstGo, occursConst], hs⟩
  | fvar _ _ _ => intro seen hs; exact ⟨by simp [occursConstGo, occursConst], hs⟩
  | app g a ihg iha =>
    intro seen hs
    simp only [occursConstGo]
    split
    · rename_i hc; exact ⟨(hs _ hc).symm, hs⟩
    · obtain ⟨hg1, hg2⟩ := ihg seen hs
      rcases hgo : occursConstGo n seen g with ⟨cg, s1⟩
      rw [hgo] at hg1 hg2
      cases cg with
      | true => simp only at hg1 ⊢; exact ⟨by simp [occursConst, ← hg1], hg2⟩
      | false =>
        simp only
        obtain ⟨ha1, ha2⟩ := iha s1 hg2
        rcases hao : occursConstGo n s1 a with ⟨ca, s2⟩
        rw [hao] at ha1 ha2
        cases ca with
        | true => simp only at ha1 ⊢; exact ⟨by simp [occursConst, ← hg1, ← ha1], ha2⟩
        | false =>
          simp only at ha1 hg1 ⊢
          have he : occursConst n (.app g a) = false := by simp [occursConst, ← hg1, ← ha1]
          refine ⟨he.symm, fun x hx => ?_⟩
          rw [Std.HashSet.contains_insert] at hx
          rcases Bool.or_eq_true_iff.mp hx with hx | hx
          · rw [← eq_of_beq hx]; exact he
          · exact ha2 x hx
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    intro seen hs
    simp only [occursConstGo]
    split
    · rename_i hc; exact ⟨(hs _ hc).symm, hs⟩
    · obtain ⟨ht1, ht2⟩ := iht seen hs
      rcases hto : occursConstGo n seen t with ⟨ct, s1⟩
      rw [hto] at ht1 ht2
      cases ct with
      | true => simp only at ht1 ⊢; exact ⟨by simp [occursConst, ← ht1], ht2⟩
      | false =>
        simp only
        obtain ⟨hb1, hb2⟩ := ihb s1 ht2
        rcases hbo : occursConstGo n s1 b with ⟨cb, s2⟩
        rw [hbo] at hb1 hb2
        cases cb with
        | true => simp only at hb1 ⊢; exact ⟨by simp [occursConst, ← ht1, ← hb1], hb2⟩
        | false =>
          simp only at hb1 ht1 ⊢
          refine ⟨by simp [occursConst, ← ht1, ← hb1], fun x hx => ?_⟩
          rw [Std.HashSet.contains_insert] at hx
          rcases Bool.or_eq_true_iff.mp hx with hx | hx
          · rw [← eq_of_beq hx]; simp [occursConst, ← ht1, ← hb1]
          · exact hb2 x hx
  | letE t v b _ iht ihv ihb =>
    intro seen hs
    simp only [occursConstGo]
    split
    · rename_i hc; exact ⟨(hs _ hc).symm, hs⟩
    · obtain ⟨ht1, ht2⟩ := iht seen hs
      rcases hto : occursConstGo n seen t with ⟨ct, s1⟩
      rw [hto] at ht1 ht2
      cases ct with
      | true => simp only at ht1 ⊢; exact ⟨by simp [occursConst, ← ht1], ht2⟩
      | false =>
        simp only
        obtain ⟨hv1, hv2⟩ := ihv s1 ht2
        rcases hvo : occursConstGo n s1 v with ⟨cv, s2⟩
        rw [hvo] at hv1 hv2
        cases cv with
        | true => simp only at hv1 ⊢; exact ⟨by simp [occursConst, ← ht1, ← hv1], hv2⟩
        | false =>
          simp only
          obtain ⟨hb1, hb2⟩ := ihb s2 hv2
          rcases hbo : occursConstGo n s2 b with ⟨cb, s3⟩
          rw [hbo] at hb1 hb2
          cases cb with
          | true => simp only at hb1 ⊢; exact ⟨by simp [occursConst, ← ht1, ← hv1, ← hb1], hb2⟩
          | false =>
            simp only at hb1 hv1 ht1 ⊢
            refine ⟨by simp [occursConst, ← ht1, ← hv1, ← hb1], fun x hx => ?_⟩
            rw [Std.HashSet.contains_insert] at hx
            rcases Bool.or_eq_true_iff.mp hx with hx | hx
            · rw [← eq_of_beq hx]; simp [occursConst, ← ht1, ← hv1, ← hb1]
            · exact hb2 x hx
  | proj _ _ e ih =>
    intro seen hs
    simp only [occursConstGo]
    split
    · rename_i hc; exact ⟨(hs _ hc).symm, hs⟩
    · obtain ⟨h1, h2⟩ := ih seen hs
      rcases ho : occursConstGo n seen e with ⟨c, s1⟩
      rw [ho] at h1 h2
      cases c with
      | true => simp only at h1 ⊢; exact ⟨by simp [occursConst, ← h1], h2⟩
      | false =>
        simp only at h1 ⊢
        refine ⟨by simp [occursConst, ← h1], fun x hx => ?_⟩
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true_iff.mp hx with hx | hx
        · rw [← eq_of_beq hx]; simp [occursConst, ← h1]
        · exact h2 x hx

/-- **The executed `occursConst` is `occursConst`.** -/
theorem occursConstFast_eq (e : Expr md) : occursConstFast n e = occursConst n e := by
  unfold occursConstFast
  rcases hb : occursConstB n 4096 e with ⟨o, k⟩
  cases o with
  | some b => exact (occursConstB_sound n e 4096 hb).symm
  | none =>
    exact (occursConstGo_spec n e {} fun x hx => by simp at hx).1

end Occurs

variable {P : KeyScope md} {f : md.Id → md'.Id}

/-- **`occursConst` under a renaming injective on the scope**, at good keys
and terms. -/
theorem occursConst_mapKeys (hf : InjOn f P) {n : Key md} (hn : n.Good P) :
    ∀ {e : Expr md}, e.Good P → occursConst (n.map f) (e.mapKeys f) = occursConst n e
  | .const m _, he => by simp only [Expr.mapKeys, occursConst]; exact Key.map_beq hf he hn
  | .app g a, he => by
    simp only [Expr.mapKeys, occursConst, occursConst_mapKeys hf hn he.1, occursConst_mapKeys hf hn he.2]
  | .lam t b _, he => by
    simp only [Expr.mapKeys, occursConst, occursConst_mapKeys hf hn he.1, occursConst_mapKeys hf hn he.2]
  | .forallE t b _, he => by
    simp only [Expr.mapKeys, occursConst, occursConst_mapKeys hf hn he.1, occursConst_mapKeys hf hn he.2]
  | .letE t v b _, he => by
    simp only [Expr.mapKeys, occursConst, occursConst_mapKeys hf hn he.1,
      occursConst_mapKeys hf hn he.2.1, occursConst_mapKeys hf hn he.2.2]
  | .proj _ _ e, he => by simp only [Expr.mapKeys, occursConst, occursConst_mapKeys hf hn he.2]
  | .bvar _, _ | .sort _, _ | .lit _, _ | .fvar _ _, _ => rfl

/-- `List.any` at pointwise-equal predicates. -/
theorem any_congr {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-! ## The modeller's block, as `lowerInductive` builds it -/

section Block

/-- A block's member type names. -/
def memberNamesOf (rb : BlockRead md) : List (CName md) := rb.types.toList.map (·.1.name)

/-- A block's constructors' field domains. -/
def fieldDomsOf (rb : BlockRead md) : List (Expr md) :=
  rb.ctors.toList.flatMap fun (cv, _, _) => (stripPisAll cv.type).1.map (·.1)

/-- Whether a member occurs in a field domain. -/
def isRecOf (rb : BlockRead md) : Bool :=
  (fieldDomsOf rb).any fun d => (memberNamesOf rb).any (occursConstFast · d)

/-- Whether a field domain is a function into a member. -/
def isReflexiveOf (rb : BlockRead md) : Bool :=
  (fieldDomsOf rb).any fun d =>
    let (bs, body) := stripPisAll d
    !bs.isEmpty && (memberNamesOf rb).any (headIs · body)

/-- The number of nested auxiliaries the first recursor's motives count. -/
def numNestedOf (rb : BlockRead md) : Nat :=
  match rb.recs[0]? with
  | some (_, r, _) => r.motives - rb.types.size
  | none => 0

/-- **The modeller's block** of a block as read: `lowerInductive`'s `b`. -/
def blockRecOf (rb : BlockRead md) : BlockRec md :=
  ⟨rb.types.toList.zip rb.ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
      { cv, nP, nIdx, ctors := cs, isRec := isRecOf rb, isReflexive := isReflexiveOf rb,
        numNested := numNestedOf rb },
   rb.ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
   rb.recs.toList.map fun (cv, r, rules) =>
     { cv, nP := r.params, nM := r.motives, nm := r.minors, nI := r.indices, rules }⟩

/-- **A block as read, renamed**: every header, constructor name and rule. -/
def _root_.Ix.Kernel.Reader.BlockRead.mapKeys (f : md.Id → md'.Id) (rb : BlockRead md) : BlockRead md' :=
  ⟨rb.numParams, rb.types.map fun (cv, p, i) => (cv.mapKeys f, p, i),
   rb.ctors.map fun (cv, p, n) => (cv.mapKeys f, p, n),
   rb.ctorNames.map (·.map (Key.map f)),
   rb.recs.map fun (cv, c, rules) => (cv.mapKeys f, c, rules.map (RecRule.mapKeys f))⟩

/-- **A good block as read**: every key it carries is good. -/
def _root_.Ix.Kernel.Reader.BlockRead.Good (P : KeyScope md) (rb : BlockRead md) : Prop :=
  (∀ x ∈ rb.types.toList, x.1.Good P) ∧ (∀ x ∈ rb.ctors.toList, x.1.Good P) ∧
    (∀ ns ∈ rb.ctorNames.toList, ∀ k ∈ ns, k.Good P) ∧
    ∀ x ∈ rb.recs.toList, x.1.Good P ∧ ∀ r ∈ x.2.2, r.Good P

theorem memberNamesOf_mapKeys (rb : BlockRead md) :
    memberNamesOf (rb.mapKeys f) = (memberNamesOf rb).map (Key.map f) := by
  simp [memberNamesOf, BlockRead.mapKeys, Function.comp_def]

theorem fieldDomsOf_mapKeys (rb : BlockRead md) :
    fieldDomsOf (rb.mapKeys f) = (fieldDomsOf rb).map (Expr.mapKeys f) := by
  simp only [fieldDomsOf, BlockRead.mapKeys, Array.toList_map, List.flatMap_map, List.map_flatMap]
  congr 1
  funext x
  simp only [ConstantVal.mapKeys_type, stripPisAll_mapKeys]
  simp [Expr.mapTele, Expr.mapBinders, Function.comp_def]

theorem memberNamesOf_good {rb : BlockRead md} (hg : rb.Good P) : ∀ k ∈ memberNamesOf rb, k.Good P := by
  intro k hk
  simp only [memberNamesOf, List.mem_map] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  exact (hg.1 x hx).1

theorem fieldDomsOf_good {rb : BlockRead md} (hg : rb.Good P) : ∀ d ∈ fieldDomsOf rb, d.Good P := by
  intro d hd
  simp only [fieldDomsOf, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨x, hx, b, hb, rfl⟩ := hd
  exact (stripPisAll_good (hg.2.1 x hx).2).1 b hb

theorem isRecOf_mapKeys (hf : InjOn f P) {rb : BlockRead md} (hg : rb.Good P) :
    isRecOf (rb.mapKeys f) = isRecOf rb := by
  simp only [isRecOf, fieldDomsOf_mapKeys, memberNamesOf_mapKeys, List.any_map, Function.comp_def]
  refine any_congr fun d hd => any_congr fun k hk => ?_
  rw [occursConstFast_eq, occursConstFast_eq,
    occursConst_mapKeys hf (memberNamesOf_good hg k hk) (fieldDomsOf_good hg d hd)]

theorem isReflexiveOf_mapKeys (hf : InjOn f P) {rb : BlockRead md} (hg : rb.Good P) :
    isReflexiveOf (rb.mapKeys f) = isReflexiveOf rb := by
  simp only [isReflexiveOf, fieldDomsOf_mapKeys, memberNamesOf_mapKeys, List.any_map, Function.comp_def]
  refine any_congr fun d hd => ?_
  have hdG := fieldDomsOf_good hg d hd
  rw [stripPisAll_mapKeys]
  have hsG := stripPisAll_good hdG
  rcases hs : stripPisAll d with ⟨bs, body⟩
  rw [hs] at hsG
  simp only [Expr.mapTele, Expr.mapBinders, List.isEmpty_map]
  congr 1
  refine any_congr fun k hk => ?_
  exact headIs_mapKeys hf (memberNamesOf_good hg k hk) hsG.2

theorem numNestedOf_mapKeys (rb : BlockRead md) : numNestedOf (rb.mapKeys f) = numNestedOf rb := by
  simp only [numNestedOf, BlockRead.mapKeys, Array.getElem?_map, Array.size_map]
  cases rb.recs[0]? <;> rfl

/-- **The modeller's block of a renamed block is the renamed block**, for a
good block under a renaming injective on the scope. -/
theorem blockRecOf_mapKeys (hf : InjOn f P) {rb : BlockRead md} (hg : rb.Good P) :
    blockRecOf (rb.mapKeys f) = (blockRecOf rb).mapKeys f := by
  have hr := isRecOf_mapKeys hf hg
  have hx := isReflexiveOf_mapKeys hf hg
  have hn := numNestedOf_mapKeys (f := f) rb
  simp only [blockRecOf, hr, hx, hn]
  simp only [BlockRec.mapKeys, Ix.Kernel.Reader.BlockRead.mapKeys, Array.toList_map, List.zip_map,
    List.map_map, BlockRec.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · congr 1
  · simp [Function.comp_def, IndCtorRec.mapKeys]
  · simp [Function.comp_def, IndRecRec.mapKeys]

/-- A good block as read gives a good modeller's block. -/
theorem blockRecOf_good {rb : BlockRead md} (hg : rb.Good P) : (blockRecOf rb).Good P := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [blockRecOf, List.mem_map] at ht
    obtain ⟨⟨⟨cv, nP, nIdx⟩, cs⟩, hm, rfl⟩ := ht
    exact ⟨(hg.1 _ (List.of_mem_zip hm).1), hg.2.2.1 cs (List.of_mem_zip hm).2⟩
  · intro c hc
    simp only [blockRecOf, List.mem_map] at hc
    obtain ⟨⟨cv, nP, nF⟩, hm, rfl⟩ := hc
    exact hg.2.1 _ hm
  · intro r hr
    simp only [blockRecOf, List.mem_map] at hr
    obtain ⟨⟨cv, c, rules⟩, hm, rfl⟩ := hr
    exact ⟨(hg.2.2.2 _ hm).1, (hg.2.2.2 _ hm).2⟩

end Block

/-! ## What `lowerInductive` returns -/

section Lower

/-- **The generator's context at a block**, as `lowerInductive` builds it from
the reader's state: the declared types, the heights, and the parsed blocks
with the block's own members visible. -/
def genCtx (st : State md) (rb : BlockRead md) : Ctx md :=
  ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
   fun n => if (memberNamesOf rb).contains n then some (blockRecOf rb) else st.indBlocks[n]?⟩

/-- A block's own declaration. -/
def indDeclOf (rb : BlockRead md) : CDecl md :=
  .indDecl (rb.types.toList.map (fun (cv, _, _) => .indInfo cv {}) ++
      rb.ctors.toList.map (fun (cv, nP, nF) => .ctorInfo cv nP nF) ++
      rb.recs.toList.map fun (cv, r, rules) =>
        .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules)
    rb.numParams

/-- What the reader's state learns of the block itself (`Read.blocks`). -/
def blocksOf (rb : BlockRead md) : List (CName md × BlockRec md) :=
  (blockRecOf rb).types.map (·.cv.name, blockRecOf rb)

/-- An accepted `if` in `ReadM` is its condition's branch. -/
theorem ite_ok' {α : Type} {c : Prop} [Decidable c] {x y : Ix.Kernel.Reader.ReadM α} {r : α}
    (h : (if c then x else y) = .ok r) : (c ∧ x = .ok r) ∨ (¬c ∧ y = .ok r) := by
  by_cases hc : c
  · exact .inl ⟨hc, by simpa [hc] using h⟩
  · exact .inr ⟨hc, by simpa [hc] using h⟩

/-- **What an accepted `lowerInductiveDecls` returns**: the modeller's records
(`generate` at `genCtx`, when the block wants them), then the block's own
declaration; the block, by its members' names. -/
theorem lowerInductiveDecls_ok {st : State md} {rb : BlockRead md} {r : Read md}
    (h : Ix.Kernel.Reader.lowerInductiveDecls st rb = .ok r) :
    ∃ gens : List (CDecl md), r.decls = gens.toArray.push (indDeclOf rb) ∧ r.generated = gens.length ∧
      r.blocks = blocksOf rb ∧
      ((wants (blockRecOf rb) = true ∧ generate (genCtx st rb) (blockRecOf rb) = .ok gens) ∨
        (wants (blockRecOf rb) = false ∧ gens = [])) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  unfold Ix.Kernel.Reader.lowerInductiveDecls at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  all_goals
    rcases ite_ok' h with ⟨-, h⟩ | ⟨-, h⟩
    all_goals first
      | (obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h)
      | skip
    all_goals
      rcases ite_ok' h with ⟨hw, h⟩ | ⟨hw, h⟩
      · split at h
        · simp [Ix.Kernel.Reader.declined, throw, throwThe, MonadExceptOf.throw] at h
        · rename_i gen hgen
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨gen, rfl, rfl, rfl, .inl ⟨hw, hgen⟩⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨[], rfl, rfl, rfl, .inr ⟨Bool.eq_false_iff.mpr hw, rfl⟩⟩

/-- **What an accepted `lowerInductive` returns**: as `lowerInductiveDecls_ok`. -/
theorem lowerInductive_ok {st : State md} {rb : BlockRead md} {r : Read md}
    (h : Ix.Kernel.Reader.lowerInductive st rb = .ok r) :
    ∃ gens : List (CDecl md), r.decls = gens.toArray.push (indDeclOf rb) ∧ r.generated = gens.length ∧
      r.blocks = blocksOf rb ∧
      ((wants (blockRecOf rb) = true ∧ generate (genCtx st rb) (blockRecOf rb) = .ok gens) ∨
        (wants (blockRecOf rb) = false ∧ gens = [])) :=
  lowerInductiveDecls_ok (LowerDistinct.lowerInductiveDecls_of_ok h)

end Lower

/-! ## Agreeing states give agreeing contexts -/

section Agree

variable (f : md.Id → md'.Id) (P : KeyScope md)

/-- **Two reader states agree on a scope** under `f`: at every renamed good key
the renamed declared type, the same height and the renamed parsed block; and the
types and blocks at good keys are good. -/
structure StateAgree (st : State md) (st' : State md') : Prop where
  types : ∀ k : Key md, k.Good P →
    st'.constTypes[k.map f]? = (st.constTypes[k]?).map fun p => (p.1, p.2.mapKeys f)
  typesGood : ∀ k : Key md, k.Good P → ∀ p, st.constTypes[k]? = some p → p.2.Good P
  heights : ∀ k : Key md, k.Good P → st'.heights.getD (k.map f) 0 = st.heights.getD k 0
  blocks : ∀ k : Key md, k.Good P → st'.indBlocks[k.map f]? = (st.indBlocks[k]?).map (BlockRec.mapKeys f)
  blocksGood : ∀ k : Key md, k.Good P → ∀ b, st.indBlocks[k]? = some b → b.Good P

variable {f P}

/-- Membership of a renamed good key in a renamed list of good keys. -/
theorem contains_map (hf : InjOn f P) {ks : List (Key md)} (hks : ∀ k ∈ ks, k.Good P) {k : Key md}
    (hk : k.Good P) : (ks.map (Key.map f)).contains (k.map f) = ks.contains k := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨k', hk', he⟩
    rwa [Key.map_inj hf (hks k' hk') hk he] at hk'
  · intro h
    exact ⟨k, h, rfl⟩

/-- **Agreeing states give agreeing generator contexts** at a good block and its
renaming. -/
theorem ctxAgree_genCtx (hf : InjOn f P) {stS : State md} {stA : State md'} (hst : StateAgree f P stS stA)
    {rb : BlockRead md} (hg : rb.Good P) :
    CtxAgree f P (genCtx stS rb) (genCtx stA (rb.mapKeys f)) where
  tbl := ⟨hst.types, hst.typesGood⟩
  heights := hst.heights
  blocks := by
    intro k hk
    simp only [genCtx, memberNamesOf_mapKeys, contains_map hf (memberNamesOf_good hg) hk,
      blockRecOf_mapKeys hf hg]
    split
    · rfl
    · exact hst.blocks k hk
  blocksGood := by
    intro k hk b hb
    simp only [genCtx] at hb
    split at hb
    · cases hb; exact blockRecOf_good hg
    · exact hst.blocksGood k hk b hb

/-- A block's own declaration, renamed. -/
theorem indDeclOf_mapKeys (rb : BlockRead md) :
    indDeclOf (rb.mapKeys f) = (indDeclOf rb).mapKeys f := by
  simp [indDeclOf, Ix.Kernel.Reader.BlockRead.mapKeys, Declaration.mapKeys, Function.comp_def,
    ConstantInfo.mapKeys, IndCaps.mapKeys]

theorem wants_mapKeys (b : BlockRec md) : wants (b.mapKeys f) = wants b := by
  unfold wants
  simp only [BlockRec.mapKeys_types, List.length_map, List.any_map, Function.comp_def,
    IndTypeRec.mapKeys_numNested]
  rfl

/-- **A block and its renaming lower to renamed records** at agreeing states,
before their names are compared (`lowerInductiveDecls`): the modeller's records
renamed (IxC's parametricity, `generate_toOption_mapKeys`), then the renamed
block's declaration; the renamed block. -/
theorem lowerInductiveDecls_mapKeys (hP : P.Pre) (hf : InjOn f P) {stS : State md} {stA : State md'}
    (hst : StateAgree f P stS stA) {rb : BlockRead md} (hg : rb.Good P) {rS : Read md} {rA : Read md'}
    (hS : Ix.Kernel.Reader.lowerInductiveDecls stS rb = .ok rS)
    (hA : Ix.Kernel.Reader.lowerInductiveDecls stA (rb.mapKeys f) = .ok rA) :
    rA.decls = rS.decls.map (Declaration.mapKeys f) ∧ rA.generated = rS.generated ∧
      rA.blocks = rS.blocks.map fun (n, b) => (n.map f, b.mapKeys f) := by
  obtain ⟨gS, hdS, hnS, hbS, hwS⟩ := lowerInductiveDecls_ok hS
  obtain ⟨gA, hdA, hnA, hbA, hwA⟩ := lowerInductiveDecls_ok hA
  rw [blockRecOf_mapKeys hf hg, wants_mapKeys] at hwA
  have hgen : gA = gS.map (Declaration.mapKeys f) := by
    rcases hwS with ⟨hw, hgS⟩ | ⟨hw, rfl⟩
    · rcases hwA with ⟨-, hgA⟩ | ⟨hw', -⟩
      · have := generate_toOption_mapKeys hP hf (ctxAgree_genCtx hf hst hg) (blockRecOf_good hg)
        rw [hgA, hgS] at this
        simpa [Except.toOption] using this
      · rw [hw] at hw'; cases hw'
    · rcases hwA with ⟨hw', -⟩ | ⟨-, rfl⟩
      · rw [hw] at hw'; cases hw'
      · rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdA, hdS, hgen, indDeclOf_mapKeys]
    simp
  · rw [hnA, hnS, hgen, List.length_map]
  · rw [hbA, hbS, blocksOf, blocksOf, blockRecOf_mapKeys hf hg]
    simp [BlockRec.mapKeys, Function.comp_def, IndTypeRec.mapKeys]

/-- **A block and its renaming lower to renamed records** at agreeing states
(`lowerInductiveDecls_mapKeys`). -/
theorem lowerInductive_mapKeys (hP : P.Pre) (hf : InjOn f P) {stS : State md} {stA : State md'}
    (hst : StateAgree f P stS stA) {rb : BlockRead md} (hg : rb.Good P) {rS : Read md} {rA : Read md'}
    (hS : Ix.Kernel.Reader.lowerInductive stS rb = .ok rS)
    (hA : Ix.Kernel.Reader.lowerInductive stA (rb.mapKeys f) = .ok rA) :
    rA.decls = rS.decls.map (Declaration.mapKeys f) ∧ rA.generated = rS.generated ∧
      rA.blocks = rS.blocks.map fun (n, b) => (n.map f, b.mapKeys f) :=
  lowerInductiveDecls_mapKeys hP hf hst hg (LowerDistinct.lowerInductiveDecls_of_ok hS)
    (LowerDistinct.lowerInductiveDecls_of_ok hA)

end Agree

/-! ## The reader's state over a stream

`State.commit` records each read's blocks (`indBlocks`) and each of its
declarations' constants (`constTypes`, and a definition's height in
`heights`), in order, overwriting. So what a state holds at a key, after a
stream prefix, comes from an entry of the prefix naming that key, or from the
state it started from; it holds nothing there only if neither has one. -/

section Fold

/-- **What a declaration notes in the reader's state** (`State.note`): each of
its constants' name, level parameters and type, and a definition's height. -/
def noteEntries : CDecl md → List (CName md × List LevelParam × CExpr md × Option Nat)
  | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
  | .defnDecl cv _ h => [(cv.name, cv.levelParams, cv.type, some (hintHeight h))]
  | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
  | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
  | .basisDecl k => k.decls.map fun ci =>
    (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
  | .quotDecl _ cv => [(cv.name, cv.levelParams, cv.type, none)]
  | .indDecl block _ => block.map fun ci =>
    (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)

/-- A noted entry. -/
abbrev Entry (md : Mode) := CName md × List LevelParam × CExpr md × Option Nat

/-- An insert where `g` gives a key and a value. -/
def insOpt {α β γ : Type} [BEq α] [Hashable α] (g : γ → Option (α × β)) (m : Std.HashMap α β) (e : γ) :
    Std.HashMap α β :=
  match g e with
  | some (a, b) => m.insert a b
  | none => m

/-- An entry's declared type, under its name. -/
def tyOf (e : Entry md) : Option (CName md × (List LevelParam × CExpr md)) := some (e.1, e.2.1, e.2.2.1)

/-- An entry's height (a definition's), under its name. -/
def htOf (e : Entry md) : Option (CName md × Nat) := e.2.2.2.map (e.1, ·)

/-- **The entries a stream prefix notes**, in order. -/
def entriesOf (rs : List (Read md)) : List (Entry md) :=
  rs.flatMap fun r => r.decls.toList.flatMap noteEntries

/-- **The blocks a stream prefix records**, in order. -/
def blocksIn (rs : List (Read md)) : List (CName md × BlockRec md) := rs.flatMap (·.blocks)

theorem foldl_proj {σ τ α : Type} (p : σ → τ) (g : σ → α → σ) (G : τ → α → τ)
    (h : ∀ s x, p (g s x) = G (p s) x) : ∀ (l : List α) (s : σ), p (l.foldl g s) = l.foldl G (p s)
  | [], _ => rfl
  | x :: l, s => by simp only [List.foldl_cons]; rw [foldl_proj p g G h l, h]

theorem foldl_keep {σ τ α : Type} (p : σ → τ) (g : σ → α → σ) (h : ∀ s x, p (g s x) = p s) :
    ∀ (l : List α) (s : σ), p (l.foldl g s) = p s
  | [], _ => rfl
  | x :: l, s => by simp only [List.foldl_cons]; rw [foldl_keep p g h l, h]

theorem foldl_flatMap' {α β γ : Type} (f : α → List β) (g : γ → β → γ) :
    ∀ (l : List α) (init : γ), (l.flatMap f).foldl g init = l.foldl (fun acc x => (f x).foldl g acc) init
  | [], _ => rfl
  | x :: l, init => by
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]; exact foldl_flatMap' f g l _

theorem foldl_self {α γ : Type} : ∀ (l : List α) (init : γ), l.foldl (fun m _ => m) init = init
  | [], _ => rfl
  | _ :: l, init => foldl_self l init

theorem foldl_zipIdx_fst {α γ : Type} (g : γ → α → γ) :
    ∀ (l : List α) (k : Nat) (init : γ), (l.zipIdx k).foldl (fun acc x => g acc x.1) init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, k, init => by simp only [List.zipIdx_cons, List.foldl_cons]; exact foldl_zipIdx_fst g l _ _

theorem note_constTypes (st : State md) (d : CDecl md) :
    (st.note d).constTypes = (noteEntries d).foldl (insOpt tyOf) st.constTypes := by
  cases d <;>
    exact foldl_proj State.constTypes _ _ (fun s e => by obtain ⟨n, lps, ty, h⟩ := e; rfl) _ _

theorem note_heights (st : State md) (d : CDecl md) :
    (st.note d).heights = (noteEntries d).foldl (insOpt htOf) st.heights := by
  cases d <;>
    exact foldl_proj State.heights _ _ (fun s e => by obtain ⟨n, lps, ty, h⟩ := e; cases h <;> rfl) _ _

theorem note_indBlocks (st : State md) (d : CDecl md) : (st.note d).indBlocks = st.indBlocks := by
  cases d <;> (refine foldl_keep State.indBlocks _ (fun s e => ?_) _ _; rfl)

/-- `noteGenerated` notes as `note` does (it also registers a projection level). -/
theorem noteGenerated_fields (st : State md) (d : CDecl md) :
    (st.noteGenerated d).constTypes = (st.note d).constTypes ∧
      (st.noteGenerated d).heights = (st.note d).heights ∧
      (st.noteGenerated d).indBlocks = (st.note d).indBlocks := by
  unfold State.noteGenerated
  refine ⟨?_, ?_, ?_⟩ <;> (split <;> (try split) <;> (try split)) <;>
    simp only [note_constTypes, note_heights, note_indBlocks]

theorem commit_eq (st : State md) (r : Read md) : st.commit r =
    let s1 := r.owners.foldl (fun s o => { s with projOwners := s.projOwners.insert o.T o }) st
    let s2 := r.blocks.foldl (fun s x => { s with indBlocks := s.indBlocks.insert x.1 x.2 }) s1
    let s3 := r.decls.toList.zipIdx.foldl
      (fun s x => if x.2 < r.generated then s.noteGenerated x.1 else s.note x.1) s2
    { s3 with projRewrites := s3.projRewrites + r.projRewrites } := by
  simp only [State.commit, Id.run, List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl,
    pure_bind, ← Array.foldl_toList, Array.toList_zipIdx]
  rfl

/-- The owner and block loops of `commit` keep a field `p` both keep. -/
theorem commit_pre_keep {τ : Type} (p : State md → τ) (r : Read md) (st : State md)
    (ho : ∀ s (o : Ix.Kernel.Frontend.ProjRecOwner md), p { s with projOwners := s.projOwners.insert o.T o } = p s)
    (hb : ∀ s (x : CName md × BlockRec md), p { s with indBlocks := s.indBlocks.insert x.1 x.2 } = p s) :
    p (r.blocks.foldl (fun s x => { s with indBlocks := s.indBlocks.insert x.1 x.2 })
      (r.owners.foldl (fun s o => { s with projOwners := s.projOwners.insert o.T o }) st)) = p st := by
  rw [foldl_keep p _ hb, foldl_keep p _ ho]

/-- The declaration loop of `commit` on a field. -/
theorem commit_decls {τ : Type} (p : State md → τ) (G : τ → CDecl md → τ) (r : Read md) (st : State md)
    (h : ∀ (s : State md) (d : CDecl md), p (s.note d) = G (p s) d)
    (hg : ∀ (s : State md) (d : CDecl md), p (s.noteGenerated d) = p (s.note d)) :
    p (r.decls.toList.zipIdx.foldl
      (fun (s : State md) (x : CDecl md × Nat) => if x.2 < r.generated then s.noteGenerated x.1 else s.note x.1) st) =
      r.decls.toList.foldl G (p st) := by
  rw [foldl_proj p _ (fun m (x : CDecl md × Nat) => G m x.1) (fun s x => by
      split
      · rw [hg, h]
      · rw [h]),
    foldl_zipIdx_fst G]

theorem commit_constTypes (st : State md) (r : Read md) :
    (st.commit r).constTypes = (r.decls.toList.flatMap noteEntries).foldl (insOpt tyOf) st.constTypes := by
  rw [commit_eq]
  simp only
  rw [commit_decls State.constTypes (fun m d => (noteEntries d).foldl (insOpt tyOf) m) r _
      note_constTypes (fun s d => (noteGenerated_fields s d).1),
    commit_pre_keep State.constTypes r st (fun _ _ => rfl) (fun _ _ => rfl), foldl_flatMap']

theorem commit_heights (st : State md) (r : Read md) :
    (st.commit r).heights = (r.decls.toList.flatMap noteEntries).foldl (insOpt htOf) st.heights := by
  rw [commit_eq]
  simp only
  rw [commit_decls State.heights (fun m d => (noteEntries d).foldl (insOpt htOf) m) r _
      note_heights (fun s d => (noteGenerated_fields s d).2.1),
    commit_pre_keep State.heights r st (fun _ _ => rfl) (fun _ _ => rfl), foldl_flatMap']

theorem commit_indBlocks (st : State md) (r : Read md) :
    (st.commit r).indBlocks = r.blocks.foldl (insOpt some) st.indBlocks := by
  rw [commit_eq]
  simp only
  rw [commit_decls State.indBlocks (fun m _ => m) r _ note_indBlocks
      (fun s d => (noteGenerated_fields s d).2.2)]
  rw [foldl_self]
  rw [foldl_proj State.indBlocks (fun s (x : CName md × BlockRec md) =>
      { s with indBlocks := s.indBlocks.insert x.1 x.2 }) (insOpt some) (fun s x => rfl),
    foldl_keep State.indBlocks (fun s (o : Ix.Kernel.Frontend.ProjRecOwner md) =>
      { s with projOwners := s.projOwners.insert o.T o }) (fun s x => rfl)]

theorem fold_fields (st0 : State md) (rs : List (Read md)) :
    (rs.foldl State.commit st0).constTypes = (entriesOf rs).foldl (insOpt tyOf) st0.constTypes ∧
      (rs.foldl State.commit st0).heights = (entriesOf rs).foldl (insOpt htOf) st0.heights ∧
      (rs.foldl State.commit st0).indBlocks = (blocksIn rs).foldl (insOpt some) st0.indBlocks := by
  refine ⟨?_, ?_, ?_⟩
  · rw [entriesOf, foldl_flatMap']
    exact foldl_proj State.constTypes _ _ (fun s r => commit_constTypes s r) rs st0
  · rw [entriesOf, foldl_flatMap']
    exact foldl_proj State.heights _ _ (fun s r => commit_heights s r) rs st0
  · rw [blocksIn, foldl_flatMap']
    exact foldl_proj State.indBlocks _ _ (fun s r => commit_indBlocks s r) rs st0

section Sources

variable {α β γ : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- **What a fold of inserts holds at a key** comes from an entry or from the start. -/
theorem foldl_insOpt_some (g : γ → Option (α × β)) :
    ∀ (l : List γ) (m : Std.HashMap α β) {k : α} {v : β},
      (l.foldl (insOpt g) m)[k]? = some v → (∃ e ∈ l, g e = some (k, v)) ∨ m[k]? = some v
  | [], _, _, _, h => .inr h
  | e :: l, m, k, v, h => by
    rcases foldl_insOpt_some g l _ h with ⟨e', he', hg⟩ | h
    · exact .inl ⟨e', List.mem_cons_of_mem _ he', hg⟩
    · unfold insOpt at h
      split at h
      · rename_i a b hge
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i hak
          cases h
          exact .inl ⟨e, List.mem_cons_self, by rw [hge, eq_of_beq hak]⟩
        · exact .inr h
      · exact .inr h

/-- **A fold of inserts holds nothing at a key** exactly when no entry and not
the start names it. -/
theorem foldl_insOpt_none (g : γ → Option (α × β)) :
    ∀ (l : List γ) (m : Std.HashMap α β) {k : α},
      (l.foldl (insOpt g) m)[k]? = none ↔ (∀ e ∈ l, ∀ v, g e ≠ some (k, v)) ∧ m[k]? = none
  | [], _, _ => by simp
  | e :: l, m, k => by
    rw [List.foldl_cons, foldl_insOpt_none g l]
    constructor
    · rintro ⟨hl, hm⟩
      refine ⟨fun e' he' v hv => ?_, ?_⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · unfold insOpt at hm
          simp [hv] at hm
        · exact hl e' he' v hv
      · unfold insOpt at hm
        cases hge : g e with
        | none => rw [hge] at hm; exact hm
        | some p =>
          obtain ⟨a, b⟩ := p
          rw [hge] at hm
          simp only [Std.HashMap.getElem?_insert] at hm
          split at hm
          · cases hm
          · exact hm
    · rintro ⟨hl, hm⟩
      refine ⟨fun e' he' v hv => hl e' (List.mem_cons_of_mem _ he') v hv, ?_⟩
      unfold insOpt
      cases hge : g e with
      | none => exact hm
      | some p =>
        obtain ⟨a, b⟩ := p
        simp only [Std.HashMap.getElem?_insert]
        split
        · rename_i hak
          exact absurd (by rw [hge, eq_of_beq hak]) (hl e List.mem_cons_self b)
        · exact hm

end Sources

end Fold

/-! ## Agreeing sources give agreeing states

What the two states hold at a key is what their prefixes noted there (or the
start). When every pair of sources agrees under the renaming, and one side has a
source exactly when the other does, the states agree there. -/

section Sources

variable {α β γ : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- **A fold of inserts whose sources at a key all hold one value** holds it. -/
theorem foldl_insOpt_eq (g : γ → Option (α × β)) (l : List γ) (m : Std.HashMap α β) {k : α} {v : β}
    (hall : ∀ e ∈ l, ∀ w, g e = some (k, w) → w = v) (hm : ∀ w, m[k]? = some w → w = v)
    (hex : (∃ e ∈ l, g e = some (k, v)) ∨ m[k]? = some v) : (l.foldl (insOpt g) m)[k]? = some v := by
  cases hr : (l.foldl (insOpt g) m)[k]? with
  | none =>
    obtain ⟨hl, hm'⟩ := (foldl_insOpt_none g l m).mp hr
    rcases hex with ⟨e, he, hg⟩ | hm''
    · exact absurd hg (hl e he v)
    · rw [hm'] at hm''; cases hm''
  | some w =>
    rcases foldl_insOpt_some g l m hr with ⟨e, he, hg⟩ | hm'
    · rw [hall e he w hg]
    · rw [hm w hm']

end Sources

/-- An entry renamed. -/
def renE (f : md.Id → md'.Id) (e : Entry md) : Entry md' := (e.1.map f, e.2.1, e.2.2.1.mapKeys f, e.2.2.2)

/-- **A declaration's entries, renamed** (no basis declaration). -/
theorem noteEntries_mapKeys {d : CDecl md} (hd : ∀ k, d ≠ .basisDecl k) :
    noteEntries (d.mapKeys f) = (noteEntries d).map (renE f) := by
  cases d with
  | basisDecl k => exact absurd rfl (hd k)
  | indDecl block _ =>
    simp [noteEntries, Declaration.mapKeys, renE, Function.comp_def, ConstantInfo.mapKeys_toConstantVal]
  | _ => rfl

theorem tyOf_renE (e : Entry md) :
    tyOf (renE f e) = (tyOf e).map fun p => (p.1.map f, (p.2.1, p.2.2.mapKeys f)) := rfl

theorem htOf_name {e : Entry md} {k : CName md} {w : Nat} (h : htOf e = some (k, w)) : e.1 = k := by
  unfold htOf at h
  cases hh : e.2.2.2 with
  | none => rw [hh] at h; cases h
  | some x => rw [hh] at h; cases h; rfl

theorem htOf_renE (e : Entry md) : htOf (renE f e) = (htOf e).map fun p => (p.1.map f, p.2) := by
  obtain ⟨n, lps, ty, h⟩ := e
  cases h <;> rfl

theorem Key.base_map (k : Key md) : (k.map f).base = k.base.map f := by
  induction k with
  | aux k d ih => simpa [Key.base] using ih
  | _ => rfl

theorem Key.good_base {P : KeyScope md} : ∀ {k : Key md}, k.Good P → k.base.Good P
  | .aux k _, h => Key.good_base (k := k) h
  | .id _, h => h
  | .role _, h => h

theorem Key.base_isAux : ∀ k : Key md, k.base.isAux = false
  | .aux k _ => Key.base_isAux k
  | .id _ => rfl
  | .role _ => rfl

/-- **An entry of a stream prefix** is one of an earlier unit's declarations'. -/
theorem mem_entriesOf_take {rs : List (Read md)} {i : Nat} {e : Entry md} :
    e ∈ entriesOf (rs.take i) ↔
      ∃ i' r, i' < i ∧ rs[i']? = some r ∧ ∃ d ∈ r.decls.toList, e ∈ noteEntries d := by
  simp only [entriesOf, List.mem_flatMap, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨r, ⟨i', hi', rfl⟩, d, hd, he⟩
    exact ⟨i', _, (Nat.lt_min.mp hi').1, List.getElem?_eq_getElem _, d, hd, he⟩
  · rintro ⟨i', r, hi', hr, d, hd, he⟩
    obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨_, ⟨i', Nat.lt_min.mpr ⟨hi', hl⟩, rfl⟩, d, hd, he⟩

/-- An entry of the stream. -/
theorem mem_entriesOf {rs : List (Read md)} {i : Nat} {r : Read md} (hr : rs[i]? = some r)
    {d : CDecl md} (hd : d ∈ r.decls.toList) {e : Entry md} (he : e ∈ noteEntries d) : e ∈ entriesOf rs := by
  simp only [entriesOf, List.mem_flatMap]
  exact ⟨r, List.mem_of_getElem? hr, d, hd, he⟩

/-- The state before unit `i` of a stream. -/
def stAt (st0 : State md) (rs : List (Read md)) (i : Nat) : State md := (rs.take i).foldl State.commit st0

/-- **The per-key relation at a block's time, off the derived keys**: at every
good key that is not derived, the renamed declared type, the same height; at
every good key the renamed parsed block; and every type and block at a good key
(derived ones included) is good. -/
structure NonAuxAgree (f : md.Id → md'.Id) (P : KeyScope md) (st : State md) (st' : State md') : Prop where
  types : ∀ k : Key md, k.Good P → k.isAux = false →
    st'.constTypes[k.map f]? = (st.constTypes[k]?).map fun p => (p.1, p.2.mapKeys f)
  typesGood : ∀ k : Key md, k.Good P → ∀ p, st.constTypes[k]? = some p → p.2.Good P
  heights : ∀ k : Key md, k.Good P → k.isAux = false → st'.heights.getD (k.map f) 0 = st.heights.getD k 0
  blocks : ∀ k : Key md, k.Good P → st'.indBlocks[k.map f]? = (st.indBlocks[k]?).map (BlockRec.mapKeys f)
  blocksGood : ∀ k : Key md, k.Good P → ∀ b, st.indBlocks[k]? = some b → b.Good P

/-- A block's names: its declaration's. -/
def blockNames (rb : BlockRead md) : List (CName md) := (noteEntries (indDeclOf rb)).map (·.1)

theorem flatMap_congr' {α β : Type} {l : List α} {g h : α → List β} (e : ∀ x ∈ l, g x = h x) :
    l.flatMap g = l.flatMap h := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, e x List.mem_cons_self, ih fun y hy => e y (List.mem_cons_of_mem _ hy)]

/-- A read's generated declarations' entries. -/
def genEntries (r : Read md) : List (Entry md) := (r.decls.toList.take r.generated).flatMap noteEntries

/-- **A unit agrees with its partner**: renamed declarations, as many generated,
renamed blocks. -/
def UnitAgree (f : md.Id → md'.Id) (rS : Read md) (rA : Read md') : Prop :=
  rA.decls = rS.decls.map (Declaration.mapKeys f) ∧ rA.generated = rS.generated ∧
    rA.blocks = rS.blocks.map fun (n, b) => (n.map f, b.mapKeys f)

theorem UnitAgree.gen_entries {rS : Read md} {rA : Read md'} (h : UnitAgree f rS rA)
    (hb : ∀ d ∈ rS.decls.toList, ∀ k, d ≠ .basisDecl k) :
    genEntries rA = (genEntries rS).map (renE f) := by
  obtain ⟨hd, hg, -⟩ := h
  simp only [genEntries, hd, hg, Array.toList_map, ← List.map_take, List.flatMap_map, List.map_flatMap]
  exact flatMap_congr' fun d hd' => noteEntries_mapKeys (hb d (List.mem_of_mem_take hd'))

/-! ## The per-key relation, read off the two streams

`NonAuxAgree` is what the two states hold. What makes it hold is what the two
prefixes read (`ReadsAgreeAt`): at a key, every type, height and block either
prefix noted (or its start held) agrees with every one the other noted at the
renamed key, and one side noted one exactly when the other did. -/

section Reads

/-- A type the prefix `l` from `st0` holds a source of at `k`. -/
def TySrc (st0 : State md) (l : List (Read md)) (k : CName md) (v : List LevelParam × CExpr md) : Prop :=
  (∃ e ∈ entriesOf l, tyOf e = some (k, v)) ∨ st0.constTypes[k]? = some v

/-- A height the prefix `l` from `st0` holds a source of at `k`. -/
def HtSrc (st0 : State md) (l : List (Read md)) (k : CName md) (h : Nat) : Prop :=
  (∃ e ∈ entriesOf l, htOf e = some (k, h)) ∨ st0.heights[k]? = some h

/-- A block the prefix `l` from `st0` holds a source of at `k`. -/
def BkSrc (st0 : State md) (l : List (Read md)) (k : CName md) (b : BlockRec md) : Prop :=
  (∃ e ∈ blocksIn l, some e = some (k, b)) ∨ st0.indBlocks[k]? = some b

/-- **Both prefixes read renamed-equal declarations at a key**: every two sources
agree under `f`, and one side has one exactly when the other does. -/
structure ReadsAgreeAt (f : md.Id → md'.Id) (st0S : State md) (lS : List (Read md)) (st0A : State md')
    (lA : List (Read md')) (k : Key md) : Prop where
  ty : ∀ v w, TySrc st0S lS k v → TySrc st0A lA (k.map f) w → w = (v.1, v.2.mapKeys f)
  tyIff : (∃ v, TySrc st0S lS k v) ↔ ∃ w, TySrc st0A lA (k.map f) w
  ht : ∀ h h', HtSrc st0S lS k h → HtSrc st0A lA (k.map f) h' → h' = h
  htIff : (∃ h, HtSrc st0S lS k h) ↔ ∃ h', HtSrc st0A lA (k.map f) h'
  bk : ∀ b b', BkSrc st0S lS k b → BkSrc st0A lA (k.map f) b' → b' = b.mapKeys f
  bkIff : (∃ b, BkSrc st0S lS k b) ↔ ∃ b', BkSrc st0A lA (k.map f) b'

section Generic

variable {α β γ α' β' γ' : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
  [BEq α'] [Hashable α'] [LawfulBEq α'] [LawfulHashable α']

/-- **Two folds of inserts agree at two keys** when their sources there agree and
one has a source exactly when the other does. -/
theorem foldl_insOpt_agree (g : γ → Option (α × β)) (g' : γ' → Option (α' × β')) (l : List γ)
    (l' : List γ') (m : Std.HashMap α β) (m' : Std.HashMap α' β') (k : α) (k' : α') (ρ : β → β')
    (agree : ∀ v w, ((∃ e ∈ l, g e = some (k, v)) ∨ m[k]? = some v) →
      ((∃ e ∈ l', g' e = some (k', w)) ∨ m'[k']? = some w) → w = ρ v)
    (iff : (∃ v, (∃ e ∈ l, g e = some (k, v)) ∨ m[k]? = some v) ↔
      ∃ w, (∃ e ∈ l', g' e = some (k', w)) ∨ m'[k']? = some w) :
    (l'.foldl (insOpt g') m')[k']? = ((l.foldl (insOpt g) m)[k]?).map ρ := by
  cases hv : (l.foldl (insOpt g) m)[k]? with
  | none =>
    obtain ⟨hl, hm⟩ := (foldl_insOpt_none g l m).mp hv
    refine (foldl_insOpt_none g' l' m').mpr ⟨fun e he w hw => ?_, ?_⟩
    · obtain ⟨v, hv'⟩ := iff.mpr ⟨w, .inl ⟨e, he, hw⟩⟩
      rcases hv' with ⟨e', he', hge⟩ | hm'
      · exact hl e' he' v hge
      · rw [hm] at hm'; cases hm'
    · cases hm'' : m'[k']? with
      | none => rfl
      | some w =>
        obtain ⟨v, hv'⟩ := iff.mpr ⟨w, .inr hm''⟩
        rcases hv' with ⟨e', he', hge⟩ | hm'
        · exact absurd hge (hl e' he' v)
        · rw [hm] at hm'; cases hm'
  | some v =>
    have src := foldl_insOpt_some g l m hv
    obtain ⟨w, hw⟩ := iff.mp ⟨v, src⟩
    cases hw' : (l'.foldl (insOpt g') m')[k']? with
    | none =>
      obtain ⟨hl', hm'⟩ := (foldl_insOpt_none g' l' m').mp hw'
      rcases hw with ⟨e, he, hge⟩ | hm''
      · exact absurd hge (hl' e he w)
      · rw [hm'] at hm''; cases hm''
    | some w' => rw [agree v w' src (foldl_insOpt_some g' l' m' hw')]; rfl

end Generic

variable {st0S : State md} {lS : List (Read md)} {st0A : State md'} {lA : List (Read md')}

/-- **The per-key relation from what the prefixes read**: at a key where they read
renamed-equal declarations, the two states agree. -/
theorem ReadsAgreeAt.states {k : Key md} (h : ReadsAgreeAt f st0S lS st0A lA k) :
    (lA.foldl State.commit st0A).constTypes[k.map f]? =
        ((lS.foldl State.commit st0S).constTypes[k]?).map (fun p => (p.1, p.2.mapKeys f)) ∧
      (lA.foldl State.commit st0A).heights.getD (k.map f) 0 = (lS.foldl State.commit st0S).heights.getD k 0 ∧
      (lA.foldl State.commit st0A).indBlocks[k.map f]? =
        ((lS.foldl State.commit st0S).indBlocks[k]?).map (BlockRec.mapKeys f) := by
  obtain ⟨tS, hS, bS⟩ := fold_fields st0S lS
  obtain ⟨tA, hA, bA⟩ := fold_fields st0A lA
  refine ⟨?_, ?_, ?_⟩
  · rw [tS, tA]
    exact foldl_insOpt_agree tyOf tyOf _ _ _ _ k (k.map f) _ h.ty h.tyIff
  · rw [hS, hA, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?,
      foldl_insOpt_agree htOf htOf _ _ _ _ k (k.map f) id h.ht h.htIff, Option.map_id, id_eq]
  · rw [bS, bA]
    exact foldl_insOpt_agree some some _ _ _ _ k (k.map f) _ h.bk h.bkIff

/-- **`NonAuxAgree` from the per-key relation** at every good key but the derived
ones (and the blocks at every good key), with the goodness of what the Source
state holds. -/
theorem nonAuxAgree_of_reads {P : KeyScope md}
    (reads : ∀ k : Key md, k.Good P → k.isAux = false → ReadsAgreeAt f st0S lS st0A lA k)
    (readsBlocks : ∀ k : Key md, k.Good P →
      (lA.foldl State.commit st0A).indBlocks[k.map f]? =
        ((lS.foldl State.commit st0S).indBlocks[k]?).map (BlockRec.mapKeys f))
    (typesGood : ∀ k : Key md, k.Good P → ∀ p, (lS.foldl State.commit st0S).constTypes[k]? = some p → p.2.Good P)
    (blocksGood : ∀ k : Key md, k.Good P → ∀ b, (lS.foldl State.commit st0S).indBlocks[k]? = some b → b.Good P) :
    NonAuxAgree f P (lS.foldl State.commit st0S) (lA.foldl State.commit st0A) where
  types k hk hx := ((reads k hk hx).states).1
  typesGood := typesGood
  heights k hk hx := ((reads k hk hx).states).2.1
  blocks := readsBlocks
  blocksGood := blocksGood

end Reads

/-! ## The cone induction

The two streams lower each block at their own states; the Source stream's
block units are numbered by position, and each has its Ixon partner (`π`). At a
block's time, the per-key relation (`NonAuxAgree`, named) covers every key but
the derived ones; a derived key's entries are the generated records of an earlier
block of the cone, on both sides, so they agree by the same theorem at that
block. That is the induction. -/

section Cone

/-- **The two streams, for the cone induction** (`f` renames Source keys to Ixon
keys; `π` gives a Source unit its Ixon unit; `blk` the block a Source unit lowers;
`P i` a block unit's scope; `Q` a scope `f` is injective on, holding every key the
Source stream notes):
* every block unit lowers its block at its state, and its partner the renamed
  block at the partner's state; the block is good in its scope;
* a unit generating a record at a key of a block's scope is a block unit, on both
  sides (on the Ixon side, before the block's partner: a partner);
* no derived key is in either start, and only generated records note one;
* a generated record's names are derived from its block's names (on the Ixon
  side, the renamed names);
* a block unit whose block meets another's scope comes before it, on both sides;
* the Source stream notes a derived key once;
* no declaration is a basis declaration;
* **the per-key relation** at every block's time (`NonAuxAgree`): what the two
  streams read for every key but the derived ones agrees under `f`, and every
  type and block at a good key is good. -/
structure Streams (f : md.Id → md'.Id) (st0S : State md) (rsS : List (Read md)) (st0A : State md')
    (rsA : List (Read md')) (π : Nat → Nat) (blk : Nat → Option (BlockRead md)) (P : Nat → KeyScope md)
    (Q : KeyScope md) : Prop where
  inj : InjOn f Q
  keysQ : ∀ e ∈ entriesOf rsS, e.1.Good Q
  scope : ∀ i, (∀ x, (P i) x → Q x) ∧ ∀ r, (P i).role r → Q.role r
  pre : ∀ i, (P i).Pre
  lower : ∀ i rb, blk i = some rb → ∃ rS rA, rsS[i]? = some rS ∧ rsA[π i]? = some rA ∧
    Ix.Kernel.Reader.lowerInductive (stAt st0S rsS i) rb = .ok rS ∧
    Ix.Kernel.Reader.lowerInductive (stAt st0A rsA (π i)) (rb.mapKeys f) = .ok rA ∧ rb.Good (P i)
  genS : ∀ i rb i' r, blk i = some rb → rsS[i']? = some r → (∃ e ∈ genEntries r, e.1.Good (P i)) →
    ∃ rb', blk i' = some rb'
  genA : ∀ i rb j r, blk i = some rb → rsA[j]? = some r → j < π i →
    (∃ e ∈ genEntries r, ∃ k : Key md, k.Good (P i) ∧ e.1 = k.map f) → ∃ i' rb', blk i' = some rb' ∧ π i' = j
  startS : ∀ k : Key md, k.isAux = true → st0S.constTypes[k]? = none ∧ st0S.heights[k]? = none
  startA : ∀ k : Key md', k.isAux = true → st0A.constTypes[k]? = none ∧ st0A.heights[k]? = none
  ownS : ∀ r ∈ rsS, ∀ d ∈ r.decls.toList.drop r.generated, ∀ e ∈ noteEntries d, e.1.isAux = false
  ownA : ∀ r ∈ rsA, ∀ d ∈ r.decls.toList.drop r.generated, ∀ e ∈ noteEntries d, e.1.isAux = false
  baseS : ∀ i rb r, blk i = some rb → rsS[i]? = some r → ∀ e ∈ genEntries r, e.1.base ∈ blockNames rb
  baseA : ∀ i rb r, blk i = some rb → rsA[π i]? = some r → ∀ e ∈ genEntries r,
    e.1.base ∈ (blockNames rb).map (Key.map f)
  order : ∀ i i' rb rb', blk i = some rb → blk i' = some rb' → i' ≠ i →
    (∃ n ∈ blockNames rb', n.Good (P i)) → i' < i ∧ π i' < π i
  uniq : ∀ e₁ ∈ entriesOf rsS, ∀ e₂ ∈ entriesOf rsS, e₁.1 = e₂.1 → e₁.1.isAux = true → e₁ = e₂
  basis : ∀ r ∈ rsS, ∀ d ∈ r.decls.toList, ∀ k, d ≠ .basisDecl k
  named : ∀ i rb, blk i = some rb → NonAuxAgree f (P i) (stAt st0S rsS i) (stAt st0A rsA (π i))

variable {st0S : State md} {rsS : List (Read md)} {st0A : State md'} {rsA : List (Read md')}
  {π : Nat → Nat} {blk : Nat → Option (BlockRead md)} {P : Nat → KeyScope md} {Q : KeyScope md}

theorem Key.map_isAux (k : Key md) : (k.map f).isAux = k.isAux := by cases k <;> rfl

/-- A derived entry of a prefix is a generated record's. -/
theorem prefix_gen {rs : List (Read md)}
    (own : ∀ r ∈ rs, ∀ d ∈ r.decls.toList.drop r.generated, ∀ e ∈ noteEntries d, e.1.isAux = false)
    {i : Nat} {e : Entry md} (he : e ∈ entriesOf (rs.take i)) (hx : e.1.isAux = true) :
    ∃ i' r, i' < i ∧ rs[i']? = some r ∧ e ∈ genEntries r := by
  obtain ⟨i', r, hi', hr, d, hd, hed⟩ := mem_entriesOf_take.mp he
  refine ⟨i', r, hi', hr, ?_⟩
  rw [← List.take_append_drop r.generated r.decls.toList, List.mem_append] at hd
  rcases hd with hd | hd
  · exact List.mem_flatMap.mpr ⟨d, hd, hed⟩
  · rw [own r (List.mem_of_getElem? hr) d hd e hed] at hx; cases hx

/-- A generated entry is an entry of its read. -/
theorem genEntries_sub {r : Read md} {e : Entry md} (he : e ∈ genEntries r) :
    ∃ d ∈ r.decls.toList, e ∈ noteEntries d := by
  obtain ⟨d, hd, hed⟩ := List.mem_flatMap.mp he
  exact ⟨d, List.mem_of_mem_take hd, hed⟩

theorem entriesOf_take_sub {rs : List (Read md)} {i : Nat} {e : Entry md} (he : e ∈ entriesOf (rs.take i)) :
    e ∈ entriesOf rs := by
  obtain ⟨i', r, -, hr, d, hd, hed⟩ := mem_entriesOf_take.mp he
  exact mem_entriesOf hr hd hed

namespace Streams

variable (h : Streams f st0S rsS st0A rsA π blk P Q)
include h

theorem good_mono (i : Nat) {k : Key md} (hk : k.Good (P i)) : k.Good Q :=
  Key.Good.mono (h.scope i).1 (h.scope i).2 hk

theorem injOn (i : Nat) : InjOn f (P i) := h.inj.mono (h.scope i).1

/-- A block unit's names are good in `Q`. -/
theorem blockNames_good {i : Nat} {rb : BlockRead md} (hb : blk i = some rb) :
    ∀ n ∈ blockNames rb, n.Good Q := by
  obtain ⟨rS, -, hrS, -, hlS, -, -⟩ := h.lower i rb hb
  obtain ⟨gens, hd, -, -, -⟩ := lowerInductive_ok hlS
  intro n hn
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
  refine h.keysQ e (mem_entriesOf hrS (d := indDeclOf rb) ?_ he)
  rw [hd]; simp

/-- **Source to Ixon**: a derived entry of the Source prefix before block `i`, at a
key good in its scope, is renamed in the Ixon prefix before `π i`, given the
units before `i` agree. -/
theorem to_ixon {i : Nat} {rb : BlockRead md} (hb : blk i = some rb)
    (IH : ∀ i' < i, ∀ rb', blk i' = some rb' → ∃ rS rA, rsS[i']? = some rS ∧ rsA[π i']? = some rA ∧
      UnitAgree f rS rA)
    {e : Entry md} (he : e ∈ entriesOf (rsS.take i)) (hk : e.1.Good (P i)) (hx : e.1.isAux = true) :
    renE f e ∈ entriesOf (rsA.take (π i)) := by
  obtain ⟨i', r, hi', hr, hg⟩ := prefix_gen h.ownS he hx
  obtain ⟨rb', hb'⟩ := h.genS i rb i' r hb hr ⟨e, hg, hk⟩
  have hbase := h.baseS i' rb' r hb' hr e hg
  obtain ⟨-, hπ⟩ := h.order i i' rb rb' hb hb' (Nat.ne_of_lt hi') ⟨_, hbase, Key.good_base hk⟩
  obtain ⟨rS, rA, hrS, hrA, hU⟩ := IH i' hi' rb' hb'
  rw [hr] at hrS; cases hrS
  have hgA : renE f e ∈ genEntries rA := by
    rw [hU.gen_entries (h.basis r (List.mem_of_getElem? hr))]
    exact List.mem_map_of_mem hg
  obtain ⟨d, hd, hed⟩ := genEntries_sub hgA
  exact mem_entriesOf_take.mpr ⟨π i', rA, hπ, hrA, d, hd, hed⟩

/-- **Ixon to Source**: a derived entry of the Ixon prefix before `π i`, at the
renaming of a key good in block `i`'s scope, is the renaming of a Source entry
at that key before `i`, given the units before `i` agree. -/
theorem to_source {i : Nat} {rb : BlockRead md} (hb : blk i = some rb)
    (IH : ∀ i' < i, ∀ rb', blk i' = some rb' → ∃ rS rA, rsS[i']? = some rS ∧ rsA[π i']? = some rA ∧
      UnitAgree f rS rA)
    {k : Key md} (hk : k.Good (P i)) (hx : k.isAux = true)
    {e' : Entry md'} (he' : e' ∈ entriesOf (rsA.take (π i))) (hn : e'.1 = k.map f) :
    ∃ e ∈ entriesOf (rsS.take i), e.1 = k ∧ e' = renE f e := by
  have hx' : e'.1.isAux = true := by rw [hn, Key.map_isAux]; exact hx
  obtain ⟨j, r', hj, hr', hg'⟩ := prefix_gen h.ownA he' hx'
  obtain ⟨i', rb', hb', rfl⟩ := h.genA i rb j r' hb hr' hj ⟨e', hg', k, hk, hn⟩
  have hbase := h.baseA i' rb' r' hb' hr' e' hg'
  obtain ⟨n, hnm, hnf⟩ := List.mem_map.mp hbase
  have hkQ := h.good_mono i hk
  have hnk : n = k.base := by
    refine Key.map_inj h.inj (h.blockNames_good hb' n hnm) (Key.good_base hkQ) ?_
    rw [hnf, hn, Key.base_map]
  have hne : i' ≠ i := by rintro rfl; exact Nat.lt_irrefl _ hj
  obtain ⟨hi', -⟩ := h.order i i' rb rb' hb hb' hne ⟨n, hnm, hnk ▸ Key.good_base hk⟩
  obtain ⟨rS, rA, hrS, hrA, hU⟩ := IH i' hi' rb' hb'
  rw [hr'] at hrA; cases hrA
  have hbS := h.basis rS (List.mem_of_getElem? hrS)
  rw [hU.gen_entries hbS] at hg'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg'
  obtain ⟨d, hd, hed⟩ := genEntries_sub he
  have heS : e ∈ entriesOf rsS := mem_entriesOf hrS hd hed
  have hek : e.1 = k := Key.map_inj h.inj (h.keysQ e heS) hkQ hn
  exact ⟨e, mem_entriesOf_take.mpr ⟨i', rS, hi', hrS, d, hd, hed⟩, hek, rfl⟩

/-- **At a derived key of a block's scope, the two states agree**, given the
units before it agree: the renamed declared type and the same height. -/
theorem aux_agree {i : Nat} {rb : BlockRead md} (hb : blk i = some rb)
    (IH : ∀ i' < i, ∀ rb', blk i' = some rb' → ∃ rS rA, rsS[i']? = some rS ∧ rsA[π i']? = some rA ∧
      UnitAgree f rS rA)
    {k : Key md} (hk : k.Good (P i)) (hx : k.isAux = true) :
    (stAt st0A rsA (π i)).constTypes[k.map f]? =
        ((stAt st0S rsS i).constTypes[k]?).map (fun p => (p.1, p.2.mapKeys f)) ∧
      (stAt st0A rsA (π i)).heights[k.map f]? = (stAt st0S rsS i).heights[k]? := by
  obtain ⟨tS, hS, -⟩ := fold_fields st0S (rsS.take i)
  obtain ⟨tA, hA, -⟩ := fold_fields st0A (rsA.take (π i))
  have hxA : (k.map f).isAux = true := by rw [Key.map_isAux]; exact hx
  obtain ⟨s0t, s0h⟩ := h.startS k hx
  obtain ⟨a0t, a0h⟩ := h.startA _ hxA
  simp only [stAt]
  rw [tS, tA, hS, hA]
  -- every Ixon entry at the renamed key is a Source entry's renaming, and the
  -- Source entries at the key are one
  have hone : ∀ e₁ ∈ entriesOf (rsS.take i), ∀ e₂ ∈ entriesOf (rsS.take i), e₁.1 = k → e₂.1 = k → e₁ = e₂ :=
    fun e₁ h₁ e₂ h₂ hk₁ hk₂ => h.uniq e₁ (entriesOf_take_sub h₁) e₂ (entriesOf_take_sub h₂)
      (hk₁.trans hk₂.symm) (hk₁ ▸ hx)
  refine ⟨?_, ?_⟩
  · cases hv : ((entriesOf (rsS.take i)).foldl (insOpt tyOf) st0S.constTypes)[k]? with
    | none =>
      obtain ⟨hl, -⟩ := (foldl_insOpt_none tyOf _ _).mp hv
      refine (foldl_insOpt_none tyOf _ _).mpr ⟨fun e' he' w hw => ?_, a0t⟩
      simp only [tyOf, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨e, he, hek, rfl⟩ := h.to_source hb IH hk hx he' hw.1
      exact hl e he (e.2.1, e.2.2.1) (by simp [tyOf, hek])
    | some v =>
      rcases foldl_insOpt_some tyOf _ _ hv with ⟨e, he, hev⟩ | h0
      · simp only [tyOf, Option.some.injEq, Prod.mk.injEq] at hev
        obtain ⟨hek, rfl⟩ := hev
        refine foldl_insOpt_eq tyOf _ _ (fun e' he' w hw => ?_) (fun w hw => by rw [a0t] at hw; cases hw)
          (.inl ⟨renE f e, h.to_ixon hb IH he (hek ▸ hk) (hek ▸ hx), by simp [tyOf, renE, hek]⟩)
        simp only [tyOf, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨e₂, he₂, he₂k, rfl⟩ := h.to_source hb IH hk hx he' hw.1
        rw [hone e₂ he₂ e he he₂k hek] at hw
        rw [← hw.2]; rfl
      · rw [s0t] at h0; cases h0
  · cases hv : ((entriesOf (rsS.take i)).foldl (insOpt htOf) st0S.heights)[k]? with
    | none =>
      obtain ⟨hl, -⟩ := (foldl_insOpt_none htOf _ _).mp hv
      refine (foldl_insOpt_none htOf _ _).mpr ⟨fun e' he' w hw => ?_, a0h⟩
      obtain ⟨e, he, hek, rfl⟩ := h.to_source hb IH hk hx he' (htOf_name hw)
      rw [htOf_renE] at hw
      refine hl e he w ?_
      cases hht : htOf e with
      | none => rw [hht] at hw; cases hw
      | some p =>
        rw [hht] at hw
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨-, rfl⟩ := hw
        rw [← hek, htOf_name hht]
    | some v =>
      rcases foldl_insOpt_some htOf _ _ hv with ⟨e, he, hev⟩ | h0
      · have hek : e.1 = k := htOf_name hev
        refine foldl_insOpt_eq htOf _ _ (fun e' he' w hw => ?_) (fun w hw => by rw [a0h] at hw; cases hw)
          (.inl ⟨renE f e, h.to_ixon hb IH he (hek ▸ hk) (hek ▸ hx), by rw [htOf_renE, hev]; simp⟩)
        obtain ⟨e₂, he₂, he₂k, rfl⟩ := h.to_source hb IH hk hx he' (htOf_name hw)
        rw [hone e₂ he₂ e he he₂k hek, htOf_renE, hev] at hw
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
        exact hw.2.symm
      · rw [s0h] at h0; cases h0

/-- **Every block unit agrees with its partner** (the cone induction): renamed
declarations (the generated records included), as many generated, renamed
blocks. -/
theorem units : ∀ i rb, blk i = some rb →
    ∃ rS rA, rsS[i]? = some rS ∧ rsA[π i]? = some rA ∧ UnitAgree f rS rA := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i IH =>
    intro rb hb
    obtain ⟨rS, rA, hrS, hrA, hlS, hlA, hg⟩ := h.lower i rb hb
    have hN := h.named i rb hb
    have hst : StateAgree f (P i) (stAt st0S rsS i) (stAt st0A rsA (π i)) :=
      { types := fun k hk => by
          cases hx : k.isAux
          · exact hN.types k hk hx
          · exact (h.aux_agree hb IH hk hx).1
        typesGood := hN.typesGood
        heights := fun k hk => by
          cases hx : k.isAux
          · exact hN.heights k hk hx
          · simp only [Std.HashMap.getD_eq_getD_getElem?, (h.aux_agree hb IH hk hx).2]
        blocks := hN.blocks
        blocksGood := hN.blocksGood }
    exact ⟨rS, rA, hrS, hrA, lowerInductive_mapKeys (h.pre i) (h.injOn i) hst hg hlS hlA⟩

end Streams

end Cone

end Ix.Cert.CtxAgree
