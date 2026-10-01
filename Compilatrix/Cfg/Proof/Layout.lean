import Compilatrix.Cfg.Lower
import Compilatrix.Cfg.Proof.Fuel
import Compilatrix.Src.Proof.NatMap

/-! # `Cfg.lower`'s block layout

What `Cfg.Lower.code` emits, as M2.4's `Cfg.lower_correct` needs it:

* `code_frame`: lowering `c` into block `cur` with fresh labels from
  `next` writes only `cur` and the `count c` labels from `next`;
* `Impl B self J cur params acc next c` (by recursion on `c`, as `count`
  lays it out): the blocks `B` hold what lowering `c` emits. A `bind`
  appends to the current block; a join point's scope continues the block
  and its body opens block `next + count k` with the join parameters; a
  `case` ends the block with a `switch` whose arms open blocks in order,
  then the default; a self tail call is a back edge to block 0;
* `code_impl`: the output of `code` implements `c` (later emissions never
  overwrite earlier labels), so every function of `Cfg.lower q` does
  (`function_impl`);
* `lower_ordered`: every forward edge goes to a higher label (join points
  in scope are above the code that jumps to them, arms above their
  `switch`), so `Cfg.lower q` is `Cfg.Ordered` and its runs are the clocked
  outcomes of its steps (`Cfg.runs_run`). -/

set_option autoImplicit false

namespace Compilatrix.Cfg.Proof

open Compilatrix.Fir (Var FunId JoinId Arg)
open Compilatrix.Cfg.Lower
open Compilatrix.Src (NatMap)

/-- `cfg_omega` after unfolding the name types (`BlockId`, `Var`, `JoinId`,
`FunId` are `Nat`, which `cfg_omega` does not see through). -/
macro "cfg_omega" : tactic =>
  `(tactic| ((try dsimp only [Compilatrix.Cfg.BlockId, Compilatrix.Fir.Var, Compilatrix.Fir.JoinId,
    Compilatrix.Fir.FunId] at *) <;> omega))

/-! ## Labels written -/

/-- The labels lowering `c` into `cur` with fresh labels from `next` owns. -/
def Owns (cur next n L : Nat) : Prop := L = cur ∨ (next ≤ L ∧ L < next + n)

theorem finish_get (out : Out) (cur : BlockId) (params : List (Var × Own.PSig)) (acc : List Instr)
    (t : Term) (L : Nat) :
    (finish out cur params acc t).get? L =
      if L = cur then some { params, body := acc.reverse, term := t } else out.get? L := by
  simp only [finish, NatMap.get?_insert]

mutual

/-- Lowering writes only the labels it owns. -/
theorem code_frame (self : FunId) :
    ∀ (J : JScope) (cur : BlockId) (params : List (Var × Own.PSig)) (acc : List Instr) (next : BlockId)
      (out : Out) (c : Own.Code) (L : Nat), ¬ Owns cur next (count c) L →
      (code self J cur params acc next out c).get? L = out.get? L
  | J, cur, params, acc, next, out, .bind x r k, L, hL => by
    simp only [code]
    exact code_frame self J cur params _ next out k L (by simpa [count] using hL)
  | J, cur, params, acc, next, out, .jp j ps φ r b k, L, hL => by
    simp only [code]
    simp only [Owns, count, not_or, not_and, Nat.not_lt] at hL
    rw [code_frame self _ _ ps [] _ _ b L (by
        simp only [Owns, not_or, not_and, Nat.not_lt]
        refine ⟨by cfg_omega, fun h => by have := hL.2 (by cfg_omega); cfg_omega⟩),
      code_frame self _ cur params acc next out k L (by
        simp only [Owns, not_or, not_and, Nat.not_lt]
        exact ⟨hL.1, fun h => by have := hL.2 h; cfg_omega⟩)]
  | J, cur, params, acc, next, out, .jmp j as, L, hL => by
    simp only [Owns, count, Nat.add_zero, not_or, not_and, Nat.not_lt] at hL
    simp only [code]
    split <;> simp only [finish_get, hL.1, ↓reduceIte]
  | J, cur, params, acc, next, out, .case x alts d, L, hL => by
    simp only [Owns, count, not_or, not_and, Nat.not_lt] at hL
    rw [code.eq_def]; simp only []
    have harms : (arms self J next (finish out cur params acc (.switch x (armEdges next alts)
        (d.map fun _ => ({ target := next + countAlts alts } : Edge)))) alts).get? L = out.get? L := by
      rw [arms_frame self J next _ alts L (fun h => by have := hL.2 h.1; cfg_omega)]
      simp only [finish_get, hL.1, ↓reduceIte]
    cases d with
    | none => exact harms
    | some c =>
      simp only
      rw [code_frame self J _ [] [] _ _ c L (by
        simp only [Owns, not_or, not_and, Nat.not_lt]
        refine ⟨by
          intro h; have := hL.2 (by cfg_omega); simp [countOpt] at this; cfg_omega, fun h => by
          have := hL.2 (by cfg_omega); simp [countOpt] at this; cfg_omega⟩), harms]
  | J, cur, params, acc, next, out, .ret a, L, hL => by
    simp only [Owns, count, Nat.add_zero, not_or, not_and, Nat.not_lt] at hL
    simp only [code]
    simp only [finish_get, hL.1, ↓reduceIte]
  | J, cur, params, acc, next, out, .tcall f as, L, hL => by
    simp only [Owns, count, Nat.add_zero, not_or, not_and, Nat.not_lt] at hL
    simp only [code]
    split <;> simp only [finish_get, hL.1, ↓reduceIte]
  | J, cur, params, acc, next, out, .trap, L, hL => by
    simp only [Owns, count, Nat.add_zero, not_or, not_and, Nat.not_lt] at hL
    simp only [code]
    simp only [finish_get, hL.1, ↓reduceIte]

theorem arms_frame (self : FunId) :
    ∀ (J : JScope) (next : BlockId) (out : Out) (alts : List Own.Alt) (L : Nat),
      ¬ (next ≤ L ∧ L < next + countAlts alts) → (arms self J next out alts).get? L = out.get? L
  | J, next, out, [], L, _ => by simp only [arms]
  | J, next, out, .mk key b :: as, L, hL => by
    simp only [countAlts, not_and, Nat.not_lt] at hL
    simp only [arms]
    have h₁ : ¬ (next + 1 + count b ≤ L ∧ L < next + 1 + count b + countAlts as) := by
      rintro ⟨h1, h2⟩
      have := hL (by cfg_omega)
      cfg_omega
    have h₂ : ¬ Owns next (next + 1) (count b) L := by
      rintro (h | ⟨h1, h2⟩)
      · subst h; have := hL (Nat.le_refl _); cfg_omega
      · have := hL (by cfg_omega); cfg_omega
    rw [arms_frame self J _ _ as L h₁, code_frame self J next [] [] (next + 1) out b L h₂]

end

/-! ## What the blocks hold -/

/-- A block lookup. -/
abbrev Blocks := BlockId → Option Block

/-- The terminator a jump lowers to. -/
def jumpTerm (J : JScope) (j : JoinId) (as : List Arg) : Term :=
  match J.lookup j with
  | some (bj, back) => .jump { target := bj, args := as, back }
  | none => .trap

/-- The terminator a tail call lowers to. -/
def tcallTerm (self f : FunId) (as : List Arg) : Term :=
  if f = self then .jump { target := 0, args := as, back := true } else .tcall f as

/-- The terminator a `case` lowers to. -/
def caseTerm (x : Var) (next : BlockId) (alts : List Own.Alt) (d : Option Own.Code) : Term :=
  .switch x (armEdges next alts) (d.map fun _ => ({ target := next + countAlts alts } : Edge))

mutual

/-- The blocks `B` hold what lowering `c` into block `cur` (parameters
`params`, body so far `acc`, reversed) with fresh labels from `next`
emits. -/
def Impl (B : Blocks) (self : FunId) : JScope → BlockId → List (Var × Own.PSig) → List Instr → BlockId →
    Own.Code → Prop
  | J, cur, params, acc, next, .bind x r k => Impl B self J cur params (.bind x r :: acc) next k
  | J, cur, params, acc, next, .jp j ps _ r b k =>
    Impl B self ((j, next + count k, false) :: J) cur params acc next k ∧
      Impl B self (if r then (j, next + count k, true) :: J else J) (next + count k) ps []
        (next + count k + 1) b
  | J, cur, params, acc, _, .jmp j as =>
    B cur = some { params, body := acc.reverse, term := jumpTerm J j as }
  | J, cur, params, acc, next, .case x alts d =>
    B cur = some { params, body := acc.reverse, term := caseTerm x next alts d } ∧
      ImplArms B self J next alts ∧ ImplOpt B self J (next + countAlts alts) d
  | _, cur, params, acc, _, .ret a => B cur = some { params, body := acc.reverse, term := .ret a }
  | _, cur, params, acc, _, .tcall f as =>
    B cur = some { params, body := acc.reverse, term := tcallTerm self f as }
  | _, cur, params, acc, _, .trap => B cur = some { params, body := acc.reverse, term := .trap }

/-- Each arm in its block, in order. -/
def ImplArms (B : Blocks) (self : FunId) (J : JScope) : BlockId → List Own.Alt → Prop
  | _, [] => True
  | next, .mk _ b :: as => Impl B self J next [] [] (next + 1) b ∧ ImplArms B self J (next + 1 + count b) as

/-- The default, in its block. -/
def ImplOpt (B : Blocks) (self : FunId) (J : JScope) : BlockId → Option Own.Code → Prop
  | _, none => True
  | dnext, some c => Impl B self J dnext [] [] (dnext + 1) c

end

mutual

/-- `Impl` reads only the labels it owns, and only blocks that are there. -/
theorem impl_congr {B B' : Blocks} {self : FunId} :
    ∀ {J : JScope} {cur : BlockId} {params : List (Var × Own.PSig)} {acc : List Instr} {next : BlockId}
      {c : Own.Code}, Impl B self J cur params acc next c →
      (∀ L blk, Owns cur next (count c) L → B L = some blk → B' L = some blk) →
      Impl B' self J cur params acc next c
  | _, _, _, _, _, .bind x r k, h, hB => impl_congr (c := k) h (by simpa [count] using hB)
  | _, _, _, _, next, .jp j ps φ r b k, h, hB =>
    ⟨impl_congr h.1 fun L blk hL hb => hB L blk (by
        rcases hL with hL | hL
        · exact .inl hL
        · simp only [count]; exact .inr ⟨hL.1, by cfg_omega⟩) hb,
      impl_congr h.2 fun L blk hL hb => hB L blk (by
        rcases hL with hL | hL
        · simp only [count]; exact .inr ⟨by cfg_omega, by cfg_omega⟩
        · simp only [count]; exact .inr ⟨by cfg_omega, by cfg_omega⟩) hb⟩
  | _, cur, _, _, _, .jmp j as, h, hB => hB cur _ (.inl rfl) h
  | _, cur, _, _, next, .case x alts d, h, hB =>
    ⟨hB cur _ (.inl rfl) h.1,
      implArms_congr h.2.1 fun L blk hL hb => hB L blk (.inr ⟨hL.1, by simp only [count]; cfg_omega⟩) hb,
      implOpt_congr h.2.2 fun L blk hL hb => hB L blk (.inr ⟨by cfg_omega, by simp only [count]; cfg_omega⟩) hb⟩
  | _, cur, _, _, _, .ret a, h, hB => hB cur _ (.inl rfl) h
  | _, cur, _, _, _, .tcall f as, h, hB => hB cur _ (.inl rfl) h
  | _, cur, _, _, _, .trap, h, hB => hB cur _ (.inl rfl) h

theorem implArms_congr {B B' : Blocks} {self : FunId} {J : JScope} :
    ∀ {next : BlockId} {alts : List Own.Alt}, ImplArms B self J next alts →
      (∀ L blk, next ≤ L ∧ L < next + countAlts alts → B L = some blk → B' L = some blk) →
      ImplArms B' self J next alts
  | _, [], _, _ => trivial
  | next, .mk key b :: as, h, hB =>
    ⟨impl_congr h.1 fun L blk hL hb => hB L blk (by
        simp only [countAlts]
        rcases hL with hL | hL
        · subst hL; exact ⟨Nat.le_refl _, by cfg_omega⟩
        · exact ⟨by cfg_omega, by cfg_omega⟩) hb,
      implArms_congr h.2 fun L blk hL hb => hB L blk (by simp only [countAlts]; cfg_omega) hb⟩

theorem implOpt_congr {B B' : Blocks} {self : FunId} {J : JScope} :
    ∀ {dnext : BlockId} {d : Option Own.Code}, ImplOpt B self J dnext d →
      (∀ L blk, dnext ≤ L ∧ L < dnext + countOpt d → B L = some blk → B' L = some blk) →
      ImplOpt B' self J dnext d
  | _, none, _, _ => trivial
  | dnext, some c, h, hB =>
    impl_congr (c := c) h fun L blk hL hb => hB L blk (by
      simp only [countOpt]
      rcases hL with hL | hL
      · subst hL; exact ⟨Nat.le_refl _, by cfg_omega⟩
      · exact ⟨by cfg_omega, by cfg_omega⟩) hb

end

/-- Agreement on the owned labels. -/
theorem agree_of_frame {B B' : Blocks} {cur next n : Nat} (h : ∀ L, Owns cur next n L → B' L = B L) :
    ∀ L blk, Owns cur next n L → B L = some blk → B' L = some blk :=
  fun L _ hL hb => (h L hL).trans hb

mutual

/-- **The lowering implements the code** it lowers. -/
theorem code_impl (self : FunId) :
    ∀ (J : JScope) (cur : BlockId) (params : List (Var × Own.PSig)) (acc : List Instr) (next : BlockId)
      (out : Out) (c : Own.Code), cur < next →
      Impl (fun L => (code self J cur params acc next out c).get? L) self J cur params acc next c
  | J, cur, params, acc, next, out, .bind x r k, h => by
    simp only [code, Impl]
    exact code_impl self J cur params _ next out k h
  | J, cur, params, acc, next, out, .jp j ps φ r b k, h => by
    simp only [code, Impl]
    refine ⟨impl_congr (code_impl self _ cur params acc next out k h) (agree_of_frame fun L hL => ?_),
      code_impl self _ _ ps [] _ _ b (by cfg_omega)⟩
    refine code_frame self _ _ ps [] _ _ b L ?_
    rintro (hL' | ⟨hL₁, hL₂⟩) <;> rcases hL with hL | ⟨hL₃, hL₄⟩ <;> cfg_omega
  | J, cur, params, acc, next, out, .jmp j as, h => by
    simp only [code, Impl]
    cases hl : J.lookup j with
    | none => simp [finish_get, jumpTerm, hl]
    | some p => obtain ⟨bj, back⟩ := p; simp [finish_get, jumpTerm, hl]
  | J, cur, params, acc, next, out, .case x alts d, h => by
    rw [code.eq_def]
    simp only [Impl]
    have harms := arms_impl self J next (finish out cur params acc (caseTerm x next alts d)) alts
    have hcur : (arms self J next (finish out cur params acc (caseTerm x next alts d)) alts).get? cur =
        some { params, body := acc.reverse, term := caseTerm x next alts d } := by
      rw [arms_frame self J next _ alts cur (fun hc => by cfg_omega)]
      simp [finish_get]
    cases d with
    | none =>
      simp only [caseTerm] at harms hcur ⊢
      exact ⟨hcur, harms, trivial⟩
    | some c =>
      simp only [caseTerm] at harms hcur ⊢
      refine ⟨?_, implArms_congr harms fun L blk hL hb => ?_, ?_⟩
      · rw [code_frame self J _ [] [] _ _ c cur (by rintro (h' | ⟨h₁, h₂⟩) <;> cfg_omega)]
        exact hcur
      · rw [code_frame self J _ [] [] _ _ c L (by rintro (h' | ⟨h₁, h₂⟩) <;> cfg_omega)]
        exact hb
      · exact code_impl self J _ [] [] _ _ c (by cfg_omega)
  | J, cur, params, acc, next, out, .ret a, h => by
    simp only [code, Impl]
    simp [finish_get]
  | J, cur, params, acc, next, out, .tcall f as, h => by
    simp only [code, Impl, tcallTerm]
    split <;> simp [finish_get]
  | J, cur, params, acc, next, out, .trap, h => by
    simp only [code, Impl]
    simp [finish_get]

theorem arms_impl (self : FunId) :
    ∀ (J : JScope) (next : BlockId) (out : Out) (alts : List Own.Alt),
      ImplArms (fun L => (arms self J next out alts).get? L) self J next alts
  | J, next, out, [] => trivial
  | J, next, out, .mk key b :: as => by
    simp only [arms, ImplArms]
    refine ⟨impl_congr (code_impl self J next [] [] (next + 1) out b (by cfg_omega))
      (agree_of_frame fun L hL => ?_), arms_impl self J _ _ as⟩
    exact arms_frame self J _ _ as L (by rintro ⟨h₁, h₂⟩; rcases hL with hL | ⟨hL₁, hL₂⟩ <;> cfg_omega)

end

/-! ## Functions and the program -/

/-- The emitted blocks of a function's body. -/
def outOf (f : FunId) (fd : Own.Fun) : Out := code f [] 0 (fd.params.zip fd.sig.params) [] 1 .leaf fd.body

theorem function_block? (f : FunId) (fd : Own.Fun) (L : BlockId) :
    (Lower.function f fd).block? L =
      if L < 1 + count fd.body then some ((outOf f fd).getD L { term := .trap }) else none := by
  simp only [Fun.block?, Lower.function, outOf]
  split
  · next h => simp [List.getElem?_map, List.getElem?_range h]
  · next h =>
    simp only [List.getElem?_map]
    rw [List.getElem?_eq_none (by simp only [List.length_range]; cfg_omega)]
    rfl

/-- **Every lowered function implements its body**, from block 0 with the
function's parameters. -/
theorem function_impl (f : FunId) (fd : Own.Fun) :
    Impl (Lower.function f fd).block? f [] 0 (fd.params.zip fd.sig.params) [] 1 fd.body := by
  refine impl_congr (code_impl f [] 0 _ [] 1 .leaf fd.body (by decide)) fun L blk hL hb => ?_
  have hlt : L < 1 + count fd.body := by rcases hL with hL | ⟨_, hL⟩ <;> cfg_omega
  rw [function_block?]
  simp only [hlt, ↓reduceIte]
  simp only [NatMap.getD, outOf]
  rw [hb]
  rfl

theorem filterMap_keys {α : Type} (g : Nat → Option α) :
    ∀ l : List Nat, (l.filterMap fun f => (g f).map (f, ·)).map (·.1) = l.filter fun f => (g f).isSome
  | [] => rfl
  | f :: l => by
    simp only [List.filterMap_cons, List.filter_cons]
    cases g f with
    | none => simp [filterMap_keys g l]
    | some x => simp [filterMap_keys g l]

theorem mem_funList {q : Own.Program} {f : FunId} {fd : Own.Fun} :
    (f, fd) ∈ q.funList ↔ f < q.size ∧ q.fun? f = some fd := by
  simp only [Own.Program.funList, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨f', hf', fd', hfd', rfl, rfl⟩; exact ⟨hf', hfd'⟩
  · rintro ⟨hf, hfd⟩; exact ⟨f, hf, fd, hfd, rfl, rfl⟩

theorem get?_ofList_none {α : Type} {xs : List (Nat × α)} (hn : (xs.map (·.1)).Nodup) {k : Nat}
    (h : k ∉ xs.map (·.1)) : (NatMap.ofList xs).get? k = none :=
  (NatMap.get?_foldl_insert (fun _ _ => rfl) xs .leaf hn).1 k h

/-- The functions of `Cfg.lower q`: each function of `q` below its size,
lowered. -/
theorem lower_fun? (q : Own.Program) (f : FunId) :
    (lower q).fun? f = if f < q.size then (q.fun? f).map (Lower.function f) else none := by
  have hkeys : ((q.funList.map fun (p : FunId × Own.Fun) => (p.1, Lower.function p.1 p.2)).map (·.1)).Nodup := by
    rw [List.map_map]
    have : ((·.1) ∘ fun (p : FunId × Own.Fun) => (p.1, Lower.function p.1 p.2)) = (·.1) := rfl
    rw [this]
    simp only [Own.Program.funList]
    rw [filterMap_keys]
    exact List.nodup_range.sublist (List.filter_sublist)
  simp only [Program.fun?, lower]
  by_cases hs : f < q.size
  · simp only [hs, ↓reduceIte]
    cases hfd : q.fun? f with
    | none =>
      have hnot : f ∉ (q.funList.map fun (p : FunId × Own.Fun) => (p.1, Lower.function p.1 p.2)).map (·.1) := by
        simp only [List.map_map, List.mem_map, Function.comp, Prod.exists, not_exists, not_and]
        intro f' fd' hm hf
        subst hf
        rw [(mem_funList.1 hm).2] at hfd
        cases hfd
      exact get?_ofList_none hkeys hnot
    | some fd =>
      simp only [Option.map_some]
      exact NatMap.get?_ofList hkeys (List.mem_map.2 ⟨(f, fd), mem_funList.2 ⟨hs, hfd⟩, rfl⟩)
  · simp only [hs, ↓reduceIte]
    have hnot : f ∉ (q.funList.map fun (p : FunId × Own.Fun) => (p.1, Lower.function p.1 p.2)).map (·.1) := by
      simp only [List.map_map, List.mem_map, Function.comp, Prod.exists, not_exists, not_and]
      intro f' fd' hm hf
      subst hf
      exact hs (mem_funList.1 hm).1
    exact get?_ofList_none hkeys hnot

/-! ## Forward edges go up -/

theorem lookup_mem {J : JScope} {j : JoinId} {bj : BlockId} {back : Bool} :
    J.lookup j = some (bj, back) → (j, bj, back) ∈ J := by
  induction J with
  | nil => simp [List.lookup]
  | cons p J ih =>
    obtain ⟨j', bj', back'⟩ := p
    simp only [List.lookup]
    split
    · next h =>
      simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      simp only [beq_iff_eq] at h
      subst h
      exact List.mem_cons_self
    · intro hl
      exact List.mem_cons_of_mem _ (ih hl)

/-- A block's forward edges go to higher labels. -/
def FwdUp (L : BlockId) (blk : Block) : Prop := ∀ e ∈ blk.term.edges, e.back = false → L < e.target

theorem armEdges_up : ∀ (next : BlockId) (alts : List Own.Alt) (e : Edge),
    e ∈ (armEdges next alts).map (·.2) → next ≤ e.target
  | _, [], _, h => by simp [armEdges] at h
  | next, .mk key b :: as, e, h => by
    simp only [armEdges, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := armEdges_up _ as e h; cfg_omega

mutual

/-- The blocks lowering emits have their forward edges going up, when the
join points in scope that a jump does not charge are above everything the
code lowers to. -/
theorem code_up (self : FunId) :
    ∀ (J : JScope) (cur : BlockId) (params : List (Var × Own.PSig)) (acc : List Instr) (next : BlockId)
      (out : Out) (c : Own.Code), cur < next → (∀ j bj, (j, bj, false) ∈ J → next + count c ≤ bj) →
      ∀ L blk, (code self J cur params acc next out c).get? L = some blk →
        out.get? L = some blk ∨ FwdUp L blk
  | J, cur, params, acc, next, out, .bind x r k, h, hJ, L, blk, hb => by
    simp only [code] at hb
    exact code_up self J cur params _ next out k h (by simpa [count] using hJ) L blk hb
  | J, cur, params, acc, next, out, .jp j ps φ r b k, h, hJ, L, blk, hb => by
    simp only [code] at hb
    rcases code_up self _ _ ps [] _ _ b (by cfg_omega) (by
        intro j' bj' hm
        cases r
        · simp only [Bool.false_eq_true, ↓reduceIte] at hm
          have := hJ j' bj' hm; simp only [count] at this; cfg_omega
        · simp only [↓reduceIte, List.mem_cons, Prod.mk.injEq, Bool.false_eq_true, and_false,
            false_or] at hm
          have := hJ j' bj' hm; simp only [count] at this; cfg_omega) L blk hb with hb' | hup
    · exact code_up self _ cur params acc next out k h (by
        intro j' bj' hm
        rcases List.mem_cons.1 hm with hm | hm
        · simp only [Prod.mk.injEq] at hm; cfg_omega
        · have := hJ j' bj' hm; simp only [count] at this; cfg_omega) L blk hb'
    · exact .inr hup
  | J, cur, params, acc, next, out, .jmp j as, h, hJ, L, blk, hb => by
    simp only [code] at hb
    split at hb
    · next bj back hl =>
      rw [finish_get] at hb
      split at hb
      · next hL =>
        subst hL
        simp only [Option.some.injEq] at hb
        subst hb
        refine .inr fun e he hback => ?_
        simp only [Term.edges, List.mem_singleton] at he
        subst he
        simp only at hback ⊢
        subst hback
        have := hJ j bj (lookup_mem hl)
        simp only [count] at this
        cfg_omega
      · exact .inl hb
    · rw [finish_get] at hb
      split at hb
      · simp only [Option.some.injEq] at hb; subst hb; exact .inr fun e he => by simp [Term.edges] at he
      · exact .inl hb
  | J, cur, params, acc, next, out, .case x alts d, h, hJ, L, blk, hb => by
    rw [code.eq_def] at hb
    simp only at hb
    have harms : ∀ L blk, (arms self J next (finish out cur params acc (caseTerm x next alts d)) alts).get? L =
        some blk → out.get? L = some blk ∨ FwdUp L blk := by
      intro L₁ blk₁ hb₁
      rcases arms_up self J next _ alts (by
          intro j' bj' hm; have := hJ j' bj' hm; simp only [count] at this; cfg_omega) L₁ blk₁ hb₁ with hb₂ | hup
      · rw [finish_get] at hb₂
        by_cases hL : L₁ = cur
        · subst hL
          simp only [↓reduceIte, Option.some.injEq] at hb₂
          subst hb₂
          refine .inr fun e he hback => ?_
          simp only [Term.edges, caseTerm, List.mem_append] at he
          rcases he with he | he
          · have := armEdges_up next alts e he; cfg_omega
          · cases d with
            | none => simp at he
            | some c =>
              simp only [Option.map_some, Option.toList_some, List.mem_singleton] at he
              subst he
              simp only
              cfg_omega
        · simp only [hL, ↓reduceIte] at hb₂
          exact .inl hb₂
      · exact .inr hup
    cases d with
    | none => exact harms L blk hb
    | some c =>
      simp only at hb
      rcases code_up self J _ [] [] _ _ c (by cfg_omega) (by
          intro j' bj' hm; have := hJ j' bj' hm; simp only [count, countOpt] at this; cfg_omega) L blk hb with
        hb | hup
      · exact harms L blk hb
      · exact .inr hup
  | J, cur, params, acc, next, out, .ret a, h, hJ, L, blk, hb => by
    simp only [code, finish_get] at hb
    split at hb
    · simp only [Option.some.injEq] at hb; subst hb; exact .inr fun e he => by simp [Term.edges] at he
    · exact .inl hb
  | J, cur, params, acc, next, out, .tcall f as, h, hJ, L, blk, hb => by
    simp only [code] at hb
    split at hb
    · rw [finish_get] at hb
      split at hb
      · simp only [Option.some.injEq] at hb; subst hb
        exact .inr fun e he hback => by simp only [Term.edges, List.mem_singleton] at he; subst he; cases hback
      · exact .inl hb
    · rw [finish_get] at hb
      split at hb
      · simp only [Option.some.injEq] at hb; subst hb; exact .inr fun e he => by simp [Term.edges] at he
      · exact .inl hb
  | J, cur, params, acc, next, out, .trap, h, hJ, L, blk, hb => by
    simp only [code, finish_get] at hb
    split at hb
    · simp only [Option.some.injEq] at hb; subst hb; exact .inr fun e he => by simp [Term.edges] at he
    · exact .inl hb

theorem arms_up (self : FunId) :
    ∀ (J : JScope) (next : BlockId) (out : Out) (alts : List Own.Alt),
      (∀ j bj, (j, bj, false) ∈ J → next + countAlts alts ≤ bj) →
      ∀ L blk, (arms self J next out alts).get? L = some blk → out.get? L = some blk ∨ FwdUp L blk
  | J, next, out, [], _, L, blk, hb => .inl hb
  | J, next, out, .mk key b :: as, hJ, L, blk, hb => by
    simp only [arms] at hb
    rcases arms_up self J _ _ as (by
        intro j' bj' hm; have := hJ j' bj' hm; simp only [countAlts] at this; cfg_omega) L blk hb with hb | hup
    · exact code_up self J next [] [] (next + 1) out b (by cfg_omega) (by
        intro j' bj' hm; have := hJ j' bj' hm; simp only [countAlts] at this; cfg_omega) L blk hb
    · exact .inr hup

end

/-- **`Cfg.lower` keeps forward edges going up**: its programs are
`Cfg.Ordered`, so `Cfg.run` is the clocked outcome of its steps. -/
theorem lower_ordered (q : Own.Program) : Ordered (lower q) where
  forward := by
    intro f fd b blk e hf hb he hback
    rw [lower_fun?] at hf
    split at hf
    · obtain ⟨fdo, -, rfl⟩ := Option.map_eq_some_iff.1 hf
      rw [function_block?] at hb
      split at hb
      · simp only [Option.some.injEq, NatMap.getD] at hb
        cases ho : (outOf f fdo).get? b with
        | none =>
          rw [ho] at hb
          simp only [Option.getD_none] at hb
          subst hb
          simp [Term.edges] at he
        | some blk' =>
          rw [ho] at hb
          simp only [Option.getD_some] at hb
          subst hb
          rcases code_up f [] 0 _ [] 1 .leaf fdo.body (by decide) (fun _ _ h => by cases h) b blk' ho with
            h | hup
          · simp [NatMap.get?] at h
          · exact hup e he hback
      · cases hb
    · cases hf
  dense := by
    intro f fd hf
    rw [lower_fun?] at hf
    split at hf
    · next h => exact h
    · cases hf

end Compilatrix.Cfg.Proof
