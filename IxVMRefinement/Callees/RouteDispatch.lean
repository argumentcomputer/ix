import IxVMRefinement.Callees.RouteScan
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.L1.Decode

/-! # The dispatch on a block, as a function of the record store

`blockRoute E B` is the answer of `KernelModeled::block_is_modeled` at the address `B`, computed
from the store `E`: unknown where `E` holds no record at `B`; `0` at a record that is no block
and at a block with no inductive member; `1` at a block of two or more inductive members; and
at a block of exactly one inductive member, the scan of its constructors in order
(`ctorAnswer`): the stored type of a constructor has the shape `exprTree?` reads off the
record's expression, reference and sharing tables, the parameters are peeled, and the body is
scanned (`nestedN`) where it mentions a member's address. The scan stops at the first
constructor that answers `1`.

`block_is_modeled_agrees`: every observation of the dispatch that is bounded and hashes no
collision with `E` agrees with `blockRoute E B` (`Agrees`): where the value is known the answer
is it, and a store that holds every canonical record the observation hashed makes it known.

* `ExprTree`, `ExprTree.functional`, `treeAt_of_rawConv`, `exprTree?`: the shape of a converted
  stored expression;
* `ctor_scan_agrees`, `ctors_nested_agrees`: one constructor and the loop;
* `first_indc_pos_spec`: the position of the inductive member and its constructor count;
* `record_route_agrees`, `block_is_modeled_agrees`: the dispatch.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace IxVM.Refinement.Route

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Whnf
open IxVM.Consistency
open IxVM (F)

noncomputable section

theorem bit_eq_zero {b : Bool} (h : bit b = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true =>
    rw [bit_true] at h
    exact absurd h NatAux.field_one_ne_zero

theorem bit_ne_zero {b : Bool} (h : bit b ≠ .field 0) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd bit_false h

theorem drop_eq_cons_of_getElem? {α : Type} :
    ∀ (l : List α) (n : Nat) (x : α), l[n]? = some x → l.drop n = x :: l.drop (n + 1)
  | [], n, x, h => by simp at h
  | y :: l, 0, x, h => by
    simp at h
    subst h
    rfl
  | y :: l, n + 1, x, h => by
    simp at h
    simpa using drop_eq_cons_of_getElem? l n x h

/-! ## The shape of a converted stored expression -/

/-- **The shape of the conversion of a stored expression**, read off the expression with the
record's reference table, the addresses its recursive references stand for and its sharing
table. A shared subterm is expanded. -/
inductive ExprTree (refs recurAddrs : List _root_.Address) (sharing : List Ixon.Expr) :
    Nat → Ixon.Expr → ScanTree → Prop where
  | var {bound : Nat} {idx : UInt64} : ExprTree refs recurAddrs sharing bound (.var idx) .atom
  | sort {bound : Nat} {uIdx : UInt64} :
      ExprTree refs recurAddrs sharing bound (.sort uIdx) .atom
  | ref {bound : Nat} {rIdx : UInt64} {uIdxs : Array UInt64} {a : _root_.Address} :
      refs[rIdx.toNat]? = some a →
      ExprTree refs recurAddrs sharing bound (.ref rIdx uIdxs) (.const a)
  | recur {bound : Nat} {rIdx : UInt64} {uIdxs : Array UInt64} {a : _root_.Address} :
      recurAddrs[rIdx.toNat]? = some a →
      ExprTree refs recurAddrs sharing bound (.recur rIdx uIdxs) (.const a)
  | prj {bound : Nat} {tIdx fIdx : UInt64} {inner : Ixon.Expr} {Ti : ScanTree} :
      ExprTree refs recurAddrs sharing bound inner Ti →
      ExprTree refs recurAddrs sharing bound (.prj tIdx fIdx inner) (.proj Ti)
  | str {bound : Nat} {bIdx : UInt64} : ExprTree refs recurAddrs sharing bound (.str bIdx) .atom
  | nat {bound : Nat} {bIdx : UInt64} : ExprTree refs recurAddrs sharing bound (.nat bIdx) .atom
  | app {bound : Nat} {f arg : Ixon.Expr} {Tf Ta : ScanTree} :
      ExprTree refs recurAddrs sharing bound f Tf →
      ExprTree refs recurAddrs sharing bound arg Ta →
      ExprTree refs recurAddrs sharing bound (.app f arg) (.app Tf Ta)
  | lam {bound : Nat} {ty body : Ixon.Expr} {Tt Tb : ScanTree} :
      ExprTree refs recurAddrs sharing bound ty Tt →
      ExprTree refs recurAddrs sharing bound body Tb →
      ExprTree refs recurAddrs sharing bound (.lam ty body) (.lam Tt Tb)
  | all {bound : Nat} {ty body : Ixon.Expr} {Tt Tb : ScanTree} :
      ExprTree refs recurAddrs sharing bound ty Tt →
      ExprTree refs recurAddrs sharing bound body Tb →
      ExprTree refs recurAddrs sharing bound (.all ty body) (.all Tt Tb)
  | letE {bound : Nat} {nd : Bool} {md : Ixon.LetMode} {ty val body : Ixon.Expr}
      {Tt Tv Tb : ScanTree} :
      ExprTree refs recurAddrs sharing bound ty Tt →
      ExprTree refs recurAddrs sharing bound val Tv →
      ExprTree refs recurAddrs sharing bound body Tb →
      ExprTree refs recurAddrs sharing bound (.letE nd md ty val body) (.letE Tt Tv Tb)
  | share {bound : Nat} {idx : UInt64} {s : Ixon.Expr} {T : ScanTree} :
      idx.toNat < bound → sharing[idx.toNat]? = some s →
      ExprTree refs recurAddrs sharing idx.toNat s T →
      ExprTree refs recurAddrs sharing bound (.share idx) T

/-- **The shape is a function of the expression.** -/
theorem ExprTree.functional {refs recurAddrs : List _root_.Address} {sharing : List Ixon.Expr} :
    ∀ {b₁ : Nat} {e : Ixon.Expr} {T₁ : ScanTree}, ExprTree refs recurAddrs sharing b₁ e T₁ →
      ∀ {b₂ : Nat} {T₂ : ScanTree}, ExprTree refs recurAddrs sharing b₂ e T₂ → T₁ = T₂ := by
  intro b₁ e T₁ h₁
  induction h₁ with
  | var =>
    intro b₂ T₂ h₂
    cases h₂
    rfl
  | sort =>
    intro b₂ T₂ h₂
    cases h₂
    rfl
  | ref href =>
    intro b₂ T₂ h₂
    cases h₂ with
    | ref href' => exact congrArg ScanTree.const (Option.some.inj (href.symm.trans href'))
  | recur hrec =>
    intro b₂ T₂ h₂
    cases h₂ with
    | recur hrec' => exact congrArg ScanTree.const (Option.some.inj (hrec.symm.trans hrec'))
  | prj _ ih =>
    intro b₂ T₂ h₂
    cases h₂ with
    | prj h' => exact congrArg ScanTree.proj (ih h')
  | str =>
    intro b₂ T₂ h₂
    cases h₂
    rfl
  | nat =>
    intro b₂ T₂ h₂
    cases h₂
    rfl
  | app _ _ ihf iha =>
    intro b₂ T₂ h₂
    cases h₂ with
    | app hf ha => rw [ihf hf, iha ha]
  | lam _ _ iht ihb =>
    intro b₂ T₂ h₂
    cases h₂ with
    | lam ht hb => rw [iht ht, ihb hb]
  | all _ _ iht ihb =>
    intro b₂ T₂ h₂
    cases h₂ with
    | all ht hb => rw [iht ht, ihb hb]
  | letE _ _ _ iht ihv ihb =>
    intro b₂ T₂ h₂
    cases h₂ with
    | letE ht hv hb => rw [iht ht, ihv hv, ihb hb]
  | share hidx hsh _ ih =>
    intro b₂ T₂ h₂
    cases h₂ with
    | share hidx' hsh' h' =>
      have e := Option.some.inj (hsh.symm.trans hsh')
      subst e
      exact ih h'

/-- **A converted stored expression has the shape its expression names.** -/
theorem treeAt_of_rawConv {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F} :
    ∀ {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F},
      L1.RawConvExpr refs recurAddrs univs sharing blobs h bound e kp →
      ∃ T, ExprTree refs recurAddrs sharing bound e T ∧ TreeAt h kp T := by
  intro bound e kp hr
  induction hr with
  | var hidx cell => exact ⟨.atom, .var, .bvar (loadValue_enum_cell cell)⟩
  | sort huIdx hu rl cell => exact ⟨.atom, .sort, .srt (loadValue_enum_cell cell)⟩
  | ref hrIdx href hd ra hls rls cell =>
    subst hd
    exact ⟨_, .ref href, .const (loadValue_enum_cell cell) ra⟩
  | recur hrIdx hrec hd ra hls rls cell =>
    subst hd
    exact ⟨_, .recur hrec, .const (loadValue_enum_cell cell) ra⟩
  | prj htIdx hfIdx href hd ra rin cell ih =>
    obtain ⟨Ti, hE, hT⟩ := ih
    exact ⟨_, .prj hE, .proj (loadValue_enum_cell cell) hT⟩
  | str hbIdx href hmem rbs hs cell => exact ⟨.atom, .str, .lit (loadValue_enum_cell cell)⟩
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    exact ⟨.atom, .nat, .lit (loadValue_enum_cell cell)⟩
  | app rf ra cell ihf iha =>
    obtain ⟨Tf, hEf, hTf⟩ := ihf
    obtain ⟨Ta, hEa, hTa⟩ := iha
    exact ⟨_, .app hEf hEa, .app (loadValue_enum_cell cell) hTf hTa⟩
  | lam rl rt rb cell iht ihb =>
    obtain ⟨Tt, hEt, hTt⟩ := iht
    obtain ⟨Tb, hEb, hTb⟩ := ihb
    exact ⟨_, .lam hEt hEb, .lam (loadValue_enum_cell cell) hTt hTb⟩
  | all rl rt rb cell iht ihb =>
    obtain ⟨Tt, hEt, hTt⟩ := iht
    obtain ⟨Tb, hEb, hTb⟩ := ihb
    exact ⟨_, .all hEt hEb, .all (loadValue_enum_cell cell) hTt hTb⟩
  | letE rt rv rb cell iht ihv ihb =>
    obtain ⟨Tt, hEt, hTt⟩ := iht
    obtain ⟨Tv, hEv, hTv⟩ := ihv
    obtain ⟨Tb, hEb, hTb⟩ := ihb
    exact ⟨_, .letE hEt hEv hEb, .letE (loadValue_enum_cell cell) hTt hTv hTb⟩
  | share hidx hsh rs ih =>
    obtain ⟨T, hE, hT⟩ := ih
    exact ⟨T, .share hidx hsh hE, hT⟩

/-- The shape of a stored expression at the conversion's sharing bound; none where the
expression has none (a dangling reference or share). -/
def exprTree? (refs recurAddrs : List _root_.Address) (sharing : List Ixon.Expr)
    (e : Ixon.Expr) : Option ScanTree :=
  @dite (Option ScanTree) (∃ T, ExprTree refs recurAddrs sharing 4294967295 e T)
    (Classical.propDecidable _) (fun h => some (Classical.choose h)) (fun _ => none)

theorem exprTree?_of {refs recurAddrs : List _root_.Address} {sharing : List Ixon.Expr}
    {e : Ixon.Expr} {T : ScanTree} (hT : ExprTree refs recurAddrs sharing 4294967295 e T) :
    exprTree? refs recurAddrs sharing e = some T := by
  have hex : ∃ T, ExprTree refs recurAddrs sharing 4294967295 e T := ⟨T, hT⟩
  unfold exprTree?
  rw [dif_pos hex]
  exact congrArg some (ExprTree.functional (Classical.choose_spec hex) hT)

/-! ## The scan of the constructors -/

/-- The answer on a constructor's body: the scan where the body mentions a member, `0`
otherwise (the scan is skipped). -/
def ctorBody (isInd : _root_.Address → Option Bool) (M : List _root_.Address) (B : ScanTree) :
    Option Bool :=
  match B.mentions M with
  | true => nestedN isInd M B.size B
  | false => some false

/-- **The answer on a stored constructor**: its type's shape, the parameters peeled, the body
scanned. Unknown where the stored type has no shape or fewer leading `∀` than parameters (the
circuit does not accept such a constructor). -/
def ctorAnswer (isInd : _root_.Address → Option Bool) (M : List _root_.Address)
    (refs : List _root_.Address) (sharing : List Ixon.Expr) (ct : Ixon.Constructor) :
    Option Bool :=
  match exprTree? refs M sharing ct.typ with
  | none => none
  | some T =>
    match T.peel ct.params.toNat with
    | none => none
    | some B => ctorBody isInd M B

/-- **One constructor of the loop**: the load of constructor `cidx` of member `p` of the block,
the peeled parameters and the scan of the body. The block's record is the one the run hashed
at the block's address (`raw`, decoding to `c`). -/
theorem ctor_scan_agrees {E : Ixon.Env} {b : Bytes.Address} {raw : ByteArray}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} {p : Nat} {ind : Ixon.Inductive}
    {mems : List Bytes.Address} {calls : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] calls) (hbd : Bounded calls)
    (hraw : Hashed calls raw) (hx : Ixon.deConstantExact raw = .ok c)
    (haddr : Address.blake3Pure raw = ixAddr b) (hinfo : c.info = .muts ms)
    (hp : ms.toList[p]? = some (.indc ind)) (hplt : p < 549755813888)
    (hmems : mems.map ixAddr = L1.blockRecurAddrs (ixAddr b) ms.toList)
    {cidx : Nat} (hcidx : cidx < 549755813888)
    {bp xs p39 w88 x_cty w89 w90 w91 x_np w92 w93 v134 rseg nc : SourceValue F}
    {h m32 m135 m230 : Heap F} {cs45 cs145 cs232 : List (Call F)}
    (hs45 : ∀ z ∈ cs45, z ∈ calls) (hs232 : ∀ z ∈ cs232, z ∈ calls)
    (hbp : Bytes.RepAddressRef addrTy h b bp) (hxs : RepList addrListEnum RepAddr h mems xs)
    (ev47 : ObsFn Obs.W "Ingress::get_ci_cprj" [bp, .field (p : F), .field (cidx : F)] h p39
      m32 cs45)
    (ld41 : loadValue m32 p39 = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
      [w88, x_cty, w89, w90, w91, x_np, w92, w93]))
    (ev147 : ObsFn Obs.W "KernelCheck::peel_n_foralls" [x_cty, x_np] m32 v134 m135 cs145)
    (sg : Obs.«KernelModeled::ctors_nested».Seg1 v134 x_cty x_np
      (.construct "KernelTypes::KConstantInfo" "Ctor" [w88, x_cty, w89, w90, w91, x_np, w92, w93])
      bp (.field (p : F)) nc xs (.field (cidx : F)) m135 rseg m230 cs232) :
    ∃ ct, ind.ctors.toList[cidx]? = some ct ∧
      Agrees (L1.CanonicalHashCoverage E calls)
        (ctorAnswer (isIndAt E) (L1.blockRecurAddrs (ixAddr b) ms.toList) c.refs.toList
          c.sharing.toList ct) rseg ∧
      Heap.Extends h m230 := by
  obtain ⟨n45, b45, -⟩ := sub_good hs45 hnc hbd
  obtain ⟨ext1, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb', hms',
    hct', -, hldv, hrawC⟩ := L1.get_ci_cprj_spec b45 hbp ev47
  have eraw : raw = blkBytes :=
    hashed_inj_of_noCollision hnc hraw (Core.hashed_mono hs45 hhB) (haddr.trans haB.symm)
  subst eraw
  have ec : c = cb' := Except.ok.inj (hx.symm.trans hexB)
  subst ec
  have ems : ms = ms' := Ixon.ConstantInfo.muts.inj (hinfo.symm.trans hcb')
  subst ems
  have hpv : ZMod.val ((p : Nat) : F) = p :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hplt (by decide))
  have hcv : ZMod.val ((cidx : Nat) : F) = cidx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcidx (by decide))
  rw [hpv] at hms' hrawC
  rw [hcv] at hct'
  have eind : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hp.symm.trans hms'))
  subst eind
  -- the loaded constructor value
  obtain ⟨-, -, hpar, -, -, tyPtr, blkPtr, b', -, -, hv, rty⟩ := hrawC
  rw [hldv] at ld41
  injection ld41 with e
  rw [hv] at e
  injection e with _ _ hargs
  injection hargs with _ hargs
  injection hargs with hty hargs
  injection hargs with _ hargs
  injection hargs with _ hargs
  injection hargs with _ hargs
  injection hargs with hnp _
  subst hty hnp
  obtain ⟨T, hET, hT⟩ := treeAt_of_rawConv rty
  have hTsome := exprTree?_of hET
  obtain ⟨B, hpeel, hB⟩ := peel_n_foralls_tree ct'.params.toNat
    (Nat.lt_trans hpar (by decide)) hT ev147
  have ext2 := ev147.heap_extends
  have hxs2 : RepList addrListEnum RepAddr m135 mems xs := se_addrs_mono (ext1.trans ext2) hxs
  refine ⟨ct', hct', ?_⟩
  rcases sg with
    ⟨m165, cs176, ev178, he199, he200, hc201⟩ |
    ⟨v164, m165, cs176, cs209, ev178, hne202, ev211, hc228⟩
  · -- the body mentions no member: no scan
    have c1 := se_mentions_exact (ms := mems) _ (Nat.le_refl _) hB hxs2 ev178
    rw [hmems] at c1
    have hm := bit_eq_zero c1.symm
    refine ⟨?_, by rw [he200]; exact (ext1.trans ext2).trans ev178.heap_extends⟩
    simp only [ctorAnswer, hTsome, hpeel, ctorBody, hm]
    exact Agrees.pure (by rw [he199, bit_false])
  · -- the body mentions a member: the scan
    subst hc228
    have c1 := se_mentions_exact (ms := mems) _ (Nat.le_refl _) hB hxs2 ev178
    rw [hmems] at c1
    have hm := bit_ne_zero (by rw [← c1]; exact hne202)
    have ext3 := ev178.heap_extends
    have hs209 : ∀ z ∈ cs209, z ∈ calls := fun z hz => hs232 z (by simp [hz])
    obtain ⟨n209, b209, c209⟩ := sub_good hs209 hnc hbd
    have a := (nested_scan_agrees (E := E) (ms := mems) B.size (Nat.le_refl _) (hB.mono ext3)
      (se_addrs_mono ext3 hxs2) n209 b209 ev211).weaken c209
    rw [hmems] at a
    refine ⟨?_, ((ext1.trans ext2).trans ext3).trans ev211.heap_extends⟩
    simp only [ctorAnswer, hTsome, hpeel, ctorBody, hm]
    exact a

/-- **The loop over the constructors**, from constructor `cidx`: the fold of the constructors'
answers in order, stopping at the first `1`. -/
theorem ctors_nested_agrees {E : Ixon.Env} {b : Bytes.Address} {raw : ByteArray}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} {p : Nat} {ind : Ixon.Inductive}
    {mems : List Bytes.Address} {calls : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] calls) (hbd : Bounded calls)
    (hraw : Hashed calls raw) (hx : Ixon.deConstantExact raw = .ok c)
    (haddr : Address.blake3Pure raw = ixAddr b) (hinfo : c.info = .muts ms)
    (hp : ms.toList[p]? = some (.indc ind)) (hplt : p < 549755813888)
    (hn : ind.ctors.toList.length < 549755813888)
    (hmems : mems.map ixAddr = L1.blockRecurAddrs (ixAddr b) ms.toList) :
    ∀ (k cidx : Nat) {bp xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cidx + k = ind.ctors.toList.length → (∀ z ∈ cs, z ∈ calls) →
      Bytes.RepAddressRef addrTy h b bp → RepList addrListEnum RepAddr h mems xs →
      ObsFn Obs.W "KernelModeled::ctors_nested"
        [bp, .field (p : F), .field (ind.ctors.toList.length : F), xs, .field (cidx : F)]
        h r h' cs →
      Agrees (L1.CanonicalHashCoverage E calls)
        (((ind.ctors.toList.drop cidx).map (ctorAnswer (isIndAt E)
          (L1.blockRecurAddrs (ixAddr b) ms.toList) c.refs.toList c.sharing.toList)).foldr
          orElse (some false)) r := by
  intro k
  induction k with
  | zero =>
    intro cidx bp xs r h h' cs hk hsub hbp hxs ev
    rcases Obs.«KernelModeled::ctors_nested».obs ev with
      ⟨op17, he24, he25, hc26⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, x_np, w92, w93, v134, m135, cs145, m230,
        cs232, op17, hne27, ev47, ld41, ev147, sg237, he252, he253, hc254⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, x_np, w92, w93, v134, m135, cs145, v229,
        m230, cs232, cs262, v269, op17, hne27, ev47, ld41, ev147, sg237, hne255, op311, ev264,
        hc313⟩
    · have hd : ind.ctors.toList.drop cidx = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd]
      simp only [List.map_nil, List.foldr_nil]
      exact Agrees.pure (by rw [he24, bit_false])
    · exfalso
      have hv := Decl.evalBinOp_sub_nat (by omega : cidx ≤ ind.ctors.toList.length) op17
      have hz : ind.ctors.toList.length - cidx = 0 := by omega
      rw [hz] at hv
      exact hne27 (by rw [hv]; simp)
    · exfalso
      have hv := Decl.evalBinOp_sub_nat (by omega : cidx ≤ ind.ctors.toList.length) op17
      have hz : ind.ctors.toList.length - cidx = 0 := by omega
      rw [hz] at hv
      exact hne27 (by rw [hv]; simp)
  | succ k ih =>
    intro cidx bp xs r h h' cs hk hsub hbp hxs ev
    rcases Obs.«KernelModeled::ctors_nested».obs ev with
      ⟨op17, he24, he25, hc26⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, x_np, w92, w93, v134, m135, cs145, m230,
        cs232, op17, hne27, ev47, ld41, ev147, sg237, he252, he253, hc254⟩ |
      ⟨v1, m32, p39, cs45, w88, x_cty, w89, w90, w91, x_np, w92, w93, v134, m135, cs145, v229,
        m230, cs232, cs262, v269, op17, hne27, ev47, ld41, ev147, sg237, hne255, op311, ev264,
        hc313⟩
    · exfalso
      have hzero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field ((ind.ctors.toList.length - cidx : Nat) : F) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : cidx ≤ ind.ctors.toList.length) op17
      have := Decl.nat_eq_of_field_eq_bounded (by decide) (by omega) hzero
      omega
    · -- the constructor answers `1`
      subst hc254
      obtain ⟨ct, hct, aC, -⟩ := ctor_scan_agrees hnc hbd hraw hx haddr hinfo hp hplt hmems
        (by omega : cidx < 549755813888) (fun z hz => hsub z (by simp [hz]))
        (fun z hz => hsub z (by simp [hz])) hbp hxs ev47 ld41 ev147 sg237
      rw [drop_eq_cons_of_getElem? _ _ _ hct]
      simp only [List.map_cons, List.foldr_cons]
      exact aC.orElse_one rfl he252
    · -- the constructor answers otherwise: the next one
      subst hc313
      obtain ⟨ct, hct, aC, ext⟩ := ctor_scan_agrees hnc hbd hraw hx haddr hinfo hp hplt hmems
        (by omega : cidx < 549755813888) (fun z hz => hsub z (by simp [hz]))
        (fun z hz => hsub z (by simp [hz])) hbp hxs ev47 ld41 ev147 sg237
      have hv := Decl.evalBinOp_add_nat cidx 1 op311
      subst hv
      have aR := ih (cidx + 1) (by omega) (fun z hz => hsub z (by simp [hz]))
        (Bytes.repAddressRef_heapMono₂ addrTy ext hbp) (se_addrs_mono ext hxs) ev264
      rw [drop_eq_cons_of_getElem? _ _ _ hct]
      simp only [List.map_cons, List.foldr_cons]
      exact aC.orElse_other hne255 aR

/-! ## The inductive member -/

/-- The first inductive member from position `pos`, with its position. -/
def firstIndc : List Ixon.MutConst → Nat → Option (Nat × Ixon.Inductive)
  | [], _ => none
  | .indc ind :: _, pos => some (pos, ind)
  | .defn _ :: rest, pos => firstIndc rest (pos + 1)
  | .recr _ :: rest, pos => firstIndc rest (pos + 1)

theorem firstIndc_spec :
    ∀ {ms : List Ixon.MutConst} {pos p : Nat} {ind : Ixon.Inductive},
      firstIndc ms pos = some (p, ind) → ∃ j, p = pos + j ∧ ms[j]? = some (.indc ind)
  | [], pos, p, ind, h => by simp [firstIndc] at h
  | .indc i :: rest, pos, p, ind, h => by
    simp only [firstIndc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, rfl⟩
  | .defn d :: rest, pos, p, ind, h => by
    obtain ⟨j, hj, hm⟩ := firstIndc_spec (ms := rest) (pos := pos + 1) h
    exact ⟨j + 1, by omega, by simpa using hm⟩
  | .recr rc :: rest, pos, p, ind, h => by
    obtain ⟨j, hj, hm⟩ := firstIndc_spec (ms := rest) (pos := pos + 1) h
    exact ⟨j + 1, by omega, by simpa using hm⟩

theorem ctor_list_length_spec {R : Heap F → Ixon.Constructor → SourceValue F → Prop}
    {xs : List Ixon.Constructor} {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<Ixon::Constructor>» [p] h r h' cs)
    (hxs : RepList Obs.Names.«Lists::Node<Ixon::Constructor>» R h xs p) :
    r = .field (xs.length : F) ∧ h' = h := by
  have ev' : ObsFn Obs.W (Instance.mk "Lists::length" [(.named "Ixon::Constructor" [])]).symbol
      [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<Ixon::Constructor>».symbol]
    exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.named "Ixon::Constructor" [])]).symbol
      R h xs p := by
    rw [Obs.Names.«Lists::Node<Ixon::Constructor>».symbol]
    exact hxs
  exact Lib.Lists.length_spec ev' hl'

theorem mutShape_of_repMutConst {h : Heap F} {m : Ixon.MutConst} {v : SourceValue F}
    (hr : L1.RepMutConst h m v) : Specs.Callees.MutShape h m v := by
  cases m with
  | defn d => obtain ⟨dv, hv, _⟩ := hr; exact ⟨dv, hv⟩
  | indc i => obtain ⟨iv, hv, _⟩ := hr; exact ⟨iv, hv⟩
  | recr r => obtain ⟨rv, hv, _⟩ := hr; exact ⟨rv, hv⟩

theorem membersRep_of_repMutConstList {h : Heap F} {xs : List Ixon.MutConst}
    {p : SourceValue F}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst h xs p) :
    Specs.Callees.MembersRep h xs p := by
  induction hrep with
  | nil cell => exact .nil cell
  | cons cell rh _ ih => exact .cons cell (mutShape_of_repMutConst rh) ih

/-- **`first_indc_pos`**: the position of the first inductive member and the number of its
constructors, which is below `2^39` at a bounded run. -/
theorem first_indc_pos_spec {calls : List (Call F)} (hbd : Bounded calls) :
    ∀ {ms : List Ixon.MutConst} {pos : Nat} {x_members r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ z ∈ cs, z ∈ calls) →
      RepList L1.mutConstListEnum L1.RepMutConst h ms x_members →
      ObsFn Obs.W "KernelModeled::first_indc_pos" [x_members, .field (pos : F)] h r h' cs →
      ∃ (p : Nat) (ind : Ixon.Inductive), firstIndc ms pos = some (p, ind) ∧
        r = .tuple [.field (p : F), .field (ind.ctors.toList.length : F)] ∧ h' = h ∧
        ind.ctors.toList.length < 2 ^ 39 := by
  intro ms
  induction ms with
  | nil =>
    intro pos x_members r h h' cs hsub hms ev
    rcases Obs.«KernelModeled::first_indc_pos».obs ev with
      ⟨x_rest, w67, w68, w69, w70, w71, x_ctors, v105, m115, cs123, ld12, he106, ev125, he134,
        hc135⟩ |
      ⟨x_m, x_rest, cs144, v148, ld12, hne137, op169, ev146, hc171⟩
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hms ld12
      cases hnil
    · obtain ⟨z, zs, hnil, -, -⟩ := RepList.cons_of_load hms ld12
      cases hnil
  | cons m ms ih =>
    intro pos x_members r h h' cs hsub hms ev
    rcases Obs.«KernelModeled::first_indc_pos».obs ev with
      ⟨x_rest, w67, w68, w69, w70, w71, x_ctors, v105, m115, cs123, ld12, he106, ev125, he134,
        hc135⟩ |
      ⟨x_m, x_rest, cs144, v148, ld12, hne137, op169, ev146, hc171⟩
    · obtain ⟨z, zs, hcons, hm, -⟩ := RepList.cons_of_load hms ld12
      injection hcons with e1 e2
      subst e1 e2
      cases m with
      | defn d =>
        obtain ⟨dv, hv, -⟩ := hm
        injection hv with _ htag _
        exact absurd htag (by decide)
      | recr rc =>
        obtain ⟨rv, hv, -⟩ := hm
        injection hv with _ htag _
        exact absurd htag (by decide)
      | indc ind =>
        obtain ⟨iv, hv, typPtr, ctorsPtr, hiv, -, hctors⟩ := hm
        injection hv with _ _ hargs
        injection hargs with hiv' _
        rw [hiv] at hiv'
        injection hiv' with _ _ hargs2
        injection hargs2 with _ hargs2
        injection hargs2 with _ hargs2
        injection hargs2 with _ hargs2
        injection hargs2 with _ hargs2
        injection hargs2 with _ hargs2
        injection hargs2 with hct _
        subst hct
        obtain ⟨hlen, hh⟩ := ctor_list_length_spec ev125 hctors
        have hcall : (⟨Obs.Names.«Lists::length<Ixon::Constructor>», [x_ctors], h⟩ : Call F) ∈
            calls := hsub _ (by rw [hc135]; simp)
        have hlt : ind.ctors.toList.length < 2 ^ 39 :=
          RomBound.bounded_length_lt hbd hcall (by simp) hctors
        refine ⟨pos, ind, rfl, ?_, he134.trans hh, hlt⟩
        rw [he106, hlen]
    · obtain ⟨z, zs, hcons, hm, hrest⟩ := RepList.cons_of_load hms ld12
      injection hcons with e1 e2
      subst e1 e2
      have hv := Decl.evalBinOp_add_nat pos 1 op169
      subst hv
      have hsub' : ∀ z ∈ cs144, z ∈ calls := fun z hz => hsub z (by rw [hc171]; simp [hz])
      obtain ⟨p, ind, hf, hr, hh, hl⟩ := ih hsub' hrest ev146
      refine ⟨p, ind, ?_, hr, hh, hl⟩
      cases m with
      | indc i =>
        obtain ⟨iv, hv, -⟩ := hm
        exact (hne137 [iv] rfl hv).elim
      | defn d => exact hf
      | recr rc => exact hf

/-! ## The dispatch -/

/-- The answer at a block of exactly one inductive member: the scan of its constructors. -/
def oneRoute (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) : Option Bool :=
  match firstIndc ms.toList 0 with
  | some (_, ind) =>
    (ind.ctors.toList.map (ctorAnswer (isIndAt E) (L1.blockRecurAddrs B ms.toList)
      cb.refs.toList cb.sharing.toList)).foldr orElse (some false)
  | none => none

/-- The answer at a block, by the number of its inductive members. -/
def mutsRoute (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) : Option Bool :=
  match (ms.toList.filter Specs.Callees.isIndc).length with
  | 0 => some false
  | 1 => oneRoute E B cb ms
  | _ + 2 => some true

/-- The answer at a record. -/
def recordRoute (E : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant) : Option Bool :=
  match cb.info with
  | .muts ms => mutsRoute E B cb ms
  | .defn _ => some false
  | .axio _ => some false
  | .quot _ => some false
  | .recr _ => some false
  | .dPrj _ => some false
  | .iPrj _ => some false
  | .cPrj _ => some false
  | .rPrj _ => some false

/-- **The dispatch's answer at the address `B`, as a function of the store `E`**: unknown where
`E` holds no record at `B`, or lacks a record the scan of a one-inductive block loads. -/
def blockRoute (E : Ixon.Env) (B : _root_.Address) : Option Bool :=
  (recordOf E B).bind (recordRoute E B)

theorem recordRoute_of_not_muts {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    (h : ∀ ms, cb.info ≠ .muts ms) : recordRoute E B cb = some false := by
  unfold recordRoute
  cases hi : cb.info with
  | muts ms => exact absurd hi (h ms)
  | defn _ => rfl
  | axio _ => rfl
  | quot _ => rfl
  | recr _ => rfl
  | dPrj _ => rfl
  | iPrj _ => rfl
  | cPrj _ => rfl
  | rPrj _ => rfl

/-- **The dispatch against the record it loaded**: the run hashed bytes at the block's address
that decode to a record `c`, and the answer agrees with `recordRoute E B c`. -/
theorem record_route_agrees {E : Ixon.Env} {b : Bytes.Address} {bp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [bp] h r h' cs) :
    ∃ (raw : ByteArray) (c : Ixon.Constant), raw.size < 4294967296 ∧ Hashed cs raw ∧
      Address.blake3Pure raw = ixAddr b ∧ Ixon.deConstantExact raw = .ok c ∧
      Agrees (L1.CanonicalHashCoverage E cs) (recordRoute E (ixAddr b) c) r := by
  -- the dispatch's load of the record
  have hload : ∀ {x_info w39 w40 w41 w42 : SourceValue F} {m2 : Heap F} {cs12 : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [bp] h
        (.construct "Ixon::Constant" "Mk" [x_info, w39, w40, w41, w42]) m2 cs12 →
      (∀ z ∈ cs12, z ∈ cs) →
      ∃ (raw : ByteArray) (c : Ixon.Constant), raw.size < 4294967296 ∧ Hashed cs raw ∧
        Address.blake3Pure raw = ixAddr b ∧ Ixon.deConstantExact raw = .ok c ∧
        L1.RepConstantInfo m2 c.info x_info := by
    intro x_info w39 w40 w41 w42 m2 cs12 ev14 hs12
    obtain ⟨-, bytes, c, hlen, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hb ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    exact ⟨⟨bytes.toArray⟩, c, by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono hs12 hh, haddr, hexact, hinfo⟩
  -- at a block: its members, fewer than `2^39`
  have hmuts : ∀ {x_members w39 w40 w41 w42 : SourceValue F} {m2 : Heap F}
      {cs12 : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [bp] h
        (.construct "Ixon::Constant" "Mk"
          [.construct "Ixon::ConstantInfo" "Muts" [x_members], w39, w40, w41, w42]) m2 cs12 →
      (∀ z ∈ cs12, z ∈ cs) →
      ∃ (raw : ByteArray) (c : Ixon.Constant) (ms : Array Ixon.MutConst),
        raw.size < 4294967296 ∧ Hashed cs raw ∧
        Address.blake3Pure raw = ixAddr b ∧ Ixon.deConstantExact raw = .ok c ∧
        c.info = .muts ms ∧ RepList L1.mutConstListEnum L1.RepMutConst m2 ms.toList x_members ∧
        ms.size < 549755813888 := by
    intro x_members w39 w40 w41 w42 m2 cs12 ev14 hs12
    obtain ⟨raw, c, hsz, hh, haddr, hx, hrep⟩ := hload ev14 hs12
    obtain ⟨ms, hinfo, hmsRep⟩ := L1.repConstantInfo_muts_inv hrep
    have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound raw c hx
    have hsize := Claim.muts_size_le hinfo
    exact ⟨raw, c, ms, hsz, hh, haddr, hx, hinfo, hmsRep, by omega⟩
  rcases Obs.«KernelModeled::block_is_modeled».obs ev with
    ⟨m2, cs12, w39, w40, w41, w42, x_members, m90, cs101, ev14, ev103, he116, he117, hc118⟩ |
    ⟨m2, cs12, w39, w40, w41, w42, x_members, m90, cs101, m125, cs135, x_pos, x_n_ctors, v166,
      m167, cs177, cs199, ev14, ev103, ev137, ev179, ev201, hc241⟩ |
    ⟨m2, cs12, w39, w40, w41, w42, x_members, v89, m90, cs101, ev14, ev103, hne119, hne242,
      he246, he247, hc248⟩ |
    ⟨m2, cs12, x_info, w39, w40, w41, w42, ev14, hne249, he253, he254, hc255⟩
  · -- no inductive member
    subst hc118
    obtain ⟨raw, c, ms, hsz, hh, haddr, hx, hinfo, hmsRep, hmslt⟩ :=
      hmuts ev14 (fun z hz => by simp [hz])
    refine ⟨raw, c, hsz, hh, haddr, hx, ?_⟩
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec (membersRep_of_repMutConstList hmsRep)
      ev103
    have hfle := List.length_filter_le Specs.Callees.isIndc ms.toList
    have hlen : ms.toList.length = ms.size := Array.length_toList
    have h39 : (549755813888 : Nat) ≤ 2 ^ 39 := by norm_num
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 := by omega
    have hk0 : (ms.toList.filter Specs.Callees.isIndc).length = 0 :=
      (ModeledAux.natCast_inj_lt (by decide) hflen (Value.field.inj hcnt)).symm
    simp only [recordRoute, hinfo, mutsRoute, hk0]
    exact Agrees.pure (by rw [he116, bit_false])
  · -- exactly one inductive member: the scan of its constructors
    subst hc241
    obtain ⟨raw, c, ms, hsz, hh, haddr, hx, hinfo, hmsRep, hmslt⟩ :=
      hmuts ev14 (fun z hz => by simp [hz])
    refine ⟨raw, c, hsz, hh, haddr, hx, ?_⟩
    obtain ⟨hcnt, hm90⟩ := ModeledAux.muts_indc_count_spec
      (membersRep_of_repMutConstList hmsRep) ev103
    subst hm90
    have hfle := List.length_filter_le Specs.Callees.isIndc ms.toList
    have hlen : ms.toList.length = ms.size := Array.length_toList
    have h39 : (549755813888 : Nat) ≤ 2 ^ 39 := by norm_num
    have h39' : (2 : Nat) ^ 39 ≤ 549755813888 := by norm_num
    have hflen : (ms.toList.filter Specs.Callees.isIndc).length < 2 ^ 39 := by omega
    have hk1 : (ms.toList.filter Specs.Callees.isIndc).length = 1 :=
      (ModeledAux.natCast_inj_lt (a := 1) (by decide) hflen
        (by simpa using Value.field.inj hcnt)).symm
    -- the inductive member
    have ev137' : ObsFn Obs.W "KernelModeled::first_indc_pos"
        [x_members, .field ((0 : Nat) : F)] m90 (.tuple [x_pos, x_n_ctors]) m125 cs135 := ev137
    obtain ⟨p, ind, hfirst, hr137, hm125, hnlt⟩ := first_indc_pos_spec hbd
      (fun z hz => by simp [hz]) hmsRep ev137'
    injection hr137 with hl
    injection hl with h1 hl
    injection hl with h2
    subst h1 h2
    subst hm125
    obtain ⟨j, hpj, hmj⟩ := firstIndc_spec hfirst
    have hpe : p = j := by omega
    subst hpe
    have hplt : p < 549755813888 := by
      have := (List.getElem?_eq_some_iff.mp hmj).1
      omega
    -- the members' addresses
    have ext2 : Heap.Extends h m90 := ev14.heap_extends
    obtain ⟨ext3, mems, hmemsRep, hmap⟩ := L1.build_recur_addrs_spec
      (membersRep_of_repMutConstList hmsRep) (Bytes.repAddressRef_heapMono₂ addrTy ext2 hb) ev179
    rw [← L1.blockRecurAddrs_eq_mapIdx] at hmap
    have ev201' : ObsFn Obs.W "KernelModeled::ctors_nested"
        [bp, .field (p : F), .field (ind.ctors.toList.length : F), v166,
          .field ((0 : Nat) : F)] m167 r h' cs199 := ev201
    have aC := ctors_nested_agrees (E := E) hnc hbd hh hx haddr hinfo hmj hplt (by omega) hmap
      ind.ctors.toList.length 0 (by omega) (fun z hz => by simp [hz])
      (Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans ext3) hb) hmemsRep ev201'
    simp only [List.drop_zero] at aC
    simp only [recordRoute, hinfo, mutsRoute, hk1, oneRoute, hfirst]
    exact aC
  · -- two or more inductive members
    subst hc248
    obtain ⟨raw, c, ms, hsz, hh, haddr, hx, hinfo, hmsRep, hmslt⟩ :=
      hmuts ev14 (fun z hz => by simp [hz])
    refine ⟨raw, c, hsz, hh, haddr, hx, ?_⟩
    obtain ⟨hcnt, -⟩ := ModeledAux.muts_indc_count_spec (membersRep_of_repMutConstList hmsRep)
      ev103
    have h0 : (ms.toList.filter Specs.Callees.isIndc).length ≠ 0 :=
      fun e => hne119 (by rw [hcnt, e]; simp)
    have h1 : (ms.toList.filter Specs.Callees.isIndc).length ≠ 1 :=
      fun e => hne242 (by rw [hcnt, e]; simp)
    obtain ⟨k, hk⟩ : ∃ k, (ms.toList.filter Specs.Callees.isIndc).length = k + 2 :=
      ⟨(ms.toList.filter Specs.Callees.isIndc).length - 2, by omega⟩
    simp only [recordRoute, hinfo, mutsRoute, hk]
    exact Agrees.pure (by rw [he246, bit_true])
  · -- no block
    subst hc255
    obtain ⟨raw, c, hsz, hh, haddr, hx, hrep⟩ := hload ev14 (fun z hz => by simp [hz])
    refine ⟨raw, c, hsz, hh, haddr, hx, ?_⟩
    have hnm : ∀ ms, c.info ≠ .muts ms := by
      intro ms hi
      rw [hi] at hrep
      obtain ⟨msPtr, hmk, -⟩ := hrep
      exact hne249 [msPtr] rfl hmk
    rw [recordRoute_of_not_muts hnm]
    exact Agrees.pure (by rw [he253, bit_false])

/-- **The dispatch agrees with `blockRoute`**: for every observation of
`KernelModeled::block_is_modeled` that is bounded and hashes no collision with the store `E`,
the answer is `blockRoute E B` where that is known, and it is known where `E` holds every
canonical record the observation hashed. -/
theorem block_is_modeled_agrees {E : Ixon.Env} {b : Bytes.Address} {bp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [bp] h r h' cs) :
    Agrees (L1.CanonicalHashCoverage E cs) (blockRoute E (ixAddr b)) r := by
  obtain ⟨raw, c, hsz, hh, haddr, hx, ha⟩ := record_route_agrees hnc hbd hb ev
  constructor
  · intro v hv
    unfold blockRoute at hv
    cases hrec : recordOf E (ixAddr b) with
    | none =>
      rw [hrec] at hv
      cases hv
    | some c' =>
      rw [hrec] at hv
      have hv' : recordRoute E (ixAddr b) c' = some v := hv
      obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrec
      have eraw : raw = lc.rawBytes := Core.load_escape hget hnc raw hh haddr
      rw [eraw, hdec] at hx
      have ec : c' = c := Except.ok.inj hx
      rw [ec] at hv'
      exact ha.value v hv'
  · intro hcov
    obtain ⟨⟨lc, c', hlc, hcached, hce⟩, hval⟩ := hcov raw c hh hsz hx
    have ec : c' = c := hval
    subst ec
    have hrec : recordOf E (ixAddr b) = some c' := by
      rw [← haddr]
      unfold recordOf
      rw [hlc]
      simp [hce, Except.toOption]
    obtain ⟨v, hv⟩ := ha.known hcov
    refine ⟨v, ?_⟩
    unfold blockRoute
    rw [hrec]
    exact hv

end

end IxVM.Refinement.Route
