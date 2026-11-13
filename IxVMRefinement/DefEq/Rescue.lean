import IxVMRefinement.DefEq.Basic
import IxVMRefinement.Core.Certs
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Lib.Words
import IxVMRefinement.Lib.WordHints
import IxVMRefinement.Obs.Blake3
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PropWhen

/-! # Step lemmas of `KernelDefEq`: the rescue tier

* `is_prop_type`: the io-inferred type, head-normalized to a sort whose level `level_equal`
  equates with the stored `Zero` level (`levelEqual_eq_true_sound`).
* `leading_foralls`: one syntactic `∀` per unit of the counter (`HasPis`).
* `compare_struct_fields`: from `i` up to `nfields`, the projection `.proj S j t` (the stored
  `Proj` cell) against the argument of the constructor's spine at `nparams + j`
  (`Lists::lookup`); the counter stays below the field count, so `i + 1` does not wrap.
* `de_rescue_tier`: the tiers' answers (proof irrelevance, unit-like types, structure η both
  ways, the second by `DefEq.symm`, then the `Nat` offsets' pair). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

private theorem fval_one : ZMod.val (1 : F) = 1 := ZMod.val_one _

private theorem cast_val (x : F) : ((ZMod.val x : Nat) : F) = x := ZMod.natCast_zmod_val x

private theorem evalBinOp_add_field {a b : F} {v : SourceValue F}
    (op : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok v) : v = .field (a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

/-- A `Zero` level cell stored at the end of the heap. -/
private theorem repKLevel_store_zero (h : Heap F) :
    RepKLevel (h ++ [.construct IxVM.Refinement.KernelLevels.klevelEnum "Zero" []]) .zero
      (.ptr (.enum IxVM.Refinement.KernelLevels.klevelEnum) h.length) :=
  RepKLevel.zero (by simp)

/-- A `Proj` cell of a represented address and term, stored at the end of the heap. -/
private theorem tm_store_proj {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {a : Bytes.Address} {i : F} {E : KExpr} {ap ep : SourceValue F} (ha : RepAddr h a ap)
    (hE : c.tmk d Γ k h E ep) :
    c.tmk d Γ k (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]])
      (.proj (c.κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) :=
    Heap.Extends.snoc h _
  exact Tm.proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hE)

/-- `Lists::lookup` on a list of top-level terms: the term at the index; no allocation. -/
private theorem tml_lookup {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : c.tml d Γ h As l) :
    (∃ x, As[ZMod.val i]? = some x ∧ c.tm d Γ h x r) ∧ h' = h :=
  Lib.Lists.lookup_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

/-! ## Lists, counts, products -/

/-- `Lists::length` on a list of top-level terms. -/
private theorem tml_length {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : c.tml d Γ h As l) : r = .field (As.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

/-- `Lists::length` on a level list. -/
private theorem lvl_length {ls : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : IxVM.Refinement.KernelLevels.RepKLevelList h ls l) :
    r = .field (ls.length : F) ∧ h' = h := by
  have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := klevelListEnum_eq
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol, e]; exact hl)

/-- `Lists::take` on a list of top-level terms. -/
private theorem tml_take {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr}
    {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : c.tml d Γ h As l) :
    ZMod.val n ≤ As.length ∧ c.tml d Γ h' (As.take (ZMod.val n)) r := by
  have := Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := TmE c.κ d Γ) tmE_heapMono₂
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

private theorem val_natCast_small {m : Nat} (hm : m < 9223372036854775808) :
    ZMod.val (m : F) = m :=
  ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le hm (by decide))

private theorem natCast_inj_small {a b : Nat} (ha : a < 9223372036854775808)
    (hb : b < 9223372036854775808) (h : (a : F) = (b : F)) : a = b := by
  have h1 := val_natCast_small ha
  have h2 := val_natCast_small hb
  rw [h] at h1
  omega

private theorem lt_of_lt_2_39 {m : Nat} (hm : m < 2 ^ 39) : m < 9223372036854775808 :=
  Nat.lt_of_lt_of_le hm (by decide)

private theorem evalBinOp_mul_inv'' {x y r : SourceValue F} (h : evalBinOp .mul x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a * b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- A product other than `0` has both factors other than `0`. -/
private theorem mul_field_ne_zero' {x y r : SourceValue F} (op : evalBinOp .mul x y = .ok r)
    (hr : r ≠ .field 0) : x ≠ .field 0 ∧ y ≠ .field 0 := by
  obtain ⟨a, b, rfl, rfl, rfl⟩ := evalBinOp_mul_inv'' op
  refine ⟨fun e => hr ?_, fun e => hr ?_⟩
  · injection e with e
    subst e
    simp
  · injection e with e
    subst e
    simp

private theorem sub_field_zero {a b : F}
    (op : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok (.field 0)) : a = b := by
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
  exact sub_eq_zero.mp op

/-! ## Telescope certificates -/

/-- Instantiating a bound variable keeps the never-zero data of a telescope's leading `∀`s. -/
private theorem forallsNever_instantiate1 (v : KExpr) :
    ∀ (n : Nat) (b : KExpr) (k : Nat), Specs.Whnf.forallsNever n b →
      Specs.Whnf.forallsNever n (b.instantiate1 v k) := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih =>
    intro b k hb
    cases b with
    | forallE ty b' m =>
      obtain ⟨hm, hb'⟩ := hb
      exact And.intro hm (ih b' (k + 1) hb')
    | _ => exact (hb : False).elim

/-- **Never-zero slots certify every argument** (`Certs.skip`, licensed). -/
private theorem certs_of_forallsNever {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (T : KExpr), Specs.Whnf.forallsNever As.length T →
      Ix.Kernel.Rules.Certs env d true T As
  | [], _, _ => .nil
  | a :: As, T, hT => by
    cases T with
    | forallE ty b m =>
      obtain ⟨hm, hb⟩ := hT
      exact .skip rfl hm (certs_of_forallsNever As _ (forallsNever_instantiate1 a _ b 0 hb))
    | _ => exact (hT : False).elim

/-- `n` syntactic `∀`s strip. -/
private theorem stripPis_of_hasPis :
    ∀ (n : Nat) (T : KExpr), Specs.DefEq.HasPis n T → (T.stripPis n).isSome = true
  | 0, _, _ => rfl
  | n + 1, T, hT => by
    cases T with
    | forallE ty b m =>
      simp only [Ix.Kernel.Expr.stripPis, Option.isSome_map]
      exact stripPis_of_hasPis n b hT
    | _ => exact (hT : False).elim

/-- An unlicensed certificate is a licensed one. -/
private theorem certs_true {env : Ix.Kernel.Env .anon} {d : Nat} {lic : Bool} :
    ∀ {T : KExpr} {As : List KExpr}, Ix.Kernel.Rules.Certs env d lic T As →
      Ix.Kernel.Rules.Certs env d true T As
  | _, [], _ => .nil
  | _, _ :: _, h => by
    cases h with
    | skip _ hn hrest => exact .skip rfl hn (certs_true hrest)
    | cert hi hd hrest => exact .cert hi hd (certs_true hrest)

/-- Pairwise definitional equality from the pointwise one. -/
private theorem defEqList_of_get {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (Bs : List KExpr) (f : Nat → KExpr),
      (∀ j, j < Bs.length → ∃ S, Bs[j]? = some S ∧ Ix.Kernel.Rules.DefEq env d (f j) S) →
      Ix.Kernel.Rules.DefEqList env d ((List.range Bs.length).map f) Bs
  | [], f, _ => .nil
  | B :: Bs, f, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    obtain ⟨S, hS, hd⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hS
    subst hS
    exact .cons hd (defEqList_of_get Bs (f ∘ Nat.succ) fun j hj => by
      obtain ⟨S, hS, hd⟩ := h (j + 1) (by simp only [List.length_cons]; omega)
      exact ⟨S, by simpa using hS, hd⟩)

/-! ## Loaded constants -/

/-- A loaded `Induct` represents a stored inductive. -/
private theorem ciRep_induct_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nc u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) ci) :
    ∃ cv caps, ci = .indInfo cv caps ∧ ValRep κ h nl ty cv ∧
      (∃ nP nI nC : Nat, np = .field (nP : F) ∧ ni = .field (nI : F) ∧ nc = .field (nC : F) ∧
        nP < 72057594037927936 ∧ nI < 72057594037927936 ∧ nC < 72057594037927936) ∧
      (∃ (b : Bytes.Address) (i : F), RepAddr h b blk ∧ idx = .field i ∧
        cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i))) := by
  generalize hv : (Value.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx] :
    SourceValue F) = v at r
  cases r
  case induct hvr hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, rfl, hvr, hcounts, hkey⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- A loaded `Ctor` represents a stored constructor. -/
private theorem ciRep_ctor_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk ind cidx np nf u : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]) ci) :
    ∃ cv nP nF, ci = .ctorInfo cv nP nF ∧ ValRep κ h nl ty cv ∧ np = .field (nP : F) ∧
      nf = .field (nF : F) ∧ nP < 72057594037927936 ∧ nF < 72057594037927936 ∧
      ∃ (b : Bytes.Address) (i j : F), RepAddr h b blk ∧ ind = .field i ∧ cidx = .field j ∧
        cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) := by
  generalize hv : (Value.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u] :
    SourceValue F) = v at r
  cases r
  case ctor hvr hnp hnf hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, _, rfl, hvr, hnp, hnf, hcounts.1, hcounts.2, hkey⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

private theorem bytes_mk_toList (x : ByteArray) :
    (⟨(x.data.toList ++ []).toArray⟩ : ByteArray) = x := by
  cases x
  simp

/-- **A run of `bytes_to_addr` hashed its input** (its `Blake3::hash` call on the byte
stream). -/
private theorem hashed_of_bytes_to_addr {calls cs : List (Call F)} {bp r : SourceValue F}
    {h h' : Heap F} {bytes : List UInt8}
    (ev : ObsFn W "Blake3::bytes_to_addr" [bp] h r h' cs) (hsub : ∀ x ∈ cs, x ∈ calls)
    (hb : RepBytes h bytes bp) : Hashed calls ⟨bytes.toArray⟩ := by
  obtain ⟨v1, m2, cs12, v23, m24, cs31, ev14, he27, hm26, ev33, hc42⟩ :=
    Obs.«Blake3::bytes_to_addr».obs ev
  subst hc42
  unfold Hashed
  refine ⟨⟨"Blake3::hash", [bp], h⟩, hsub _ (by simp), rfl, bp, rfl, ?_⟩
  have e : (byteStreamEnum : String) = byteListEnum := rfl
  rw [e]
  simpa using hb

end IxVM.Refinement.Core.DefEqAux

/-! ## Positional levels

The composition of level instantiations at a positional term (as in the inference package's
`InferAux.posOf_instantiateLevelParams`). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel (Expr)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem instantiateLevelParams_comp' {ks : List Ix.Kernel.LevelParam} {us : List KLevel}
    {ps : List Ix.Kernel.LevelParam} {vs : List KLevel} (hl : vs.length = ps.length) :
    ∀ {e : KExpr}, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps vs).instantiateLevelParams ks us =
        e.instantiateLevelParams ps (vs.map (Ix.Kernel.Level.subst ks us)) := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]
  | sort u =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams,
      Ix.Kernel.Level.subst_subst (ks := ks) (us := us) hl h]
  | const n ls =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun u hu =>
      Ix.Kernel.Level.subst_subst (ks := ks) (us := us) hl (h u hu)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Ix.Kernel.Level.substPW_comp (ks := ks) (us := us) hl h.2]
  | forallE ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Ix.Kernel.Level.substPW_comp (ks := ks) (us := us) hl h.2]
  | letE ty val body l iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit _ => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]

private theorem getElem?_subst_go_range'' :
    ∀ (s : Nat) (us : List KLevel) (i : Nat), s ≤ i → i < s + us.length →
      us[i - s]? = some (Ix.Kernel.Level.subst.go (List.range' s us.length) us i)
  | s, [], i, h1, h2 => by
    have : ([] : List KLevel).length = 0 := rfl
    omega
  | s, u :: us, i, h1, h2 => by
    show _ = some (if s = i then u else
      Ix.Kernel.Level.subst.go (List.range' (s + 1) us.length) us i)
    have hl : (u :: us).length = us.length + 1 := rfl
    by_cases h : s = i
    · subst h
      rw [ite_eq_left rfl, Nat.sub_self, List.getElem?_cons_zero]
    · rw [ite_eq_right h, show i - s = i - (s + 1) + 1 by omega, List.getElem?_cons_succ]
      exact getElem?_subst_go_range'' (s + 1) us i (by omega) (by omega)

private theorem getElem?_eq_subst_go_range' {us : List KLevel} {i : Nat} (hi : i < us.length) :
    us[i]? = some (Ix.Kernel.Level.subst.go (List.range us.length) us i) := by
  have := getElem?_subst_go_range'' 0 us i (Nat.zero_le i) (by omega)
  rwa [Nat.sub_zero, ← List.range_eq_range'] at this

private theorem posLevels_map_subst' {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hlen : us.length = ps.length) :
    (posLevels ps).map (Ix.Kernel.Level.subst (List.range us.length) us) = us := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < us.length
  · have h1 : (posLevels ps)[i]? = some (Ix.Kernel.Level.param i) := by
      rw [posLevels, List.getElem?_map, List.getElem?_range (by omega)]; rfl
    rw [h1, getElem?_eq_subst_go_range' hi]; rfl
  · have h1 : (posLevels ps)[i]? = none := by
      rw [List.getElem?_eq_none_iff, posLevels, List.length_map, List.length_range]
      omega
    have h2 : us[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h1, h2]; rfl

/-- **Instantiating a positional term positionally** is instantiating the term at its own
parameters. -/
private theorem posOf_instantiateLevelParams' {ps : List Ix.Kernel.LevelParam}
    {us : List KLevel} {T : KExpr} (hlen : us.length = ps.length)
    (hdef : T.allLevelParamsDefined ps = true) :
    (posOf ps T).instantiateLevelParams (List.range us.length) us =
      T.instantiateLevelParams ps us := by
  have hl : (posLevels ps).length = ps.length := by
    rw [posLevels, List.length_map, List.length_range]
  unfold posOf
  rw [instantiateLevelParams_comp' hl hdef, posLevels_map_subst' hlen]

end IxVM.Refinement.Core.DefEqAux

/-! ## The install facts the rescue tier reads -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Infer)

/-- **What the unit-like and structure-η tests need from the environment**, stated over what
the circuit observes: the kernel environment, the records `c.E`, and an observed load with the
value it loads (as `LoadFacts.indRecord` states one). The capability record and the
projection tables are the kernel's install computation (`nativeCapsAt` and the native tables,
`IxC/Kernel/Inductives/NativeInstall.lean`; the pinned `PUnit`), which the declarations layer
relates to the records the loads decode. -/
structure RescueFacts (c : Ctx) : Prop where
  /-- Every stored type mentions only its constant's level parameters (`ConstWF`). -/
  typeLevels : ∀ k ci, c.env.find? k = some ci →
    ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true
  /-- **A stored record whose bytes are a projection record's canonical encoding decodes to that
  record** (the claim's canonical store, `Ix.Cert.Stream.StoredCanonical`, and the injectivity
  of the encoding on wire-valid constants). -/
  canonical : ∀ (x : _root_.Address) (lc : Ixon.LazyConstant) (info : Ixon.ConstantInfo),
    c.E.consts.get? x = some lc → lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[]⟩ →
      ∀ cm, lc.get? = some cm → cm.info = info
  /-- **Unit-likeness**: an inductive that `get_ci` loads with no index and one constructor
  (whose stored constructor, at the first constructor record of its member, has no field), at a
  block with at most one inductive, is unit-like at its loaded parameter count; at a reserved
  basis key it is the pinned `PUnit` (no parameter, `isUnitLikeTy`). -/
  unitLike : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs → RepAddr h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    RepAddr h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) →
    Specs.Callees.FewInductives c (ixAddr b) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  /-- **Structure η**: the inductive member `i` of the block `b`, as `get_ci_iprj` loads it with
  no index and one constructor, whose block `block_is_modeled` answers `0`, whose sort after the
  constructor's parameters is never zero at some levels, and whose projection record
  `struct_is_rec` does not find recursive, is η-capable through the constructor `c.κ ac` (a
  stored constructor of that member with at least one field), with that constructor's field
  count (`nativeCapsAt`: `eta`, `etaCtor`, `etaFields`). -/
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    c.env.find? (c.κ (ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Good c cs1 → RepAddr h1 b bp →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Good c cs3 ∧
        RepAddr h3 b bq) →
    Specs.Whnf.piSortAt cnP (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c cs5 ∧
        RepAddr h5 sa sp) →
    ixAddr sa = iprjAddr (ixAddr b) (ZMod.val i) →
    caps.eta = true ∧ caps.etaCtor = some (c.κ (ixAddr ac)) ∧ caps.etaFields = cnF
  /-- **An η-capable stored family has a projection table entry at each of its `etaFields`
  slots** (`EtaTowers`, `IxC/Kernel/Model/StoreCompanions.lean`). -/
  etaTowers : ∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    Ix.Kernel.towerSlotsAll c.env T caps.etaFields = true
  /-- **The type of a full application of an η-constructor**: its io-inferred type reduces to the
  structure at the same levels applied to the parameters (the stored constructor's type is the
  telescope of the parameters and fields ending in the structure at the constructor's level
  parameters applied to the parameter variables). -/
  etaType : ∀ (T kc : KKey) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (nP nF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    c.env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ (d : Nat) (us : List KLevel) (Ss : List KExpr) (ta : KExpr), Ss.length = nP + nF →
      Infer c.env .io d (Ix.Kernel.Expr.mkAppN (.const kc us) Ss) ta →
      Red c.env d ta (Ix.Kernel.Expr.mkAppN (.const T us) (Ss.take nP))

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEq)
open IxVM.Refinement.Core.DefEqAux

set_option linter.unusedVariables false

/-! ## Propositions -/

/-- `KernelDefEq::is_prop_type`: the io-inferred type (`k_infer_only`) head-normalizes (`whnf`)
to a sort whose level `level_equal` equates with `Zero`, so it is `0` at every assignment. -/
theorem is_prop_type_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::is_prop_type" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.is_prop_type c args h r h' calls := by
  intro rc ty types hargs good hrc d Γ htypes T hT hr
  subst hargs
  rcases Obs.«KernelDefEq::is_prop_type».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, x_l, cs104, m117, ev14, ev52, ld88, hm125, ev106, hc129⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, ev14, ev52, ld88, hne130, he134, he135, hc136⟩
  · subst hc129 hm125
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨S, hS, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc ty types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes T hT
    obtain ⟨S', hS', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) S hS
    obtain ⟨u, rfl, l, hl, hul⟩ := hS'.sort_of_load ld88
    obtain ⟨hr', -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev106 x_l _ rfl
      (good.sub fun x hx => by simp [hx]).2 l .zero (hl.mono (Heap.Extends.snoc _ _))
      (repKLevel_store_zero m40)
    have he : IxVM.Refinement.KernelLevels.levelEqual l .zero = true :=
      of_ite_field_ne_zero hr' hr
    exact ⟨S, u, hinf, hred, fun φ =>
      (hul φ).trans (IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound he φ)⟩
  · exact absurd he134 hr

/-! ## Telescopes -/

/-- `KernelDefEq::leading_foralls`: one `∀` node per unit of the counter. -/
theorem leading_foralls_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::leading_foralls" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.leading_foralls c args h r h' calls := by
  intro t n hargs good hr d Γ k T hT
  subst hargs
  rcases Obs.«KernelDefEq::leading_foralls».obs ev with
    ⟨hv14, he15, he16, hc17⟩ |
    ⟨w41, x_body, w42, cs61, v65, hne18, ld33, op86, ev63, hc88⟩ |
    ⟨v22, hne18, ld33, hne89, he93, he94, hc95⟩
  · injection hv14 with hn
    subst hn
    simp only [ZMod.val_zero]
    exact True.intro
  · subst hc88
    have hn0 : n ≠ 0 := fun hn => hne18 (by subst hn; rfl)
    obtain rfl := Lib.sub_one_inv op86
    obtain ⟨T1, B1, ℓ1, rfl, -, hB1, -⟩ := hT.forallE_of_load ld33
    have hrec := ih.get (.defEq .leading_foralls) (by lt_calls) ev63 x_body (n - 1) rfl
      (good.sub fun x hx => by simp [hx]) hr d Γ (k + 1) B1 hB1
    rw [← Lib.val_sub_one hn0]
    exact hrec
  · exact absurd he93 hr

/-! ## Structure η: the fields -/

/-- `KernelDefEq::compare_struct_fields`: from `i` up to `nfields`, each projection of `t`
(the stored `Proj` cell) against the argument of `s_args` at `nparams + j` (`Lists::lookup`).
The counter stays below `nfields`, so `i + 1` reads as the next natural. -/
theorem compare_struct_fields_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::compare_struct_fields" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.compare_struct_fields c args h r h' calls := by
  intro rc sp np nf t sargs ip types hargs good hrc sa p n i hsa hnp hnf hip hin d Γ htypes T Ss
    hT hSs hr
  subst hargs hnp hnf hip
  rcases Obs.«KernelDefEq::compare_struct_fields».obs ev with
    ⟨op17, he24, he25, hc26⟩ |
    ⟨v1, m32, v70, m71, cs81, v85, m110, cs121, op17, hne27, hm42, op106, ev83, ev123, he160,
      he161, hc162⟩ |
    ⟨v1, m32, v70, m71, cs81, v85, v109, m110, cs121, cs170, v179, op17, hne27, hm42, op106, ev83,
      ev123, hne163, op236, ev172, hc245⟩
  · -- no field left: the range is empty
    intro j hij hjn
    obtain ⟨k, hk1, hk2⟩ := eq_of_sub_field op17
    injection hk1 with hk1
    injection hk2 with hk2
    subst hk1 hk2
    omega
  · exact absurd he160 hr
  · subst hc245 hm42
    obtain ⟨a1, b1, ha1, hb1, rfl⟩ := evalBinOp_sub_inv' op17
    injection ha1 with ha1
    injection hb1 with hb1
    subst ha1 hb1
    have hni : n ≠ i := fun e => hne27 (by rw [e]; simp)
    have hlt : ZMod.val i < ZMod.val n :=
      lt_of_le_of_ne hin fun e => hni (ZMod.val_injective _ e).symm
    have hvi : ZMod.val (i + 1) = ZMod.val i + 1 := by
      have := ZMod.val_lt n
      rw [ZMod.val_add_of_lt (by have := fval_one; omega), fval_one]
    obtain rfl := evalBinOp_add_field op106
    obtain rfl := evalBinOp_add_field op236
    have e0 : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [sp, .field i, t]]) :=
      Heap.Extends.snoc _ _
    -- field `i`: the projection against the spine's argument at `nparams + i`
    obtain ⟨⟨S0, hS0, hS0r⟩, rfl⟩ := tml_lookup ev83 (tml_mono e0 hSs)
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev123 rc _ v70 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) _ S0
      (tm_store_proj hsa hT) hS0r hne163
    -- the fields from `i + 1` on
    have E := e0.trans (ObsFn.heap_extends ev123)
    have hrec := ih.get (.defEq .compare_struct_fields) (by lt_calls) ev172 rc sp _ _ t sargs _
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E hrc) sa p n (i + 1)
      (Bytes.repAddressRef_heapMono₂ addrTy E hsa) rfl rfl rfl (by omega) d Γ
      (types_mono E htypes) T Ss (Tm.mono E hT) (tml_mono E hSs) hr
    intro j hij hjn
    rcases Nat.eq_or_lt_of_le hij with rfl | hj
    · exact ⟨S0, by simpa only [cast_val] using hS0, hde⟩
    · exact hrec j (by omega) hjn

/-! ## The rescue tier -/

/-- `KernelDefEq::de_rescue_tier`: a decided answer `1` is the `DefEq` of the tier that decided
it: proof irrelevance, unit-like types, structure η (`try_eta_struct(bw, aw)` by `DefEq.symm`),
or the `Nat` offsets' pair. -/
theorem de_rescue_tier_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_rescue_tier" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.de_rescue_tier c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB y hy hy0
  subst hargs
  rcases Obs.«KernelDefEq::de_rescue_tier».obs ev with
    ⟨m2, cs13, ev15, he56, he69, hc70⟩ |
    ⟨v1, m2, cs13, m76, cs87, ev15, hne71, ev89, he130, he143, hc144⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, m150, cs161, ev15, hne71, ev89, hne145, ev163, he204, he217,
      hc218⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, v149, m150, cs161, m224, cs235, ev15, hne71, ev89, hne145, ev163,
      hne219, ev237, he278, he291, hc292⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, v149, m150, cs161, v223, m224, cs235, cs300, ev15, hne71, ev89,
      hne145, ev163, hne219, ev237, hne293, ev302, hc335⟩
  · subst hc70
    exact ih.get (.defEq .try_proof_irrel) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc144
    have e := ObsFn.heap_extends ev15
    exact ih.get (.defEq .try_unit_like) (by lt_calls) ev89 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) field_one_ne_zero
  · subst hc218
    have e := (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev89)
    exact ih.get (.defEq .try_eta_struct) (by lt_calls) ev163 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) field_one_ne_zero
  · subst hc292
    have e := (ObsFn.heap_extends ev15).trans
      ((ObsFn.heap_extends ev89).trans (ObsFn.heap_extends ev163))
    exact .symm (ih.get (.defEq .try_eta_struct) (by lt_calls) ev237 rc b a types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) B A
      (Tm.mono e hB) (Tm.mono e hA) field_one_ne_zero)
  · subst hc335
    have e := (ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev89).trans
      ((ObsFn.heap_extends ev163).trans (ObsFn.heap_extends ev237)))
    exact ih.get (.defEq .try_def_eq_nat) (by lt_calls) ev302 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) y hy hy0

/-! ## Projection records -/

/-- `KernelDefEq::compute_iprj_addr`: the inductive-projection record built from the index's
bytes (`UInt64::from_field`) and the block address, with empty tables, serialized
(`put_constant`) and hashed (`bytes_to_addr`): its address is `iprjAddr`. The run hashed those
bytes, so a record of `c.E` there has them as its bytes (`load_escape`, under `Good`), and
decodes to that record (`RescueFacts.canonical`). -/
theorem compute_iprj_addr_step (c : Ctx) (rf : RescueFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::compute_iprj_addr" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.compute_iprj_addr c args h r h' calls := by
  intro bp ip hargs good b i hb hip
  subst hargs hip
  obtain ⟨v1, m2, cs12, m83, m96, m109, v121, m122, cs132, m145, cs160, ev14, hm91, hm104, hm117,
    hm153, ev134, ev162, hc171⟩ := Obs.«KernelDefEq::compute_iprj_addr».obs ev
  subst hc171
  obtain ⟨n, hn, hx, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  injection hx with hx
  have hval : ZMod.val i = n := by
    rw [hx]
    exact val_natCast_small (by omega)
  have e1 : Heap.Extends m2 m83 := by rw [hm91]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m83 m96 := by rw [hm104]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m96 m109 := by rw [hm117]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m109 m145 := by rw [hm153]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m145 := by
    rw [← hm2]
    exact e1.trans (e2.trans (e3.trans e4))
  have c1 : m145[m2.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans e4)).getElem?_eq (by rw [hm91]; simp)
  have c2 : m145[m83.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans e4).getElem?_eq (by rw [hm104]; simp)
  have c3 : m145[m96.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    e4.getElem?_eq (by rw [hm117]; simp)
  have c4 : m145[m109.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm153]
    simp
  have hrep : RepU64 m145 (ZMod.val i).toUInt64 (TagN.u64Value n) := by
    rw [hval]
    have e := Lib.repU64_ofNatLT m145 (m := n) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m145 (.iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [TagN.u64Value n, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value n, bp, b, rfl, hrep, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := ih.get (.callees .put_constant) (by lt_calls) ev134 _ _
    (.iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩) [] rfl
    (by
      unfold Specs.Callees.ProjConstRep
      exact ⟨_, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
        RepLinkedList.nil c3⟩)
    (RepLinkedList.nil c4)
  obtain ⟨a, ha, haddr⟩ := ih.get (.callees .bytes_to_addr) (by lt_calls) ev162 v121 _ rfl hbytes
  refine ⟨a, ha, ?_, ?_⟩
  · rw [haddr, bytes_mk_toList]
    rfl
  · -- the run hashed the record's bytes
    intro cm hcm
    have key : ∀ o : Option Ixon.LazyConstant, o.bind (·.get?) = some cm →
        ∃ lc, o = some lc ∧ lc.get? = some cm := by
      intro o ho
      cases o with
      | none => simp at ho
      | some lc => exact ⟨lc, rfl, ho⟩
    obtain ⟨lc, hlc, hget⟩ := key (c.E.consts.get? (ixAddr a)) hcm
    have hraw := load_escape hlc good.1 _
      (hashed_of_bytes_to_addr ev162 (fun x hx => by simp [hx]) hbytes) haddr.symm
    rw [bytes_mk_toList] at hraw
    exact rf.canonical _ lc _ hlc hraw.symm cm hget

/-! ## A family's parameters -/

/-- The counts `family_params` compares: the argument and level lists have the given lengths
(`Lists::length`, then `Fields::is_zero` of the differences; the lists have fewer than `2^39`
elements, so the field equations are equations of naturals). No allocation. -/
private theorem fp_counts {c : Ctx} {calls : List (Call F)} (good : Good c calls) {d : Nat}
    {Γ : Nat → KExpr} {h m33 m12 m69 m2 : Heap F}
    {xs lvls x31 x67 v24 v60 x10 y11 : SourceValue F} {n p : F} {As : List KExpr}
    {us : List KLevel} {cs42 cs21 cs78 cs57 : List (Call F)}
    (hm1 : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xs], h⟩ : Call F) ∈ calls)
    (hm2 : (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], m12⟩ : Call F) ∈ calls)
    (hAs : c.tml d Γ h As xs) (hus : LvListRep h us lvls)
    (ev44 : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [xs] h x31 m33 cs42)
    (op38 : evalBinOp .sub x31 (.field p) = .ok v24)
    (ev23 : ObsFn W "Fields::is_zero" [v24] m33 x10 m12 cs21)
    (ev80 : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [lvls] m12 x67 m69 cs78)
    (op74 : evalBinOp .sub x67 (.field n) = .ok v60)
    (ev59 : ObsFn W "Fields::is_zero" [v60] m69 y11 m2 cs57)
    (op17 : evalBinOp .mul x10 y11 = .ok (.field 1)) :
    m2 = h ∧ As.length = ZMod.val p ∧ us.length = ZMod.val n := by
  obtain ⟨hx31, hm33⟩ := tml_length ev44 hAs
  obtain ⟨hx10, hm12⟩ := Lib.is_zero_spec ev23
  obtain ⟨ls, hls, hlv⟩ := hus
  have hlen : us.length = ls.length := Ix.Kernel.Level.EvalEqList.length_eq (hlv fun _ => 0)
  have hls12 : IxVM.Refinement.KernelLevels.RepKLevelList m12 ls lvls := by
    rw [hm12, hm33]
    exact hls
  obtain ⟨hx67, hm69⟩ := lvl_length ev80 hls12
  obtain ⟨hy11, hm2'⟩ := Lib.is_zero_spec ev59
  obtain ⟨hz1, hz2⟩ := mul_field_ne_zero' op17 field_one_ne_zero
  have hv24 : v24 = .field 0 := of_ite_field_ne_zero hx10 hz1
  have hv60 : v60 = .field 0 := of_ite_field_ne_zero hy11 hz2
  subst hx31 hx67 hv24 hv60
  have hpA : ((As.length : ℕ) : F) = p := sub_field_zero op38
  have hpU : ((ls.length : ℕ) : F) = n := sub_field_zero op74
  have hbA : As.length < 2 ^ 39 := RomBound.bounded_length_lt good.2 hm1 (by simp) hAs
  have hbU : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2 hm2 (by simp) hls12
  refine ⟨by rw [hm2', hm69, hm12, hm33], ?_, ?_⟩
  · rw [← hpA, val_natCast_small (lt_of_lt_2_39 hbA)]
  · rw [hlen, ← hpU, val_natCast_small (lt_of_lt_2_39 hbU)]

/-- `KernelDefEq::family_params`: the counts (`fp_counts`), then the level instantiation of the
closed type (`expr_inst_levels`, at depth `0`, which reads at every depth) and its licensed
certificate: all slots `never` (`slots_never`, `Certs.skip`), or `n` syntactic `∀`s
(`leading_foralls`) and the unlicensed walk (`certs_all`, read as `Certs` by
`CertsR.toCerts`). -/
theorem family_params_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::family_params" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.family_params c args h r h' calls := by
  intro rc nl ty np lvls xs types hargs good hrc n p hnl hnp d Γ htypes T us As hT hus hAs hr
  subst hargs hnl hnp
  rcases Obs.«KernelDefEq::family_params».obs ev with
    ⟨m2, x10, y11, m12, cs21, v24, x31, m33, cs42, cs57, v60, x67, m69, cs78, v94, m95, cs105,
      m125, cs136, ev44, op38, ev23, ev80, op74, ev59, op17, ev107, ev138, he159, he160, hc161⟩ |
    ⟨m2, x10, y11, m12, cs21, v24, x31, m33, cs42, cs57, v60, x67, m69, cs78, v94, m95, cs105,
      v124, m125, cs136, m167, cs178, cs204, m234, ev44, op38, ev23, ev80, op74, ev59, op17, ev107,
      ev138, hne162, ev180, hm242, ev206, hc253⟩ |
    ⟨m2, x10, y11, m12, cs21, v24, x31, m33, cs42, cs57, v60, x67, m69, cs78, v94, m95, cs105,
      v124, m125, cs136, v166, m167, cs178, ev44, op38, ev23, ev80, op74, ev59, op17, ev107, ev138,
      hne162, ev180, hne254, he258, he259, hc260⟩ |
    ⟨v1, m2, x10, y11, m12, cs21, v24, x31, m33, cs42, cs57, v60, x67, m69, cs78, ev44, op38, ev23,
      ev80, op74, ev59, op17, hne261, he265, he266, hc267⟩
  · -- every slot `never`
    subst hc161
    obtain ⟨rfl, hlA, hlU⟩ := fp_counts good (by simp) (by simp) hAs hus ev44 op38 ev23 ev80 op74
      ev59 op17
    have hTI := ih.get (.subst .expr_inst_levels) (by lt_calls) ev107 ty lvls rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 T us (hT 0 Γ) hus
    have hfn := ih.get (.whnf .slots_never) (by lt_calls) ev138 v94 _ rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ p (Tm.of_depth_zero hTI d) rfl
      field_one_ne_zero
    refine ⟨hlA, hlU, certs_of_forallsNever As _ ?_⟩
    rw [hlA]
    exact hfn
  · -- `n` syntactic `∀`s and the walk
    subst hc253
    obtain ⟨rfl, hlA, hlU⟩ := fp_counts good (by simp) (by simp) hAs hus ev44 op38 ev23 ev80 op74
      ev59 op17
    have hTI := ih.get (.subst .expr_inst_levels) (by lt_calls) ev107 ty lvls rfl
      (good.sub fun x hx => by simp [hx]) Γ 0 T us (hT 0 Γ) hus
    have e1 := ObsFn.heap_extends ev107
    have e2 := ObsFn.heap_extends ev138
    have e3 := ObsFn.heap_extends ev180
    have e4 : Heap.Extends m167 m234 := by rw [hm242]; exact Heap.Extends.snoc _ _
    have hpis := ih.get (.defEq .leading_foralls) (by lt_calls) ev180 v94 p rfl
      (good.sub fun x hx => by simp [hx]) field_one_ne_zero d Γ 0 _
      (Tm.of_depth_zero (Tm.mono e2 hTI) d)
    have E := e1.trans (e2.trans (e3.trans e4))
    have hnil : c.tml d Γ m234 [] (.ptr (.enum kexprListEnum) m167.length) := by
      rw [hm242]
      exact TmL.store_nil m167
    have hcr := ih.get (.whnf .certs_all) (by lt_calls) ev206 rc v94 xs _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E hrc) d Γ (types_mono E htypes) _ [] As
      (Tm.of_depth_zero (Tm.mono (e2.trans (e3.trans e4)) hTI) d) hnil (tml_mono E hAs) hr
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcr
    refine ⟨hlA, hlU, certs_true (Specs.Whnf.CertsR.toCerts hcr ?_)⟩
    rw [hlA]
    exact stripPis_of_hasPis _ _ hpis
  · exact absurd he258 hr
  · exact absurd he265 hr

/-! ## Unit-like types -/

/-- `KernelDefEq::is_unit_like_type`: the head of the spine is a constant (`collect_spine`) whose
loaded constant is an inductive (`get_ci`) with no index, at a block with at most one inductive
(`block_is_multi`), with one constructor (its first constructor record, `get_ci_cprj`, has no
field) and not recursive (`struct_is_rec`); its parameters are certified (`family_params`). The
capabilities are the install's (`RescueFacts.unitLike`); the family's telescope at the
positional levels is its type at its own parameters (`RescueFacts.typeLevels`). -/
theorem is_unit_like_type_step (c : Ctx) (rf : RescueFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::is_unit_like_type" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.is_unit_like_type c args h r h' calls := by
  intro rc ty types hargs good hrc d Γ htypes T hT hr
  subst hargs
  have p := Obs.«KernelDefEq::is_unit_like_type».obs ev
  cases p
  case Const_Induct_n0_n0_Ctor_n0_n0 m2 cs13 x_head x_args x_addr x_lvls m70 p77 cs83 x_ind_nl
      x_ind_ty x_ind_np x_n_indices x_num_ctors w110 x_block x_idx m152 y161 cs172 m210 p217 cs223
      w265 w266 w267 w268 w269 w270 w271 m327 cs338 cs356 ev15 ld51 ev85 ld79 ev174 op167 op203
      ev225 ld219 ev340 ev358 hc =>
    subst hc
    have e15 := ObsFn.heap_extends ev15
    have e85 := ObsFn.heap_extends ev85
    have e174 := ObsFn.heap_extends ev174
    have e225 := ObsFn.heap_extends ev225
    have e340 := ObsFn.heap_extends ev340
    -- the spine and its head
    obtain ⟨hd, sp, H, As, he, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev15
      ty rfl (good.sub fun x hx => by simp [hx]) d Γ 0 T hT
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld51
    -- the loaded inductive
    obtain ⟨ci, hfind, v, hv, hrep⟩ := ih.get (.callees .get_ci) (by lt_calls) ev85 x_addr a rfl
      (good.sub fun x hx => by simp [hx]) ha
    rw [ld79] at hv
    injection hv with hv
    subst hv
    obtain ⟨cvT, caps, rfl, hval, ⟨nP, nI, nC, rfl, rfl, rfl, hnP, hnI, hnC⟩, ⟨b, i, hb, rfl, -⟩⟩ :=
      ciRep_induct_inv hrep
    obtain ⟨hnl, hlp, hnd, hty⟩ := hval
    subst hnl
    -- no index; at most one inductive in the block
    obtain ⟨h01, hmulti⟩ := ih.get (.callees .block_is_multi) (by lt_calls) ev174 x_block b rfl
      (good.sub fun x hx => by simp [hx]) hb
    have hnI0 : nI = 0 ∧ y161 = .field 0 := by
      rcases h01 with rfl | rfl
      · refine ⟨natCast_inj_small (b := 0) (by omega) (by omega) ?_, rfl⟩
        rw [Nat.cast_zero]
        simpa only [evalBinOp, Except.ok.injEq, Value.field.injEq, add_zero] using op167
      · exfalso
        have h1 : ((nI + 1 : ℕ) : F) = ((0 : ℕ) : F) := by
          rw [Nat.cast_succ, Nat.cast_zero]
          simpa only [evalBinOp, Except.ok.injEq, Value.field.injEq] using op167
        have := natCast_inj_small (by omega) (by omega) h1
        omega
    obtain ⟨rfl, rfl⟩ := hnI0
    have hfew : Specs.Callees.FewInductives c (ixAddr b) := by
      intro cst ms hcst hms
      exact Nat.le_of_not_lt fun hlt =>
        zero_ne_one (Value.field.inj ((hmulti cst hcst).mpr ⟨ms, hms, hlt⟩))
    -- one constructor, with no field
    have hnC1 : ((nC : ℕ) : F) = 1 := sub_field_zero op203
    have hnC' : nC = 1 :=
      natCast_inj_small (b := 1) (by omega) (by omega) (by rw [Nat.cast_one]; exact hnC1)
    subst hnC'
    have hb152 : RepAddr m152 b x_block := Bytes.repAddressRef_heapMono₂ addrTy e174 hb
    obtain ⟨ciC, hfindC, vC, hvC, hrepC⟩ := ih.get (.callees .get_ci_cprj) (by lt_calls) ev225
      x_block i 0 b rfl (good.sub fun x hx => by simp [hx]) hb152
    rw [ld219] at hvC
    injection hvC with hvC
    subst hvC
    obtain ⟨cvC, nPc, nF, rfl, -, -, hnf, -, hnF, -⟩ := ciRep_ctor_inv hrepC
    have hnF0 : nF = 0 := natCast_inj_small (by omega) (by omega)
      (by rw [Nat.cast_zero]; exact (Value.field.inj hnf).symm)
    subst hnF0
    simp only [ZMod.val_zero] at hfindC
    -- the parameters
    have E327 : Heap.Extends m70 m327 := e174.trans (e225.trans e340)
    have E2 : Heap.Extends m2 m327 := e85.trans E327
    obtain ⟨hlA, hlU, hcerts⟩ := ih.get (.defEq .family_params) (by lt_calls) ev358 rc _ x_ind_ty
      _ x_lvls x_args types rfl (good.sub fun x hx => by simp [hx])
      (RCRep.mono (e15.trans E2) hrc) (cvT.levelParams.length : F) (nP : F) rfl rfl d Γ
      (types_mono (e15.trans E2) htypes) (posOf cvT.levelParams cvT.type) us As
      (TmC.mono E327 hty) (LvListRep.mono E2 hus) (tml_mono E2 hAs) hr
    rw [val_natCast_small (m := nP) (by omega)] at hlA
    rw [val_natCast_small (m := cvT.levelParams.length) (by omega)] at hlU
    have htl : cvT.type.allLevelParamsDefined cvT.levelParams = true := rf.typeLevels _ _ hfind
    rw [posOf_instantiateLevelParams' hlU htl] at hcerts
    -- the capabilities
    rw [Nat.cast_zero, Nat.cast_one] at ld79
    obtain ⟨hul, hup, hbasis⟩ := rf.unitLike x_addr p77 m2 m70 cs83 a _ x_ind_ty w110 x_block
      (nP : F) i b cvT caps cvC nPc ev85 (good.sub fun x hx => by simp [hx]) ha ld79 hb hfind
      hfew hfindC
    rw [val_natCast_small (m := nP) (by omega)] at hup hbasis
    have hargs' : (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr a)) us) As).getAppArgs = As := by
      rw [getAppArgs_mkAppN]; rfl
    refine ⟨c.κ (ixAddr a), us, cvT, caps, ?_, hfind, hul, ?_, ?_, ?_⟩
    · rw [getAppFn_mkAppN]; rfl
    · rw [hargs', hlA, hup]
    · rw [hargs']; exact hcerts
    · rcases hbasis with hb' | ⟨h0, hiu⟩
      · exact .inl hb'
      · right
        have hA0 : As = [] := List.eq_nil_of_length_eq_zero (hlA.trans h0)
        subst hA0
        exact hiu us
  all_goals (subst_vars; exact absurd rfl hr)

/-- `KernelDefEq::try_unit_like`: `DefEq.unitLikeTy`. `a`'s io-inferred type head-normalizes to a
unit-like family at its parameters (`is_unit_like_type`), and the two io-inferred types compare
(`k_is_def_eq`). -/
theorem try_unit_like_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_unit_like" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_unit_like c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_unit_like».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, ev14, ev52, ev91, he120, he121, hc⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, v127, m128, cs138, cs168, ev14, ev52, ev91,
      hne123, ev140, ev170, hc⟩
  · exact absurd he120 hr
  · subst hc
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev52
    have e3 := ObsFn.heap_extends ev91
    have e4 := ObsFn.heap_extends ev140
    obtain ⟨TA, hTA, hinfA⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    obtain ⟨WA, hWA, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) TA hTA
    have E40 := e1.trans e2
    obtain ⟨K, us, cvT, caps, hfn, hfind, hul, hlen, hcerts, hbasis⟩ :=
      ih.get (.defEq .is_unit_like_type) (by lt_calls) ev91 rc v39 types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono E40 hrc) d Γ (types_mono E40 htypes) WA
        hWA hne123
    have E78 := E40.trans e3
    obtain ⟨TB, hTB, hinfB⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev140 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E78 hrc) d Γ (types_mono E78 htypes) B
      (Tm.mono E78 hB)
    have E128 := E78.trans e4
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev170 rc v1 v127 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E128 hrc) d Γ (types_mono E128 htypes) TA
      TB (Tm.mono (e2.trans (e3.trans e4)) hTA) hTB hr
    exact .unitLikeTy hinfA hred hfn hfind hul hlen hcerts hbasis hinfB hde

/-! ## Structure η -/

/-- `KernelDefEq::try_eta_struct`: `DefEq.structEtaTy` (its `b` is `t`, its `a` is `s`). `s` is a
fully applied constructor (`collect_spine`, `get_ci`, `Lists::length`) of an inductive
(`get_ci_iprj`) with no index and one constructor, at a block `block_is_modeled` answers `0`
for, with at least one field and a never-zero sort (`type_sort_never`), not recursive
(`struct_is_rec` at its projection record, `compute_iprj_addr`); the parameters are certified
(`family_params` on `Lists::take`), the io-inferred types compare (`k_is_def_eq`), and every
field compares with its projection of `t` (`compare_struct_fields`). The capabilities, the
projection table and the constructor application's type are the install's (`RescueFacts`). -/
theorem try_eta_struct_step (c : Ctx) (rf : RescueFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_eta_struct" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_eta_struct c args h r h' calls := by
  intro rc t s types hargs good hrc d Γ htypes T S hT hS hr
  subst hargs
  have p := Obs.«KernelDefEq::try_eta_struct».obs ev
  cases p
  case Const_Ctor_n0_Induct_other_other_other_other m2 cs13 x_s_head x_s_args x_ctor_addr
      x_s_lvls m70 p77 cs83 w110 w111 x_ind_block_addr x_ind_idx w112 x_nparams x_nfields w113 x163
      y164 m165 cs174 m200 p207 cs213 x_ind_nl x_ind_ty w248 x_nindices x_nctors w249 w250 w251
      v292 m293 x300 y301 m302 x308 y309 m310 x316 y317 m318 cs327 cs341 v344 cs363 v366 m368
      cs376 x387 y388 m389 y396 cs406 cs420 v468 m469 cs479 v498 m499 cs510 v532 m533 cs544 v552
      m590 cs598 v635 m636 cs646 v673 m674 cs684 v711 m712 cs723 cs772 ev15 ld51 ev85 ld79 ev176
      op192 op170 ev215 ld209 ev329 op358 ev343 op323 ev378 ev365 op315 ev408 op402 ev422 op394
      op307 hne464 ev481 ev512 hne528 ev600 ev546 hne631 ev648 ev686 ev725 hne765 ev774 hc838 =>
    subst hc838
    have e15 := ObsFn.heap_extends ev15
    have e85 := ObsFn.heap_extends ev85
    have e176 := ObsFn.heap_extends ev176
    have e215 := ObsFn.heap_extends ev215
    have e329 := ObsFn.heap_extends ev329
    have e343 := ObsFn.heap_extends ev343
    have e378 := ObsFn.heap_extends ev378
    have e365 := ObsFn.heap_extends ev365
    have e408 := ObsFn.heap_extends ev408
    have e422 := ObsFn.heap_extends ev422
    have e481 := ObsFn.heap_extends ev481
    have e512 := ObsFn.heap_extends ev512
    have e600 := ObsFn.heap_extends ev600
    have e546 := ObsFn.heap_extends ev546
    have e648 := ObsFn.heap_extends ev648
    have e686 := ObsFn.heap_extends ev686
    have e725 := ObsFn.heap_extends ev725
    have E310 : Heap.Extends m200 m310 := e329.trans e343
    have E389 : Heap.Extends m310 m389 := e378.trans (e365.trans e408)
    have E200_293 : Heap.Extends m200 m293 := E310.trans (E389.trans e422)
    have E165_293 : Heap.Extends m165 m293 := e215.trans E200_293
    have E70_499 : Heap.Extends m70 m499 := e176.trans (E165_293.trans (e481.trans e512))
    have E70_712 : Heap.Extends m70 m712 :=
      E70_499.trans (e600.trans (e546.trans (e648.trans (e686.trans e725))))
    have E590 : Heap.Extends h m590 := (e15.trans (e85.trans E70_499)).trans e600
    have E533 : Heap.Extends h m533 := E590.trans e546
    have E636 : Heap.Extends h m636 := E533.trans e648
    have E674 : Heap.Extends h m674 := E636.trans e686
    have E712 : Heap.Extends h m712 := E674.trans e725
    -- the spine of `s`: a constant head
    obtain ⟨hd, sp, H, Ss, he, hH, hSs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev15 s
      rfl (good.sub fun x hx => by simp [hx]) d Γ 0 S hS
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ac, us, rfl, hac, hus⟩ := hH.const_of_load ld51
    -- the loaded constructor
    obtain ⟨ciC, hfindC, vC, hvC, hrepC⟩ := ih.get (.callees .get_ci) (by lt_calls) ev85
      x_ctor_addr ac rfl (good.sub fun x hx => by simp [hx]) hac
    rw [ld79] at hvC
    injection hvC with hvC
    subst hvC
    obtain ⟨cvc, cnP, cnF, rfl, -, rfl, rfl, hcnP, hcnF, b, i, j, hb, rfl, -, hcname⟩ :=
      ciRep_ctor_inv hrepC
    -- the spine has `cnP + cnF` arguments
    have hSs70 : c.tml d Γ m70 Ss x_s_args := tml_mono e85 hSs
    obtain ⟨hx163, -⟩ := tml_length ev176 hSs70
    subst hx163
    obtain rfl := evalBinOp_add_field op192
    have hlenF : ((Ss.length : ℕ) : F) = ((cnP + cnF : ℕ) : F) := by
      rw [Nat.cast_add]
      exact sub_field_zero op170
    have hb39 : Ss.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_s_args], m70⟩) (by simp)
      (by simp) hSs70
    have hSlen : Ss.length = cnP + cnF :=
      natCast_inj_small (lt_of_lt_2_39 hb39) (by omega) hlenF
    -- the loaded inductive
    have hb165 : RepAddr m165 b x_ind_block_addr := Bytes.repAddressRef_heapMono₂ addrTy e176 hb
    obtain ⟨ciT, hfindT, vT, hvT, hrepT⟩ := ih.get (.callees .get_ci_iprj) (by lt_calls) ev215
      x_ind_block_addr i b rfl (good.sub fun x hx => by simp [hx]) hb165
    rw [ld209] at hvT
    injection hvT with hvT
    subst hvT
    obtain ⟨cvT, caps, rfl, hvalT, ⟨nP', nI, nC, rfl, rfl, rfl, -, hnI, hnC⟩, -⟩ :=
      ciRep_induct_inv hrepT
    obtain ⟨hnlT, hlpT, hndT, htyT⟩ := hvalT
    subst hnlT
    -- the shape: no index, one constructor, a block `block_is_modeled` answers `0` for, a field,
    -- a never-zero sort
    obtain ⟨hx300, hy301⟩ := mul_field_ne_zero' op307 hne464
    obtain ⟨hx308, hy309⟩ := mul_field_ne_zero' op315 hx300
    obtain ⟨hx316, hy317⟩ := mul_field_ne_zero' op323 hx308
    obtain ⟨hx387, hy388⟩ := mul_field_ne_zero' op394 hy301
    obtain ⟨h316, -⟩ := Lib.is_zero_spec ev329
    obtain ⟨h317, -⟩ := Lib.is_zero_spec ev343
    obtain ⟨h309, -⟩ := Lib.is_zero_spec ev365
    obtain ⟨h396, -⟩ := Lib.is_zero_spec ev408
    have hnI0 := of_ite_field_ne_zero h316 hx316
    have hv344 := of_ite_field_ne_zero h317 hy317
    have hv366 := of_ite_field_ne_zero h309 hy309
    subst hv344 hv366
    have hnI' : nI = 0 := natCast_inj_small (b := 0) (by omega) (by omega)
      (by rw [Nat.cast_zero]; exact Value.field.inj hnI0)
    have hnC1 : ((nC : ℕ) : F) = 1 := sub_field_zero op358
    have hnC' : nC = 1 :=
      natCast_inj_small (b := 1) (by omega) (by omega) (by rw [Nat.cast_one]; exact hnC1)
    subst hnI' hnC'
    rw [Nat.cast_zero, Nat.cast_one] at ld209
    have hnf0 : 0 < cnF := by
      rcases Nat.eq_zero_or_pos cnF with h0 | h0
      · exfalso
        subst h0
        have hy : y396 = .field 1 := by
          rw [h396]
          simp
        subst hy
        obtain ⟨a1, b1, ha1, hb1, rfl⟩ := evalBinOp_sub_inv' op402
        injection ha1 with ha1
        injection hb1 with hb1
        subst ha1 hb1
        exact hx387 (by simp)
      · exact h0
    have hcnPv : ZMod.val (cnP : F) = cnP := val_natCast_small (by omega)
    have hcnFv : ZMod.val (cnF : F) = cnF := val_natCast_small (by omega)
    have hus389 : LvListRep m389 us x_s_lvls :=
      LvListRep.mono (e85.trans (e176.trans (e215.trans (E310.trans E389)))) hus
    have hTy389 : c.tmk d Γ 0 m389 (posOf cvT.levelParams cvT.type) x_ind_ty :=
      (TmC.mono (E310.trans E389) htyT) d Γ
    obtain ⟨l, hpi, hnz⟩ := ih.get (.whnf .type_sort_never) (by lt_calls) ev422 x_ind_ty _
      x_s_lvls rfl (good.sub fun x hx => by simp [hx]) d Γ 0 _ (cnP : F) us hTy389 rfl hus389
      hy388
    rw [hcnPv] at hpi
    -- the structure's projection record
    obtain ⟨sa, hsa, hsaddr, -⟩ := ih.get (.defEq .compute_iprj_addr) (by lt_calls) ev481
      x_ind_block_addr _ rfl (good.sub fun x hx => by simp [hx]) b i
      (Bytes.repAddressRef_heapMono₂ addrTy E165_293 hb165) rfl
    -- the parameters
    obtain ⟨-, hTake⟩ := tml_take ev600 (tml_mono E70_499 hSs70)
    obtain ⟨-, hlenU, hcerts⟩ := ih.get (.defEq .family_params) (by lt_calls) ev546 rc _
      x_ind_ty _ x_s_lvls v552 types rfl (good.sub fun x hx => by simp [hx])
      (RCRep.mono E590 hrc) (cvT.levelParams.length : F) (cnP : F) rfl rfl d Γ
      (types_mono E590 htypes) (posOf cvT.levelParams cvT.type) us
      (Ss.take (ZMod.val (cnP : F)))
      (TmC.mono (E200_293.trans (e481.trans (e512.trans e600))) htyT)
      (LvListRep.mono (e85.trans (E70_499.trans e600)) hus) hTake hne631
    rw [val_natCast_small (m := cvT.levelParams.length) (by omega)] at hlenU
    have htl : cvT.type.allLevelParamsDefined cvT.levelParams = true := rf.typeLevels _ _ hfindT
    rw [hcnPv, posOf_instantiateLevelParams' hlenU htl] at hcerts
    -- the io-inferred types
    obtain ⟨TT, hTT, hinfT⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev648 rc t types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E533 hrc) d Γ (types_mono E533 htypes) T
      (Tm.mono E533 hT)
    obtain ⟨TS, hTS, hinfS⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev686 rc s types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E636 hrc) d Γ (types_mono E636 htypes) _
      (Tm.mono E636 hS)
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev725 rc v635 v673 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E674 hrc) d Γ (types_mono E674 htypes) TT
      TS (Tm.mono e686 hTT) hTS hne765
    -- the fields
    have hflds := ih.get (.defEq .compare_struct_fields) (by lt_calls) ev774 rc v468 _ _ t
      x_s_args _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E712 hrc) sa
      (cnP : F) (cnF : F) 0
      (Bytes.repAddressRef_heapMono₂ addrTy
        (e512.trans (e600.trans (e546.trans (e648.trans (e686.trans e725))))) hsa)
      rfl rfl rfl (by simp) d Γ (types_mono E712 htypes) T Ss (Tm.mono E712 hT)
      (tml_mono E70_712 hSs70) hr
    -- the install facts
    obtain ⟨heta, hctor, hetaF⟩ := rf.eta ac b sa i (ZMod.val j) cvc cvT caps cnP cnF us l
      x_ind_block_addr p207 _ _ _ _ _ _ m165 m200 cs213 hfindC hcname hnf0 ev215
      (good.sub fun x hx => by simp [hx]) hb165 ld209 hfindT
      ⟨x_ind_block_addr, m310, m368, cs376, ev378, good.sub fun x hx => by simp [hx],
        Bytes.repAddressRef_heapMono₂ addrTy (e215.trans E310) hb165⟩
      hpi hnz
      ⟨v468, v498, m469, m499, cs510, ev512, hne528, good.sub fun x hx => by simp [hx], hsa⟩
      hsaddr
    have htower := rf.etaTowers _ cvT caps hfindT heta
    rw [hetaF] at htower
    have hred := rf.etaType _ _ cvT cvc caps cnP cnF hfindT heta hctor hfindC d us Ss TS hSlen
      hinfS
    -- the rule
    have hargs' : (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr ac)) us) Ss).getAppArgs = Ss := by
      rw [getAppArgs_mkAppN]; rfl
    have hfn : (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr ac)) us) Ss).getAppFn =
        .const (c.κ (ixAddr ac)) us := by
      rw [getAppFn_mkAppN]; rfl
    have hdl : Ix.Kernel.Rules.DefEqList c.env d
        ((List.range cnF).map fun k => .proj (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) k T)
        (Ss.drop cnP) := by
      have hlen' : (Ss.drop cnP).length = cnF := by
        rw [List.length_drop]
        omega
      rw [← hlen']
      refine defEqList_of_get _ _ fun k hk => ?_
      rw [hlen'] at hk
      obtain ⟨S', hS', hd'⟩ := hflds k (by simp) (by rw [hcnFv]; exact hk)
      have hv : ZMod.val (((cnP + k : ℕ)) : F) = cnP + k := val_natCast_small (by omega)
      refine ⟨S', ?_, ?_⟩
      · rw [List.getElem?_drop]
        rw [← Nat.cast_add, hv] at hS'
        exact hS'
      · rw [hsaddr] at hd'
        exact hd'
    refine DefEq.structEtaTy hfn hfindC (by rw [hargs']; exact hSlen) hfindT heta hctor hnf0
      htower hinfS (by rw [hargs']; exact hred) (by rw [hargs']; exact hcerts) hinfT hde ?_
    rw [hargs']
    exact hdl
  all_goals (subst_vars; exact absurd rfl hr)

end IxVM.Refinement.Core
