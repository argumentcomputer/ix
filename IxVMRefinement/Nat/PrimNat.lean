import IxVMRefinement.Nat.Basic
import IxVMRefinement.Core.Open
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Obs.KernelNatPrim

/-! # `KernelNatPrim`: reading `Nat` values, folding operations, the stuck offset forms

Step lemmas of the `Nat` reading and dispatching functions of `KernelNatPrim`, against the
kernel's rules: a literal, `Nat.zero` and `Nat.succ x` read as literals (`Red.refl`,
`Red.natZeroLit`, `Red.natSucc`); a binary operation on two readable arguments folds to
`natOpResult` (`Red.natOp`, the `Nat.pow` cap included); `Nat.add b (lit (k + 1))` steps to
`Nat.succ (b + k)` (`Red.natAddSucc`); the stuck forms keep a readable second argument as a
literal (`Red.natAddZero`, `Red.appArg`), and a reduct of the head is carried through the rest of
the spine (`Red.appFn`).

The rules' guards come from the environment invariant: `natLitSupported` once one role of `Nat`'s
block is in force (or `Nat.add`, a dependent of `Nat`), `natAddTyOk` for `Nat.add`, and
`natOpStored` for the operation in force. The key of an address the table binds to a role is the
role (`keyOf_of_addressOf`).

Two callees are read through a stronger statement than their registered specs:
`try_match_nat_add_strong` also gives that `Nat.add` is in force (its `role_is` answer), and
`try_nat_binop_addr_strong` that tag `1` comes only at the codes `3 … 16` (so never at
`Nat.pred`, which `natBinOpNames` does not hold). `try_nat_offset_dispatch`'s `match` has the
or-pattern `6 | 7`; its paths are read off its derivation here
(`try_nat_offset_dispatch_obs`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open NatAux

set_option linter.unusedVariables false

/-- The value of a small field literal. -/
local macro "prim_val_lit" n:num : tactic =>
  `(tactic| simpa using (val_natCast (n := $n) (by decide)))

namespace PrimNat

/-! ## Helpers -/

theorem val_two : ZMod.val (2 : F) = 2 := by prim_val_lit 2

theorem ext_snoc {h₁ h₂ : Heap F} (e : Heap.Extends h₁ h₂) (v : SourceValue F) :
    Heap.Extends h₁ (h₂ ++ [v]) :=
  e.trans (Heap.Extends.snoc h₂ v)

theorem tag_one_ne_zero {x y : SourceValue F} :
    (Value.tuple [.field 1, x] : SourceValue F) ≠ .tuple [.field 0, y] := by
  intro e
  injection e with e1
  injection e1 with e2
  exact field_one_ne_zero e2

theorem tag3_one_ne_zero {x y z w : SourceValue F} :
    (Value.tuple [.field 1, x, y] : SourceValue F) ≠ .tuple [.field 0, z, w] := by
  intro e
  injection e with e1
  injection e1 with e2
  exact field_one_ne_zero e2

theorem tag_eq_zero {t : F} {x y : SourceValue F}
    (e : (Value.tuple [.field t, x] : SourceValue F) = .tuple [.field 0, y]) : t = 0 := by
  injection e with e1
  injection e1 with e2
  exact field_inj e2

theorem tag_snd {a b : F} {x y : SourceValue F}
    (e : (Value.tuple [.field a, x] : SourceValue F) = .tuple [.field b, y]) : x = y :=
  (List.cons.inj (List.cons.inj (Value.tuple.inj e)).2).1

theorem tag3_snd {a b : F} {x y z w : SourceValue F}
    (e : (Value.tuple [.field a, x, y] : SourceValue F) = .tuple [.field b, z, w]) :
    x = z ∧ y = w :=
  have e1 := (List.cons.inj (Value.tuple.inj e)).2
  ⟨(List.cons.inj e1).1, (List.cons.inj (List.cons.inj e1).2).1⟩

/-- **The role of a `Nat` operation code**, `natPrimOp`'s inverse. -/
def natPrimRole : Nat → Option Ix.Kernel.Role
  | 1 => some .natSucc
  | 2 => some .natPred
  | 3 => some .natAdd
  | 4 => some .natSub
  | 5 => some .natMul
  | 6 => some .natDiv
  | 7 => some .natMod
  | 8 => some .natGcd
  | 9 => some .natPow
  | 10 => some .natLand
  | 11 => some .natLor
  | 12 => some .natXor
  | 13 => some .natShiftLeft
  | 14 => some .natShiftRight
  | 15 => some .natBeq
  | 16 => some .natBle
  | _ => none

theorem natPrimOp_inv {r : Ix.Kernel.Role} {o : Nat} (h : Specs.Nat.natPrimOp r = some o) :
    natPrimRole o = some r := by
  cases r <;> simp [Specs.Nat.natPrimOp] at h <;> subst h <;> rfl

/-- **A code determines its role.** -/
theorem natPrimOp_role {r r' : Ix.Kernel.Role} {o : Nat} (h : Specs.Nat.natPrimOp r = some o)
    (h' : natPrimRole o = some r') : r = r' := by
  have := natPrimOp_inv h
  rw [h'] at this
  exact (Option.some.inj this).symm

/-- **A binary `Nat` operation** (a code from `3` on) is one of the fourteen the kernel
accelerates. -/
theorem natBinOp_mem {ro : Ix.Kernel.Role} {o : Nat} (h : Specs.Nat.natPrimOp ro = some o)
    (h3 : 3 ≤ o) : (Ix.Kernel.Key.role ro : KKey) ∈ Ix.Kernel.Rules.natBinOpNames := by
  cases ro <;> first
    | decide
    | (exfalso; simp [Specs.Nat.natPrimOp] at h <;> omega)

/-- `natLitSupported` from a role in force whose block holds `Nat`, `Nat.zero` and `Nat.succ`. -/
theorem natLit_of_natBlock {c : Ctx} (hc : CoreFacts c) {r : Ix.Kernel.Role} (hr : c.inForce r)
    (h0 : Ix.Kernel.Role.nat ∈ r.block) (h1 : Ix.Kernel.Role.natZero ∈ r.block)
    (h2 : Ix.Kernel.Role.natSucc ∈ r.block) : Ix.Kernel.natLitSupported c.env = true :=
  hc.env.natLit (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h0))
    (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h1))
    (Ctx.inForce_of_block_or_dep hc.env.tableWf hr (.inl h2))

/-- `natLitSupported` from `Nat.add` in force (`Nat` is a dependency of `Nat.add`). -/
theorem natLit_of_natAdd {c : Ctx} (hc : CoreFacts c) (hr : c.inForce .natAdd) :
    Ix.Kernel.natLitSupported c.env = true :=
  natLit_of_natBlock hc
    (Ctx.inForce_of_block_or_dep (s := .nat) hc.env.tableWf hr (.inr (by decide)))
    (by decide) (by decide) (by decide)

theorem natAddLit_zero (B : KExpr) : Ix.Kernel.Rules.natAddLit B 0 = B := by
  simp [Ix.Kernel.Rules.natAddLit]

theorem natAddLit_ne {B : KExpr} {n : Nat} (hn : n ≠ 0) :
    Ix.Kernel.Rules.natAddLit B n =
      .app (.app (.const Ix.Kernel.natAddName []) B) (.lit (.natVal n)) := by
  simp [Ix.Kernel.Rules.natAddLit, hn]

/-- **A reduct of the head, through the rest of a spine** (`Red.appFn` at each argument). -/
theorem red_mkAppN {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (Ps : List KExpr) {f f' : KExpr},
      Red env d f f' → Red env d (Ix.Kernel.Expr.mkAppN f Ps) (Ix.Kernel.Expr.mkAppN f' Ps)
  | [], _, _, h => h
  | _ :: Ps, _, _, h => red_mkAppN Ps (.appFn h)

theorem red_mkAppN₁ {env : Ix.Kernel.Env .anon} {d : Nat} {f a₀ E : KExpr} (Ps : List KExpr)
    (h : Red env d (.app f a₀) E) :
    Red env d (Ix.Kernel.Expr.mkAppN f (a₀ :: Ps)) (Ix.Kernel.Expr.mkAppN E Ps) :=
  red_mkAppN Ps h

theorem red_mkAppN₂ {env : Ix.Kernel.Env .anon} {d : Nat} {f a₀ a₁ E : KExpr} (Ps : List KExpr)
    (h : Red env d (.app (.app f a₀) a₁) E) :
    Red env d (Ix.Kernel.Expr.mkAppN f (a₀ :: a₁ :: Ps)) (Ix.Kernel.Expr.mkAppN E Ps) :=
  red_mkAppN Ps h

theorem spine_one {As : List KExpr} {x : KExpr} (h0 : As[ZMod.val (0 : F)]? = some x) :
    ∃ Ps, As = x :: Ps := by
  rw [val_zero] at h0
  rcases As with _ | ⟨a, Ps⟩
  · simp at h0
  · simp at h0
    exact ⟨Ps, by rw [h0]⟩

theorem spine_two {As : List KExpr} {x y : KExpr} (h0 : As[ZMod.val (0 : F)]? = some x)
    (h1 : As[ZMod.val (1 : F)]? = some y) : ∃ Ps, As = x :: y :: Ps := by
  rw [val_zero] at h0
  rw [val_one] at h1
  rcases As with _ | ⟨a, _ | ⟨b, Ps⟩⟩
  · simp at h0
  · simp at h1
  · simp at h0 h1
    exact ⟨Ps, by rw [h0, h1]⟩

/-! ### Lists of terms -/

theorem kl_lookup {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr} {l r : SourceValue F}
    {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : c.tml d Γ h As l) :
    (∃ x, As[ZMod.val i]? = some x ∧ c.tm d Γ h x r) ∧ h' = h :=
  Lib.Lists.lookup_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

theorem kl_drop {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr} {l r : SourceValue F}
    {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : c.tml d Γ h As l) :
    ZMod.val n ≤ As.length ∧ c.tml d Γ h (As.drop (ZMod.val n)) r ∧ h' = h := by
  have := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    _ rfl (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

theorem kl_length {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : c.tml d Γ h As l) : r = .field (As.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

/-! ### Building terms -/

/-- **A `Const` node over a fresh empty level list**, at a represented address. -/
theorem tm_const_nil {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {a : Bytes.Address} {ap : SourceValue F} (ra : RepAddr h a ap) :
    Tm κ d Γ ((h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []]) ++
        [.construct "KernelTypes::KExprNode" "Const"
          [ap, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length]]) 0
      (.const (κ (ixAddr a)) [])
      (.ptr (.enum "KernelTypes::KExprNode")
        (h ++ [(.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [] :
          SourceValue F)]).length) := by
  have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := klevelListEnum_eq
  have ext2 := ext_snoc (Heap.Extends.snoc h
    (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []))
    (.construct "KernelTypes::KExprNode" "Const"
      [ap, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length])
  refine Tm.const (ls := []) (ap := ap)
    (lsp := .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») h.length) (by simp)
    (Bytes.repAddressRef_heapMono₂ addrTy ext2 ra) ?_ (LvEqList.refl [])
  rw [e]
  exact .nil (by simp)

/-- **A stored literal node** of canonical limbs. -/
theorem tm_store_lit {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₀ h : Heap F}
    {n : Nat} {lp : SourceValue F} (hl : Specs.Nat.RepLimbsC h₀ n lp) (ext : Heap.Extends h₀ h) :
    Tm κ d Γ (h ++ [.construct "KernelTypes::KExprNode" "Lit"
        [.construct "KernelTypes::KLiteral" "Nat" [lp]]]) 0
      (.lit (.natVal n)) (.ptr (.enum "KernelTypes::KExprNode") h.length) := by
  obtain ⟨ls, hls, rfl, hcn⟩ := hl
  exact .litNat (by simp) (lrep_mono (ext_snoc ext _) hls) hcn

/-- The word `[0, 0, 0, 1, 0, …]` holds `2^24`, `Nat.pow`'s exponent cap. -/
theorem word_cap (h : Heap F) :
    ∃ w : UInt64, w.toNat = 16777216 ∧ RepU64 h w (.tuple [.field 0, .field 0, .field 0,
      .field 1, .field 0, .field 0, .field 0, .field 0]) := by
  obtain ⟨w, hw, hr⟩ := word_of h (m := 16777216) (by norm_num)
  refine ⟨w, hw, ?_⟩
  have e : (TagN.u64Value 16777216 : SourceValue F) = .tuple [.field 0, .field 0, .field 0,
      .field 1, .field 0, .field 0, .field 0, .field 0] := by
    simp [TagN.u64Value]
  rwa [e] at hr

/-- **A limb result, normalized and stored as a literal**: the closed literal of its value. -/
theorem norm_lit {c : Ctx} {calls : List (Call F)} (ih : IH c calls) (good : Good c calls)
    {v51 v38 v18 : SourceValue F} {m53 m40 m27 : Heap F} {cs48 cs35 : List (Call F)} {k : Nat}
    (ev50 : ObsFn W "KernelKlimbs::klimbs_normalize" [v51] m53 v38 m40 cs48)
    (ev37 : ObsFn W "KernelNatPrim::mk_nat_lit" [v38] m40 v18 m27 cs35)
    (s1 : ∀ x ∈ cs48, x ∈ calls) (l1 : cs48.length < calls.length)
    (s2 : ∀ x ∈ cs35, x ∈ calls) (l2 : cs35.length < calls.length)
    (hv : RepLimbs m53 k v51) : c.tmc m27 (Specs.Nat.natLit k) v18 := by
  have hn := ih.get (.nat .klimbs_normalize) l1 ev50 v51 rfl (good.sub s1) k hv
  exact ih.get (.nat .mk_nat_lit) l2 ev37 v38 rfl (good.sub s2) k hn

/-! ### The or-pattern `6 | 7` -/

theorem matchPattern_orLiteral {world : World F} {types : Types} (a b : F) (v : SourceValue F)
    (heap : Heap F) :
    world.matchPattern types heap
        (Aiur.Generic.Pattern.orElse (.literal a) (.literal b) { names := [] }) v =
      .ok (if v = .field a ∨ v = .field b then some [] else none) := by
  unfold World.matchPattern
  rw [matchPatternWith]
  have hl : ∀ x : F, matchPatternWith world.constant world.constDepth types heap (.literal x) v =
      .ok (if v = .field x then some [] else none) := fun x => matchPattern_literal_any x v heap
  rw [hl a, hl b]
  by_cases ha : v = .field a
  · subst ha
    simp [bind, Except.bind, pure, Except.pure, Aiur.Generic.reorderBindings]
  · by_cases hb : v = .field b
    · subst hb
      simp [ha, bind, Except.bind, pure, Except.pure, Except.map, Aiur.Generic.reorderBindings]
    · simp [ha, hb, bind, Except.bind, pure, Except.pure, Except.map]

theorem matchPattern_orLiteral_some {world : World F} {types : Types} {a b : F}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    (h : world.matchPattern types heap
        (Aiur.Generic.Pattern.orElse (.literal a) (.literal b) { names := [] }) v = .ok (some bs)) :
    bs = [] := by
  rw [matchPattern_orLiteral] at h
  by_cases hv : v = .field a ∨ v = .field b
  · simp only [hv, ite_true, Except.ok.injEq, Option.some.injEq] at h
    exact h.symm
  · simp [hv] at h

end PrimNat

open PrimNat

/-! ## The paths of `try_nat_offset_dispatch` -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The paths of `KernelNatPrim::try_nat_offset_dispatch`**, read off its derivation (its
`match op` has the or-pattern `6 | 7`). The spine's tail is `post = Lists::drop(spine, 2)`; at
code `3` the result is tag `2` and `mk_nat_offset_stuck`'s tag-`1` term; at code `6` or `7`, tag
`2` and `mk_nat_binop_stuck`'s term, or tag `0`; at any other code, tag `0`. -/
theorem try_nat_offset_dispatch_obs {x_rc x_ap x_op x_a0 x_nb x_sp : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_offset_dispatch" [x_rc, x_ap, x_op, x_a0, x_nb, x_sp]
      h r h' calls) :
    (∃ (post : SourceValue F) (m₁ : Heap F) (cs₁ : List (Call F)) (stuck : SourceValue F)
        (cs₂ : List (Call F)),
      ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [x_sp, .field 2] h post m₁ cs₁ ∧
      x_op = .field 3 ∧
      ObsFn W "KernelNatPrim::mk_nat_offset_stuck" [x_rc, x_a0, x_nb, post] m₁
        (.tuple [.field 1, stuck]) h' cs₂ ∧
      r = .tuple [.field 2, stuck] ∧ (∀ x ∈ cs₂, x ∈ calls) ∧ cs₂.length < calls.length) ∨
    (∃ (post : SourceValue F) (m₁ m₂ : Heap F) (cs₁ : List (Call F)) (s : SourceValue F)
        (cs₂ : List (Call F)),
      ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [x_sp, .field 2] h post m₁ cs₁ ∧
      Heap.Extends m₁ m₂ ∧
      ObsFn W "KernelNatPrim::mk_nat_binop_stuck" [x_ap, x_a0, x_nb, post] m₂ s h' cs₂ ∧
      r = .tuple [.field 2, s] ∧ (∀ x ∈ cs₂, x ∈ calls) ∧ cs₂.length < calls.length) ∨
    (∃ p, r = .tuple [.field 0, p]) := by
  have d0 := ObsFn.function_inv (s := IxVM.source)
    IxVM.KernelNatPrim.try_nat_offset_dispatch.lookup
    (by simp [IxVM.KernelNatPrim.try_nat_offset_dispatch, ControlLower.hasControl]) ev
  simp only [IxVM.KernelNatPrim.try_nat_offset_dispatch] at d0
  -- `let post = Lists::drop(spine, 2)`
  obtain ⟨v1, m2, bs3, c4, c5, d6, mt7, d8, rfl⟩ := d0.letValue_inv
  obtain ⟨vs9, m10, c11, cs12, a13, ev14, rfl⟩ := d6.call_inv
  rw [Obs.Names.n4825454920124213627] at ev14
  obtain ⟨v15, vs16, m17, c18, c19, rfl, d20, a21, rfl⟩ := a13.cons_inv
  obtain ⟨l22, rfl, rfl⟩ := d20.var_inv
  simp at l22
  subst l22
  obtain ⟨v23, vs24, m25, c26, c27, rfl, d28, a29, rfl⟩ := a21.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := d28.literal_inv
  obtain ⟨rfl, rfl, rfl⟩ := a29.nil_inv
  obtain rfl := matchPattern_bind_inv mt7
  -- `match op`
  obtain ⟨v30, m31, bs32, body33, c34, c35, d36, sel37, d38, rfl⟩ := d8.matchValue_inv
  obtain ⟨l39, rfl, rfl⟩ := d36.var_inv
  simp at l39
  subst l39
  rcases selectArm_cons_inv sel37 with ⟨mt40, rfl⟩ | ⟨nm41, sel42⟩
  · -- `3 => match mk_nat_offset_stuck(rc, a0_w, nb, post) { (1, stuck) => (2, stuck), _ => … }`
    obtain ⟨hv43, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt40
    obtain ⟨v44, m45, bs46, body47, c48, c49, d50, sel51, d52, rfl⟩ := d38.matchValue_inv
    obtain ⟨vs53, m54, c55, cs56, a57, ev58, rfl⟩ := d50.call_inv
    rw [instanceName_plain_some] at ev58
    obtain ⟨u1, us1, n1, k1, k2, rfl, e1, a1, rfl⟩ := a57.cons_inv
    obtain ⟨l1, rfl, rfl⟩ := e1.var_inv
    simp at l1
    subst l1
    obtain ⟨u2, us2, n2, k3, k4, rfl, e2, a2, rfl⟩ := a1.cons_inv
    obtain ⟨l2, rfl, rfl⟩ := e2.var_inv
    simp at l2
    subst l2
    obtain ⟨u3, us3, n3, k5, k6, rfl, e3, a3, rfl⟩ := a2.cons_inv
    obtain ⟨l3, rfl, rfl⟩ := e3.var_inv
    simp at l3
    subst l3
    obtain ⟨u4, us4, n4, k7, k8, rfl, e4, a4, rfl⟩ := a3.cons_inv
    obtain ⟨l4, rfl, rfl⟩ := e4.var_inv
    simp at l4
    subst l4
    obtain ⟨rfl, rfl, rfl⟩ := a4.nil_inv
    rcases selectArm_cons_inv sel51 with ⟨mt60, rfl⟩ | ⟨nm61, sel62⟩
    · obtain ⟨vs63, hv64, -, ml65⟩ := matchPattern_tuple_inv mt60
      subst hv64
      obtain ⟨w66, vs67, b68, b69, rfl, mt70, ml71, rfl⟩ := matchListWith_cons_inv ml65
      obtain ⟨hv72, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt70
      subst hv72
      obtain ⟨x_stuck, vs73, b74, b75, rfl, mt76, ml77, rfl⟩ := matchListWith_cons_inv ml71
      obtain rfl := matchPattern_bind_inv mt76
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml77
      obtain ⟨vs78, a79, rfl⟩ := d52.tuple_inv
      obtain ⟨u80, us81, n82, k83, k84, rfl, e85, a86, rfl⟩ := a79.cons_inv
      obtain ⟨rfl, rfl, rfl⟩ := e85.literal_inv
      obtain ⟨u87, us88, n89, k90, k91, rfl, e92, a93, rfl⟩ := a86.cons_inv
      obtain ⟨l94, rfl, rfl⟩ := e92.var_inv
      simp at l94
      subst l94
      obtain ⟨rfl, rfl, rfl⟩ := a93.nil_inv
      exact .inl ⟨_, _, _, _, _, ev14, hv43, ev58, rfl, fun x hx => by simp [hx],
        by simp only [List.length_cons, List.length_append, List.length_nil]; omega⟩
    · rcases selectArm_cons_inv sel62 with ⟨mt95, rfl⟩ | ⟨nm96, -⟩
      · obtain rfl := matchPattern_wildcard_inv mt95
        obtain ⟨vs97, a98, rfl⟩ := d52.tuple_inv
        obtain ⟨u99, us100, n101, k102, k103, rfl, e104, a105, rfl⟩ := a98.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := e104.literal_inv
        obtain ⟨u106, us107, n108, k109, k110, rfl, -, a111, rfl⟩ := a105.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := a111.nil_inv
        exact .inr (.inr ⟨_, rfl⟩)
      · exact (matchPattern_wildcard_none nm96).elim
  · rcases selectArm_cons_inv sel42 with ⟨mt112, rfl⟩ | ⟨nm113, sel114⟩
    · -- `6 | 7 => let ge_two = …; match ge_two { 0 => (0, …), _ => (2, mk_nat_binop_stuck(…)) }`
      obtain rfl := matchPattern_orLiteral_some mt112
      obtain ⟨v115, m116, bs117, c118, c119, d120, mt121, d122, rfl⟩ := d38.letValue_inv
      have ext120 := d120.heap_extends
      obtain rfl := matchPattern_bind_inv mt121
      obtain ⟨v123, m124, bs125, body126, c127, c128, d129, sel130, d131, rfl⟩ :=
        d122.matchValue_inv
      obtain ⟨l132, rfl, rfl⟩ := d129.var_inv
      simp at l132
      subst l132
      rcases selectArm_cons_inv sel130 with ⟨mt133, rfl⟩ | ⟨nm134, sel135⟩
      · obtain ⟨-, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) mt133
        obtain ⟨vs136, a137, rfl⟩ := d131.tuple_inv
        obtain ⟨u138, us139, n140, k141, k142, rfl, e143, a144, rfl⟩ := a137.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := e143.literal_inv
        obtain ⟨u145, us146, n147, k148, k149, rfl, -, a150, rfl⟩ := a144.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := a150.nil_inv
        exact .inr (.inr ⟨_, rfl⟩)
      · rcases selectArm_cons_inv sel135 with ⟨mt151, rfl⟩ | ⟨nm152, -⟩
        · obtain rfl := matchPattern_wildcard_inv mt151
          obtain ⟨vs153, a154, rfl⟩ := d131.tuple_inv
          obtain ⟨u155, us156, n157, k158, k159, rfl, e160, a161, rfl⟩ := a154.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := e160.literal_inv
          obtain ⟨u162, us163, n164, k165, k166, rfl, e167, a168, rfl⟩ := a161.cons_inv
          obtain ⟨vs169, m170, c171, cs172, a173, ev174, rfl⟩ := e167.call_inv
          rw [instanceName_plain_some] at ev174
          obtain ⟨u175, us176, n177, k178, k179, rfl, e180, a181, rfl⟩ := a173.cons_inv
          obtain ⟨l182, rfl, rfl⟩ := e180.var_inv
          simp at l182
          subst l182
          obtain ⟨u183, us184, n185, k186, k187, rfl, e188, a189, rfl⟩ := a181.cons_inv
          obtain ⟨l190, rfl, rfl⟩ := e188.var_inv
          simp at l190
          subst l190
          obtain ⟨u191, us192, n193, k194, k195, rfl, e196, a197, rfl⟩ := a189.cons_inv
          obtain ⟨l198, rfl, rfl⟩ := e196.var_inv
          simp at l198
          subst l198
          obtain ⟨u199, us200, n201, k202, k203, rfl, e204, a205, rfl⟩ := a197.cons_inv
          obtain ⟨l206, rfl, rfl⟩ := e204.var_inv
          simp at l206
          subst l206
          obtain ⟨rfl, rfl, rfl⟩ := a205.nil_inv
          obtain ⟨rfl, rfl, rfl⟩ := a168.nil_inv
          exact .inr (.inl ⟨_, _, _, _, _, _, ev14, ext120, ev174, rfl,
            fun x hx => by simp [hx],
            by simp only [List.length_cons, List.length_append, List.length_nil]; omega⟩)
        · exact (matchPattern_wildcard_none nm152).elim
    · rcases selectArm_cons_inv sel114 with ⟨mt207, rfl⟩ | ⟨nm208, -⟩
      · obtain rfl := matchPattern_wildcard_inv mt207
        obtain ⟨vs209, a210, rfl⟩ := d38.tuple_inv
        obtain ⟨u211, us212, n213, k214, k215, rfl, e216, a217, rfl⟩ := a210.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := e216.literal_inv
        obtain ⟨u218, us219, n220, k221, k222, rfl, -, a223, rfl⟩ := a217.cons_inv
        obtain ⟨rfl, rfl, rfl⟩ := a223.nil_inv
        exact .inr (.inr ⟨_, rfl⟩)
      · exact (matchPattern_wildcard_none nm208).elim

/-! ## Reading a `Nat` value -/

/-- `try_extract_nat(rc, e)`: tag `1` at a literal (`Red.refl`), at `Nat.zero` with no levels
(`Red.natZeroLit`), and at an application `try_extract_nat_app` reads. -/
theorem try_extract_nat_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_extract_nat" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_extract_nat c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE x hr
  subst hargs
  rcases Obs.«KernelNatPrim::try_extract_nat».obs ev with
    ⟨x_limbs, ld, hr', hh, -⟩ |
    ⟨_, _, _, _, hr', _, _, _⟩ |
    ⟨x_caddr, x_clvls, m114, x122, y123, m124, cs133, v138, m154, cs162, cs168, m195,
      ld, ev164, ev135, ev170, op, hr', hm, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨x_f, x_a, cs259, ld, ev261, hcalls⟩ |
    ⟨_, _, _, _, _, _, hr', _, _, _⟩
  · -- a literal: itself
    subst h'
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    rcases Tm.lit_of_load hE ld with ⟨lp, limbs, hx, hl, hcn, rfl⟩ | ⟨bp, bytes, s, hx, -⟩
    · injection hx with _ _ hx'
      injection hx' with hx''
      subst hx''
      exact ⟨limbsVal limbs, ⟨limbs, hl, rfl, hcn⟩, .refl⟩
    · injection hx with _ hc'
      simp at hc'
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero
  · -- `Nat.zero` at no levels: the literal `0`
    subst hcalls
    obtain ⟨ad, us, rfl, rad, hus⟩ := Tm.const_of_load hE ld
    obtain ⟨rfl, hm1⟩ := ih.get (.roles .role_nat_zero) (by nat_lt_calls) ev164 rfl
    subst m154
    have hrole := ih.get (.roles .role_is) (by nat_lt_calls) ev135 rc x_caddr ad .natZero rfl
      (good.sub fun x hx => by simp [hx]) hrc rad
    have e1 := ObsFn.heap_extends ev135
    obtain ⟨hy, hm2⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev170 x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus)
    subst m114
    obtain ⟨u, w, rfl, rfl⟩ := binop_fields op
    have huw : u * w = 1 := (field_inj (mul_ok op)).symm
    obtain rfl : us = [] := by
      by_contra hne
      rw [ite_eq_right hne] at hy
      exact right_ne_zero_of_mul_eq_one huw (field_inj hy)
    obtain ⟨haddr, hforce⟩ := hrole (fun e0 => left_ne_zero_of_mul_eq_one huw (field_inj e0))
    have hk : c.κ (ixAddr ad) = .role .natZero := keyOf_of_addressOf hc.env.tableWf haddr
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst m195
    subst h'
    refine ⟨0, ⟨[], lrep_store_nil _, rfl, by simp⟩, ?_⟩
    rw [hk]
    exact .natZeroLit (natLit_of_natBlock hc hforce (by decide) (by decide) (by decide))
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero
  · -- an application: `try_extract_nat_app`
    subst hcalls
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    exact ih.get (.nat .try_extract_nat_app) (by nat_lt_calls) ev261 rc x_f x_a rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ Ef Ea hf ha x hr
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero

/-- `try_extract_nat_app(rc, f, a)`: tag `1` at `Nat.succ` (no levels) applied to a readable
argument, the successor literal (`Red.natSucc`). -/
theorem try_extract_nat_app_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_extract_nat_app" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_extract_nat_app c args h r h' calls := by
  intro rc f a hargs good hrc d Γ Fh A hF hA x hr
  subst hargs
  rcases Obs.«KernelNatPrim::try_extract_nat_app».obs ev with
    ⟨x_caddr, x_clvls, m31, x39, y40, m41, cs50, v55, m71, cs79, cs85, m101, cs112, x_pred, v152,
      m161, cs169, ld, ev81, ev52, ev87, op, ev114, hr', ev171, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨_, _, _, _, hr', _, _, _⟩
  · subst hcalls
    obtain ⟨ad, us, rfl, rad, hus⟩ := Tm.const_of_load hF ld
    obtain ⟨rfl, hm1⟩ := ih.get (.roles .role_nat_succ) (by nat_lt_calls) ev81 rfl
    subst m71
    have hrole := ih.get (.roles .role_is) (by nat_lt_calls) ev52 rc x_caddr ad .natSucc rfl
      (good.sub fun x hx => by simp [hx]) hrc rad
    have e1 := ObsFn.heap_extends ev52
    obtain ⟨hy, hm2⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev87 x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us (LvListRep.mono e1 hus)
    subst m31
    obtain ⟨u, w, rfl, rfl⟩ := binop_fields op
    have huw : u * w = 1 := (field_inj (mul_ok op)).symm
    obtain rfl : us = [] := by
      by_contra hne
      rw [ite_eq_right hne] at hy
      exact right_ne_zero_of_mul_eq_one huw (field_inj hy)
    obtain ⟨haddr, hforce⟩ := hrole (fun e0 => left_ne_zero_of_mul_eq_one huw (field_inj e0))
    have hk : c.κ (ixAddr ad) = .role .natSucc := keyOf_of_addressOf hc.env.tableWf haddr
    obtain ⟨n, hn, hred⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev114 rc a rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ A (Tm.mono e1 hA) x_pred rfl
    have hs := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev171 x_pred rfl
      (good.sub fun x hx => by simp [hx]) n).2 hn
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨n + 1, hs, ?_⟩
    rw [hk]
    exact .natSucc (natLit_of_natBlock hc hforce (by decide) (by decide) (by decide)) hred rfl
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero

/-! ## Folding a binary operation -/

/-- **`try_nat_binop_addr`, strengthened**: tag `1` comes only at the codes `3 … 16` (an operation
`natBinOpNames` holds, never `Nat.succ` or `Nat.pred`), with `natOpResult`'s closed term. -/
theorem try_nat_binop_addr_strong (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_binop_addr" args h r h' calls) (ih : IH c calls) :
    ∀ rc (o : F) a b, args = [rc, .field o, a, b] → Good c calls → c.rc h rc →
      ∀ n m, Specs.Nat.RepLimbsC h n a → Specs.Nat.RepLimbsC h m b →
        ∀ x, r = .tuple [.field 1, x] →
          (3 ≤ ZMod.val o ∧ ZMod.val o ≤ 16) ∧
          ∀ role, Specs.Nat.natPrimOp role = some (ZMod.val o) →
            ∃ E, Ix.Kernel.natOpResult (.role role) n m = some E ∧ c.tmc h' E x := by
  intro rc o a b hargs good hrc n m ha hb x hr
  subst hargs
  rcases Obs.«KernelNatPrim::try_nat_binop_addr».obs ev with
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, hv, hr', evop, evn, evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, hv, hr', evop, evn, evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, hv, hr', evop, evn, evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, hv, hr', evop, evn, evl, hh,
      hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, hv, hr', evop, evn, evl, hh,
      hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, hv, hr', evop, evn, evl, hh,
      hcalls⟩ |
    ⟨m448, m529, m542, cs553, v579, m588, cs596, v599, m601, cs609, v612, m614, cs622,
      _, _, _, _, _, _, hv, hm458, hm537, ev555, hr', ev624, ev611, ev598, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, _, _, hv, hr', evop, evn, evl,
      hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, _, _, _, hv, hr', evop, evn,
      evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, _, _, _, _, hv, hr', evop,
      evn, evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, _, _, _, _, _, hv, hr', evop,
      evn, evl, hh, hcalls⟩ |
    ⟨v18, m27, cs35, v38, m40, cs48, v51, m53, cs61, _, _, _, _, _, _, _, _, _, _, _, hv, hr',
      evop, evn, evl, hh, hcalls⟩ |
    ⟨v1048, m1057, cs1065, v1069, m1078, cs1086, _, _, _, _, _, _, _, _, _, _, _, _, hv, hr',
      ev1088, ev1067, hh, hcalls⟩ |
    ⟨v1115, m1124, cs1132, v1136, m1145, cs1153, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hr',
      ev1155, ev1134, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩
  · -- `Nat.add`
    subst hcalls
    have hvo : ZMod.val o = 3 := by rw [field_inj hv]; prim_val_lit 3
    have hs := ih.get (.nat .klimbs_add) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natAdd) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.sub`
    subst hcalls
    have hvo : ZMod.val o = 4 := by rw [field_inj hv]; prim_val_lit 4
    have hs := ih.get (.nat .klimbs_sub) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) (RepLimbsC.toRepLimbs hs)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natSub) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.mul`
    subst hcalls
    have hvo : ZMod.val o = 5 := by rw [field_inj hv]; prim_val_lit 5
    have hs := ih.get (.nat .klimbs_mul) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natMul) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.div`
    subst hcalls
    have hvo : ZMod.val o = 6 := by rw [field_inj hv]; prim_val_lit 6
    have hs := ih.get (.nat .klimbs_div) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) (RepLimbsC.toRepLimbs hs)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natDiv) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.mod`
    subst hcalls
    have hvo : ZMod.val o = 7 := by rw [field_inj hv]; prim_val_lit 7
    have hs := ih.get (.nat .klimbs_mod) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) (RepLimbsC.toRepLimbs hs)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natMod) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.gcd`
    subst hcalls
    have hvo : ZMod.val o = 8 := by rw [field_inj hv]; prim_val_lit 8
    have hs := ih.get (.nat .klimbs_gcd) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natGcd) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.pow`, at an exponent of at most `2^24`
    have x458 : Heap.Extends m529 m448 := ⟨_, hm458⟩
    have x537 : Heap.Extends h m529 := ⟨_, hm537⟩
    have e555 := ObsFn.heap_extends ev555
    subst hcalls
    subst m448
    subst m529
    have hvo : ZMod.val o = 9 := by rw [field_inj hv]; prim_val_lit 9
    obtain ⟨w, hw, hrw⟩ := word_cap h
    have hle := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev555 b _ rfl
      (good.sub fun x hx => by simp [hx]) m 16777216
      (repLimbs_mono (x537.trans x458) (RepLimbsC.toRepLimbs hb))
      ⟨[w], lrep_store_cons hrw (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw]⟩
    have hcap : m ≤ 16777216 := by
      by_contra hgt
      rw [ite_eq_right hgt] at hle
      exact field_one_ne_zero hle
    have e1 := (x537.trans x458).trans e555
    have hp := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev624 a b rfl
      (good.sub fun x hx => by simp [hx]) n m (repLimbs_mono e1 (RepLimbsC.toRepLimbs ha))
      (repLimbs_mono e1 (RepLimbsC.toRepLimbs hb))
    have hl := norm_lit ih good ev611 ev598 (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hp
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natPow) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit]; omega, hl⟩
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero
  · -- `Nat.land`
    subst hcalls
    have hvo : ZMod.val o = 10 := by rw [field_inj hv]; prim_val_lit 10
    have hs := ih.get (.nat .klimbs_land) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natLand) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.lor`
    subst hcalls
    have hvo : ZMod.val o = 11 := by rw [field_inj hv]; prim_val_lit 11
    have hs := ih.get (.nat .klimbs_lor) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natLor) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.xor`
    subst hcalls
    have hvo : ZMod.val o = 12 := by rw [field_inj hv]; prim_val_lit 12
    have hs := ih.get (.nat .klimbs_xor_op) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natXor) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.shiftLeft`
    subst hcalls
    have hvo : ZMod.val o = 13 := by rw [field_inj hv]; prim_val_lit 13
    have hs := ih.get (.nat .klimbs_shl) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natShiftLeft) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.shiftRight`
    subst hcalls
    have hvo : ZMod.val o = 14 := by rw [field_inj hv]; prim_val_lit 14
    have hs := ih.get (.nat .klimbs_shr) (by nat_lt_calls) evop a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    have hl := norm_lit ih good evn evl (fun x hx => by simp [hx]) (by nat_lt_calls)
      (fun x hx => by simp [hx]) (by nat_lt_calls) hs
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natShiftRight) hrole (by decide)
    exact ⟨_, by simp [Ix.Kernel.natOpResult, Specs.Nat.natLit], hl⟩
  · -- `Nat.beq`: canonical limb lists are equal exactly at equal values
    subst hcalls
    have hvo : ZMod.val o = 15 := by rw [field_inj hv]; prim_val_lit 15
    obtain ⟨la, hla, rfl, hca⟩ := ha
    obtain ⟨lb, hlb, rfl, hcb⟩ := hb
    obtain ⟨hg, hm1⟩ := ih.get (.levels .klimbs_eq) (by nat_lt_calls) ev1088 a b rfl
      (good.sub fun x hx => by simp [hx]) la lb hla hlb
    subst m1078
    subst hg
    have hbo := ih.get (.nat .mk_bool) (by nat_lt_calls) ev1067 rc _ rfl
      (good.sub fun x hx => by simp [hx]) hrc
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natBeq) hrole (by decide)
    refine ⟨_, ?_, hbo⟩
    by_cases hl : la = lb
    · subst hl
      simp [Ix.Kernel.natOpResult]
    · have hv' : limbsVal la ≠ limbsVal lb := fun e => hl (canon_inj hca hcb e)
      simp [Ix.Kernel.natOpResult, hl, hv']
  · -- `Nat.ble`
    subst hcalls
    have hvo : ZMod.val o = 16 := by rw [field_inj hv]; prim_val_lit 16
    have hg := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev1155 a b rfl
      (good.sub fun x hx => by simp [hx]) n m (RepLimbsC.toRepLimbs ha) (RepLimbsC.toRepLimbs hb)
    subst hg
    have hbo := ih.get (.nat .mk_bool) (by nat_lt_calls) ev1134 rc _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (ObsFn.heap_extends ev1155) hrc)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨by omega, fun role hrole => ?_⟩
    rw [hvo] at hrole
    obtain rfl := natPrimOp_role (r' := .natBle) hrole (by decide)
    refine ⟨_, ?_, hbo⟩
    by_cases hl : n ≤ m <;> simp [Ix.Kernel.natOpResult, hl]
  · exact absurd (hr.symm.trans hr') tag_one_ne_zero

/-- `try_nat_binop_addr(rc, op, a, b)`: tag `1` gives `natOpResult`'s closed term. -/
theorem try_nat_binop_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_binop_addr" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_nat_binop_addr c args h r h' calls :=
  fun rc o a b hargs good hrc n m ha hb x hr role hrole =>
    (try_nat_binop_addr_strong c ev ih rc o a b hargs good hrc n m ha hb x hr).2 role hrole

/-! ## The `Nat.add` offset form -/

/-- **`try_match_nat_add`, strengthened**: tag `1` also gives `Nat.add` in force (the answer of
`role_is`), which the offset rules' guards need. -/
theorem try_match_nat_add_strong (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_match_nat_add" args h r h' calls) (ih : IH c calls) :
    ∀ rc hd sp, args = [rc, hd, sp] → Good c calls → c.rc h rc →
      ∀ d Γ H As, c.tm d Γ h H hd → c.tml d Γ h As sp → ∀ b l, r = .tuple [.field 1, b, l] →
        c.inForce .natAdd ∧ ∃ us B n, H = .const Ix.Kernel.natAddName us ∧
          As = [B, Specs.Nat.natLit n] ∧ c.tm d Γ h' B b ∧ Specs.Nat.RepLimbsC h' n l := by
  intro rc hd sp hargs good hrc d Γ H As hH hAs b l hr
  subst hargs
  rcases Obs.«KernelNatPrim::try_match_nat_add».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨x_caddr, w20, v31, m32, cs43, v48, m64, cs72, x126, m128, cs137, v152, m153, cs163, v181,
      m182, cs192, x_limbs, ld, ev74, ev45, hne, ev139, op, ev165, ev194, ld221, hr', hh,
      hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _,
      _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _,
      _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨_, _, _, _, hr', _, _, _⟩
  · exact absurd (hr.symm.trans hr') tag3_one_ne_zero
  · subst hcalls
    obtain ⟨ad, us, rfl, rad, hus⟩ := Tm.const_of_load hH ld
    obtain ⟨rfl, hm1⟩ := ih.get (.roles .role_nat_add) (by nat_lt_calls) ev74 rfl
    subst m64
    obtain ⟨haddr, hforce⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev45 rc x_caddr ad .natAdd
      rfl (good.sub fun x hx => by simp [hx]) hrc rad hne
    have hk : c.κ (ixAddr ad) = .role .natAdd := keyOf_of_addressOf hc.env.tableWf haddr
    have e1 := ObsFn.heap_extends ev45
    have hAs1 : c.tml d Γ m32 As sp := TmL.mono e1 hAs
    obtain ⟨rfl, hm2⟩ := kl_length ev139 hAs1
    subst m128
    have hb39 : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [sp], m32⟩) (by simp) (by simp)
        hAs1
    have hlen : As.length = 2 := by
      have h1 : ((As.length : ℕ) : F) = ((2 : ℕ) : F) := by
        have := sub_eq_zero.mp (field_inj (sub_ok op)).symm
        exact_mod_cast this
      have h39 : (2 : ℕ) ^ 39 = 549755813888 := by norm_num
      exact (NatAux.natCast_inj (by omega) (by decide)).mp h1
    obtain ⟨⟨A0, hA0, rA0⟩, hm3⟩ := kl_lookup ev165 hAs1
    subst m153
    obtain ⟨⟨A1, hA1, rA1⟩, hm4⟩ := kl_lookup ev194 hAs1
    subst h'
    subst m182
    obtain ⟨Ps, rfl⟩ := spine_two hA0 hA1
    obtain rfl : Ps = [] := by simpa using hlen
    rcases Tm.lit_of_load rA1 ld221 with ⟨lp, limbs, hx, hl, hcn, rfl⟩ | ⟨bp, bytes, s, hx, -⟩
    · injection hx with _ _ hx'
      injection hx' with hx''
      subst hx''
      rw [hr'] at hr
      obtain ⟨rfl, rfl⟩ := tag3_snd hr
      exact ⟨hforce, us, A0, limbsVal limbs, by rw [hk], rfl, rA0, ⟨limbs, hl, rfl, hcn⟩⟩
    · injection hx with _ hc'
      simp at hc'
  · exact absurd (hr.symm.trans hr') tag3_one_ne_zero
  · exact absurd (hr.symm.trans hr') tag3_one_ne_zero
  · exact absurd (hr.symm.trans hr') tag3_one_ne_zero
  · exact absurd (hr.symm.trans hr') tag3_one_ne_zero

/-- `try_match_nat_add(rc, head, args)`: tag `1` at `Nat.add` applied to a base and a literal. -/
theorem try_match_nat_add_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_match_nat_add" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_match_nat_add c args h r h' calls :=
  fun rc hd sp hargs good hrc d Γ H As hH hAs b l hr =>
    (try_match_nat_add_strong c hc ev ih rc hd sp hargs good hrc d Γ H As hH hAs b l hr).2

/-! ## Building the stuck forms -/

/-- `mk_nat_offset_stuck(rc, base_w, n, post)`: `base + n` (`natAddLit`) applied to `post`. -/
theorem mk_nat_offset_stuck_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::mk_nat_offset_stuck" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.mk_nat_offset_stuck c args h r h' calls := by
  intro rc b np post hargs good hrc d Γ B n Ps hB hn hPs
  subst hargs
  rcases Obs.«KernelNatPrim::mk_nat_offset_stuck».obs ev with
    ⟨m2, cs13, v31, m40, cs48, ev15, hr, ev50, hh, hcalls⟩ |
    ⟨v1, m2, cs13, m74, v88, m91, cs99, v103, m112, cs120, m124, m137, v152, m154, m183, cs191,
      v205, m214, cs222, ev15, hne, hm84, ev122, ev101, hm132, hm147, hm162, ev193, hr, ev224, hh,
      hcalls⟩
  · -- `n = 0`: the base applied to `post`
    subst hcalls
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev15 np rfl
      (good.sub fun x hx => by simp [hx]) n (RepLimbsC.toRepLimbs hn)
    have hn0 : n = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    have e1 := ObsFn.heap_extends ev15
    have hap := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev50 b post rfl
      (good.sub fun x hx => by simp [hx]) d Γ B Ps (Tm.mono e1 hB) (TmL.mono e1 hPs)
    subst h'
    refine ⟨v31, hr, ?_⟩
    rw [hn0, natAddLit_zero]
    exact hap
  · -- `n ≠ 0`: `Nat.add base (lit n)` applied to `post`
    have x84 : Heap.Extends m124 m74 := ⟨_, hm84⟩
    have x132 : Heap.Extends m91 m124 := ⟨_, hm132⟩
    have x147 : Heap.Extends m183 m137 := ⟨_, hm147⟩
    have x162 : Heap.Extends m74 m154 := ⟨_, hm162⟩
    have e15 := ObsFn.heap_extends ev15
    have e122 := ObsFn.heap_extends ev122
    have e101 := ObsFn.heap_extends ev101
    have e193 := ObsFn.heap_extends ev193
    subst hcalls
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev15 np rfl
      (good.sub fun x hx => by simp [hx]) n (RepLimbsC.toRepLimbs hn)
    have hn0 : n ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact hne hz
    obtain ⟨rfl, hm1⟩ := ih.get (.roles .role_nat_add) (by nat_lt_calls) ev122 rfl
    obtain ⟨ad, rad, haddr, -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev101 rc .natAdd rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e15.trans e122) hrc)
    have hk : c.κ (ixAddr ad) = .role .natAdd := keyOf_of_addressOf hc.env.tableWf haddr
    have eB : Heap.Extends h m74 := (((e15.trans e122).trans e101).trans x132).trans x84
    have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev193 np rfl
      (good.sub fun x hx => by simp [hx]) n (repLimbsC_mono (eB.trans x162) hn)
    subst m124
    subst m74
    subst m154
    subst m137
    have hconst := tm_const_nil (κ := c.κ) (d := d) (Γ := Γ) rad
    rw [hk] at hconst
    have happ1 := Tm.store_app hconst (Tm.mono eB hB)
    have happ2 := Tm.store_app (Tm.mono e193 happ1) (hlit d Γ)
    have hsp := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev224 _ post rfl
      (good.sub fun x hx => by simp [hx]) d Γ _ Ps happ2
      (TmL.mono (((eB.trans x162).trans e193).trans x147) hPs)
    subst h'
    refine ⟨v205, hr, ?_⟩
    rw [natAddLit_ne hn0]
    exact hsp

/-- `mk_nat_binop_stuck(op_addr, base_w, n, post)`: the operation on the base and the literal,
applied to `post`. -/
theorem mk_nat_binop_stuck_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::mk_nat_binop_stuck" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.mk_nat_binop_stuck c args h r h' calls := by
  intro ap b np post hargs good a d Γ B n Ps ha hB hn hPs
  subst hargs
  obtain ⟨m2, m26, m39, v54, m56, m85, cs93, cs107, hm12, hm34, hm49, hm64, ev95, ev109, hcalls⟩ :=
    Obs.«KernelNatPrim::mk_nat_binop_stuck».obs ev
  have x12 : Heap.Extends m26 m2 := ⟨_, hm12⟩
  have x34 : Heap.Extends h m26 := ⟨_, hm34⟩
  have x49 : Heap.Extends m85 m39 := ⟨_, hm49⟩
  have x64 : Heap.Extends m2 m56 := ⟨_, hm64⟩
  have e95 := ObsFn.heap_extends ev95
  subst hcalls
  have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev95 np rfl
    (good.sub fun x hx => by simp [hx]) n (repLimbsC_mono ((x34.trans x12).trans x64) hn)
  subst m26
  subst m2
  subst m56
  subst m39
  have hconst := tm_const_nil (κ := c.κ) (d := d) (Γ := Γ) ha
  have happ1 := Tm.store_app hconst (Tm.mono (x34.trans x12) hB)
  have happ2 := Tm.store_app (Tm.mono e95 happ1) (hlit d Γ)
  exact ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev109 _ post rfl
    (good.sub fun x hx => by simp [hx]) d Γ _ Ps happ2
    (TmL.mono ((((x34.trans x12).trans x64).trans e95).trans x49) hPs)

/-- `build_succ_offset(rc, base, lit)`: `Nat.succ (base + (lit - 1))` (`natAddLit`). -/
theorem build_succ_offset_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::build_succ_offset" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.build_succ_offset c args h r h' calls := by
  intro rc b lp hargs good hrc d Γ B n hB hn
  subst hargs
  rcases Obs.«KernelNatPrim::build_succ_offset».obs ev with
    ⟨m2, m83, v95, m96, cs106, v109, m111, cs119, m139, v153, m156, cs164, v168, m177, cs185, m189,
      m202, cs213, hm12, hm91, ev121, ev108, hm149, ev187, ev166, hm197, ev215, hr, hh, hcalls⟩ |
    ⟨m2, m83, v95, m96, cs106, v109, m111, cs119, m139, v153, m156, cs164, v168, m177, cs185, m189,
      v201, m202, cs213, m258, v272, m275, cs283, v287, m296, cs304, m308, m321, m354, m371,
      hm12, hm91, ev121, ev108, hm149, ev187, ev166, hm197, ev215, hne, hm268, ev306, ev285, hm316,
      hm331, hm364, hm379, hr, hh, hcalls⟩
  · -- `n - 1 = 0`: `Nat.succ base`
    have x12 : Heap.Extends m83 m2 := ⟨_, hm12⟩
    have x91 : Heap.Extends h m83 := ⟨_, hm91⟩
    have x149 : Heap.Extends m189 m139 := ⟨_, hm149⟩
    have x197 : Heap.Extends m156 m189 := ⟨_, hm197⟩
    have e121 := ObsFn.heap_extends ev121
    have e108 := ObsFn.heap_extends ev108
    have e187 := ObsFn.heap_extends ev187
    have e166 := ObsFn.heap_extends ev166
    have e215 := ObsFn.heap_extends ev215
    subst hcalls
    subst m83
    subst m2
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    have hs := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev121 lp _ rfl
      (good.sub fun x hx => by simp [hx]) n 1 (repLimbs_mono (x91.trans x12) hn)
      ⟨[w1], lrep_store_cons hr1 (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw1]⟩
    have hnm := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev108 v109 rfl
      (good.sub fun x hx => by simp [hx]) (n - 1) (RepLimbsC.toRepLimbs hs)
    have e0 := (((x91.trans x12).trans e121).trans e108).trans e187
    obtain ⟨rfl, -⟩ := ih.get (.roles .role_nat_succ) (by nat_lt_calls) ev187 rfl
    obtain ⟨ad, rad, haddr, -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev166 rc .natSucc
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc)
    have hks : c.κ (ixAddr ad) = .role .natSucc := keyOf_of_addressOf hc.env.tableWf haddr
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev215 v95 rfl
      (good.sub fun x hx => by simp [hx]) (n - 1)
      (RepLimbsC.toRepLimbs (repLimbsC_mono (((e187.trans e166).trans x197).trans x149) hnm))
    have hn1 : n - 1 = 0 := by
      by_contra hne
      rw [ite_eq_right hne] at hz
      exact field_one_ne_zero hz
    have eB := (((e0.trans e166).trans x197).trans x149).trans e215
    subst m189
    subst m139
    have hsucc := tm_const_nil (κ := c.κ) (d := d) (Γ := Γ) rad
    rw [hks] at hsucc
    subst r
    subst h'
    rw [hn1, natAddLit_zero]
    exact Tm.store_app (Tm.mono e215 hsucc) (Tm.mono eB hB)
  · -- `n - 1 ≠ 0`: `Nat.succ (Nat.add base (lit (n - 1)))`
    have x12 : Heap.Extends m83 m2 := ⟨_, hm12⟩
    have x91 : Heap.Extends h m83 := ⟨_, hm91⟩
    have x149 : Heap.Extends m189 m139 := ⟨_, hm149⟩
    have x197 : Heap.Extends m156 m189 := ⟨_, hm197⟩
    have x268 : Heap.Extends m308 m258 := ⟨_, hm268⟩
    have x316 : Heap.Extends m275 m308 := ⟨_, hm316⟩
    have x331 : Heap.Extends m258 m321 := ⟨_, hm331⟩
    have x364 : Heap.Extends m371 m354 := ⟨_, hm364⟩
    have x379 : Heap.Extends m321 m371 := ⟨_, hm379⟩
    have e121 := ObsFn.heap_extends ev121
    have e108 := ObsFn.heap_extends ev108
    have e187 := ObsFn.heap_extends ev187
    have e166 := ObsFn.heap_extends ev166
    have e215 := ObsFn.heap_extends ev215
    have e306 := ObsFn.heap_extends ev306
    have e285 := ObsFn.heap_extends ev285
    subst hcalls
    subst m83
    subst m2
    obtain ⟨w1, hw1, hr1⟩ := word_one h
    have hs := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev121 lp _ rfl
      (good.sub fun x hx => by simp [hx]) n 1 (repLimbs_mono (x91.trans x12) hn)
      ⟨[w1], lrep_store_cons hr1 (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw1]⟩
    have hnm := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev108 v109 rfl
      (good.sub fun x hx => by simp [hx]) (n - 1) (RepLimbsC.toRepLimbs hs)
    have e0 := (((x91.trans x12).trans e121).trans e108).trans e187
    obtain ⟨rfl, -⟩ := ih.get (.roles .role_nat_succ) (by nat_lt_calls) ev187 rfl
    obtain ⟨ad, rad, haddr, -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev166 rc .natSucc
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc)
    have hks : c.κ (ixAddr ad) = .role .natSucc := keyOf_of_addressOf hc.env.tableWf haddr
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev215 v95 rfl
      (good.sub fun x hx => by simp [hx]) (n - 1)
      (RepLimbsC.toRepLimbs (repLimbsC_mono (((e187.trans e166).trans x197).trans x149) hnm))
    have hn1 : n - 1 ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact hne hz
    have e202 := (((e0.trans e166).trans x197).trans x149).trans e215
    obtain ⟨rfl, -⟩ := ih.get (.roles .role_nat_add) (by nat_lt_calls) ev306 rfl
    obtain ⟨aa, raa, haddr', -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev285 rc .natAdd
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono (e202.trans e306) hrc)
    have hka : c.κ (ixAddr aa) = .role .natAdd := keyOf_of_addressOf hc.env.tableWf haddr'
    have eL := (((((((e187.trans e166).trans x197).trans x149).trans e215).trans e306).trans
      e285).trans x316).trans x268
    have eB := ((((e202.trans e306).trans e285).trans x316).trans x268).trans x331
    have eS := ((((((e215.trans e306).trans e285).trans x316).trans x268).trans x331).trans
      x379).trans x364
    subst m189
    subst m139
    have hsucc := tm_const_nil (κ := c.κ) (d := d) (Γ := Γ) rad
    rw [hks] at hsucc
    subst m308
    subst m258
    have hadd := tm_const_nil (κ := c.κ) (d := d) (Γ := Γ) raa
    rw [hka] at hadd
    have hlitn := tm_store_lit (κ := c.κ) (d := d) (Γ := Γ) hnm eL
    subst m321
    subst m371
    have happ1 := Tm.store_app (Tm.mono x331 hadd) (Tm.mono eB hB)
    subst m354
    have happ2 := Tm.store_app happ1 (Tm.mono x379 hlitn)
    subst r
    subst h'
    rw [natAddLit_ne hn1]
    exact Tm.store_app (Tm.mono eS hsucc) happ2

/-! ## The offset rewrite of a major -/

/-- `cleanup_nat_offset_major(rc, e)`: `Nat.add b (lit (k + 1))` steps to `Nat.succ (b + k)`
(`Red.natAddSucc`); any other term is kept (`Red.refl`). -/
theorem cleanup_nat_offset_major_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::cleanup_nat_offset_major" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.cleanup_nat_offset_major c args h r h' calls := by
  intro rc e hargs good hrc d Γ E hE
  subst hargs
  have ext := ObsFn.heap_extends ev
  rcases Obs.«KernelNatPrim::cleanup_nat_offset_major».obs ev with
    ⟨_, _, hr', _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _⟩ |
    ⟨v1, m35, cs46, x_head, x_args, w92, w93, m105, cs116, x_base, x_lit, v166, m167, cs177, v188,
      m189, cs200, cs226, ld, hne30, ev48, ld84, ev118, ev179, ev202, hne219, ev228, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hr', _, _⟩
  · rw [hr']
    exact ⟨E, Tm.mono ext hE, .refl⟩
  · rw [hr']
    exact ⟨E, Tm.mono ext hE, .refl⟩
  · subst hcalls
    obtain ⟨hd, sp, H, As, hres, hH, hAs, hEq⟩ := ih.get (.subst .collect_spine) (by nat_lt_calls)
      ev48 e rfl (good.sub fun x hx => by simp [hx]) d Γ 0 E hE
    obtain ⟨rfl, rfl⟩ : x_head = hd ∧ x_args = sp := by
      injection hres with h1
      injection h1 with h2 h3
      injection h3 with h4 _
      exact ⟨h2, h4⟩
    have e1 := ObsFn.heap_extends ev48
    obtain ⟨hforce, us, B, n, rfl, rfl, hB, hn⟩ :=
      try_match_nat_add_strong c hc ev118 (ih.mono (by nat_lt_calls)) rc x_head x_args rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ H As hH hAs x_base x_lit rfl
    have e2 := ObsFn.heap_extends ev118
    have hnm := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev179 x_lit rfl
      (good.sub fun x hx => by simp [hx]) n (RepLimbsC.toRepLimbs hn)
    have e3 := ObsFn.heap_extends ev179
    have hz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev202 v166 rfl
      (good.sub fun x hx => by simp [hx]) n (RepLimbsC.toRepLimbs hnm)
    have hn0 : n ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hz
      exact hne219 hz
    have e4 := ObsFn.heap_extends ev202
    have hb := ih.get (.nat .build_succ_offset) (by nat_lt_calls) ev228 rc x_base v166 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (((e1.trans e2).trans e3).trans e4) hrc) d Γ
      B n (Tm.mono (e3.trans e4) hB) (RepLimbsC.toRepLimbs (repLimbsC_mono e4 hnm))
    refine ⟨_, hb, ?_⟩
    subst hEq
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact .natAddSucc (natLit_of_natAdd hc hforce) (hc.env.natAdd hforce)
  · rw [hr']
    exact ⟨E, Tm.mono ext hE, .refl⟩
  · rw [hr']
    exact ⟨E, Tm.mono ext hE, .refl⟩

/-! ## Dispatching -/

/-- `try_nat_offset_dispatch(rc, head_addr, op, a0_w, nb, spine)`: the stuck form of the applied
operation, a reduct (`Nat.add`: `Red.natAddZero` at `0`, else `Red.appArg`; `div`/`mod`:
`Red.appArg`), through the rest of the spine (`Red.appFn`). -/
theorem try_nat_offset_dispatch_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_offset_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_nat_offset_dispatch c args h r h' calls := by
  intro rc ap o a0 nb sp hargs good hrc a ha hop d Γ A₀ A₁ Ps n hsp hA₀ hn hred t x hr ht
  subst hargs
  rcases try_nat_offset_dispatch_obs ev with
    ⟨post, m₁, cs₁, stuck, cs₂, evd, hv, evs, hr', hsub, hlt⟩ |
    ⟨post, m₁, m₂, cs₁, s, cs₂, evd, ext, evb, hr', hsub, hlt⟩ |
    ⟨p, hr'⟩
  · -- `Nat.add`: `A₀ + n`
    have hvo : ZMod.val o = 3 := by rw [field_inj hv]; prim_val_lit 3
    obtain ⟨-, hpost, hm⟩ := kl_drop evd hsp
    subst m₁
    have e2 : (A₀ :: A₁ :: Ps).drop (ZMod.val (2 : F)) = Ps := by rw [val_two]; rfl
    rw [e2] at hpost
    obtain ⟨y, hy, hstk⟩ := ih.get (.nat .mk_nat_offset_stuck) hlt evs rc a0 nb post rfl
      (good.sub hsub) hrc d Γ A₀ n Ps hA₀ hn hpost
    obtain rfl := tag_snd hy
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    refine ⟨_, hstk, ?_⟩
    obtain ⟨ro, hro, haddr, hforce⟩ := hop
    rw [hvo] at hro
    obtain rfl := natPrimOp_role (r' := .natAdd) hro (by decide)
    have hk : c.κ (ixAddr a) = .role .natAdd := keyOf_of_addressOf hc.env.tableWf haddr
    rw [hk]
    refine red_mkAppN₂ Ps ?_
    by_cases hn0 : n = 0
    · subst hn0
      rw [natAddLit_zero]
      exact .natAddZero (natLit_of_natAdd hc hforce) (hc.env.natAdd hforce) hred rfl
    · rw [natAddLit_ne hn0]
      exact .appArg hred
  · -- `Nat.div`, `Nat.mod`: the operation on `A₀` and the literal
    obtain ⟨-, hpost, hm⟩ := kl_drop evd hsp
    subst m₁
    have e2 : (A₀ :: A₁ :: Ps).drop (ZMod.val (2 : F)) = Ps := by rw [val_two]; rfl
    rw [e2] at hpost
    have hstk := ih.get (.nat .mk_nat_binop_stuck) hlt evb ap a0 nb post rfl (good.sub hsub)
      a d Γ A₀ n Ps (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hA₀)
      (repLimbsC_mono ext hn) (TmL.mono ext hpost)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    exact ⟨_, hstk, red_mkAppN₂ Ps (.appArg hred)⟩
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht

/-- `try_nat_binop_dispatch(rc, head_addr, op, spine, spine_len)`: `Red.natOp` on two readable
arguments, or the offset dispatch's stuck form. -/
theorem try_nat_binop_dispatch_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_binop_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_nat_binop_dispatch c args h r h' calls := by
  intro rc ap o sp sl hargs good hrc a ha hop d Γ As hAs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_nat_binop_dispatch».obs ev with
    ⟨_, _, _, _, hr', _, _, _⟩ |
    ⟨v1, m2, cs13, v72, m73, cs83, v101, m102, cs112, m131, cs142, x_na, m180, cs191, x_nb, m229,
      cs240, x_result, v293, m294, cs304, v325, m334, cs342,
      ev15, hne68, ev85, ev114, ev144, ev193, ev242, ev306, hr', ev344, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨v1, m2, cs13, v72, m73, cs83, v101, m102, cs112, v130, m131, cs142, m439, cs450, x_nb, cs490,
      ev15, hne68, ev85, ev114, ev144, ev452, ev492, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · -- both readable: `Red.natOp`
    subst hcalls
    have e0 := ObsFn.heap_extends ev15
    have hAs0 := TmL.mono e0 hAs
    obtain ⟨⟨A₀, hA₀, rA₀⟩, hm1⟩ := kl_lookup ev85 hAs0
    subst m73
    obtain ⟨⟨A₁, hA₁, rA₁⟩, hm2⟩ := kl_lookup ev114 hAs0
    subst m102
    obtain ⟨Ps, rfl⟩ := spine_two hA₀ hA₁
    obtain ⟨n₁, hn₁, hred₁⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev144 rc v72 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ A₀ rA₀ x_na rfl
    have e1 := ObsFn.heap_extends ev144
    obtain ⟨n₂, hn₂, hred₂⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev193 rc v101 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e0.trans e1) hrc) d Γ A₁ (Tm.mono e1 rA₁)
      x_nb rfl
    have e2 := ObsFn.heap_extends ev193
    obtain ⟨hcode, hres⟩ := try_nat_binop_addr_strong c ev242 (ih.mono (by nat_lt_calls)) rc o
      x_na x_nb rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ((e0.trans e1).trans e2) hrc)
      n₁ n₂ (repLimbsC_mono e2 hn₁) hn₂ x_result rfl
    obtain ⟨ro, hro, haddr, hforce⟩ := hop
    obtain ⟨E, hE, hEt⟩ := hres ro hro
    have e3 := ObsFn.heap_extends ev242
    obtain ⟨-, hpost, hm3⟩ := kl_drop ev306 (TmL.mono (((e0.trans e1).trans e2).trans e3) hAs)
    subst m294
    have e22 : (A₀ :: A₁ :: Ps).drop (ZMod.val (2 : F)) = Ps := by rw [val_two]; rfl
    rw [e22] at hpost
    have hsp := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev344 x_result v293 rfl
      (good.sub fun x hx => by simp [hx]) d Γ E Ps (hEt d Γ) hpost
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨_, hsp, ?_⟩
    have hk : c.κ (ixAddr a) = .role ro := keyOf_of_addressOf hc.env.tableWf haddr
    have hmem := natBinOp_mem hro hcode.1
    rw [hk]
    exact red_mkAppN₂ Ps (.natOp hmem (hc.env.natOps ro hforce hmem) hred₁ rfl hred₂ rfl hE)
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · -- the second readable only: the offset dispatch
    subst hcalls
    have e0 := ObsFn.heap_extends ev15
    have hAs0 := TmL.mono e0 hAs
    obtain ⟨⟨A₀, hA₀, rA₀⟩, hm1⟩ := kl_lookup ev85 hAs0
    subst m73
    obtain ⟨⟨A₁, hA₁, rA₁⟩, hm2⟩ := kl_lookup ev114 hAs0
    subst m102
    obtain ⟨Ps, rfl⟩ := spine_two hA₀ hA₁
    have e1 := ObsFn.heap_extends ev144
    obtain ⟨n₂, hn₂, hred₂⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev452 rc v101 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e0.trans e1) hrc) d Γ A₁ (Tm.mono e1 rA₁)
      x_nb rfl
    have e2 := ObsFn.heap_extends ev452
    have eE := (e0.trans e1).trans e2
    exact ih.get (.nat .try_nat_offset_dispatch) (by nat_lt_calls) ev492 rc ap o v72 x_nb sp rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono eE hrc) a
      (Bytes.repAddressRef_heapMono₂ addrTy eE ha) hop d Γ A₀ A₁ Ps n₂ (TmL.mono eE hAs)
      (Tm.mono (e1.trans e2) rA₀) hn₂ hred₂ t x hr ht
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht

/-- `try_nat_dispatch(rc, head_addr, op, spine, types)`: `Red.natSucc` for `Nat.succ` on a
readable argument, the binary dispatch for the other operations (`Nat.pred` is not native). -/
theorem try_nat_dispatch_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_nat_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_nat_dispatch c args h r h' calls := by
  intro rc ap o sp types hargs good hrc a ha hop d Γ htypes As hAs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_nat_dispatch».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨v1, m2, cs12, v37, m38, cs49, v108, m109, cs119, m138, cs149, x_na, v186, m187, cs197, v218,
      m227, cs235, v238, m241, cs249, v252, m254, cs262,
      ev14, hv36, ev51, hne104, ev121, ev151, ev199, hr', ev264, ev251, ev237, hh, hcalls⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, hr', _, _, _⟩ |
    ⟨v1, m2, cs12, cs363, ev14, hne318, hne356, ev365, hcalls⟩
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · -- `Nat.succ`
    subst hcalls
    have hvo : ZMod.val o = 1 := by rw [field_inj hv36]; exact val_one
    have e0 := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev51)
    obtain ⟨⟨A₀, hA₀, rA₀⟩, hm1⟩ := kl_lookup ev121 (TmL.mono e0 hAs)
    subst m109
    obtain ⟨Ps, rfl⟩ := spine_one hA₀
    obtain ⟨n, hn, hred⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev151 rc v108 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ A₀ rA₀ x_na rfl
    have e1 := ObsFn.heap_extends ev151
    obtain ⟨-, hpost, hm2⟩ := kl_drop ev199 (TmL.mono (e0.trans e1) hAs)
    subst m187
    have e11 : (A₀ :: Ps).drop (ZMod.val (1 : F)) = Ps := by rw [val_one]; rfl
    rw [e11] at hpost
    have hs := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev264 x_na rfl
      (good.sub fun x hx => by simp [hx]) n).2 hn
    have hl := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev251 v252 rfl
      (good.sub fun x hx => by simp [hx]) (n + 1) hs
    have e2 := (ObsFn.heap_extends ev264).trans (ObsFn.heap_extends ev251)
    have hsp := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev237 v238 v186 rfl
      (good.sub fun x hx => by simp [hx]) d Γ _ Ps (hl d Γ) (TmL.mono e2 hpost)
    rw [hr'] at hr
    obtain rfl := tag_snd hr
    subst h'
    refine ⟨_, hsp, ?_⟩
    obtain ⟨ro, hro, haddr, hforce⟩ := hop
    rw [hvo] at hro
    obtain rfl := natPrimOp_role (r' := .natSucc) hro (by decide)
    have hk : c.κ (ixAddr a) = .role .natSucc := keyOf_of_addressOf hc.env.tableWf haddr
    rw [hk]
    exact red_mkAppN₁ Ps
      (.natSucc (natLit_of_natBlock hc hforce (by decide) (by decide) (by decide)) hred rfl)
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · exact absurd (tag_eq_zero (hr.symm.trans hr')) ht
  · -- the binary dispatch
    subst hcalls
    obtain ⟨-, hm1⟩ := kl_length ev14 hAs
    subst m2
    exact ih.get (.nat .try_nat_binop_dispatch) (by nat_lt_calls) ev365 rc ap o sp v1 rfl
      (good.sub fun x hx => by simp [hx]) hrc a ha hop d Γ As hAs t x hr ht

end IxVM.Refinement.Core
