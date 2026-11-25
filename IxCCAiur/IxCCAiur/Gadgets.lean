import IxCCAiur.Lower
import Aiur.Library.U64.Correctness
import Aiur.Library.U32.Goldilocks
import Aiur.Generic.SourceSemantics

/-! # Gadget Contracts for `UInt8`, `UInt64`, and Lowered `Nat` Primitives

Proves the complete operational contracts over `Aiur.Generic.SourceSemantics.EvalFn`
for:
1. `FieldCompatible F`: natural casts injective below `2^57` (discharged for
   Goldilocks `Aiur.Library.U32.Goldilocks.F`), extending `Aiur.Library.U64.Compatible F`.
2. `no_evalExit_of_plain`: plain expressions (no `.control` or expression `.global`)
   admit no abrupt `EvalExit`, reducing `EvalFn` directly to `EvalExpr`.
3. `U8MapSpec` & symbolic `u8MapSpec_of_source`: soundness of the three `UInt8`
   lookup maps (`range_pair`, `raw_xor`, `raw_sum_byte`) directly from `UInt8.tables`.
4. `U64LibraryWorld` → `U64Contracts`: all 8 `UInt64` operations (`to_field`,
   `from_field`, `is_zero`, `sub_with_borrow`, `mul`, `and`, `or`, `xor`) proved
   directly by inverting `EvalFn` and invoking `Aiur.Library.U64.Correctness`.
5. `PrimHelpersWorld` → `PrimContracts`: all 13 lowered `Prog::` primitive helpers
   (`p_add`, `p_sub`, `p_mul`, `divmod`, `p_div`, `p_mod`, `p_pred`, `p_land`,
   `p_lor`, `p_xor`, `p_beq`, `p_ble`, `p_blt`) proved directly over `EvalFn`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`. -/

namespace IxCC.AiurBackend.Gadgets

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Fir IxCC.Key IxCC.AiurBackend.Lower
open IxCC.Lam (Lit Prim)

/-! ## Field Compatibility (`< 2^57`) -/

/-- Natural casts are injective below `2^57` (so sums of two `< 2^56` naturals
never wrap modulo the field characteristic). -/
def FieldCompatible (F : Type) [NatCast F] : Prop :=
  Set.InjOn (Nat.cast : Nat → F) (Set.Iio (2 ^ 57))

theorem FieldCompatible.of_charP (F : Type) [AddGroupWithOne F] (p : Nat) [CharP F p]
    (large : 2 ^ 57 ≤ p) : FieldCompatible F := by
  intro a ha b hb equal
  exact CharP.natCast_injOn_Iio F p (lt_of_lt_of_le ha large) (lt_of_lt_of_le hb large) equal

theorem goldilocks_fieldCompatible : FieldCompatible U32.Goldilocks.F :=
  FieldCompatible.of_charP U32.Goldilocks.F U32.Goldilocks.modulus (by decide)

theorem FieldCompatible.u64 {F : Type} [NatCast F] (fc : FieldCompatible F) :
    U64.Compatible F := by
  intro a ha b hb equal
  exact fc (lt_trans ha (by norm_num : 2 ^ 56 < 2 ^ 57))
    (lt_trans hb (by norm_num : 2 ^ 56 < 2 ^ 57)) equal

section FieldFacts

variable {F : Type} [Field F]

theorem FieldCompatible.natCast_inj (fc : FieldCompatible F) {a b : Nat}
    (ha : a < 2 ^ 57) (hb : b < 2 ^ 57) (heq : (a : F) = (b : F)) : a = b :=
  fc ha hb heq

theorem FieldCompatible.natCast_inj56 (fc : FieldCompatible F) {a b : Nat}
    (ha : a < natLimit) (hb : b < natLimit) (heq : (a : F) = (b : F)) : a = b :=
  fc.natCast_inj (lt_trans ha (by unfold natLimit; omega))
    (lt_trans hb (by unfold natLimit; omega)) heq

theorem FieldCompatible.ne_zero_of_pos (fc : FieldCompatible F) {a : Nat}
    (hpos : 0 < a) (hlt : a < 2 ^ 57) : (a : F) ≠ 0 := by
  intro h
  have h0 : a = 0 := fc.natCast_inj hlt (by omega : 0 < 2 ^ 57) (by simp [h])
  omega

theorem FieldCompatible.sub_eq_zero_iff (fc : FieldCompatible F) {a b : Nat}
    (ha : a < 2 ^ 57) (hb : b < 2 ^ 57) : ((a : F) - (b : F) = 0) ↔ a = b := by
  rw [sub_eq_zero]
  exact ⟨fc.natCast_inj ha hb, fun h => by subst h; rfl⟩

theorem FieldCompatible.two_ne_zero (fc : FieldCompatible F) : (2 : F) ≠ 0 :=
  U64.two_ne_zero fc.u64

theorem FieldCompatible.radix_ne_zero (fc : FieldCompatible F) : (256 : F) ≠ 0 :=
  U64.radix_ne_zero fc.u64

theorem FieldCompatible.one_ne_zero (_ : FieldCompatible F) : (1 : F) ≠ 0 :=
  _root_.one_ne_zero

end FieldFacts

/-! ## Plain Expressions Have No `EvalExit` -/

section Plain

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] in
theorem selectArm_body_mem {world : World F} {types : Types} {heap : Heap F} {v : SourceValue F} :
    ∀ {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
      {bindings : Environment F Nat} {body : Aiur.Generic.Expr F},
      SourceSemantics.selectArm world types heap v arms = .ok (some (bindings, body)) →
      ∃ p, (p, body) ∈ arms
  | [], _, _, h => by simp [SourceSemantics.selectArm, pure, Except.pure] at h
  | (p, b) :: rest, bindings, body, h => by
    simp only [SourceSemantics.selectArm, bind, Except.bind] at h
    cases hm : world.matchPattern types heap p v with
    | error _ => simp [hm] at h
    | ok opt =>
      simp only [hm] at h
      cases opt with
      | some bs =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨p, List.mem_cons_self⟩
      | none =>
        obtain ⟨p', hp'⟩ := selectArm_body_mem h
        exact ⟨p', List.mem_cons_of_mem _ hp'⟩

mutual

theorem no_evalExit_of_plain {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {before after : Heap F} {target : ExitTarget} {result : SourceValue F},
      isPlainExpr e = true →
      EvalExit world types locals e before target result after → False
  | _, _, _, _, _, _, _, hplain, .exit _
  | _, _, _, _, _, _, _, hplain, .exitPayload _
  | _, _, _, _, _, _, _, hplain, .fromBlock _ _
  | _, _, _, _, _, _, _, hplain, .fromGlobal _ _ _ => by
    simp [isPlainExpr] at hplain
  | _, _, _, _, _, _, _, hplain, .fromTuple items
  | _, _, _, _, _, _, _, hplain, .fromArray items
  | _, _, _, _, _, _, _, hplain, .fromBuiltin items
  | _, _, _, _, _, _, _, hplain, .fromUpdate items
  | _, _, _, _, _, _, _, hplain, .fromRecord items
  | _, _, _, _, _, _, _, hplain, .fromConstruct items
  | _, _, _, _, _, _, _, hplain, .fromConstructAs items
  | _, _, _, _, _, _, _, hplain, .fromCall items => by
    simp only [isPlainExpr] at hplain
    exact no_evalArgsExit_of_plain hplain items
  | _, _, _, _, _, _, _, hplain, .fromRepeat h
  | _, _, _, _, _, _, _, hplain, .fromIndex h
  | _, _, _, _, _, _, _, hplain, .fromSlice h
  | _, _, _, _, _, _, _, hplain, .fromMember h
  | _, _, _, _, _, _, _, hplain, .fromProject h
  | _, _, _, _, _, _, _, hplain, .fromStore h
  | _, _, _, _, _, _, _, hplain, .fromLoad h
  | _, _, _, _, _, _, _, hplain, .fromHint h
  | _, _, _, _, _, _, _, hplain, .fromNeg h => by
    simp only [isPlainExpr] at hplain
    exact no_evalExit_of_plain hplain h
  | _, _, _, _, _, _, _, hplain, .fromLetValue h
  | _, _, _, _, _, _, _, hplain, .binaryLeft h => by
    simp only [isPlainExpr, Bool.and_eq_true] at hplain
    exact no_evalExit_of_plain hplain.1 h
  | _, _, _, _, _, _, _, hplain, .letBody _ _ h
  | _, _, _, _, _, _, _, hplain, .binaryRight _ h => by
    simp only [isPlainExpr, Bool.and_eq_true] at hplain
    exact no_evalExit_of_plain hplain.2 h
  | _, _, _, _, _, _, _, hplain, .fromMatchValue h => by
    simp only [isPlainExpr, Bool.and_eq_true] at hplain
    exact no_evalExit_of_plain hplain.1 h
  | _, _, _, _, _, _, _, hplain, .matchBody _ sel h => by
    simp only [isPlainExpr, Bool.and_eq_true] at hplain
    obtain ⟨p, hmem⟩ := selectArm_body_mem sel
    exact no_evalExit_of_plain ((isPlainArms_iff.mp hplain.2) (p, _) hmem) h

theorem no_evalArgsExit_of_plain {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {before after : Heap F} {target : ExitTarget} {result : SourceValue F},
      isPlainList es = true →
      EvalArgsExit world types locals es before target result after → False
  | _, _, _, _, _, _, _, hplain, .head h => by
    simp only [isPlainList, Bool.and_eq_true] at hplain
    exact no_evalExit_of_plain hplain.1 h
  | _, _, _, _, _, _, _, hplain, .tail _ h => by
    simp only [isPlainList, Bool.and_eq_true] at hplain
    exact no_evalArgsExit_of_plain hplain.2 h

end

end Plain

/-! ## `WorldHasFn` and Straight-Line `EvalExpr` Inversion Helpers -/

section WorldHelpers

variable {F : Type} [Field F] [DecidableEq F]

/-- `world` binds non-generic function `name` to parameters `paramNames` and body `body`. -/
def WorldHasFn (world : World F) (name : String) (paramNames : List String)
    (body : Aiur.Generic.Expr F) : Prop :=
  ∀ args types locals expr,
    world.prepare name args = .ok (types, locals, expr) →
    types = [] ∧ args.length = paramNames.length ∧ locals = paramNames.zip args ∧ expr = body

omit [Field F] in
/-- Any non-generic function in a prepared `Generic.Source` satisfies `WorldHasFn`
for its own `source.world`. -/
theorem worldHasFn_of_findFunction? (s : Generic.Source F) {name : String}
    {f : Generic.Function F} (hnoDollar : name.toList.head? ≠ some '$')
    (hfind : s.program.findFunction? name = some f) (htp : f.typeParams = []) :
    WorldHasFn s.world name (f.params.map Prod.fst) f.body := by
  intro args types locals expr hprep
  have hsym : Instance.ofSymbol name = .ok ⟨name, []⟩ := by
    unfold Instance.ofSymbol
    cases hl : name.toList with
    | nil => rfl
    | cons c cs =>
      rw [hl] at hnoDollar
      have hc : c ≠ '$' := by simpa using hnoDollar
      simp [hc]
  have hsf : s.program.sourceFunction? name =
      some { types := [], params := f.params.map fun (n, t) => (n, (t.subst []).toCore),
             body := f.body } := by
    unfold Program.sourceFunction?
    rw [hsym]
    simp [Except.toOption, hfind, arguments, htp, pure, Except.pure, bind, Except.bind]
  simp only [Generic.Source.world, sourceWorld, hsf, SourceFunction.prepare] at hprep
  split at hprep
  · next hcond =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
    obtain ⟨rfl, rfl, rfl⟩ := hprep
    have hlen : args.length = (f.params.map Prod.fst).length := by
      have h1 := congrArg List.length hcond.1
      simp only [List.length_map] at h1 ⊢
      exact h1.symm
    have hnames : (List.map (fun x => (x.1, (x.2.subst []).toCore)) f.params).map Prod.fst =
        f.params.map Prod.fst := by
      rw [List.map_map]; rfl
    refine ⟨rfl, hlen, ?_, rfl⟩
    rw [hnames]
  · simp at hprep

theorem evalFn_plain_inv {world : World F} {name : String} {paramNames : List String}
    {body : Aiur.Generic.Expr F} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F}
    (hfn : WorldHasFn world name paramNames body) (hplain : isPlainExpr body = true)
    (ev : EvalFn world name args h r h') :
    args.length = paramNames.length ∧
    EvalExpr world [] (paramNames.zip args) body h r h' := by
  cases ev with
  | intro prep b =>
    obtain ⟨rfl, hlen, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact ⟨hlen, b⟩
  | returned prep b =>
    obtain ⟨rfl, _, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact False.elim (no_evalExit_of_plain hplain b)

theorem evalExpr_literal_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x : F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.literal x) h r h') :
    r = .field x ∧ h' = h := by
  cases ev; exact ⟨rfl, rfl⟩

theorem evalExpr_var_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {name : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.var name) h r h') :
    locals.find? (·.1 == name) = some (name, r) ∧ h' = h := by
  cases ev with
  | var hlook => exact ⟨hlook, rfl⟩

theorem evalExpr_binary_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {op : BinOp} {lhs rhs : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.binary op lhs rhs) h r h') :
    ∃ x y hm,
      EvalExpr world types locals lhs h x hm ∧
      EvalExpr world types locals rhs hm y h' ∧
      evalBinOp op x y = .ok r := by
  cases ev with
  | binary hl hr hop => exact ⟨_, _, _, hl, hr, hop⟩

theorem evalExpr_index_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {idx : Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.index e idx) h r h') :
    ∃ v, EvalExpr world types locals e h v h' ∧ projectValue v idx = .ok r := by
  cases ev with
  | index hv hp => exact ⟨_, hv, hp⟩

theorem evalExpr_call_inv {world : World F} {locals : Environment F Nat}
    {name : String} {args : List (Aiur.Generic.Expr F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) args) h r h') :
    ∃ vs hm,
      EvalArgs world [] locals args h vs hm ∧
      EvalFn world name vs hm r h' := by
  cases ev with
  | call hargs hcal =>
    simp only [instanceName, Option.getD_some, List.map_nil, Instance.symbol, List.isEmpty_nil,
      ↓reduceIte] at hcal
    exact ⟨_, _, hargs, hcal⟩

theorem evalExpr_call1_inv {world : World F} {locals : Environment F Nat}
    {name : String} {a : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [a]) h r h') :
    ∃ va hm,
      EvalExpr world [] locals a h va hm ∧
      EvalFn world name [va] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with
  | cons ha ht =>
    cases ht
    exact ⟨_, _, ha, hcal⟩

theorem evalExpr_call2_inv {world : World F} {locals : Environment F Nat}
    {name : String} {a b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [a, b]) h r h') :
    ∃ va vb h1 hm,
      EvalExpr world [] locals a h va h1 ∧
      EvalExpr world [] locals b h1 vb hm ∧
      EvalFn world name [va, vb] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with
  | cons ha ht1 =>
    cases ht1 with
    | cons hb ht2 =>
      cases ht2
      exact ⟨_, _, _, _, ha, hb, hcal⟩

theorem evalExpr_tuple2_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {a b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.tuple [a, b]) h r h') :
    ∃ va vb h1,
      EvalExpr world types locals a h va h1 ∧
      EvalExpr world types locals b h1 vb h' ∧
      r = .tuple [va, vb] := by
  cases ev with
  | tuple hargs =>
    cases hargs with
    | cons ha ht1 =>
      cases ht1 with
      | cons hb ht2 =>
        cases ht2
        exact ⟨_, _, _, ha, hb, rfl⟩

theorem evalExpr_array2_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {a b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [a, b]) h r h') :
    ∃ va vb h1,
      EvalExpr world types locals a h va h1 ∧
      EvalExpr world types locals b h1 vb h' ∧
      r = .tuple [va, vb] := by
  cases ev with
  | array hargs =>
    cases hargs with
    | cons ha ht1 =>
      cases ht1 with
      | cons hb ht2 =>
        cases ht2
        exact ⟨_, _, _, ha, hb, rfl⟩

theorem evalExpr_array3_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {a b c : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [a, b, c]) h r h') :
    ∃ va vb vc h1 h2,
      EvalExpr world types locals a h va h1 ∧
      EvalExpr world types locals b h1 vb h2 ∧
      EvalExpr world types locals c h2 vc h' ∧
      r = .tuple [va, vb, vc] := by
  cases ev with
  | array hargs =>
    cases hargs with
    | cons ha ht1 =>
      cases ht1 with
      | cons hb ht2 =>
        cases ht2 with
        | cons hc ht3 =>
          cases ht3
          exact ⟨_, _, _, _, _, ha, hb, hc, rfl⟩

theorem evalExpr_array8_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e0 e1 e2 e3 e4 e5 e6 e7 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [e0, e1, e2, e3, e4, e5, e6, e7]) h r h') :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 h4 h5 h6 h7,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h3 ∧
      EvalExpr world types locals e3 h3 v3 h4 ∧
      EvalExpr world types locals e4 h4 v4 h5 ∧
      EvalExpr world types locals e5 h5 v5 h6 ∧
      EvalExpr world types locals e6 h6 v6 h7 ∧
      EvalExpr world types locals e7 h7 v7 h' ∧
      r = .tuple [v0, v1, v2, v3, v4, v5, v6, v7] := by
  cases ev with
  | array hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2 with | cons h3 t3 =>
    cases t3 with | cons h4 t4 =>
    cases t4 with | cons h5 t5 =>
    cases t5 with | cons h6 t6 =>
    cases t6 with | cons h7 t7 =>
    cases t7
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, h6, h7, rfl⟩

theorem evalExpr_let_wildcard_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.letValue .wildcard e b) h r h') :
    ∃ v hm,
      EvalExpr world types locals e h v hm ∧
      EvalExpr world types locals b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    simp [World.matchPattern, matchPatternWith] at hm
    subst hm
    exact ⟨_, _, hv, hb⟩

theorem evalExpr_let_bind_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x : String} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.letValue (.bind x) e b) h r h') :
    ∃ v hm,
      EvalExpr world types locals e h v hm ∧
      EvalExpr world types ((x, v) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    simp [World.matchPattern, matchPatternWith] at hm
    subst hm
    exact ⟨_, _, hv, hb⟩

theorem evalExpr_let_tuple2_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x y : String} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.letValue (.tuple [.bind x, .bind y]) e b) h r h') :
    ∃ vx vy hm,
      EvalExpr world types locals e h (.tuple [vx, vy]) hm ∧
      EvalExpr world types ((x, vx) :: (y, vy) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      cases vs with
      | nil => simp [World.matchPattern, matchPatternWith] at hm
      | cons v0 t0 =>
        cases t0 with
        | nil => simp [World.matchPattern, matchPatternWith] at hm
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            simp [World.matchPattern, matchPatternWith, matchListWith] at hm
            subst hm
            exact ⟨v0, v1, _, hv, hb⟩
          | cons _ _ => simp [World.matchPattern, matchPatternWith] at hm
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

theorem evalExpr_let_tuple2_wild_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x : String} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.letValue (.tuple [.bind x, .wildcard]) e b) h r h') :
    ∃ vx vy hm,
      EvalExpr world types locals e h (.tuple [vx, vy]) hm ∧
      EvalExpr world types ((x, vx) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      cases vs with
      | nil => simp [World.matchPattern, matchPatternWith] at hm
      | cons v0 t0 =>
        cases t0 with
        | nil => simp [World.matchPattern, matchPatternWith] at hm
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            simp [World.matchPattern, matchPatternWith, matchListWith] at hm
            subst hm
            exact ⟨v0, v1, _, hv, hb⟩
          | cons _ _ => simp [World.matchPattern, matchPatternWith] at hm
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

theorem evalExpr_let_array8_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 : String} {e b : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals
      (.letValue (.array [.bind x0, .bind x1, .bind x2, .bind x3,
                          .bind x4, .bind x5, .bind x6, .bind x7]) e b) h r h') :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 hm,
      EvalExpr world types locals e h (.tuple [v0, v1, v2, v3, v4, v5, v6, v7]) hm ∧
      EvalExpr world types
        ([(x0, v0), (x1, v1), (x2, v2), (x3, v3), (x4, v4), (x5, v5), (x6, v6), (x7, v7)] ++ locals)
        b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, _ | ⟨v7, _ | ⟨v8, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

theorem evalExpr_assertEq_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {a : Aiur.Assertion} {lhs rhs : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.builtin (.assertEq a) [lhs, rhs]) h r h') :
    ∃ vl vr hm,
      EvalExpr world types locals lhs h vl hm ∧
      EvalExpr world types locals rhs hm vr h' ∧
      vl = vr ∧ r = .tuple [] := by
  cases ev with
  | builtin hargs happ =>
    cases hargs with
    | cons hl ht1 =>
      cases ht1 with
      | cons hr ht2 =>
        cases ht2
        simp only [Aiur.Generic.Builtin.apply, Aiur.evalAssertEq] at happ
        split at happ
        · split at happ
          · next heq =>
            simp only [Except.ok.injEq] at happ
            exact ⟨_, _, _, hl, hr, heq, happ.symm⟩
          · cases happ
        · cases happ

theorem evalExpr_hint_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {t : Generic.Ty} {key : Aiur.Generic.Expr F} {ch : String}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.hint t key ch) h r h') :
    ∃ kv, EvalExpr world types locals key h kv h' := by
  cases ev with
  | hint hk _ => exact ⟨_, hk⟩

theorem evalExpr_construct0_inv {world : World F} {locals : Environment F Nat}
    {en ctor : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct en (some []) ctor []) h r h') :
    r = .construct en ctor [] ∧ h' = h := by
  cases ev with
  | construct hargs =>
    cases hargs
    simp [instanceName, Instance.symbol]

theorem evalExpr_construct1_inv {world : World F} {locals : Environment F Nat}
    {en ctor : String} {a : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct en (some []) ctor [a]) h r h') :
    ∃ va, EvalExpr world [] locals a h va h' ∧ r = .construct en ctor [va] := by
  cases ev with
  | construct hargs =>
    cases hargs with
    | cons ha ht =>
      cases ht
      exact ⟨_, ha, by simp [instanceName, Instance.symbol]⟩

end WorldHelpers

/-! ## `UInt8` Maps and `UInt64` Library Contracts -/

section U64Library

variable {F : Type} [Field F] [DecidableEq F]

/-- Checked 64-bit word value: 8 little-endian byte fields `< 256` packing to `n`. -/
def isU64Val (n : Nat) (v : SourceValue F) : Prop :=
  ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Nat,
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
    b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
    n = U64.pack b0 b1 b2 b3 b4 b5 b6 b7 ∧
    v = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
                .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]

/-- Contracts for the three `UInt8` lookup maps used by `UInt64`. -/
structure U8MapSpec (world : World F) : Prop where
  range_pair : ∀ v1 v2 h r h',
    EvalFn world "UInt8::range_pair" [v1, v2] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)
  raw_xor : ∀ v1 v2 h r h',
    EvalFn world "UInt8::raw_xor" [v1, v2] h r h' →
    h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧
      v1 = .field (a : F) ∧ v2 = .field (b : F) ∧ r = .field ((Nat.xor a b : Nat) : F)
  raw_sum_byte : ∀ v h r h',
    EvalFn world "UInt8::raw_sum_byte" [v] h r h' →
    h' = h ∧ ∃ s : Nat, s < 768 ∧ v = .field (s : F) ∧ r = .field ((s % 256 : Nat) : F)

/-- Symbolic proof helper for `List.zip` of two `List.map`s over the same index list. -/
private theorem mem_zip_map_iff {α β γ : Type*} {f : α → β} {g : α → γ} {l : List α}
    {x : β} {y : γ} :
    (x, y) ∈ (l.map f).zip (l.map g) ↔ ∃ a ∈ l, f a = x ∧ g a = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq,
      exists_eq_or_imp, ih]
    tauto

/-- Evaluating `constantExpr c` produces `c.toValue` and leaves the heap unchanged. -/
private theorem evalExpr_constantExpr_inv {world : World F} {types : Types}
    {locals : Environment F Nat} :
    ∀ (c : Constant F) {h h' : Heap F} {r : SourceValue F},
      EvalExpr world types locals (Generic.constantExpr c) h r h' →
      r = c.toValue ∧ h' = h
  | .field x, _, _, _, ev => by
    simp only [Generic.constantExpr] at ev
    cases ev
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩
  | .tuple xs, h, h', r, ev => by
    simp only [Generic.constantExpr] at ev
    cases ev with
    | tuple hargs =>
      have aux : ∀ (ys : List (Constant F)) (h1 h2 : Heap F) (vs : List (SourceValue F)),
          (∀ y ∈ ys, ∀ h1 h2 r, EvalExpr world types locals (Generic.constantExpr y) h1 r h2 →
            r = y.toValue ∧ h2 = h1) →
          EvalArgs world types locals (ys.map Generic.constantExpr) h1 vs h2 →
          vs = ys.map Constant.toValue ∧ h2 = h1 := by
        intro ys
        induction ys with
        | nil =>
          intro h1 h2 vs _ ha
          cases ha; exact ⟨rfl, rfl⟩
        | cons y yt ih =>
          intro h1 h2 vs hrec ha
          cases ha with
          | cons hd tl =>
            obtain ⟨rfl, rfl⟩ := hrec y List.mem_cons_self _ _ _ hd
            obtain ⟨rfl, rfl⟩ := ih _ _ _ (fun z hz => hrec z (List.mem_cons_of_mem _ hz)) tl
            exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := aux xs h h' _ (fun y hy => by
        have : sizeOf y < sizeOf (Value.tuple xs) := by
          have := List.sizeOf_lt_of_mem hy
          simp [Value.tuple.sizeOf_spec]; omega
        exact fun _ _ _ ev => evalExpr_constantExpr_inv y ev) hargs
      exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩
  | .construct n ctor xs, h, h', r, ev => by
    simp only [Generic.constantExpr] at ev
    cases ev with
    | construct hargs =>
      have aux : ∀ (ys : List (Constant F)) (h1 h2 : Heap F) (vs : List (SourceValue F)),
          (∀ y ∈ ys, ∀ h1 h2 r, EvalExpr world types locals (Generic.constantExpr y) h1 r h2 →
            r = y.toValue ∧ h2 = h1) →
          EvalArgs world types locals (ys.map Generic.constantExpr) h1 vs h2 →
          vs = ys.map Constant.toValue ∧ h2 = h1 := by
        intro ys
        induction ys with
        | nil =>
          intro h1 h2 vs _ ha
          cases ha; exact ⟨rfl, rfl⟩
        | cons y yt ih =>
          intro h1 h2 vs hrec ha
          cases ha with
          | cons hd tl =>
            obtain ⟨rfl, rfl⟩ := hrec y List.mem_cons_self _ _ _ hd
            obtain ⟨rfl, rfl⟩ := ih _ _ _ (fun z hz => hrec z (List.mem_cons_of_mem _ hz)) tl
            exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := aux xs h h' _ (fun y hy => by
        have : sizeOf y < sizeOf (Value.construct n ctor xs) := by
          have := List.sizeOf_lt_of_mem hy
          simp [Value.construct.sizeOf_spec]; omega
        exact fun _ _ _ ev => evalExpr_constantExpr_inv y ev) hargs
      exact ⟨by simp [instanceName, Instance.symbol, Constant.toValue, Value.mapAddress], rfl⟩
  | .ptr _ a, _, _, _, _ => Empty.elim a
termination_by c => sizeOf c

omit [Field F] [DecidableEq F] in
private theorem isPlainExpr_constantExpr :
    ∀ (c : Constant F), isPlainExpr (Generic.constantExpr c) = true
  | .field _ => by simp [Generic.constantExpr, isPlainExpr]
  | .tuple xs => by
    simp only [Generic.constantExpr, isPlainExpr, isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.tuple xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.tuple.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .construct n ctor xs => by
    simp only [Generic.constantExpr, isPlainExpr, isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.construct n ctor xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.construct.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .ptr _ a => Empty.elim a
termination_by c => sizeOf c

/-- Symbolic table specification for the 5 tables backing `range_pair`, `raw_xor`, and
`raw_sum_byte` in `Aiur.Library.U8.source`. -/
structure U8TablesMatch (s : Generic.Source F) : Prop where
  noFn_range_pair : s.program.sourceFunction? "UInt8::range_pair" = none
  noFn_raw_xor : s.program.sourceFunction? "UInt8::raw_xor" = none
  noFn_raw_sum_byte : s.program.sourceFunction? "UInt8::raw_sum_byte" = none
  map_range_pair : ∃ m, s.tables.findMap? "UInt8::range_pair" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_units"
  map_raw_xor : ∃ m, s.tables.findMap? "UInt8::raw_xor" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_xors"
  map_raw_sum_byte : ∃ m, s.tables.findMap? "UInt8::raw_sum_byte" = some m ∧
    m.input = "UInt8::sum_inputs" ∧ m.output = "UInt8::sum_bytes"
  tbl_pair_inputs : ∃ t, s.tables.findTable? "UInt8::pair_inputs" = some t ∧
    t.rows = ((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun (a, b) => .tuple [.field (a : F), .field (b : F)]
  tbl_pair_units : ∃ t, s.tables.findTable? "UInt8::pair_units" = some t ∧
    t.rows = ((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun _ => .tuple []
  tbl_pair_xors : ∃ t, s.tables.findTable? "UInt8::pair_xors" = some t ∧
    t.rows = ((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun (a, b) => .field ((Nat.xor a b : Nat) : F)
  tbl_sum_inputs : ∃ t, s.tables.findTable? "UInt8::sum_inputs" = some t ∧
    t.rows = (Carry.rows 256 768).map fun (n, _) => .tuple [.field (n : F)]
  tbl_sum_bytes : ∃ t, s.tables.findTable? "UInt8::sum_bytes" = some t ∧
    t.rows = (Carry.rows 256 768).map fun (_, b) => .field (b : F)

/-- Helper: inverting a map call in `s.world` when `sourceFunction?` is `none`. -/
private theorem evalFn_map_inv (s : Generic.Source F) {name : String}
    (hnone : s.program.sourceFunction? name = none)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world name args h r h') :
    ∃ row : Constant F, lookupMap s.tables name args = .ok row ∧ r = row.toValue ∧ h' = h := by
  cases ev with
  | intro prep b =>
    simp only [Generic.Source.world, sourceWorld, hnone, bind, Except.bind, pure, Except.pure] at prep
    cases hl : lookupMap s.tables name args with
    | error _ => simp [hl] at prep
    | ok row =>
      simp only [hl, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      obtain ⟨rfl, rfl⟩ := evalExpr_constantExpr_inv row b
      exact ⟨row, rfl, rfl, rfl⟩
  | returned prep b =>
    simp only [Generic.Source.world, sourceWorld, hnone, bind, Except.bind, pure, Except.pure] at prep
    cases hl : lookupMap s.tables name args with
    | error _ => simp [hl] at prep
    | ok row =>
      simp only [hl, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      exact False.elim (no_evalExit_of_plain (isPlainExpr_constantExpr row) b)

/-- Every `Generic.Source` whose static tables match `UInt8.tables` satisfies `U8MapSpec`
(proved symbolically with zero table expansion). -/
theorem u8MapSpec_of_source (s : Generic.Source F) (ht : U8TablesMatch s) :
    U8MapSpec s.world := by
  refine ⟨?_, ?_, ?_⟩
  · intro v1 v2 h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_range_pair ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_range_pair
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_pair_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_pair_units
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := mem_zip_map_iff.mp hmem
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
    obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, a', b', ha', hb', hv.1.symm, hv.2.symm⟩
  · intro v1 v2 h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_raw_xor ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_raw_xor
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_pair_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_pair_xors
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := mem_zip_map_iff.mp hmem
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
    obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨rfl, a', b', ha', hb', hv.1.symm, hv.2.symm, by simp [Constant.toValue, Value.mapAddress]⟩
  · intro v h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_raw_sum_byte ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_raw_sum_byte
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_sum_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_sum_bytes
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows] at hmem
    obtain ⟨⟨n, b⟩, hnb, hkeq, hreq⟩ := mem_zip_map_iff.mp hmem
    simp only [Carry.rows, List.mem_map, List.mem_range, Prod.mk.injEq] at hnb
    obtain ⟨s', hs', rfl, rfl⟩ := hnb
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨rfl, s', hs', hv.symm, by simp [Constant.toValue, Value.mapAddress]⟩

/-! ### Expected Elaborated ASTs of `UInt8` and `UInt64` Library Functions -/

private abbrev u8f (e : Aiur.Generic.Expr F) : Aiur.Generic.Expr F :=
  .call "UInt8::to_field" (some []) [e]

private def u8ToFieldBody : Aiur.Generic.Expr F := .var "byte"

private def u8FromFieldsBody : Aiur.Generic.Expr F :=
  .letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
    (.tuple [.var "a", .var "b"])

private def u8SplitSumBody : Aiur.Generic.Expr F :=
  .letValue (.bind "byte") (.call "UInt8::raw_sum_byte" (some []) [.var "sum"])
    (.tuple [.var "byte",
      .binary .div (.binary .sub (.var "sum") (.var "byte")) (.literal (256 : F))])

private def u8RawAndBody : Aiur.Generic.Expr F :=
  .letValue (.bind "x") (.call "UInt8::raw_xor" (some []) [.var "a", .var "b"])
    (.binary .div (.binary .sub (.binary .add (.var "a") (.var "b")) (.var "x")) (.literal (2 : F)))

private def u8RawOrBody : Aiur.Generic.Expr F :=
  .letValue (.bind "x") (.call "UInt8::raw_xor" (some []) [.var "a", .var "b"])
    (.binary .div (.binary .add (.binary .add (.var "a") (.var "b")) (.var "x")) (.literal (2 : F)))

private def u8AndBody : Aiur.Generic.Expr F :=
  .call "UInt8::raw_and" (some []) [.var "a", .var "b"]

private def u8OrBody : Aiur.Generic.Expr F :=
  .call "UInt8::raw_or" (some []) [.var "a", .var "b"]

private def u8XorBody : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor" (some []) [.var "a", .var "b"]

private def u64ToFieldBody : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                     .bind "b4", .bind "b5", .bind "b6", .bind "b7"]) (.var "x") <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u64 -> field: value exceeds 2^56 (top byte must be zero)",
                           runtimeCheck := true })
      [u8f (.var "b7"), .literal (0 : F)]) <|
  .binary .add
    (.binary .add
      (.binary .add
        (.binary .add
          (.binary .add
            (.binary .add (u8f (.var "b0"))
              (.binary .mul (.literal (256 : F)) (u8f (.var "b1"))))
            (.binary .mul (.literal (65536 : F)) (u8f (.var "b2"))))
          (.binary .mul (.literal (16777216 : F)) (u8f (.var "b3"))))
        (.binary .mul (.literal (4294967296 : F)) (u8f (.var "b4"))))
      (.binary .mul (.literal (1099511627776 : F)) (u8f (.var "b5"))))
    (.binary .mul (.literal (281474976710656 : F)) (u8f (.var "b6")))

private def u64FromFieldBody : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "h0", .bind "h1", .bind "h2", .bind "h3",
                     .bind "h4", .bind "h5", .bind "h6", .bind "h7"])
    (.hint (.array .field 8) (.var "value") "bytes_le") <|
  .letValue (.tuple [.bind "b0", .bind "b1"])
    (.call "UInt8::from_fields" (some []) [.var "h0", .var "h1"]) <|
  .letValue (.tuple [.bind "b2", .bind "b3"])
    (.call "UInt8::from_fields" (some []) [.var "h2", .var "h3"]) <|
  .letValue (.tuple [.bind "b4", .bind "b5"])
    (.call "UInt8::from_fields" (some []) [.var "h4", .var "h5"]) <|
  .letValue (.tuple [.bind "b6", .bind "b7"])
    (.call "UInt8::from_fields" (some []) [.var "h6", .var "h7"]) <|
  .letValue (.bind "bytes")
    (.array [.var "b0", .var "b1", .var "b2", .var "b3",
             .var "b4", .var "b5", .var "b6", .var "b7"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u64 bytes do not recompose to the field value",
                           runtimeCheck := false })
      [.call "UInt64::to_field" (some []) [.var "bytes"], .var "value"]) <|
  .var "bytes"

private def u64IsZeroBody : Aiur.Generic.Expr F :=
  .matchValue (.var "x")
    [(.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))), .literal (1 : F)),
     (.wildcard, .literal (0 : F))]

private def subStepExpr (i : Nat) (cin : String) : Aiur.Generic.Expr F :=
  .call "UInt8::split_sum" (some [])
    [.binary .add
      (.binary .sub
        (.binary .add (u8f (.index (.var "a") i)) (.literal (255 : F)))
        (u8f (.index (.var "b") i)))
      (u8f (.var cin))]

private def u64SubWithBorrowBody : Aiur.Generic.Expr F :=
  .letValue (.tuple [.bind "s0", .bind "c1"])
    (.call "UInt8::split_sum" (some [])
      [.binary .sub
        (.binary .add (u8f (.index (.var "a") 0)) (.literal (256 : F)))
        (u8f (.index (.var "b") 0))]) <|
  .letValue (.tuple [.bind "s1", .bind "c2"]) (subStepExpr 1 "c1") <|
  .letValue (.tuple [.bind "s2", .bind "c3"]) (subStepExpr 2 "c2") <|
  .letValue (.tuple [.bind "s3", .bind "c4"]) (subStepExpr 3 "c3") <|
  .letValue (.tuple [.bind "s4", .bind "c5"]) (subStepExpr 4 "c4") <|
  .letValue (.tuple [.bind "s5", .bind "c6"]) (subStepExpr 5 "c5") <|
  .letValue (.tuple [.bind "s6", .bind "c7"]) (subStepExpr 6 "c6") <|
  .letValue (.tuple [.bind "s7", .bind "c8"]) (subStepExpr 7 "c7") <|
  .tuple
    [.array [.var "s0", .var "s1", .var "s2", .var "s3",
             .var "s4", .var "s5", .var "s6", .var "s7"],
     .binary .sub (.literal (1 : F)) (u8f (.var "c8"))]

private def u64MulColumnBody : Aiur.Generic.Expr F :=
  .letValue (.bind "bytes") (.hint (.array .field 8) (.var "x") "bytes_le") <|
  .letValue (.tuple [.bind "r0", .bind "r1"])
    (.call "UInt8::from_fields" (some []) [.index (.var "bytes") 0, .index (.var "bytes") 1]) <|
  .letValue (.tuple [.bind "c0", .bind "c1"])
    (.call "UInt8::from_fields" (some []) [.index (.var "bytes") 2, .index (.var "bytes") 3]) <|
  .letValue (.tuple [.bind "c2", .wildcard])
    (.call "UInt8::from_fields" (some []) [.index (.var "bytes") 4, .literal (0 : F)]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "mul: column hint does not recompose",
                           runtimeCheck := false })
      [.var "x",
       .binary .add
         (.binary .add (u8f (.var "r0")) (.binary .mul (.literal (256 : F)) (u8f (.var "r1"))))
         (.binary .mul (.literal (65536 : F))
           (.binary .add
             (.binary .add (u8f (.var "c0")) (.binary .mul (.literal (256 : F)) (u8f (.var "c1"))))
             (.binary .mul (.literal (65536 : F)) (u8f (.var "c2")))))]) <|
  .tuple [.array [.var "r0", .var "r1"], .array [.var "c0", .var "c1", .var "c2"]]

private def limbExpr (v : String) (i j : Nat) : Aiur.Generic.Expr F :=
  .binary .add (u8f (.index (.var v) i))
    (.binary .mul (.literal (256 : F)) (u8f (.index (.var v) j)))

private def addCarryExpr (base : Aiur.Generic.Expr F) (c : String) : Aiur.Generic.Expr F :=
  .binary .add
    (.binary .add
      (.binary .add base (u8f (.index (.var c) 0)))
      (.binary .mul (.literal (256 : F)) (u8f (.index (.var c) 1))))
    (.binary .mul (.literal (65536 : F)) (u8f (.index (.var c) 2)))

private def u64MulBody : Aiur.Generic.Expr F :=
  .letValue (.bind "a0") (limbExpr "a" 0 1) <|
  .letValue (.bind "b0") (limbExpr "b" 0 1) <|
  .letValue (.bind "a1") (limbExpr "a" 2 3) <|
  .letValue (.bind "b1") (limbExpr "b" 2 3) <|
  .letValue (.bind "a2") (limbExpr "a" 4 5) <|
  .letValue (.bind "b2") (limbExpr "b" 4 5) <|
  .letValue (.bind "a3") (limbExpr "a" 6 7) <|
  .letValue (.bind "b3") (limbExpr "b" 6 7) <|
  .letValue (.tuple [.bind "r0", .bind "c0"])
    (.call "UInt64::mul_column" (some []) [.binary .mul (.var "a0") (.var "b0")]) <|
  .letValue (.tuple [.bind "r1", .bind "c1"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .add (.binary .mul (.var "a0") (.var "b1"))
                                  (.binary .mul (.var "a1") (.var "b0"))) "c0"]) <|
  .letValue (.tuple [.bind "r2", .bind "c2"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .add (.binary .add (.binary .mul (.var "a0") (.var "b2"))
                                                (.binary .mul (.var "a1") (.var "b1")))
                                  (.binary .mul (.var "a2") (.var "b0"))) "c1"]) <|
  .letValue (.tuple [.bind "r3", .bind "c3"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .add (.binary .add (.binary .add (.binary .mul (.var "a0") (.var "b3"))
                                                              (.binary .mul (.var "a1") (.var "b2")))
                                                (.binary .mul (.var "a2") (.var "b1")))
                                  (.binary .mul (.var "a3") (.var "b0"))) "c2"]) <|
  .letValue (.tuple [.bind "r4", .bind "c4"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .add (.binary .add (.binary .mul (.var "a1") (.var "b3"))
                                                (.binary .mul (.var "a2") (.var "b2")))
                                  (.binary .mul (.var "a3") (.var "b1"))) "c3"]) <|
  .letValue (.tuple [.bind "r5", .bind "c5"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .add (.binary .mul (.var "a2") (.var "b3"))
                                  (.binary .mul (.var "a3") (.var "b2"))) "c4"]) <|
  .letValue (.tuple [.bind "r6", .bind "c6"])
    (.call "UInt64::mul_column" (some [])
      [addCarryExpr (.binary .mul (.var "a3") (.var "b3")) "c5"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "mul: final carry exceeds one radix digit",
                           runtimeCheck := true })
      [u8f (.index (.var "c6") 2), .literal (0 : F)]) <|
  .tuple
    [.array [.index (.var "r0") 0, .index (.var "r0") 1,
             .index (.var "r1") 0, .index (.var "r1") 1,
             .index (.var "r2") 0, .index (.var "r2") 1,
             .index (.var "r3") 0, .index (.var "r3") 1],
     .array [.index (.var "r4") 0, .index (.var "r4") 1,
             .index (.var "r5") 0, .index (.var "r5") 1,
             .index (.var "r6") 0, .index (.var "r6") 1,
             .index (.var "c6") 0, .index (.var "c6") 1]]

private def u64BitwiseBody (op : String) : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "a0", .bind "a1", .bind "a2", .bind "a3",
                     .bind "a4", .bind "a5", .bind "a6", .bind "a7"]) (.var "a") <|
  .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                     .bind "b4", .bind "b5", .bind "b6", .bind "b7"]) (.var "b") <|
  .array
    [.call op (some []) [.var "a0", .var "b0"],
     .call op (some []) [.var "a1", .var "b1"],
     .call op (some []) [.var "a2", .var "b2"],
     .call op (some []) [.var "a3", .var "b3"],
     .call op (some []) [.var "a4", .var "b4"],
     .call op (some []) [.var "a5", .var "b5"],
     .call op (some []) [.var "a6", .var "b6"],
     .call op (some []) [.var "a7", .var "b7"]]

/-- World hypothesis for the linked `Aiur.Library.U64.source` library. -/
structure U64LibraryWorld (world : World F) : Prop where
  maps : U8MapSpec world
  constDepth_pos : 0 < world.constDepth
  const_byte0 : world.constant "UInt8::BYTE_0" .field = .ok (.literal (0 : F))
  u8_to_field : WorldHasFn world "UInt8::to_field" ["byte"] u8ToFieldBody
  u8_from_fields : WorldHasFn world "UInt8::from_fields" ["a", "b"] u8FromFieldsBody
  u8_split_sum : WorldHasFn world "UInt8::split_sum" ["sum"] u8SplitSumBody
  u8_raw_and : WorldHasFn world "UInt8::raw_and" ["a", "b"] u8RawAndBody
  u8_raw_or : WorldHasFn world "UInt8::raw_or" ["a", "b"] u8RawOrBody
  u8_and : WorldHasFn world "UInt8::and" ["a", "b"] u8AndBody
  u8_or : WorldHasFn world "UInt8::or" ["a", "b"] u8OrBody
  u8_xor : WorldHasFn world "UInt8::xor" ["a", "b"] u8XorBody
  u64_to_field : WorldHasFn world "UInt64::to_field" ["x"] u64ToFieldBody
  u64_from_field : WorldHasFn world "UInt64::from_field" ["value"] u64FromFieldBody
  u64_is_zero : WorldHasFn world "UInt64::is_zero" ["x"] u64IsZeroBody
  u64_sub_with_borrow : WorldHasFn world "UInt64::sub_with_borrow" ["a", "b"] u64SubWithBorrowBody
  u64_mul_column : WorldHasFn world "UInt64::mul_column" ["x"] u64MulColumnBody
  u64_mul : WorldHasFn world "UInt64::mul" ["a", "b"] u64MulBody
  u64_and : WorldHasFn world "UInt64::and" ["a", "b"] (u64BitwiseBody "UInt8::and")
  u64_or : WorldHasFn world "UInt64::or" ["a", "b"] (u64BitwiseBody "UInt8::or")
  u64_xor : WorldHasFn world "UInt64::xor" ["a", "b"] (u64BitwiseBody "UInt8::xor")

/-- Computable checker verifying that a prepared `Generic.Source` contains all 17
exact `UInt8`/`UInt64` library functions and the `UInt8::BYTE_0` constant. -/
def checkU64Functions (s : Generic.Source F) : Bool :=
  let checkFn (nm : String) (ps : List String) (body : Aiur.Generic.Expr F) : Bool :=
    match s.program.findFunction? nm with
    | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == ps) && (f.body == body)
    | none => false
  let checkByte0 : Bool :=
    match elaborateConst s.program "UInt8::BYTE_0" .field with
    | .ok p => p == .literal (0 : F)
    | .error _ => false
  checkByte0 &&
  checkFn "UInt8::to_field" ["byte"] u8ToFieldBody &&
  checkFn "UInt8::from_fields" ["a", "b"] u8FromFieldsBody &&
  checkFn "UInt8::split_sum" ["sum"] u8SplitSumBody &&
  checkFn "UInt8::raw_and" ["a", "b"] u8RawAndBody &&
  checkFn "UInt8::raw_or" ["a", "b"] u8RawOrBody &&
  checkFn "UInt8::and" ["a", "b"] u8AndBody &&
  checkFn "UInt8::or" ["a", "b"] u8OrBody &&
  checkFn "UInt8::xor" ["a", "b"] u8XorBody &&
  checkFn "UInt64::to_field" ["x"] u64ToFieldBody &&
  checkFn "UInt64::from_field" ["value"] u64FromFieldBody &&
  checkFn "UInt64::is_zero" ["x"] u64IsZeroBody &&
  checkFn "UInt64::sub_with_borrow" ["a", "b"] u64SubWithBorrowBody &&
  checkFn "UInt64::mul_column" ["x"] u64MulColumnBody &&
  checkFn "UInt64::mul" ["a", "b"] u64MulBody &&
  checkFn "UInt64::and" ["a", "b"] (u64BitwiseBody "UInt8::and") &&
  checkFn "UInt64::or" ["a", "b"] (u64BitwiseBody "UInt8::or") &&
  checkFn "UInt64::xor" ["a", "b"] (u64BitwiseBody "UInt8::xor")

/-- Behavioral contracts for the 8 `UInt64` operations over `EvalFn`. -/
structure U64Contracts (world : World F) : Prop where
  to_field : ∀ n w h r h', isU64Val n w →
    EvalFn world "UInt64::to_field" [w] h r h' →
    n < natLimit ∧ r = .field (n : F) ∧ h' = h
  from_field : ∀ v h r h',
    EvalFn world "UInt64::from_field" [v] h r h' →
    ∃ n, n < natLimit ∧ v = .field (n : F) ∧ isU64Val n r ∧ h' = h
  is_zero : ∀ n w h r h', isU64Val n w →
    EvalFn world "UInt64::is_zero" [w] h r h' →
    r = .field (if n = 0 then 1 else 0) ∧ h' = h
  sub_with_borrow : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
    EvalFn world "UInt64::sub_with_borrow" [wa, wb] h r h' →
    ∃ wd, isU64Val ((a + U64.base - b) % U64.base) wd ∧
      r = .tuple [wd, .field (if a < b then 1 else 0)] ∧ h' = h
  mul : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
    EvalFn world "UInt64::mul" [wa, wb] h r h' →
    ∃ wlo whi, isU64Val ((a * b) % U64.base) wlo ∧ isU64Val ((a * b) / U64.base) whi ∧
      r = .tuple [wlo, whi] ∧ h' = h
  and : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
    EvalFn world "UInt64::and" [wa, wb] h r h' →
    isU64Val (a &&& b) r ∧ h' = h
  or : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
    EvalFn world "UInt64::or" [wa, wb] h r h' →
    isU64Val (a ||| b) r ∧ h' = h
  xor : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
    EvalFn world "UInt64::xor" [wa, wb] h r h' →
    isU64Val (a ^^^ b) r ∧ h' = h

/-! ### Direct Proofs of `UInt8` and `UInt64` Contracts over `EvalFn` -/

section U64Proofs

variable {world : World F} (fc : FieldCompatible F) (lib : U64LibraryWorld world)
include lib

theorem u8_to_field_spec {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::to_field" [v] h r h') : r = v ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_to_field (by rfl) ev
  obtain ⟨hlook, rfl⟩ := evalExpr_var_inv b
  simp only [List.zip_cons_cons, List.zip_nil_right, List.find?_cons, beq_self_eq_true,
    Option.some.injEq, Prod.mk.injEq, true_and] at hlook
  exact ⟨hlook.symm, rfl⟩

theorem u8_from_fields_spec {v1 v2 r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::from_fields" [v1, v2] h r h') :
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F) := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_from_fields (by rfl) ev
  obtain ⟨_, hm, hcall, hret⟩ := evalExpr_let_wildcard_inv b
  obtain ⟨va, vb, h1, h2, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
  obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
  obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
  simp at hla hlb
  subst hla hlb
  obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := lib.maps.range_pair _ _ _ _ _ hcal
  obtain ⟨va', vb', h3, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
  obtain ⟨hla', rfl⟩ := evalExpr_var_inv eva'
  obtain ⟨hlb', rfl⟩ := evalExpr_var_inv evb'
  simp at hla' hlb'
  exact ⟨by rw [hla', hlb'], rfl, a, b', ha, hb, rfl, rfl⟩

theorem u8_split_sum_spec (fc : FieldCompatible F) {s : Nat} (hs : s < 768)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::split_sum" [.field (s : F)] h r h') :
    r = .tuple [.field ((s % 256 : Nat) : F), .field ((s / 256 : Nat) : F)] ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_plain_inv lib.u8_split_sum (by rfl) ev
  obtain ⟨vb, hm, hcall, hret⟩ := evalExpr_let_bind_inv b
  obtain ⟨vs, h1, evs, hcal⟩ := evalExpr_call1_inv hcall
  obtain ⟨hls, rfl⟩ := evalExpr_var_inv evs
  simp at hls; subst hls
  obtain ⟨rfl, s', hs', heqF, rfl⟩ := lib.maps.raw_sum_byte _ _ _ _ hcal
  have hss : s = s' := fc.natCast_inj (by omega) (by omega) (Value.field.inj heqF)
  subst hss
  obtain ⟨v0, v1, h2, ev0, ev1, rfl⟩ := evalExpr_tuple2_inv hret
  obtain ⟨hl0, rfl⟩ := evalExpr_var_inv ev0
  simp at hl0; subst hl0
  obtain ⟨xdiv, ydiv, h3, evsub, ev256, hdiv⟩ := evalExpr_binary_inv ev1
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev256
  obtain ⟨xs, ys, h4, evsum, evbyte, hsub⟩ := evalExpr_binary_inv evsub
  obtain ⟨hlsum, rfl⟩ := evalExpr_var_inv evsum
  obtain ⟨hlbyte, rfl⟩ := evalExpr_var_inv evbyte
  simp at hlsum hlbyte; subst hlsum hlbyte
  simp only [evalBinOp, Except.ok.injEq] at hsub
  subst hsub
  have h256 : (256 : F) ≠ 0 := fc.radix_ne_zero
  simp only [evalBinOp, h256, ↓reduceIte, Except.ok.injEq] at hdiv
  subst hdiv
  have hrec := U64.split_sum_recover fc.u64 s
  exact ⟨by simp [hrec], rfl⟩

theorem u8_xor_spec (fc : FieldCompatible F) {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::xor" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.xor a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_xor (by rfl) ev
  obtain ⟨va, vb, h1, h2, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
  obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
  simp at hla hlb; subst hla hlb
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hcal
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj haEq)
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj hbEq)
  subst_vars
  exact ⟨rfl, rfl⟩

theorem u8_and_spec (fc : FieldCompatible F) {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::and" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.land a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_and (by rfl) ev
  obtain ⟨va, vb, h1, h2, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
  obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
  simp at hla hlb; subst hla hlb
  obtain ⟨_, body2⟩ := evalFn_plain_inv lib.u8_raw_and (by rfl) hcal
  obtain ⟨vx, hm, hcallx, hret⟩ := evalExpr_let_bind_inv body2
  obtain ⟨va', vb', h3, h4, eva', evb', hxor⟩ := evalExpr_call2_inv hcallx
  obtain ⟨hla', rfl⟩ := evalExpr_var_inv eva'
  obtain ⟨hlb', rfl⟩ := evalExpr_var_inv evb'
  simp at hla' hlb'; subst hla' hlb'
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hxor
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj haEq)
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj hbEq)
  subst_vars
  obtain ⟨xn, yn, h5, evnum, ev2, hdiv⟩ := evalExpr_binary_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨xs, ys, h6, evadd, evx, hsub⟩ := evalExpr_binary_inv evnum
  obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
  simp at hlx; subst hlx
  obtain ⟨xa, xb, h7, eva2, evb2, hadd⟩ := evalExpr_binary_inv evadd
  obtain ⟨hla2, rfl⟩ := evalExpr_var_inv eva2
  obtain ⟨hlb2, rfl⟩ := evalExpr_var_inv evb2
  simp at hla2 hlb2; subst hla2 hlb2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
  have h2ne : (2 : F) ≠ 0 := fc.two_ne_zero
  simp only [evalBinOp, h2ne, ↓reduceIte, Except.ok.injEq] at hdiv; subst hdiv
  have hand := (U64.and_sound fc.u64 ha (by omega : 0 < 256) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    hb (by omega : 0 < 256) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).1
  exact ⟨congrArg Value.field hand, rfl⟩

theorem u8_or_spec (fc : FieldCompatible F) {a b : Nat} (ha : a < 256) (hb : b < 256)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::or" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((Nat.lor a b : Nat) : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u8_or (by rfl) ev
  obtain ⟨va, vb, h1, h2, eva, evb, hcal⟩ := evalExpr_call2_inv body
  obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
  obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
  simp at hla hlb; subst hla hlb
  obtain ⟨_, body2⟩ := evalFn_plain_inv lib.u8_raw_or (by rfl) hcal
  obtain ⟨vx, hm, hcallx, hret⟩ := evalExpr_let_bind_inv body2
  obtain ⟨va', vb', h3, h4, eva', evb', hxor⟩ := evalExpr_call2_inv hcallx
  obtain ⟨hla', rfl⟩ := evalExpr_var_inv eva'
  obtain ⟨hlb', rfl⟩ := evalExpr_var_inv evb'
  simp at hla' hlb'; subst hla' hlb'
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ hxor
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj haEq)
  have := fc.natCast_inj (by omega) (by omega) (Value.field.inj hbEq)
  subst_vars
  obtain ⟨xn, yn, h5, evnum, ev2, hdiv⟩ := evalExpr_binary_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨xs, ys, h6, evadd, evx, hadd2⟩ := evalExpr_binary_inv evnum
  obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
  simp at hlx; subst hlx
  obtain ⟨xa, xb, h7, eva2, evb2, hadd⟩ := evalExpr_binary_inv evadd
  obtain ⟨hla2, rfl⟩ := evalExpr_var_inv eva2
  obtain ⟨hlb2, rfl⟩ := evalExpr_var_inv evb2
  simp at hla2 hlb2; subst hla2 hlb2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  simp only [evalBinOp, Except.ok.injEq] at hadd2; subst hadd2
  have h2ne : (2 : F) ≠ 0 := fc.two_ne_zero
  simp only [evalBinOp, h2ne, ↓reduceIte, Except.ok.injEq] at hdiv; subst hdiv
  have hor := (U64.or_sound fc.u64 ha (by omega : 0 < 256) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    hb (by omega : 0 < 256) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).1
  exact ⟨congrArg Value.field hor, rfl⟩

/-- Helper: inverting `UInt8::to_field(var nm)`. -/
private theorem eval_u8f_var {locals : Environment F Nat} {nm : String} {v : SourceValue F}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (u8f (.var nm)) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨va, hm, eva, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv eva
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, rfl⟩ := hl
  exact u8_to_field_spec lib hcal

/-- Helper: inverting `UInt8::to_field(index (var nm) idx)`. -/
private theorem eval_u8f_idx {locals : Environment F Nat} {nm : String}
    {vs : List (SourceValue F)} {idx : Nat} {v : SourceValue F}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .tuple vs))
    (hidx : vs[idx]? = some v)
    (ev : EvalExpr world [] locals (u8f (.index (.var nm) idx)) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨va, hm, eva, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨vt, evt, hproj⟩ := evalExpr_index_inv eva
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv evt
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, rfl⟩ := hl
  simp only [projectValue, hidx, pure, Except.pure, Except.ok.injEq] at hproj
  subst hproj
  exact u8_to_field_spec lib hcal

/-- Helper: inverting `lit * UInt8::to_field(var nm)`. -/
private theorem eval_mul_u8f_var {locals : Environment F Nat} {c x : F} {nm : String}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .field x))
    (ev : EvalExpr world [] locals (.binary .mul (.literal c) (u8f (.var nm))) h r h') :
    r = .field (c * x) ∧ h' = h := by
  obtain ⟨vl, vr, hm, evl, evr, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evl
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib hlook evr
  simp only [evalBinOp, Except.ok.injEq] at hop
  exact ⟨hop.symm, rfl⟩

/-- Helper: inverting `lit * UInt8::to_field(index (var nm) idx)`. -/
private theorem eval_mul_u8f_idx {locals : Environment F Nat} {c x : F} {nm : String}
    {vs : List (SourceValue F)} {idx : Nat} {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .tuple vs))
    (hidx : vs[idx]? = some (.field x))
    (ev : EvalExpr world [] locals (.binary .mul (.literal c) (u8f (.index (.var nm) idx))) h r h') :
    r = .field (c * x) ∧ h' = h := by
  obtain ⟨vl, vr, hm, evl, evr, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evl
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib hlook hidx evr
  simp only [evalBinOp, Except.ok.injEq] at hop
  exact ⟨hop.symm, rfl⟩

theorem u64_to_field_spec (fc : FieldCompatible F) {n : Nat} {w r : SourceValue F}
    {h h' : Heap F} (hw : isU64Val n w)
    (ev : EvalFn world "UInt64::to_field" [w] h r h') :
    n < natLimit ∧ r = .field (n : F) ∧ h' = h := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩ := hw
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u64_to_field (by rfl) ev
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, hm0, evx, rest0⟩ := evalExpr_let_array8_inv body
  obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
  simp only [List.zip_cons_cons, List.zip_nil_right, List.find?_cons, beq_self_eq_true,
    Option.some.injEq, Prod.mk.injEq, true_and, Value.tuple.injEq, List.cons.injEq, and_true] at hlx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hlx
  obtain ⟨_, hm1, hass, hsum⟩ := evalExpr_let_wildcard_inv rest0
  obtain ⟨vl, vr, hm2, evl, evr, htop, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib (by simp; rfl) evl
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  have htopF : (b7 : F) = 0 := Value.field.inj htop
  obtain ⟨hlt, hcast⟩ := U64.to_field_sound fc.u64 h0 h1 h2 h3 h4 h5 h6 h7 htopF
  -- Unwind the 6 nested additions
  obtain ⟨s5, t6, ha6, ev5, evt6, hop6⟩ := evalExpr_binary_inv hsum
  obtain ⟨s4, t5, ha5, ev4, evt5, hop5⟩ := evalExpr_binary_inv ev5
  obtain ⟨s3, t4, ha4, ev3, evt4, hop4⟩ := evalExpr_binary_inv ev4
  obtain ⟨s2, t3, ha3, ev2, evt3, hop3⟩ := evalExpr_binary_inv ev3
  obtain ⟨s1, t2, ha2, ev1, evt2, hop2⟩ := evalExpr_binary_inv ev2
  obtain ⟨s0, t1, ha1, ev0, evt1, hop1⟩ := evalExpr_binary_inv ev1
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib (by simp; rfl) ev0
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt1
  simp only [evalBinOp, Except.ok.injEq] at hop1; subst hop1
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt2
  simp only [evalBinOp, Except.ok.injEq] at hop2; subst hop2
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt3
  simp only [evalBinOp, Except.ok.injEq] at hop3; subst hop3
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt4
  simp only [evalBinOp, Except.ok.injEq] at hop4; subst hop4
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt5
  simp only [evalBinOp, Except.ok.injEq] at hop5; subst hop5
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evt6
  simp only [evalBinOp, Except.ok.injEq] at hop6; subst hop6
  exact ⟨by simpa [natLimit, U64.fieldBound] using hlt, by rw [hcast], rfl⟩

theorem u64_from_field_spec (fc : FieldCompatible F) {v r : SourceValue F}
    {h h' : Heap F} (ev : EvalFn world "UInt64::from_field" [v] h r h') :
    ∃ n, n < natLimit ∧ v = .field (n : F) ∧ isU64Val n r ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u64_from_field (by rfl) ev
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm0, evhint, r0⟩ := evalExpr_let_array8_inv body
  obtain ⟨_, evval⟩ := evalExpr_hint_inv evhint
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evval
  obtain ⟨b0v, b1v, hm1, ev01, r1⟩ := evalExpr_let_tuple2_inv r0
  obtain ⟨_, _, _, _, e0, e1, c01⟩ := evalExpr_call2_inv ev01
  obtain ⟨l0, rfl⟩ := evalExpr_var_inv e0
  obtain ⟨l1, rfl⟩ := evalExpr_var_inv e1
  simp at l0 l1; subst l0 l1
  obtain ⟨heq01, rfl, b0, b1, hb0, hb1, rfl, rfl⟩ := u8_from_fields_spec lib c01
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq01
  obtain ⟨rfl, rfl⟩ := heq01
  obtain ⟨b2v, b3v, hm2, ev23, r2⟩ := evalExpr_let_tuple2_inv r1
  obtain ⟨_, _, _, _, e2, e3, c23⟩ := evalExpr_call2_inv ev23
  obtain ⟨l2, rfl⟩ := evalExpr_var_inv e2
  obtain ⟨l3, rfl⟩ := evalExpr_var_inv e3
  simp at l2 l3; subst l2 l3
  obtain ⟨heq23, rfl, b2, b3, hb2, hb3, rfl, rfl⟩ := u8_from_fields_spec lib c23
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq23
  obtain ⟨rfl, rfl⟩ := heq23
  obtain ⟨b4v, b5v, hm3, ev45, r3⟩ := evalExpr_let_tuple2_inv r2
  obtain ⟨_, _, _, _, e4, e5, c45⟩ := evalExpr_call2_inv ev45
  obtain ⟨l4, rfl⟩ := evalExpr_var_inv e4
  obtain ⟨l5, rfl⟩ := evalExpr_var_inv e5
  simp at l4 l5; subst l4 l5
  obtain ⟨heq45, rfl, b4, b5, hb4, hb5, rfl, rfl⟩ := u8_from_fields_spec lib c45
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq45
  obtain ⟨rfl, rfl⟩ := heq45
  obtain ⟨b6v, b7v, hm4, ev67, r4⟩ := evalExpr_let_tuple2_inv r3
  obtain ⟨_, _, _, _, e6, e7, c67⟩ := evalExpr_call2_inv ev67
  obtain ⟨l6, rfl⟩ := evalExpr_var_inv e6
  obtain ⟨l7, rfl⟩ := evalExpr_var_inv e7
  simp at l6 l7; subst l6 l7
  obtain ⟨heq67, rfl, b6, b7, hb6, hb7, rfl, rfl⟩ := u8_from_fields_spec lib c67
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq67
  obtain ⟨rfl, rfl⟩ := heq67
  obtain ⟨bytesv, hm5, evarr, r5⟩ := evalExpr_let_bind_inv r4
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, _, _, _, _, _, _, _,
    eu0, eu1, eu2, eu3, eu4, eu5, eu6, eu7, rfl⟩ := evalExpr_array8_inv evarr
  obtain ⟨lu0, rfl⟩ := evalExpr_var_inv eu0
  obtain ⟨lu1, rfl⟩ := evalExpr_var_inv eu1
  obtain ⟨lu2, rfl⟩ := evalExpr_var_inv eu2
  obtain ⟨lu3, rfl⟩ := evalExpr_var_inv eu3
  obtain ⟨lu4, rfl⟩ := evalExpr_var_inv eu4
  obtain ⟨lu5, rfl⟩ := evalExpr_var_inv eu5
  obtain ⟨lu6, rfl⟩ := evalExpr_var_inv eu6
  obtain ⟨lu7, rfl⟩ := evalExpr_var_inv eu7
  simp at lu0 lu1 lu2 lu3 lu4 lu5 lu6 lu7
  subst lu0 lu1 lu2 lu3 lu4 lu5 lu6 lu7
  have hu64 : isU64Val (U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
      (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
               .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]) :=
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, rfl, rfl⟩
  obtain ⟨_, hm6, hass, evret⟩ := evalExpr_let_wildcard_inv r5
  obtain ⟨vl, vr, hm7, evtf, evv, heqvv, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨vb, hm8, evbytes, ctf⟩ := evalExpr_call1_inv evtf
  obtain ⟨lbytes, rfl⟩ := evalExpr_var_inv evbytes
  simp at lbytes; subst lbytes
  obtain ⟨hlt, rfl, rfl⟩ := u64_to_field_spec lib fc hu64 ctf
  obtain ⟨lv, rfl⟩ := evalExpr_var_inv evv
  simp at lv; subst lv
  obtain ⟨lret, rfl⟩ := evalExpr_var_inv evret
  simp at lret; subst lret
  exact ⟨U64.pack b0 b1 b2 b3 b4 b5 b6 b7, hlt, heqvv.symm, hu64, rfl⟩

/-- Matching `.global "UInt8::BYTE_0" (some .field)` against `.field x` succeeds iff `x = 0`. -/
private theorem match_byte0_iff (x : F) (h : Heap F) :
    world.matchPattern [] h (.global "UInt8::BYTE_0" (some .field)) (.field x) =
      .ok (if x = 0 then some [] else none) := by
  obtain ⟨d, hd⟩ : ∃ d, world.constDepth = d + 1 :=
    ⟨world.constDepth - 1, by have := lib.constDepth_pos; omega⟩
  unfold World.matchPattern
  rw [hd]
  simp only [matchPatternWith, Ty.subst, lib.const_byte0, bind, Except.bind,
    Aiur.Pattern.bindings]
  by_cases hx : x = 0
  · subst hx; simp [pure, Except.pure]
  · have hx' : (0 : F) ≠ x := Ne.symm hx
    simp [hx, hx', pure, Except.pure]

private theorem match_byte0_array8 (b0 b1 b2 b3 b4 b5 b6 b7 : F) (h : Heap F) :
    world.matchPattern [] h
      (.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))))
      (.tuple [.field b0, .field b1, .field b2, .field b3,
               .field b4, .field b5, .field b6, .field b7]) =
    .ok (if b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0 ∧ b7 = 0
         then some [] else none) := by
  have hm0 := match_byte0_iff lib b0 h
  have hm1 := match_byte0_iff lib b1 h
  have hm2 := match_byte0_iff lib b2 h
  have hm3 := match_byte0_iff lib b3 h
  have hm4 := match_byte0_iff lib b4 h
  have hm5 := match_byte0_iff lib b5 h
  have hm6 := match_byte0_iff lib b6 h
  have hm7 := match_byte0_iff lib b7 h
  have hpat : world.matchPattern [] h
      (.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))))
      (.tuple [.field b0, .field b1, .field b2, .field b3,
               .field b4, .field b5, .field b6, .field b7]) =
      matchListWith (fun pat value => world.matchPattern [] h pat.val value)
        (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))).attach
        [.field b0, .field b1, .field b2, .field b3,
         .field b4, .field b5, .field b6, .field b7] := by
    simp [World.matchPattern, matchPatternWith, List.replicate]
  rw [hpat]
  simp only [List.replicate, List.attach, List.attachWith, List.pmap, matchListWith,
    hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, bind, Except.bind, pure, Except.pure]
  by_cases h0 : b0 = 0
  · simp only [h0, ↓reduceIte, true_and]
    by_cases h1 : b1 = 0
    · simp only [h1, ↓reduceIte, true_and]
      by_cases h2 : b2 = 0
      · simp only [h2, ↓reduceIte, true_and]
        by_cases h3 : b3 = 0
        · simp only [h3, ↓reduceIte, true_and]
          by_cases h4 : b4 = 0
          · simp only [h4, ↓reduceIte, true_and]
            by_cases h5 : b5 = 0
            · simp only [h5, ↓reduceIte, true_and]
              by_cases h6 : b6 = 0
              · simp only [h6, ↓reduceIte, true_and]
                by_cases h7 : b7 = 0
                · simp [h7]
                · simp [h7]
              · simp [h6]
            · simp [h5]
          · simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [h0]

theorem u64_is_zero_spec (fc : FieldCompatible F) {n : Nat} {w r : SourceValue F}
    {h h' : Heap F} (hw : isU64Val n w)
    (ev : EvalFn world "UInt64::is_zero" [w] h r h') :
    r = .field (if n = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩ := hw
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u64_is_zero (by rfl) ev
  cases body with
  | matchValue evx hsel hbr =>
    obtain ⟨hlx, hmid⟩ := evalExpr_var_inv evx
    rw [hmid] at hsel hbr
    simp at hlx; subst hlx
    have hiff := U64.is_zero_sound fc.u64 h0 h1 h2 h3 h4 h5 h6 h7
    have hm8 := match_byte0_array8 lib (b0 : F) (b1 : F) (b2 : F) (b3 : F)
      (b4 : F) (b5 : F) (b6 : F) (b7 : F) h
    by_cases hall : (b0 : F) = 0 ∧ (b1 : F) = 0 ∧ (b2 : F) = 0 ∧ (b3 : F) = 0 ∧
                    (b4 : F) = 0 ∧ (b5 : F) = 0 ∧ (b6 : F) = 0 ∧ (b7 : F) = 0
    · have hpack0 : U64.pack b0 b1 b2 b3 b4 b5 b6 b7 = 0 := hiff.mp hall
      unfold SourceSemantics.selectArm at hsel
      rw [hm8] at hsel
      simp [hall] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hbr
      simp [hpack0]
    · have hpackNe : U64.pack b0 b1 b2 b3 b4 b5 b6 b7 ≠ 0 := fun h0' => hall (hiff.mpr h0')
      unfold SourceSemantics.selectArm at hsel
      rw [hm8] at hsel
      simp [hall, SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hbr
      simp [hpackNe]

/-- Helper for byte `i ≥ 1` of `UInt64::sub_with_borrow`. -/
private theorem eval_sub_step (fc : FieldCompatible F) {locals : Environment F Nat}
    {as bs : List (SourceValue F)} {i : Nat} {ai bi ci : Nat} {cin : String}
    {h h' : Heap F} {r : SourceValue F}
    (ha_l : locals.find? (·.1 == "a") = some ("a", .tuple as))
    (hb_l : locals.find? (·.1 == "b") = some ("b", .tuple bs))
    (hc_l : locals.find? (·.1 == cin) = some (cin, .field (ci : F)))
    (hai_g : as[i]? = some (.field (ai : F)))
    (hbi_g : bs[i]? = some (.field (bi : F)))
    (hai : ai < 256) (hbi : bi < 256) (hci : ci < 2)
    (ev : EvalExpr world [] locals (subStepExpr i cin) h r h') :
    let sum := ai + 255 - bi + ci
    r = .tuple [.field ((sum % 256 : Nat) : F), .field ((sum / 256 : Nat) : F)] ∧ h' = h := by
  obtain ⟨varg, hm, evarg, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨vl, vr, h1, evl, evr, hadd⟩ := evalExpr_binary_inv evarg
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib hc_l evr
  obtain ⟨vll, vlr, h2, evll, evlr, hsub⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib hb_l hbi_g evlr
  obtain ⟨vlll, vllr, h3, evlll, evllr, hadd2⟩ := evalExpr_binary_inv evll
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib ha_l hai_g evlll
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evllr
  simp only [evalBinOp, Except.ok.injEq] at hadd2; subst hadd2
  simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  have hcast : ((ai : F) + (255 : F) - (bi : F) + (ci : F)) =
      ((ai + 255 - bi + ci : Nat) : F) := by
    have hle : bi ≤ ai + 255 := by omega
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_add]
    simp
  rw [hcast] at hcal
  exact u8_split_sum_spec lib fc (by omega) hcal

theorem u64_sub_with_borrow_spec (fc : FieldCompatible F) {a b : Nat} {wa wb r : SourceValue F}
    {h h' : Heap F} (hwa : isU64Val a wa) (hwb : isU64Val b wb)
    (ev : EvalFn world "UInt64::sub_with_borrow" [wa, wb] h r h') :
    ∃ wd, isU64Val ((a + U64.base - b) % U64.base) wd ∧
      r = .tuple [wd, .field (if a < b then 1 else 0)] ∧ h' = h := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, rfl, rfl⟩ := hwa
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, rfl, rfl⟩ := hwb
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u64_sub_with_borrow (by rfl) ev
  -- Step 0
  obtain ⟨s0v, c1v, _, ev0, r1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨varg0, _, evarg0, hcal0⟩ := evalExpr_call1_inv ev0
  obtain ⟨vl0, vr0, _, evl0, evr0, hsub0⟩ := evalExpr_binary_inv evarg0
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib (by simp; rfl) (by simp; rfl) evr0
  obtain ⟨vll0, vlr0, _, evll0, evlr0, hadd0⟩ := evalExpr_binary_inv evl0
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib (by simp; rfl) (by simp; rfl) evll0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evlr0
  simp only [evalBinOp, Except.ok.injEq] at hadd0; subst hadd0
  simp only [evalBinOp, Except.ok.injEq] at hsub0; subst hsub0
  have hcast0 : ((a0 : F) + (256 : F) - (b0 : F)) = ((a0 + 256 - b0 : Nat) : F) := by
    have hle : b0 ≤ a0 + 256 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add]; simp
  rw [hcast0] at hcal0
  obtain ⟨heq0, rfl⟩ := u8_split_sum_spec lib fc (by omega) hcal0
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
  obtain ⟨rfl, rfl⟩ := heq0
  set s0 := (a0 + 256 - b0) % 256
  set c1 := (a0 + 256 - b0) / 256
  have hs0 : s0 < 256 := Nat.mod_lt _ (by omega)
  have hc1 : c1 < 2 := by omega
  have he0 : a0 + 256 - b0 = s0 + 256 * c1 := (Nat.mod_add_div _ 256).symm
  -- Step 1
  obtain ⟨s1v, c2v, _, ev1, r2⟩ := evalExpr_let_tuple2_inv r1
  obtain ⟨heq1, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha1 hb1 hc1 ev1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl⟩ := heq1
  set s1 := (a1 + 255 - b1 + c1) % 256
  set c2 := (a1 + 255 - b1 + c1) / 256
  have hs1 : s1 < 256 := Nat.mod_lt _ (by omega)
  have hc2 : c2 < 2 := by omega
  have he1 : a1 + 255 - b1 + c1 = s1 + 256 * c2 := (Nat.mod_add_div _ 256).symm
  -- Step 2
  obtain ⟨s2v, c3v, _, ev2, r3⟩ := evalExpr_let_tuple2_inv r2
  obtain ⟨heq2, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha2 hb2 hc2 ev2
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl⟩ := heq2
  set s2 := (a2 + 255 - b2 + c2) % 256
  set c3 := (a2 + 255 - b2 + c2) / 256
  have hs2 : s2 < 256 := Nat.mod_lt _ (by omega)
  have hc3 : c3 < 2 := by omega
  have he2 : a2 + 255 - b2 + c2 = s2 + 256 * c3 := (Nat.mod_add_div _ 256).symm
  -- Step 3
  obtain ⟨s3v, c4v, _, ev3, r4⟩ := evalExpr_let_tuple2_inv r3
  obtain ⟨heq3, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha3 hb3 hc3 ev3
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3
  obtain ⟨rfl, rfl⟩ := heq3
  set s3 := (a3 + 255 - b3 + c3) % 256
  set c4 := (a3 + 255 - b3 + c3) / 256
  have hs3 : s3 < 256 := Nat.mod_lt _ (by omega)
  have hc4 : c4 < 2 := by omega
  have he3 : a3 + 255 - b3 + c3 = s3 + 256 * c4 := (Nat.mod_add_div _ 256).symm
  -- Step 4
  obtain ⟨s4v, c5v, _, ev4, r5⟩ := evalExpr_let_tuple2_inv r4
  obtain ⟨heq4, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha4 hb4 hc4 ev4
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4
  obtain ⟨rfl, rfl⟩ := heq4
  set s4 := (a4 + 255 - b4 + c4) % 256
  set c5 := (a4 + 255 - b4 + c4) / 256
  have hs4 : s4 < 256 := Nat.mod_lt _ (by omega)
  have hc5 : c5 < 2 := by omega
  have he4 : a4 + 255 - b4 + c4 = s4 + 256 * c5 := (Nat.mod_add_div _ 256).symm
  -- Step 5
  obtain ⟨s5v, c6v, _, ev5, r6⟩ := evalExpr_let_tuple2_inv r5
  obtain ⟨heq5, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha5 hb5 hc5 ev5
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq5
  obtain ⟨rfl, rfl⟩ := heq5
  set s5 := (a5 + 255 - b5 + c5) % 256
  set c6 := (a5 + 255 - b5 + c5) / 256
  have hs5 : s5 < 256 := Nat.mod_lt _ (by omega)
  have hc6 : c6 < 2 := by omega
  have he5 : a5 + 255 - b5 + c5 = s5 + 256 * c6 := (Nat.mod_add_div _ 256).symm
  -- Step 6
  obtain ⟨s6v, c7v, _, ev6, r7⟩ := evalExpr_let_tuple2_inv r6
  obtain ⟨heq6, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha6 hb6 hc6 ev6
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq6
  obtain ⟨rfl, rfl⟩ := heq6
  set s6 := (a6 + 255 - b6 + c6) % 256
  set c7 := (a6 + 255 - b6 + c6) / 256
  have hs6 : s6 < 256 := Nat.mod_lt _ (by omega)
  have hc7 : c7 < 2 := by omega
  have he6 : a6 + 255 - b6 + c6 = s6 + 256 * c7 := (Nat.mod_add_div _ 256).symm
  -- Step 7
  obtain ⟨s7v, c8v, _, ev7, r8⟩ := evalExpr_let_tuple2_inv r7
  obtain ⟨heq7, rfl⟩ := eval_sub_step lib fc (by simp; rfl) (by simp; rfl) (by simp) (by simp) (by simp)
    ha7 hb7 hc7 ev7
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq7
  obtain ⟨rfl, rfl⟩ := heq7
  set s7 := (a7 + 255 - b7 + c7) % 256
  set c8 := (a7 + 255 - b7 + c7) / 256
  have hs7 : s7 < 256 := Nat.mod_lt _ (by omega)
  have he7 : a7 + 255 - b7 + c7 = s7 + 256 * c8 := (Nat.mod_add_div _ 256).symm
  -- Final tuple
  obtain ⟨vdiff, vbor, _, evdiff, evbor, rfl⟩ := evalExpr_tuple2_inv r8
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, _, _, _, _, _, _, _,
    eu0, eu1, eu2, eu3, eu4, eu5, eu6, eu7, rfl⟩ := evalExpr_array8_inv evdiff
  obtain ⟨l0, rfl⟩ := evalExpr_var_inv eu0
  obtain ⟨l1, rfl⟩ := evalExpr_var_inv eu1
  obtain ⟨l2, rfl⟩ := evalExpr_var_inv eu2
  obtain ⟨l3, rfl⟩ := evalExpr_var_inv eu3
  obtain ⟨l4, rfl⟩ := evalExpr_var_inv eu4
  obtain ⟨l5, rfl⟩ := evalExpr_var_inv eu5
  obtain ⟨l6, rfl⟩ := evalExpr_var_inv eu6
  obtain ⟨l7, rfl⟩ := evalExpr_var_inv eu7
  simp at l0 l1 l2 l3 l4 l5 l6 l7
  subst l0 l1 l2 l3 l4 l5 l6 l7
  obtain ⟨v1, vc8, _, evone, evc8, hsubb⟩ := evalExpr_binary_inv evbor
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evone
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib (by simp; rfl) evc8
  simp only [evalBinOp, Except.ok.injEq] at hsubb; subst hsubb
  obtain ⟨hmod, hbor⟩ := U64.sub_with_borrow_sound (F := F)
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 he0 he1 he2 he3 he4 he5 he6 he7
  refine ⟨_, ⟨s0, s1, s2, s3, s4, s5, s6, s7, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7,
    hmod.symm, rfl⟩, ?_, rfl⟩
  rw [hbor]

theorem u64_mul_column_spec (fc : FieldCompatible F) {val : Nat} (hval : val < U64.fieldBound)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt64::mul_column" [.field (val : F)] h r h') :
    ∃ r0 r1 c0 c1 c2 : Nat,
      r0 < 256 ∧ r1 < 256 ∧ c0 < 256 ∧ c1 < 256 ∧ c2 < 256 ∧
      val = U64.limb2 r0 r1 + 65536 * U64.carry3 c0 c1 c2 ∧
      r = .tuple [.tuple [.field (r0 : F), .field (r1 : F)],
                  .tuple [.field (c0 : F), .field (c1 : F), .field (c2 : F)]] ∧
      h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv lib.u64_mul_column (by rfl) ev
  obtain ⟨bytesv, _, evhint, r0⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evx⟩ := evalExpr_hint_inv evhint
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
  obtain ⟨r0v, r1v, _, evr01, r1⟩ := evalExpr_let_tuple2_inv r0
  obtain ⟨_, _, _, _, ei0, ei1, c01⟩ := evalExpr_call2_inv evr01
  obtain ⟨_, evb0, _⟩ := evalExpr_index_inv ei0
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evb0
  obtain ⟨_, evb1, _⟩ := evalExpr_index_inv ei1
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evb1
  obtain ⟨heq01, rfl, r0n, r1n, hr0, hr1, hr0Eq, hr1Eq⟩ := u8_from_fields_spec lib c01
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq01
  obtain ⟨rfl, rfl⟩ := heq01
  subst hr0Eq hr1Eq
  obtain ⟨c0v, c1v, _, evc01, r2⟩ := evalExpr_let_tuple2_inv r1
  obtain ⟨_, _, _, _, ei2, ei3, c23⟩ := evalExpr_call2_inv evc01
  obtain ⟨_, evb2, _⟩ := evalExpr_index_inv ei2
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evb2
  obtain ⟨_, evb3, _⟩ := evalExpr_index_inv ei3
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evb3
  obtain ⟨heq23, rfl, c0n, c1n, hc0, hc1, hc0Eq, hc1Eq⟩ := u8_from_fields_spec lib c23
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq23
  obtain ⟨rfl, rfl⟩ := heq23
  subst hc0Eq hc1Eq
  obtain ⟨c2v, _, _, evc2, r3⟩ := evalExpr_let_tuple2_wild_inv r2
  obtain ⟨_, _, _, _, ei4, el0, c4⟩ := evalExpr_call2_inv evc2
  obtain ⟨_, evb4, _⟩ := evalExpr_index_inv ei4
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evb4
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el0
  obtain ⟨heq4, rfl, c2n, _, hc2, _, hc2Eq, _⟩ := u8_from_fields_spec lib c4
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4
  obtain ⟨rfl, rfl⟩ := heq4
  subst hc2Eq
  obtain ⟨_, _, hass, evret⟩ := evalExpr_let_wildcard_inv r3
  obtain ⟨vl, vr, _, evxl, evrhs, heqval, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evxl
  simp at hlx; subst hlx
  obtain ⟨vlo, vhi, _, evlo, evhi, haddOut⟩ := evalExpr_binary_inv evrhs
  obtain ⟨vr0, vr1, _, evr0, evr1, haddLo⟩ := evalExpr_binary_inv evlo
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib (by simp; rfl) evr0
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evr1
  simp only [evalBinOp, Except.ok.injEq] at haddLo; subst haddLo
  obtain ⟨v65536, vcarry, _, ev65536, evcarry, hmulHi⟩ := evalExpr_binary_inv evhi
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev65536
  obtain ⟨vc01, vc2t, _, evc01', evc2t, haddCarry⟩ := evalExpr_binary_inv evcarry
  obtain ⟨vc0', vc1', _, evc0', evc1', haddC01⟩ := evalExpr_binary_inv evc01'
  obtain ⟨rfl, rfl⟩ := eval_u8f_var lib (by simp; rfl) evc0'
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evc1'
  simp only [evalBinOp, Except.ok.injEq] at haddC01; subst haddC01
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_var lib (by simp; rfl) evc2t
  simp only [evalBinOp, Except.ok.injEq] at haddCarry; subst haddCarry
  simp only [evalBinOp, Except.ok.injEq] at hmulHi; subst hmulHi
  simp only [evalBinOp, Except.ok.injEq] at haddOut; subst haddOut
  have heqF : (val : F) = (r0n : F) + 256 * (r1n : F) +
      65536 * ((c0n : F) + 256 * (c1n : F) + 65536 * (c2n : F)) := Value.field.inj heqval
  obtain ⟨hlift, _, _⟩ := U64.mul_column_sound fc.u64 hval hr0 hr1 hc0 hc1 hc2 heqF
  obtain ⟨va, vb, _, eva, evb, rfl⟩ := evalExpr_tuple2_inv evret
  obtain ⟨a0', a1', _, ea0', ea1', rfl⟩ := evalExpr_array2_inv eva
  obtain ⟨la0', rfl⟩ := evalExpr_var_inv ea0'
  obtain ⟨la1', rfl⟩ := evalExpr_var_inv ea1'
  simp at la0' la1'; subst la0' la1'
  obtain ⟨b0', b1', b2', _, _, eb0', eb1', eb2', rfl⟩ := evalExpr_array3_inv evb
  obtain ⟨lb0', rfl⟩ := evalExpr_var_inv eb0'
  obtain ⟨lb1', rfl⟩ := evalExpr_var_inv eb1'
  obtain ⟨lb2', rfl⟩ := evalExpr_var_inv eb2'
  simp at lb0' lb1' lb2'; subst lb0' lb1' lb2'
  exact ⟨r0n, r1n, c0n, c1n, c2n, hr0, hr1, hc0, hc1, hc2, hlift, rfl, rfl⟩

private theorem eval_limbExpr {locals : Environment F Nat} {v : String}
    {vs : List (SourceValue F)} {i j xi xj : Nat} {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == v) = some (v, .tuple vs))
    (hi : vs[i]? = some (.field (xi : F))) (hj : vs[j]? = some (.field (xj : F)))
    (ev : EvalExpr world [] locals (limbExpr v i j) h r h') :
    r = .field ((U64.limb2 xi xj : Nat) : F) ∧ h' = h := by
  obtain ⟨vl, vr, _, evl, evr, hadd⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib hlook hi evl
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_idx lib hlook hj evr
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  exact ⟨by unfold U64.limb2; push_cast; rfl, rfl⟩

omit lib in
private theorem eval_mul_vars {locals : Environment F Nat} {x y : String} {nx ny : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (hx : locals.find? (·.1 == x) = some (x, .field (nx : F)))
    (hy : locals.find? (·.1 == y) = some (y, .field (ny : F)))
    (ev : EvalExpr world [] locals (.binary .mul (.var x) (.var y)) h r h') :
    r = .field ((nx * ny : Nat) : F) ∧ h' = h := by
  obtain ⟨vl, vr, _, evl, evr, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv evl
  obtain ⟨hr, rfl⟩ := evalExpr_var_inv evr
  rw [hx, Option.some.injEq, Prod.mk.injEq] at hl
  rw [hy, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨_, rfl⟩ := hl
  obtain ⟨_, rfl⟩ := hr
  simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
  exact ⟨by push_cast; rfl, rfl⟩

private theorem eval_addCarryExpr {locals : Environment F Nat} {base : Aiur.Generic.Expr F}
    {nb : Nat} {c : String} {c0 c1 c2 : Nat} {h h' : Heap F} {r : SourceValue F}
    (hc : locals.find? (·.1 == c) = some (c, .tuple [.field (c0 : F), .field (c1 : F), .field (c2 : F)]))
    (hbase : ∀ h1 h2 r1, EvalExpr world [] locals base h1 r1 h2 →
      r1 = .field (nb : F) ∧ h2 = h1)
    (ev : EvalExpr world [] locals (addCarryExpr base c) h r h') :
    r = .field ((nb + U64.carry3 c0 c1 c2 : Nat) : F) ∧ h' = h := by
  obtain ⟨vl1, vr1, _, evl1, evr1, hadd1⟩ := evalExpr_binary_inv ev
  obtain ⟨vl2, vr2, _, evl2, evr2, hadd2⟩ := evalExpr_binary_inv evl1
  obtain ⟨vl3, vr3, _, evl3, evr3, hadd3⟩ := evalExpr_binary_inv evl2
  obtain ⟨rfl, rfl⟩ := hbase _ _ _ evl3
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib hc (by simp; rfl) evr3
  simp only [evalBinOp, Except.ok.injEq] at hadd3; subst hadd3
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_idx lib hc (by simp; rfl) evr2
  simp only [evalBinOp, Except.ok.injEq] at hadd2; subst hadd2
  obtain ⟨rfl, rfl⟩ := eval_mul_u8f_idx lib hc (by simp; rfl) evr1
  simp only [evalBinOp, Except.ok.injEq] at hadd1; subst hadd1
  exact ⟨by unfold U64.carry3; push_cast; ring_nf, rfl⟩

omit lib in
private theorem eval_idx_var {locals : Environment F Nat} {nm : String}
    {vs : List (SourceValue F)} {idx : Nat} {v : SourceValue F}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .tuple vs))
    (hidx : vs[idx]? = some v)
    (ev : EvalExpr world [] locals (.index (.var nm) idx) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨vt, evt, hproj⟩ := evalExpr_index_inv ev
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv evt
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, rfl⟩ := hl
  simp only [projectValue, hidx, pure, Except.pure, Except.ok.injEq] at hproj
  exact ⟨hproj.symm, rfl⟩

omit [DecidableEq F] lib in
private theorem isPlainExpr_u64MulBody : isPlainExpr (u64MulBody (F := F)) = true := by
  simp [u64MulBody, limbExpr, addCarryExpr, u8f, isPlainExpr, isPlainList]

private theorem eval_mul_col_step (fc : FieldCompatible F) {locals : Environment F Nat}
    {rName cName : String} {argExpr rest : Aiur.Generic.Expr F} {val : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals
      (.letValue (.tuple [.bind rName, .bind cName])
        (.call "UInt64::mul_column" (some []) [argExpr]) rest) h r h')
    (harg : ∀ h1 h2 v, EvalExpr world [] locals argExpr h1 v h2 → v = .field (val : F) ∧ h2 = h1)
    (hval : val < U64.fieldBound) :
    ∃ r0 r1 c0 c1 c2 : Nat,
      r0 < 256 ∧ r1 < 256 ∧ c0 < 256 ∧ c1 < 256 ∧ c2 < 256 ∧
      val = U64.limb2 r0 r1 + 65536 * U64.carry3 c0 c1 c2 ∧
      EvalExpr world []
        ((rName, .tuple [.field (r0 : F), .field (r1 : F)]) ::
         (cName, .tuple [.field (c0 : F), .field (c1 : F), .field (c2 : F)]) :: locals)
        rest h r h' := by
  obtain ⟨vr, vc, _, evcol, k⟩ := evalExpr_let_tuple2_inv ev
  obtain ⟨varg, _, evarg, ccol⟩ := evalExpr_call1_inv evcol
  obtain ⟨rfl, rfl⟩ := harg _ _ _ evarg
  obtain ⟨r0, r1, c0, c1, c2, hr0, hr1, hc0, hc1, hc2, hcol, heq, rfl⟩ :=
    u64_mul_column_spec lib fc hval ccol
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨r0, r1, c0, c1, c2, hr0, hr1, hc0, hc1, hc2, hcol, k⟩

private theorem eval_mul_limb_step {locals : Environment F Nat}
    {nm v : String} {vs : List (SourceValue F)} {i j xi xj : Nat}
    {rest : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == v) = some (v, .tuple vs))
    (hi : vs[i]? = some (.field (xi : F))) (hj : vs[j]? = some (.field (xj : F)))
    (ev : EvalExpr world [] locals (.letValue (.bind nm) (limbExpr v i j) rest) h r h') :
    EvalExpr world [] ((nm, .field ((U64.limb2 xi xj : Nat) : F)) :: locals) rest h r h' := by
  obtain ⟨vl, _, evl, k⟩ := evalExpr_let_bind_inv ev
  obtain ⟨rfl, rfl⟩ := eval_limbExpr lib hlook hi hj evl
  exact k

private theorem eval_mul_finish (fc : FieldCompatible F) {locals : Environment F Nat}
    {r00 r01 r10 r11 r20 r21 r30 r31 r40 r41 r50 r51 r60 r61 c60 c61 c62 : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (hc62 : c62 < 256)
    (hr0 : locals.find? (·.1 == "r0") = some ("r0", .tuple [.field (r00 : F), .field (r01 : F)]))
    (hr1 : locals.find? (·.1 == "r1") = some ("r1", .tuple [.field (r10 : F), .field (r11 : F)]))
    (hr2 : locals.find? (·.1 == "r2") = some ("r2", .tuple [.field (r20 : F), .field (r21 : F)]))
    (hr3 : locals.find? (·.1 == "r3") = some ("r3", .tuple [.field (r30 : F), .field (r31 : F)]))
    (hr4 : locals.find? (·.1 == "r4") = some ("r4", .tuple [.field (r40 : F), .field (r41 : F)]))
    (hr5 : locals.find? (·.1 == "r5") = some ("r5", .tuple [.field (r50 : F), .field (r51 : F)]))
    (hr6 : locals.find? (·.1 == "r6") = some ("r6", .tuple [.field (r60 : F), .field (r61 : F)]))
    (hc6 : locals.find? (·.1 == "c6") =
      some ("c6", .tuple [.field (c60 : F), .field (c61 : F), .field (c62 : F)]))
    (ev : EvalExpr world [] locals
      (.letValue .wildcard
        (.builtin (.assertEq { message := some "mul: final carry exceeds one radix digit",
                               runtimeCheck := true })
          [u8f (.index (.var "c6") 2), .literal (0 : F)])
        (.tuple
          [.array [.index (.var "r0") 0, .index (.var "r0") 1,
                   .index (.var "r1") 0, .index (.var "r1") 1,
                   .index (.var "r2") 0, .index (.var "r2") 1,
                   .index (.var "r3") 0, .index (.var "r3") 1],
           .array [.index (.var "r4") 0, .index (.var "r4") 1,
                   .index (.var "r5") 0, .index (.var "r5") 1,
                   .index (.var "r6") 0, .index (.var "r6") 1,
                   .index (.var "c6") 0, .index (.var "c6") 1]])) h r h') :
    c62 = 0 ∧
    r = .tuple
      [.tuple [.field (r00 : F), .field (r01 : F), .field (r10 : F), .field (r11 : F),
               .field (r20 : F), .field (r21 : F), .field (r30 : F), .field (r31 : F)],
       .tuple [.field (r40 : F), .field (r41 : F), .field (r50 : F), .field (r51 : F),
               .field (r60 : F), .field (r61 : F), .field (c60 : F), .field (c61 : F)]] ∧
    h' = h := by
  obtain ⟨_, _, hass, evret⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨vl, vr, _, evc62, ev0, hc62Eq, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨rfl, rfl⟩ := eval_u8f_idx lib hc6 (by simp; rfl) evc62
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
  have hc62Zero : c62 = 0 :=
    (U64.byte_eq_zero_iff fc.u64 hc62).mp (Value.field.inj hc62Eq)
  obtain ⟨vlo, vhi, _, evlo, evhi, rfl⟩ := evalExpr_tuple2_inv evret
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    el0, el1, el2, el3, el4, el5, el6, el7, rfl⟩ := evalExpr_array8_inv evlo
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr0 (by simp; rfl) el0
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr0 (by simp; rfl) el1
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr1 (by simp; rfl) el2
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr1 (by simp; rfl) el3
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr2 (by simp; rfl) el4
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr2 (by simp; rfl) el5
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr3 (by simp; rfl) el6
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr3 (by simp; rfl) el7
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    eh0, eh1, eh2, eh3, eh4, eh5, eh6, eh7, rfl⟩ := evalExpr_array8_inv evhi
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr4 (by simp; rfl) eh0
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr4 (by simp; rfl) eh1
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr5 (by simp; rfl) eh2
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr5 (by simp; rfl) eh3
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr6 (by simp; rfl) eh4
  obtain ⟨rfl, rfl⟩ := eval_idx_var hr6 (by simp; rfl) eh5
  obtain ⟨rfl, rfl⟩ := eval_idx_var hc6 (by simp; rfl) eh6
  obtain ⟨rfl, rfl⟩ := eval_idx_var hc6 (by simp; rfl) eh7
  exact ⟨hc62Zero, rfl, rfl⟩

omit [Field F] [DecidableEq F] lib in
private theorem limb_mul_lt {x y : Nat} (hx : x < 65536) (hy : y < 65536) :
    x * y < 65536 * 65536 := by
  calc x * y < 65536 * (y + 1) :=
      Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_succ y) (Nat.succ_pos y)
    _ ≤ 65536 * 65536 := Nat.mul_le_mul_left 65536 hy

theorem u64_mul_spec (fc : FieldCompatible F) {a b : Nat} {wa wb r : SourceValue F}
    {h h' : Heap F} (hwa : isU64Val a wa) (hwb : isU64Val b wb)
    (ev : EvalFn world "UInt64::mul" [wa, wb] h r h') :
    ∃ wlo whi, isU64Val ((a * b) % U64.base) wlo ∧ isU64Val ((a * b) / U64.base) whi ∧
      r = .tuple [wlo, whi] ∧ h' = h := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, rfl, rfl⟩ := hwa
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, rfl, rfl⟩ := hwb
  obtain ⟨_, k0⟩ := evalFn_plain_inv lib.u64_mul isPlainExpr_u64MulBody ev
  clear ev
  -- 8 limb bindings
  have k1 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k0; clear k0
  have k2 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k1; clear k1
  have k3 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k2; clear k2
  have k4 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k3; clear k3
  have k5 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k4; clear k4
  have k6 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k5; clear k5
  have k7 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k6; clear k6
  have k8 := eval_mul_limb_step lib (by simp; rfl) (by simp; rfl) (by simp; rfl) k7; clear k7
  have hL0 := U64.limb2_lt ha0 ha1; have hM0 := U64.limb2_lt hb0 hb1
  have hL1 := U64.limb2_lt ha2 ha3; have hM1 := U64.limb2_lt hb2 hb3
  have hL2 := U64.limb2_lt ha4 ha5; have hM2 := U64.limb2_lt hb4 hb5
  have hL3 := U64.limb2_lt ha6 ha7; have hM3 := U64.limb2_lt hb6 hb7
  -- Column 0
  obtain ⟨r00, r01, c00, c01, c02, hr00, hr01, hc00, hc01, hc02, col0, k9⟩ :=
    eval_mul_col_step lib fc k8
      (fun _ _ _ e => eval_mul_vars (by simp; rfl) (by simp; rfl) e)
      (by have := limb_mul_lt hL0 hM0; unfold U64.fieldBound; omega)
  clear k8
  have hC0 := U64.carry3_lt hc00 hc01 hc02
  -- Column 1
  obtain ⟨r10, r11, c10, c11, c12, hr10, hr11, hc10, hc11, hc12, col1, k10⟩ :=
    eval_mul_col_step lib fc k9
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' => by
        obtain ⟨v1, v2, _, e1, e2, ho⟩ := evalExpr_binary_inv e'
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e2
        simp only [evalBinOp, Except.ok.injEq] at ho; subst ho
        exact ⟨by rw [← Nat.cast_add], rfl⟩) e)
      (by have := limb_mul_lt hL0 hM1; have := limb_mul_lt hL1 hM0; unfold U64.fieldBound; omega)
  clear k9
  have hC1 := U64.carry3_lt hc10 hc11 hc12
  -- Column 2
  obtain ⟨r20, r21, c20, c21, c22, hr20, hr21, hc20, hc21, hc22, col2, k11⟩ :=
    eval_mul_col_step lib fc k10
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' => by
        obtain ⟨v12, v3, _, e12, e3, ho2⟩ := evalExpr_binary_inv e'
        obtain ⟨v1, v2, _, e1, e2, ho1⟩ := evalExpr_binary_inv e12
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e2
        simp only [evalBinOp, Except.ok.injEq] at ho1; subst ho1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e3
        simp only [evalBinOp, Except.ok.injEq] at ho2; subst ho2
        exact ⟨by rw [← Nat.cast_add, ← Nat.cast_add], rfl⟩) e)
      (by have := limb_mul_lt hL0 hM2; have := limb_mul_lt hL1 hM1; have := limb_mul_lt hL2 hM0
          unfold U64.fieldBound; omega)
  clear k10
  have hC2 := U64.carry3_lt hc20 hc21 hc22
  -- Column 3
  obtain ⟨r30, r31, c30, c31, c32, hr30, hr31, hc30, hc31, hc32, col3, k12⟩ :=
    eval_mul_col_step lib fc k11
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' => by
        obtain ⟨v123, v4, _, e123, e4, ho3⟩ := evalExpr_binary_inv e'
        obtain ⟨v12, v3, _, e12, e3, ho2⟩ := evalExpr_binary_inv e123
        obtain ⟨v1, v2, _, e1, e2, ho1⟩ := evalExpr_binary_inv e12
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e2
        simp only [evalBinOp, Except.ok.injEq] at ho1; subst ho1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e3
        simp only [evalBinOp, Except.ok.injEq] at ho2; subst ho2
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e4
        simp only [evalBinOp, Except.ok.injEq] at ho3; subst ho3
        exact ⟨by rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add], rfl⟩) e)
      (by have := limb_mul_lt hL0 hM3; have := limb_mul_lt hL1 hM2
          have := limb_mul_lt hL2 hM1; have := limb_mul_lt hL3 hM0
          unfold U64.fieldBound; omega)
  clear k11
  have hC3 := U64.carry3_lt hc30 hc31 hc32
  -- Column 4
  obtain ⟨r40, r41, c40, c41, c42, hr40, hr41, hc40, hc41, hc42, col4, k13⟩ :=
    eval_mul_col_step lib fc k12
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' => by
        obtain ⟨v12, v3, _, e12, e3, ho2⟩ := evalExpr_binary_inv e'
        obtain ⟨v1, v2, _, e1, e2, ho1⟩ := evalExpr_binary_inv e12
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e2
        simp only [evalBinOp, Except.ok.injEq] at ho1; subst ho1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e3
        simp only [evalBinOp, Except.ok.injEq] at ho2; subst ho2
        exact ⟨by rw [← Nat.cast_add, ← Nat.cast_add], rfl⟩) e)
      (by have := limb_mul_lt hL1 hM3; have := limb_mul_lt hL2 hM2; have := limb_mul_lt hL3 hM1
          unfold U64.fieldBound; omega)
  clear k12
  have hC4 := U64.carry3_lt hc40 hc41 hc42
  -- Column 5
  obtain ⟨r50, r51, c50, c51, c52, hr50, hr51, hc50, hc51, hc52, col5, k14⟩ :=
    eval_mul_col_step lib fc k13
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' => by
        obtain ⟨v1, v2, _, e1, e2, ho⟩ := evalExpr_binary_inv e'
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := eval_mul_vars (by simp; rfl) (by simp; rfl) e2
        simp only [evalBinOp, Except.ok.injEq] at ho; subst ho
        exact ⟨by rw [← Nat.cast_add], rfl⟩) e)
      (by have := limb_mul_lt hL2 hM3; have := limb_mul_lt hL3 hM2; unfold U64.fieldBound; omega)
  clear k13
  have hC5 := U64.carry3_lt hc50 hc51 hc52
  -- Column 6
  obtain ⟨r60, r61, c60, c61, c62, hr60, hr61, hc60, hc61, hc62, col6, k15⟩ :=
    eval_mul_col_step lib fc k14
      (fun _ _ _ e => eval_addCarryExpr lib (by simp; exact ⟨rfl, rfl, rfl⟩) (fun _ _ _ e' =>
        eval_mul_vars (by simp; rfl) (by simp; rfl) e') e)
      (by have := limb_mul_lt hL3 hM3; unfold U64.fieldBound; omega)
  clear k14
  -- Final carry assertion & tuple `(lo, hi)`
  obtain ⟨hc62Zero, rfl, rfl⟩ := eval_mul_finish lib fc hc62
    (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩)
    (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩)
    (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) k15
  obtain ⟨_, hlo, hhi, _⟩ := U64.mul_sound
    hr00 hr01 hr10 hr11 hr20 hr21 hr30 hr31 hr40 hr41 hr50 hr51 hr60 hr61 hc60 hc61
    col0 col1 col2 col3 col4 col5 col6 hc62Zero
  exact ⟨_, _,
    ⟨r00, r01, r10, r11, r20, r21, r30, r31, hr00, hr01, hr10, hr11, hr20, hr21, hr30, hr31,
      hlo.symm, rfl⟩,
    ⟨r40, r41, r50, r51, r60, r61, c60, c61, hr40, hr41, hr50, hr51, hr60, hr61, hc60, hc61,
      hhi.symm, rfl⟩,
    rfl, rfl⟩

omit lib in
/-- Shared proof template for `UInt64::{and, or, xor}`. -/
private theorem u64_bitwise_spec {fnName opName : String} {op : Nat → Nat → Nat}
    (hfn : WorldHasFn world fnName ["a", "b"] (u64BitwiseBody opName))
    (hopSpec : ∀ x y : Nat, ∀ h r h', x < 256 → y < 256 →
      EvalFn world opName [.field (x : F), .field (y : F)] h r h' →
      r = .field ((op x y : Nat) : F) ∧ h' = h)
    (hopLt : ∀ x y, x < 256 → y < 256 → op x y < 256)
    (hopPack : ∀ a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7,
      a0 < 256 → a1 < 256 → a2 < 256 → a3 < 256 →
      a4 < 256 → a5 < 256 → a6 < 256 → a7 < 256 →
      b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 →
      b4 < 256 → b5 < 256 → b6 < 256 → b7 < 256 →
      U64.pack (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3)
        (op a4 b4) (op a5 b5) (op a6 b6) (op a7 b7) =
        op (U64.pack a0 a1 a2 a3 a4 a5 a6 a7) (U64.pack b0 b1 b2 b3 b4 b5 b6 b7))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU64Val a wa) (hwb : isU64Val b wb)
    (ev : EvalFn world fnName [wa, wb] h r h') :
    isU64Val (op a b) r ∧ h' = h := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, rfl, rfl⟩ := hwa
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, rfl, rfl⟩ := hwb
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn (by simp [u64BitwiseBody, isPlainExpr, isPlainList]) ev
  obtain ⟨_, _, _, _, _, _, _, _, _, eva, r1⟩ := evalExpr_let_array8_inv body
  obtain ⟨la, rfl⟩ := evalExpr_var_inv eva
  simp only [List.zip_cons_cons, List.zip_nil_right, List.find?_cons, beq_self_eq_true,
    Option.some.injEq, Prod.mk.injEq, true_and, Value.tuple.injEq, List.cons.injEq, and_true] at la
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := la
  obtain ⟨_, _, _, _, _, _, _, _, _, evb, r2⟩ := evalExpr_let_array8_inv r1
  obtain ⟨lb, rfl⟩ := evalExpr_var_inv evb
  simp at lb
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := lb
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, _, _, _, _, _, _, _,
    e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩ := evalExpr_array8_inv r2
  have step : ∀ {x y : String} {nx ny : Nat} {h1 h2 : Heap F} {v : SourceValue F}
      {locs : Environment F Nat},
      locs.find? (·.1 == x) = some (x, .field (nx : F)) →
      locs.find? (·.1 == y) = some (y, .field (ny : F)) →
      nx < 256 → ny < 256 →
      EvalExpr world [] locs (.call opName (some []) [.var x, .var y]) h1 v h2 →
      v = .field ((op nx ny : Nat) : F) ∧ h2 = h1 := by
    intro x y nx ny h1 h2 v locs hx hy hnx hny evc
    obtain ⟨vx, vy, _, _, evx, evy, hcal⟩ := evalExpr_call2_inv evc
    obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨hly, rfl⟩ := evalExpr_var_inv evy
    rw [hx, Option.some.injEq, Prod.mk.injEq] at hlx
    rw [hy, Option.some.injEq, Prod.mk.injEq] at hly
    obtain ⟨_, rfl⟩ := hlx
    obtain ⟨_, rfl⟩ := hly
    exact hopSpec nx ny _ _ _ hnx hny hcal
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha0 hb0 e0
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha1 hb1 e1
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha2 hb2 e2
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha3 hb3 e3
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha4 hb4 e4
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha5 hb5 e5
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha6 hb6 e6
  obtain ⟨rfl, rfl⟩ := step (by simp) (by simp) ha7 hb7 e7
  exact ⟨⟨op a0 b0, op a1 b1, op a2 b2, op a3 b3, op a4 b4, op a5 b5, op a6 b6, op a7 b7,
    hopLt _ _ ha0 hb0, hopLt _ _ ha1 hb1, hopLt _ _ ha2 hb2, hopLt _ _ ha3 hb3,
    hopLt _ _ ha4 hb4, hopLt _ _ ha5 hb5, hopLt _ _ ha6 hb6, hopLt _ _ ha7 hb7,
    (hopPack a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7).symm, rfl⟩, rfl⟩

/-- **Complete `UInt64` Library Contracts**, proved directly over `EvalFn`. -/
theorem U64Contracts.ofLibraryWorld (fc : FieldCompatible F) : U64Contracts world where
  to_field _ _ _ _ _ hw ev := u64_to_field_spec lib fc hw ev
  from_field _ _ _ _ ev := u64_from_field_spec lib fc ev
  is_zero _ _ _ _ _ hw ev := u64_is_zero_spec lib fc hw ev
  sub_with_borrow _ _ _ _ _ _ _ hwa hwb ev := u64_sub_with_borrow_spec lib fc hwa hwb ev
  mul _ _ _ _ _ _ _ hwa hwb ev := u64_mul_spec lib fc hwa hwb ev
  and _ _ _ _ _ _ _ hwa hwb ev :=
    u64_bitwise_spec (op := Nat.land) lib.u64_and
      (fun _ _ _ _ _ hx hy e => u8_and_spec lib fc hx hy e)
      (fun _ _ hx hy => U64.bitwise_lt_two_pow rfl 8 hx hy)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
           hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 =>
        (U64.and_sound fc.u64 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
          hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7).2)
      hwa hwb ev
  or _ _ _ _ _ _ _ hwa hwb ev :=
    u64_bitwise_spec (op := Nat.lor) lib.u64_or
      (fun _ _ _ _ _ hx hy e => u8_or_spec lib fc hx hy e)
      (fun _ _ hx hy => U64.bitwise_lt_two_pow rfl 8 hx hy)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
           hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 =>
        (U64.or_sound fc.u64 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
          hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7).2)
      hwa hwb ev
  xor _ _ _ _ _ _ _ hwa hwb ev :=
    u64_bitwise_spec (op := Nat.xor) lib.u64_xor
      (fun _ _ _ _ _ hx hy e => u8_xor_spec lib fc hx hy e)
      (fun _ _ hx hy => U8Facts.xor_lt_256 hx hy)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
           hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 =>
        U64.xor_sound ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
      hwa hwb ev

end U64Proofs

end U64Library

/-! ## Lowered `Prog::p_*` Primitive Helper Contracts -/

section PrimHelpers

variable {F : Type} [Field F] [DecidableEq F]

/-- Representation of a small `Nat` in `Prog::Obj`. -/
def natV (e : String) (n : Nat) : SourceValue F :=
  .construct e "N" [.field (n : F)]

/-- World hypothesis for the lowered `Prog::` primitive helpers. -/
structure PrimHelpersWorld (P : Fir.Program) (world : World F) : Prop where
  u64 : U64Contracts world
  p_add : WorldHasFn world (qualified "p_add") ["a", "b"] (qualifyExprF F pAdd.body)
  p_sub : WorldHasFn world (qualified "p_sub") ["a", "b"] (qualifyExprF F pSub.body)
  p_mul : WorldHasFn world (qualified "p_mul") ["a", "b"] (qualifyExprF F pMul.body)
  divmod : WorldHasFn world (qualified "divmod") ["x", "y"] (qualifyExprF F divmod.body)
  p_div : WorldHasFn world (qualified "p_div") ["a", "b"] (qualifyExprF F pDiv.body)
  p_mod : WorldHasFn world (qualified "p_mod") ["a", "b"] (qualifyExprF F pMod.body)
  p_pred : WorldHasFn world (qualified "p_pred") ["a"] (qualifyExprF F pPred.body)
  p_land : WorldHasFn world (qualified "p_land") ["a", "b"]
    (qualifyExprF F (pBitwise "p_land" "UInt64::and").body)
  p_lor : WorldHasFn world (qualified "p_lor") ["a", "b"]
    (qualifyExprF F (pBitwise "p_lor" "UInt64::or").body)
  p_xor : WorldHasFn world (qualified "p_xor") ["a", "b"]
    (qualifyExprF F (pBitwise "p_xor" "UInt64::xor").body)
  p_bool : ∀ tt ff, (Cx.mk P).boolNames = some (tt, ff) →
    WorldHasFn world (qualified "p_beq") ["a", "b"] (qualifyExprF F (pBeq tt ff).body) ∧
    WorldHasFn world (qualified "p_ble") ["a", "b"] (qualifyExprF F (pBle tt ff).body) ∧
    WorldHasFn world (qualified "p_blt") ["a", "b"] (qualifyExprF F (pBlt tt ff).body)

/-- Inverting `natPair body` over `EvalExpr`: BOTH arguments MUST be `Obj::N(_)`
(otherwise no derivation exists!), and `body` runs with `("x", vx) :: ("y", vy) :: locals`. -/
private theorem eval_natPair_inv {world : World F} {body : Lower.Expr}
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalExpr world [] [("a", wa), ("b", wb)] (qualifyExprF F (natPair body)) h r h') :
    ∃ x y : SourceValue F,
      wa = .construct objQName "N" [x] ∧
      wb = .construct objQName "N" [y] ∧
      EvalExpr world [] [("x", x), ("y", y), ("a", wa), ("b", wb)] (qualifyExprF F body) h r h' := by
  simp only [natPair, matchE, vE, pN, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy,
    objTy, qualifyName_obj, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
  cases ev with
  | matchValue evscrut hsel hbr =>
    obtain ⟨va, vb, _, eva, evb, rfl⟩ := evalExpr_tuple2_inv evscrut
    obtain ⟨la, rfl⟩ := evalExpr_var_inv eva
    obtain ⟨lb, rfl⟩ := evalExpr_var_inv evb
    simp at la lb; subst la lb
    cases wa with
    | construct ea ca psa =>
      by_cases hca : (ea != objQName || ca != "N" || (1 != psa.length)) = true
      · simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith,
          constructorName, Ty.toCore, Instance.symbol, hca] at hsel
      · have hca' : ea = objQName ∧ ca = "N" ∧ psa.length = 1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at hca
          exact ⟨hca.1.1, hca.1.2, hca.2.symm⟩
        obtain ⟨rfl, rfl, hlena⟩ := hca'
        rcases psa with _ | ⟨xa, _ | _⟩ <;> simp at hlena
        cases wb with
        | construct eb cb psb =>
          by_cases hcb : (eb != objQName || cb != "N" || (1 != psb.length)) = true
          · simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith,
              constructorName, Ty.toCore, Instance.symbol, hcb] at hsel
          · have hcb' : eb = objQName ∧ cb = "N" ∧ psb.length = 1 := by
              simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at hcb
              exact ⟨hcb.1.1, hcb.1.2, hcb.2.symm⟩
            obtain ⟨rfl, rfl, hlenb⟩ := hcb'
            rcases psb with _ | ⟨xb, _ | _⟩ <;> simp at hlenb
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith,
              constructorName, Ty.toCore, Instance.symbol] at hsel
            obtain ⟨rfl, rfl⟩ := hsel
            exact ⟨xa, xb, rfl, rfl, hbr⟩
        | field _ | tuple _ | ptr _ _ =>
          simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith,
            constructorName, Ty.toCore, Instance.symbol] at hsel
    | field _ | tuple _ | ptr _ _ =>
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith] at hsel

/-- Helper: inverting `wordE (vE nm)` with `U64Contracts` when `nm` holds `.field (x : F)` (`x < natLimit`). -/
private theorem eval_wordE_nat {world : World F} (fc : FieldCompatible F) (u64 : U64Contracts world)
    {locals : Environment F Nat} {nm : String} {x : Nat} (hx : x < natLimit)
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .field (x : F)))
    (ev : EvalExpr world [] locals (qualifyExprF F (wordE (vE nm))) h r h') :
    isU64Val x r ∧ h' = h := by
  simp only [wordE, callE, vE, qualifyExprF, qualifyExpr, qualifyName_u64_from_field,
    Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
  obtain ⟨va, _, eva, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv eva
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, rfl⟩ := hl
  obtain ⟨n, hn, heq, hu, rfl⟩ := u64.from_field _ _ _ _ hcal
  have hxn : x = n := fc.natCast_inj56 hx hn (Value.field.inj heq)
  subst hxn
  exact ⟨hu, rfl⟩

/-- Helper: inverting `wordE (vE nm)` for an arbitrary `SourceValue F`. -/
private theorem eval_wordE_any {world : World F} (u64 : U64Contracts world)
    {locals : Environment F Nat} {nm : String} {v : SourceValue F}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (qualifyExprF F (wordE (vE nm))) h r h') :
    ∃ n, n < natLimit ∧ v = .field (n : F) ∧ isU64Val n r ∧ h' = h := by
  simp only [wordE, callE, vE, qualifyExprF, qualifyExpr, qualifyName_u64_from_field,
    Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
  obtain ⟨va, _, eva, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv eva
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, rfl⟩ := hl
  exact u64.from_field _ _ _ _ hcal

/-- Helper: inverting `match (UInt64::sub_with_borrow(wordE a, wordE b)) { (_, 0) => e0, _ => e1 }`. -/
private theorem eval_sub_cmp_inv {world : World F} (fc : FieldCompatible F) (u64 : U64Contracts world)
    {locals : Environment F Nat} {na nb : String} {x y : Nat}
    (hx : x < natLimit) (hy : y < natLimit)
    (hlx : locals.find? (·.1 == na) = some (na, .field (x : F)))
    (hly : locals.find? (·.1 == nb) = some (nb, .field (y : F)))
    {e0 e1 : Lower.Expr} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals
      (qualifyExprF F (matchE (callE "UInt64::sub_with_borrow" [wordE (vE na), wordE (vE nb)])
        [(.tuple [.wildcard, .literal 0], e0), (.wildcard, e1)])) h r h') :
    (¬ x < y ∧ EvalExpr world [] locals (qualifyExprF F e0) h r h') ∨
    (x < y ∧ EvalExpr world [] locals (qualifyExprF F e1) h r h') := by
  simp only [matchE, callE, qualifyExprF, qualifyExpr, qualifyPat, qualifyName_u64_sub_with_borrow,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
  cases ev with
  | matchValue evscrut hsel hbr =>
    obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv evscrut
    obtain ⟨hwa, rfl⟩ := eval_wordE_nat fc u64 hx hlx eva
    obtain ⟨hwb, rfl⟩ := eval_wordE_nat fc u64 hy hly evb
    obtain ⟨wd, _, rfl, rfl⟩ := u64.sub_with_borrow _ _ _ _ _ _ _ hwa hwb hcal
    by_cases hlt : x < y
    · simp only [hlt, ↓reduceIte, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        matchListWith, Aiur.Pattern.bindings, Nat.cast_zero, zero_ne_one, List.length_cons,
        List.length_nil, bne_self_eq_false, Bool.false_eq_true, List.attach, List.attachWith,
        List.pmap, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact Or.inr ⟨hlt, hbr⟩
    · simp only [hlt, ↓reduceIte, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        matchListWith, Aiur.Pattern.bindings, Nat.cast_zero, List.length_cons, List.length_nil,
        bne_self_eq_false, Bool.false_eq_true, List.attach, List.attachWith, List.pmap, bind,
        Except.bind, pure, Except.pure, List.nil_append, Except.ok.injEq, Option.some.injEq,
        Prod.mk.injEq] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact Or.inl ⟨hlt, hbr⟩

/-! ### All 13 Lowered Primitive Helper Contracts -/

variable {P : Fir.Program} {world : World F}

theorem pAdd_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_add") [natV objQName x, natV objQName y] h r h') :
    x + y < natLimit ∧ r = natV objQName (x + y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_add
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pAdd (by simp [helpers])) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [letE, seqE, addE, natE, mk, vE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_obj, Option.map_some, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map] at hbody
  obtain ⟨vs, _, evadd, rest1⟩ := evalExpr_let_bind_inv hbody
  obtain ⟨v1, v2, _, ev1, ev2, hadd⟩ := evalExpr_binary_inv evadd
  obtain ⟨l1, rfl⟩ := evalExpr_var_inv ev1
  obtain ⟨l2, rfl⟩ := evalExpr_var_inv ev2
  simp at l1 l2; subst l1 l2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  obtain ⟨_, _, evw, evret⟩ := evalExpr_let_wildcard_inv rest1
  obtain ⟨n, hn, hcastEq, _, rfl⟩ := eval_wordE_any pw.u64 (by simp; rfl) evw
  have hsumEq : x + y = n := by
    apply fc.natCast_inj (by unfold natLimit at *; omega) (by unfold natLimit at *; omega)
    push_cast
    exact Value.field.inj hcastEq
  obtain ⟨vn, evvn, rfl⟩ := evalExpr_construct1_inv evret
  obtain ⟨ln, rfl⟩ := evalExpr_var_inv evvn
  simp at ln; subst ln
  refine ⟨by omega, ?_, rfl⟩
  simp [natV, objQName, qualified, moduleName, objName, Nat.cast_add]

theorem pAdd_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_add") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_add
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pAdd (by simp [helpers])) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pSub_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_sub") [natV objQName x, natV objQName y] h r h') :
    x - y < natLimit ∧ r = natV objQName (x - y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_sub
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pSub (by simp [helpers])) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  rcases eval_sub_cmp_inv fc pw.u64 hx hy (by simp) (by simp) hbody with ⟨hnlt, h0⟩ | ⟨hlt, h1⟩
  · simp only [natE, mk, subE, vE, qualifyExprF, qualifyExpr, qualifyName_obj,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at h0
    obtain ⟨vn, evsub, rfl⟩ := evalExpr_construct1_inv h0
    obtain ⟨v1, v2, _, ev1, ev2, hsub⟩ := evalExpr_binary_inv evsub
    obtain ⟨l1, rfl⟩ := evalExpr_var_inv ev1
    obtain ⟨l2, rfl⟩ := evalExpr_var_inv ev2
    simp at l1 l2; subst l1 l2
    simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
    refine ⟨by omega, ?_, rfl⟩
    simp [natV, objQName, qualified, moduleName, objName, Nat.cast_sub (Nat.le_of_not_lt hnlt)]
  · simp only [natE, mk, litE, qualifyExprF, qualifyExpr, qualifyName_obj,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at h1
    obtain ⟨vn, ev0, rfl⟩ := evalExpr_construct1_inv h1
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
    have hsub0 : x - y = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    exact ⟨by omega, by simp [hsub0, natV, objQName, qualified, moduleName, objName], rfl⟩

theorem pSub_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_sub") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_sub
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pSub (by simp [helpers])) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pMul_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_mul") [natV objQName x, natV objQName y] h r h') :
    x * y < natLimit ∧ r = natV objQName (x * y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_mul
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pMul (by simp [helpers])) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [matchE, callE, natE, mk, vE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_obj, qualifyName_u64_mul, qualifyName_u64_is_zero, qualifyName_u64_to_field,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at hbody
  cases hbody with
  | matchValue evmul hsel1 hbr1 =>
    obtain ⟨wx, wy, _, _, evwx, evwy, cmul⟩ := evalExpr_call2_inv evmul
    obtain ⟨hwx, rfl⟩ := eval_wordE_nat fc pw.u64 hx (by simp) evwx
    obtain ⟨hwy, rfl⟩ := eval_wordE_nat fc pw.u64 hy (by simp) evwy
    obtain ⟨wlo, whi, hwlo, hwhi, rfl, rfl⟩ := pw.u64.mul _ _ _ _ _ _ _ hwx hwy cmul
    simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith] at hsel1
    obtain ⟨rfl, rfl⟩ := hsel1
    cases hbr1 with
    | matchValue eviz hsel2 hbr2 =>
      obtain ⟨vhi, _, evhi, ciz⟩ := evalExpr_call1_inv eviz
      obtain ⟨lhi, rfl⟩ := evalExpr_var_inv evhi
      simp at lhi; subst lhi
      obtain ⟨rfl, rfl⟩ := pw.u64.is_zero _ _ _ _ _ hwhi ciz
      by_cases hhi0 : x * y / U64.base = 0
      · simp [hhi0, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        have hprodEq : (x * y) % U64.base = x * y := by
          have := Nat.div_add_mod (x * y) U64.base
          rw [hhi0, Nat.mul_zero, Nat.zero_add] at this
          exact this
        obtain ⟨vtf, evtf, rfl⟩ := evalExpr_construct1_inv hbr2
        obtain ⟨vlo, _, evlo, ctf⟩ := evalExpr_call1_inv evtf
        obtain ⟨llo, rfl⟩ := evalExpr_var_inv evlo
        simp at llo; subst llo
        obtain ⟨hlt, rfl, rfl⟩ := pw.u64.to_field _ _ _ _ _ hwlo ctf
        rw [hprodEq] at hlt ⊢
        exact ⟨hlt, by simp [natV, objQName, qualified, moduleName, objName], rfl⟩
      · simp [hhi0, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel2

theorem pMul_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_mul") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_mul
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pMul (by simp [helpers])) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem divmod_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit) (hy0 : y ≠ 0)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "divmod") [.field (x : F), .field (y : F)] h r h') :
    x / y < natLimit ∧ x % y < natLimit ∧
    r = .tuple [.field ((x / y : Nat) : F), .field ((x % y : Nat) : F)] ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.divmod
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ Lower.divmod (by simp [helpers])) ev
  simp only [Lower.divmod, letE, seqE, matchE, callE, addE, vE, qualifyExprF, qualifyExpr,
    qualifyPat, qualifyTy, qualifyName_u64_mul, qualifyName_u64_is_zero, qualifyName_u64_to_field,
    qualifyName_u64_sub_with_borrow, Option.map_some, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨vq, vr, _, evhint, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨_, evkey⟩ := evalExpr_hint_inv evhint
  obtain ⟨_, _, _, ekx, eky, _⟩ := evalExpr_tuple2_inv evkey
  obtain ⟨_, rfl⟩ := evalExpr_var_inv ekx
  obtain ⟨_, rfl⟩ := evalExpr_var_inv eky
  obtain ⟨vyw, _, evyw, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨hwy, rfl⟩ := eval_wordE_nat fc pw.u64 hy (by simp) evyw
  obtain ⟨vrw, _, evrw, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨rn, hrn, rfl, hwr, rfl⟩ := eval_wordE_any pw.u64 (by simp; rfl) evrw
  cases k3 with
  | matchValue evmul hsel1 hbr1 =>
    obtain ⟨vqw, vyw', _, _, evqw, evyw', cmul⟩ := evalExpr_call2_inv evmul
    obtain ⟨qn, hqn, rfl, hwq, rfl⟩ := eval_wordE_any pw.u64 (by simp; rfl) evqw
    obtain ⟨lyw, rfl⟩ := evalExpr_var_inv evyw'
    simp at lyw; subst lyw
    obtain ⟨wlo, whi, hwlo, hwhi, rfl, rfl⟩ := pw.u64.mul _ _ _ _ _ _ _ hwq hwy cmul
    simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith] at hsel1
    obtain ⟨rfl, rfl⟩ := hsel1
    cases hbr1 with
    | matchValue eviz hsel2 hbr2 =>
      obtain ⟨vhi, _, evhi, ciz⟩ := evalExpr_call1_inv eviz
      obtain ⟨lhi, rfl⟩ := evalExpr_var_inv evhi
      simp at lhi; subst lhi
      obtain ⟨rfl, rfl⟩ := pw.u64.is_zero _ _ _ _ _ hwhi ciz
      by_cases hhi0 : qn * y / U64.base = 0
      · simp [hhi0, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        have hprodEq : (qn * y) % U64.base = qn * y := by
          have := Nat.div_add_mod (qn * y) U64.base
          rw [hhi0, Nat.mul_zero, Nat.zero_add] at this
          exact this
        obtain ⟨vl, _, evtf, k4⟩ := evalExpr_let_bind_inv hbr2
        obtain ⟨vlo, _, evlo, ctf⟩ := evalExpr_call1_inv evtf
        obtain ⟨llo, rfl⟩ := evalExpr_var_inv evlo
        simp at llo; subst llo
        obtain ⟨hltProd, rfl, rfl⟩ := pw.u64.to_field _ _ _ _ _ hwlo ctf
        rw [hprodEq] at hltProd k4
        obtain ⟨_, _, hass, k5⟩ := evalExpr_let_wildcard_inv k4
        obtain ⟨vlhs, vrhs, _, evadd, evx, heqX, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨v1, v2, _, ev1, ev2, hadd⟩ := evalExpr_binary_inv evadd
        obtain ⟨l1, rfl⟩ := evalExpr_var_inv ev1
        obtain ⟨l2, rfl⟩ := evalExpr_var_inv ev2
        simp at l1 l2; subst l1 l2
        simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
        obtain ⟨lx, rfl⟩ := evalExpr_var_inv evx
        simp at lx; subst lx
        have heqNat : qn * y + rn = x := by
          apply fc.natCast_inj (by unfold natLimit at *; omega) (by unfold natLimit at *; omega)
          push_cast
          exact Value.field.inj heqX
        cases k5 with
        | matchValue evcmp hsel3 hbr3 =>
          obtain ⟨vrw', vyw'', _, _, evrw', evyw'', csub⟩ := evalExpr_call2_inv evcmp
          obtain ⟨lrw', rfl⟩ := evalExpr_var_inv evrw'
          obtain ⟨lyw'', rfl⟩ := evalExpr_var_inv evyw''
          simp at lrw' lyw''; subst lrw' lyw''
          obtain ⟨wd, _, rfl, rfl⟩ := pw.u64.sub_with_borrow _ _ _ _ _ _ _ hwr hwy csub
          by_cases hlt : rn < y
          · simp [hlt, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              matchListWith, Aiur.Pattern.bindings] at hsel3
            obtain ⟨rfl, rfl⟩ := hsel3
            obtain ⟨vq', vr', _, evq', evr', rfl⟩ := evalExpr_tuple2_inv hbr3
            obtain ⟨lq', rfl⟩ := evalExpr_var_inv evq'
            obtain ⟨lr', rfl⟩ := evalExpr_var_inv evr'
            simp at lq' lr'; subst lq' lr'
            have hqEq : qn = x / y := by
              rw [← heqNat, Nat.mul_comm qn y, Nat.mul_add_div (Nat.pos_of_ne_zero hy0),
                  Nat.div_eq_of_lt hlt, Nat.add_zero]
            have hrEq : rn = x % y := by
              rw [← heqNat, Nat.mul_comm qn y, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
            subst hqEq hrEq
            exact ⟨hqn, hrn, rfl, rfl⟩
          · simp [hlt, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              matchListWith, Aiur.Pattern.bindings] at hsel3
      · simp [hhi0, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel2

theorem pDiv_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_div") [natV objQName x, natV objQName y] h r h') :
    (if y == 0 then 0 else x / y) < natLimit ∧
    r = natV objQName (if y == 0 then 0 else x / y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_div
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pDiv (by simp [helpers])) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [matchE, callE, natE, mk, litE, vE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_obj, qualifyName_divmod, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at hbody
  cases hbody with
  | matchValue evy hsel1 hbr1 =>
    obtain ⟨ly, rfl⟩ := evalExpr_var_inv evy
    simp at ly; subst ly
    by_cases hy0 : y = 0
    · subst hy0
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel1
      obtain ⟨rfl, rfl⟩ := hsel1
      obtain ⟨v0, ev0, rfl⟩ := evalExpr_construct1_inv hbr1
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
      exact ⟨by simp [natLimit], by simp [natV, objQName, qualified, moduleName, objName], rfl⟩
    · have hyF : (0 : F) ≠ (y : F) :=
        Ne.symm (fc.ne_zero_of_pos (Nat.pos_of_ne_zero hy0) (lt_trans hy (by unfold natLimit; omega)))
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings, hyF] at hsel1
      obtain ⟨rfl, rfl⟩ := hsel1
      cases hbr1 with
      | matchValue evdm hsel2 hbr2 =>
        obtain ⟨vx', vy', _, _, evx', evy', cdm⟩ := evalExpr_call2_inv evdm
        obtain ⟨lx', rfl⟩ := evalExpr_var_inv evx'
        obtain ⟨ly', rfl⟩ := evalExpr_var_inv evy'
        simp at lx' ly'; subst lx' ly'
        obtain ⟨hqlt, _, rfl, rfl⟩ := divmod_sound fc pw hx hy hy0 cdm
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        obtain ⟨vq, evq, rfl⟩ := evalExpr_construct1_inv hbr2
        obtain ⟨lq, rfl⟩ := evalExpr_var_inv evq
        simp at lq; subst lq
        have hyb : (y == 0) = false := beq_false_of_ne hy0
        exact ⟨by simp [hyb, hqlt], by simp [hyb, natV, objQName, qualified, moduleName, objName], rfl⟩

theorem pDiv_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_div") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_div
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pDiv (by simp [helpers])) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pMod_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_mod") [natV objQName x, natV objQName y] h r h') :
    (if y == 0 then x else x % y) < natLimit ∧
    r = natV objQName (if y == 0 then x else x % y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_mod
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pMod (by simp [helpers])) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [matchE, callE, natE, mk, vE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_obj, qualifyName_divmod, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at hbody
  cases hbody with
  | matchValue evy hsel1 hbr1 =>
    obtain ⟨ly, rfl⟩ := evalExpr_var_inv evy
    simp at ly; subst ly
    by_cases hy0 : y = 0
    · subst hy0
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel1
      obtain ⟨rfl, rfl⟩ := hsel1
      obtain ⟨vx', evx', rfl⟩ := evalExpr_construct1_inv hbr1
      obtain ⟨lx', rfl⟩ := evalExpr_var_inv evx'
      simp at lx'; subst lx'
      exact ⟨by simpa using hx, by simp [natV, objQName, qualified, moduleName, objName], rfl⟩
    · have hyF : (0 : F) ≠ (y : F) :=
        Ne.symm (fc.ne_zero_of_pos (Nat.pos_of_ne_zero hy0) (lt_trans hy (by unfold natLimit; omega)))
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings, hyF] at hsel1
      obtain ⟨rfl, rfl⟩ := hsel1
      cases hbr1 with
      | matchValue evdm hsel2 hbr2 =>
        obtain ⟨vx', vy', _, _, evx', evy', cdm⟩ := evalExpr_call2_inv evdm
        obtain ⟨lx', rfl⟩ := evalExpr_var_inv evx'
        obtain ⟨ly', rfl⟩ := evalExpr_var_inv evy'
        simp at lx' ly'; subst lx' ly'
        obtain ⟨_, hrlt, rfl, rfl⟩ := divmod_sound fc pw hx hy hy0 cdm
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        obtain ⟨vr, evr, rfl⟩ := evalExpr_construct1_inv hbr2
        obtain ⟨lr, rfl⟩ := evalExpr_var_inv evr
        simp at lr; subst lr
        have hyb : (y == 0) = false := beq_false_of_ne hy0
        exact ⟨by simp [hyb, hrlt], by simp [hyb, natV, objQName, qualified, moduleName, objName], rfl⟩

theorem pMod_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_mod") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_mod
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pMod (by simp [helpers])) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pPred_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x : Nat} (hx : x < natLimit) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_pred") [natV objQName x] h r h') :
    x - 1 < natLimit ∧ r = natV objQName (x - 1) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_pred
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pPred (by simp [helpers])) ev
  simp only [pPred, helper, matchE, pN, natE, mk, subE, litE, vE, qualifyExprF, qualifyExpr,
    qualifyPat, qualifyTy, objTy, qualifyName_obj, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  cases body with
  | matchValue eva hsel1 hbr1 =>
    obtain ⟨la, rfl⟩ := evalExpr_var_inv eva
    simp at la; subst la
    simp [natV, SourceSemantics.selectArm, World.matchPattern, matchPatternWith, matchListWith,
      constructorName, Ty.toCore, Instance.symbol] at hsel1
    obtain ⟨rfl, rfl⟩ := hsel1
    cases hbr1 with
    | matchValue evx hsel2 hbr2 =>
      obtain ⟨lx, rfl⟩ := evalExpr_var_inv evx
      simp at lx; subst lx
      cases x with
      | zero =>
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        obtain ⟨v0, ev0, rfl⟩ := evalExpr_construct1_inv hbr2
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
        exact ⟨by unfold natLimit; omega, by simp [natV, objQName, qualified, moduleName, objName], rfl⟩
      | succ m =>
        have hne : (0 : F) ≠ (m : F) + 1 := by
          have h0 : ((m + 1 : Nat) : F) ≠ 0 :=
            fc.ne_zero_of_pos (Nat.succ_pos m) (lt_trans hx (by unfold natLimit; omega))
          rw [Nat.cast_add, Nat.cast_one] at h0
          exact Ne.symm h0
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings, hne] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        obtain ⟨vsub, evsub, rfl⟩ := evalExpr_construct1_inv hbr2
        obtain ⟨v1, v2, _, ev1, ev2, hsub⟩ := evalExpr_binary_inv evsub
        obtain ⟨l1, rfl⟩ := evalExpr_var_inv ev1
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
        simp at l1; subst l1
        simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
        refine ⟨by omega, ?_, rfl⟩
        simp [natV, objQName, qualified, moduleName, objName]

theorem pPred_only_nat (pw : PrimHelpersWorld P world)
    {wa r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_pred") [wa] h r h') :
    ∃ vx, wa = .construct objQName "N" [vx] := by
  obtain ⟨_, body⟩ := evalFn_plain_inv pw.p_pred
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_helpers ⟨P⟩ pPred (by simp [helpers])) ev
  simp only [pPred, helper, matchE, pN, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy,
    objTy, qualifyName_obj,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  cases body with
  | matchValue eva hsel _ =>
    obtain ⟨la, rfl⟩ := evalExpr_var_inv eva
    simp at la; subst la
    cases wa with
    | construct ea ca psa =>
      simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        constructorName, Ty.subst, Ty.toCore, Instance.symbol] at hsel
      by_cases hca : (ea != objQName || ca != "N" || (1 != psa.length)) = true
      · simp [hca] at hsel
      · simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at hca
        obtain ⟨⟨rfl, rfl⟩, hlen⟩ := hca
        rcases psa with _ | ⟨vx, _ | _⟩ <;> simp at hlen
        exact ⟨vx, rfl⟩
    | field _ | tuple _ | ptr _ _ =>
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at hsel

/-- Shared proof for `p_land`, `p_lor`, `p_xor`. -/
private theorem pBitwise_sound (fc : FieldCompatible F) {fnName opName : String}
    {op : Nat → Nat → Nat} (u64 : U64Contracts world)
    (hq : qualifyName opName = opName)
    (hfn : WorldHasFn world (qualified fnName) ["a", "b"] (qualifyExprF F (pBitwise fnName opName).body))
    (hop : ∀ a b wa wb h r h', isU64Val a wa → isU64Val b wb →
      EvalFn world opName [wa, wb] h r h' → isU64Val (op a b) r ∧ h' = h)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified fnName) [natV objQName x, natV objQName y] h r h') :
    op x y < natLimit ∧ r = natV objQName (op x y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBitwise, helper, natPair, matchE, natE, mk, callE,
      wordE, vE, isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [natE, mk, callE, qualifyExprF, qualifyExpr, qualifyName_obj,
    qualifyName_u64_to_field, hq, Option.map_some,
    Aiur.Generic.Expr.map, List.map] at hbody
  obtain ⟨vtf, evtf, rfl⟩ := evalExpr_construct1_inv hbody
  obtain ⟨vop, _, evop, ctf⟩ := evalExpr_call1_inv evtf
  obtain ⟨wx, wy, _, _, evwx, evwy, cop⟩ := evalExpr_call2_inv evop
  obtain ⟨hwx, rfl⟩ := eval_wordE_nat fc u64 hx (by simp) evwx
  obtain ⟨hwy, rfl⟩ := eval_wordE_nat fc u64 hy (by simp) evwy
  obtain ⟨hwop, rfl⟩ := hop _ _ _ _ _ _ _ hwx hwy cop
  obtain ⟨hlt, rfl, rfl⟩ := u64.to_field _ _ _ _ _ hwop ctf
  exact ⟨hlt, by simp [natV, objQName, qualified, moduleName, objName], rfl⟩

private theorem pBitwise_only_nat {fnName opName : String}
    (hfn : WorldHasFn world (qualified fnName) ["a", "b"] (qualifyExprF F (pBitwise fnName opName).body))
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified fnName) [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBitwise, helper, natPair, matchE, natE, mk, callE,
      wordE, vE, isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pLand_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_land") [natV objQName x, natV objQName y] h r h') :
    (x &&& y) < natLimit ∧ r = natV objQName (x &&& y) ∧ h' = h :=
  pBitwise_sound fc pw.u64 rfl pw.p_land pw.u64.and hx hy ev

theorem pLand_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_land") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) :=
  pBitwise_only_nat pw.p_land ev

theorem pLor_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_lor") [natV objQName x, natV objQName y] h r h') :
    (x ||| y) < natLimit ∧ r = natV objQName (x ||| y) ∧ h' = h :=
  pBitwise_sound fc pw.u64 rfl pw.p_lor pw.u64.or hx hy ev

theorem pLor_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_lor") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) :=
  pBitwise_only_nat pw.p_lor ev

theorem pXor_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_xor") [natV objQName x, natV objQName y] h r h') :
    (x ^^^ y) < natLimit ∧ r = natV objQName (x ^^^ y) ∧ h' = h :=
  pBitwise_sound fc pw.u64 rfl pw.p_xor pw.u64.xor hx hy ev

theorem pXor_only_nat (pw : PrimHelpersWorld P world)
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_xor") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) :=
  pBitwise_only_nat pw.p_xor ev

theorem pBeq_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_beq") [natV objQName x, natV objQName y] h r h') :
    r = .construct objQName (if x == y then tt else ff) [] ∧ h' = h := by
  have hfn := (pw.p_bool tt ff hb).1
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBeq, helper, natPair, matchE, subE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  simp only [matchE, subE, mk, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyName_obj,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
    List.map] at hbody
  cases hbody with
  | matchValue evsub hsel hbr =>
    obtain ⟨v1, v2, _, ev1, ev2, hsub⟩ := evalExpr_binary_inv evsub
    obtain ⟨l1, rfl⟩ := evalExpr_var_inv ev1
    obtain ⟨l2, rfl⟩ := evalExpr_var_inv ev2
    simp at l1 l2; subst l1 l2
    simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
    have hiff := fc.sub_eq_zero_iff (lt_trans hx (by unfold natLimit; omega))
      (lt_trans hy (by unfold natLimit; omega))
    by_cases hxy : x = y
    · have hsub0 : (x : F) - (y : F) = 0 := hiff.mpr hxy
      simp [hsub0, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv hbr
      simp [hxy, objQName, qualified, moduleName, objName]
    · have hsubNe : (0 : F) ≠ (x : F) - (y : F) := Ne.symm (fun h0 => hxy (hiff.mp h0))
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings, hsubNe] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv hbr
      have hbf : (x == y) = false := beq_false_of_ne hxy
      simp [hbf, objQName, qualified, moduleName, objName]

theorem pBeq_only_nat (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_beq") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  have hfn := (pw.p_bool tt ff hb).1
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBeq, helper, natPair, matchE, subE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pBle_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_ble") [natV objQName x, natV objQName y] h r h') :
    r = .construct objQName (if decide (x ≤ y) then tt else ff) [] ∧ h' = h := by
  have hfn := (pw.p_bool tt ff hb).2.1
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBle, helper, natPair, matchE, callE, wordE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  rcases eval_sub_cmp_inv fc pw.u64 hy hx (by simp) (by simp) hbody with ⟨hnlt, h0⟩ | ⟨hlt, h1⟩
  · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at h0
    obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv h0
    have hle : x ≤ y := Nat.le_of_not_lt hnlt
    simp [hle, objQName, qualified, moduleName, objName]
  · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at h1
    obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv h1
    have hnle : ¬ x ≤ y := Nat.not_le.mpr hlt
    simp [hnle, objQName, qualified, moduleName, objName]

theorem pBle_only_nat (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_ble") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  have hfn := (pw.p_bool tt ff hb).2.1
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBle, helper, natPair, matchE, callE, wordE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

theorem pBlt_sound (fc : FieldCompatible F) (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_blt") [natV objQName x, natV objQName y] h r h') :
    r = .construct objQName (if decide (x < y) then tt else ff) [] ∧ h' = h := by
  have hfn := (pw.p_bool tt ff hb).2.2
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBlt, helper, natPair, matchE, callE, wordE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, heqx, heqy, hbody⟩ := eval_natPair_inv body
  simp only [natV, Value.construct.injEq, List.cons.injEq, and_true] at heqx heqy
  obtain ⟨_, _, rfl⟩ := heqx
  obtain ⟨_, _, rfl⟩ := heqy
  rcases eval_sub_cmp_inv fc pw.u64 hx hy (by simp) (by simp) hbody with ⟨hnlt, h0⟩ | ⟨hlt, h1⟩
  · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at h0
    obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv h0
    simp [hnlt, objQName, qualified, moduleName, objName]
  · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at h1
    obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv h1
    simp [hlt, objQName, qualified, moduleName, objName]

theorem pBlt_only_nat (pw : PrimHelpersWorld P world)
    {tt ff : String} (hb : (Cx.mk P).boolNames = some (tt, ff))
    {wa wb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "p_blt") [wa, wb] h r h') :
    (∃ vx, wa = .construct objQName "N" [vx]) ∧ (∃ vy, wb = .construct objQName "N" [vy]) := by
  have hfn := (pw.p_bool tt ff hb).2.2
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; simp [pBlt, helper, natPair, matchE, callE, wordE, vE, mk,
      isPlainExpr, isPlainList, isPlainArms]) ev
  obtain ⟨vx, vy, hwa, hwb, _⟩ := eval_natPair_inv body
  exact ⟨⟨vx, hwa⟩, ⟨vy, hwb⟩⟩

/-- Build `PrimHelpersWorld` whenever every function in `Lower.helpers ⟨P⟩` is installed in `world`. -/
theorem PrimHelpersWorld.ofFunctions (u64 : U64Contracts world)
    (hmem : ∀ g ∈ helpers ⟨P⟩,
      WorldHasFn world (qualified g.name) (g.params.map Prod.fst) (qualifyExprF F g.body)) :
    PrimHelpersWorld P world where
  u64 := u64
  p_add := hmem pAdd (by simp [helpers])
  p_sub := hmem pSub (by simp [helpers])
  p_mul := hmem pMul (by simp [helpers])
  divmod := hmem Lower.divmod (by simp [helpers])
  p_div := hmem pDiv (by simp [helpers])
  p_mod := hmem pMod (by simp [helpers])
  p_pred := hmem pPred (by simp [helpers])
  p_land := hmem (pBitwise "p_land" "UInt64::and") (by simp [helpers])
  p_lor := hmem (pBitwise "p_lor" "UInt64::or") (by simp [helpers])
  p_xor := hmem (pBitwise "p_xor" "UInt64::xor") (by simp [helpers])
  p_bool := by
    intro tt ff hb
    refine ⟨?_, ?_, ?_⟩
    · exact hmem (pBeq tt ff) (by simp [helpers, hb, boolHelpers])
    · exact hmem (pBle tt ff) (by simp [helpers, hb, boolHelpers])
    · exact hmem (pBlt tt ff) (by simp [helpers, hb, boolHelpers])

end PrimHelpers

end IxCC.AiurBackend.Gadgets
