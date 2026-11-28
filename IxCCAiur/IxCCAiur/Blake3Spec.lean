import IxCCAiur.TypedGadgets
import Aiur.Library.Blake3.BlockLoop
import Aiur.Library.Bytes.Correctness
import Aiur.Generic.LawfulBEq
import Mathlib.Tactic.IntervalCases

/-! # Standalone Operational `EvalFn` Contracts for `Aiur.Library.Blake3` (`IxCCAiur.Blake3Spec`)

Certified Tier-1 compiler-intrinsic contracts for `Aiur.Library.Blake3` directly over
`Aiur.Generic.SourceSemantics.EvalFn`, with zero dependency on `IxVM` or `IxVMRefinement`.

This module provides:
1. **`hasNoControl` / `no_evalExit_of_noControl`**: proves that any source expression without
   `.control` nodes (even when it references `.global` constants such as `UInt8::BYTE_0` or
   `UInt32::ZERO`) cannot produce an abrupt `EvalExit`, reducing `EvalFn` directly to `EvalExpr`.
2. **Value representations, byte streams, and layer stacks**: `bv`, `w4`, `wv`, `vecV`, `stateV`,
   `u64v`, `digestV`, `Stream` (over `Aiur.Library.Bytes.RepByteStream`), and `Stack` — plus
   bridge lemmas to `TypedGadgets.isU32Val` and `Gadgets.isU64Val`.
3. **Decidably checkable `Blake3LibraryWorld` and `checkBlake3World`**: checks the 5 static
   `UInt8` lookup maps and 7 backing tables (`checkBlake3Tables`), the byte/zero constants, and
   all 43 elaborated library functions (`checkBlake3Functions`), with soundness theorem
   `blake3LibraryWorld_of_check`.
4. **Complete operational `EvalFn` contracts** over ANY `[Field F] [DecidableEq F]` satisfying
   `Aiur.Library.U32.Compatible F` (covering `TypedGadgets.FieldCompatible64 F`,
   `Gadgets.FieldCompatible F`, Goldilocks `ZMod (2^64 - 2^32 + 1)`, and every prime field
   `ZMod p` with `3 * 2^32 ≤ p`), building directly on `Aiur.Library.Blake3.Correctness` and
   `Aiur.Library.Blake3.BlockLoop`:
   * `eval_iv`, `eval_g_function`, `eval_compress_inner_j`, `eval_compress`, `eval_compress_init`
   * `eval_take_block`, `eval_bytes_to_block`, `eval_pad_block`, `eval_finish`,
     `eval_compress_chunks`, `eval_hash_blocks`
   * `eval_next_layer`, `eval_compress_layer`, `eval_hash`, `eval_hash_digest`
   * `eval_digest_bytes`, `eval_address_to_fields`, `eval_address_from_fields`,
     `eval_verify_bytes_against`, `eval_bytes_to_addr`, `eval_pack_word`, `eval_pack_digest`
5. **Bundled `Blake3Contracts`** with `ofLibraryWorld`, `ofCheck`, `ofCheck64`, `ofCheckZMod`,
   and `ofCheckGoldilocks`.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Blake3Spec

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Gadgets IxCC.AiurBackend.World IxCC.AiurBackend.TypedGadgets

/-! ## Section 1: Control-Free Expressions and `EvalExpr` Inversion Helpers -/

section NoControl

variable {F : Type}

mutual

/-- Syntactic predicate: `e` contains no `.control` node (allowing `.global` constants). -/
def hasNoControl : Aiur.Generic.Expr F → Bool
  | .control _ _ => false
  | .literal _ | .var _ | .global _ _ => true
  | .tuple xs | .array xs | .builtin _ xs | .update _ xs | .record _ xs
  | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs => hasNoControlList xs
  | .repeat e _ | .index e _ | .slice e _ _ | .member e _ | .project e _
  | .store e | .load e | .hint _ e _ | .neg e => hasNoControl e
  | .letValue _ e b | .binary _ e b => hasNoControl e && hasNoControl b
  | .matchValue e arms => hasNoControl e && hasNoControlArms arms

def hasNoControlList : List (Aiur.Generic.Expr F) → Bool
  | [] => true
  | e :: es => hasNoControl e && hasNoControlList es

def hasNoControlArms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F) → Bool
  | [] => true
  | (_, b) :: rest => hasNoControl b && hasNoControlArms rest

end

theorem hasNoControlList_iff {es : List (Aiur.Generic.Expr F)} :
    hasNoControlList es = true ↔ ∀ e ∈ es, hasNoControl e = true := by
  induction es with
  | nil => simp [hasNoControlList]
  | cons a tl ih =>
    simp [hasNoControlList, Bool.and_eq_true, ih]

theorem hasNoControlArms_iff {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)} :
    hasNoControlArms arms = true ↔ ∀ arm ∈ arms, hasNoControl arm.2 = true := by
  induction arms with
  | nil => simp [hasNoControlArms]
  | cons a tl ih =>
    rcases a with ⟨p, b⟩
    simp [hasNoControlArms, Bool.and_eq_true, ih]

private theorem mapM_toExpr_noControl
    {ps : List (Aiur.Generic.Pattern F)} {es : List (Aiur.Generic.Expr F)}
    (hrec : ∀ p ∈ ps, ∀ e, Consts.toExpr p = .ok e → hasNoControl e = true)
    (h : ps.mapM Consts.toExpr = .ok es) :
    hasNoControlList es = true := by
  induction ps generalizing es with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons p tl ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hp : Consts.toExpr p with
    | error _ => simp [hp] at h
    | ok e =>
      simp only [hp] at h
      cases htl : tl.mapM Consts.toExpr with
      | error _ => simp [htl] at h
      | ok es' =>
        simp only [htl, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [hasNoControlList, Bool.and_eq_true]
        exact ⟨hrec p List.mem_cons_self e hp,
          ih (fun q hq => hrec q (List.mem_cons_of_mem _ hq)) htl⟩

/-- Any expression produced by `Consts.toExpr` has no `.control` nodes. -/
theorem hasNoControl_of_toExpr :
    ∀ {p : Aiur.Generic.Pattern F} {e : Aiur.Generic.Expr F},
      Consts.toExpr p = .ok e → hasNoControl e = true
  | .literal _, _, h => by
    simp [Consts.toExpr, pure, Except.pure] at h; subst h; rfl
  | .global _ _, _, h => by
    simp [Consts.toExpr, pure, Except.pure] at h; subst h; rfl
  | .wildcard, _, h | .bind _, _, h | .orElse _ _ _, _, h => by
    simp [Consts.toExpr] at h
  | .load p, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp : Consts.toExpr p with
    | error _ => simp [hp] at h
    | ok e' =>
      simp only [hp, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [hasNoControl] using hasNoControl_of_toExpr hp
  | .repeat p n, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp : Consts.toExpr p with
    | error _ => simp [hp] at h
    | ok e' =>
      simp only [hp, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [hasNoControl] using hasNoControl_of_toExpr hp
  | .tuple ps, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => simp [hps] at h
    | ok es =>
      simp only [hps, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact mapM_toExpr_noControl (fun q hq _ hq' => by
        have : sizeOf q < sizeOf (Generic.Pattern.tuple ps) := by
          have := List.sizeOf_lt_of_mem hq
          simp [Generic.Pattern.tuple.sizeOf_spec]; omega
        exact hasNoControl_of_toExpr hq') hps
  | .array ps, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => simp [hps] at h
    | ok es =>
      simp only [hps, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact mapM_toExpr_noControl (fun q hq _ hq' => by
        have : sizeOf q < sizeOf (Generic.Pattern.array ps) := by
          have := List.sizeOf_lt_of_mem hq
          simp [Generic.Pattern.array.sizeOf_spec]; omega
        exact hasNoControl_of_toExpr hq') hps
  | .record head ps, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => simp [hps] at h
    | ok es =>
      simp only [hps, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact mapM_toExpr_noControl (fun q hq _ hq' => by
        have : sizeOf q < sizeOf (Generic.Pattern.record head ps) := by
          have := List.sizeOf_lt_of_mem hq
          simp [Generic.Pattern.record.sizeOf_spec]; omega
        exact hasNoControl_of_toExpr hq') hps
  | .construct t c ps, e, h => by
    cases t with
    | named n ts =>
      simp only [Consts.toExpr, bind, Except.bind] at h
      cases hps : ps.mapM Consts.toExpr with
      | error _ => simp [hps] at h
      | ok es =>
        simp only [hps, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact mapM_toExpr_noControl (fun q hq _ hq' => by
          have : sizeOf q < sizeOf (Generic.Pattern.construct (.named n ts) c ps) := by
            have := List.sizeOf_lt_of_mem hq
            simp [Generic.Pattern.construct.sizeOf_spec]; omega
          exact hasNoControl_of_toExpr hq') hps
    | field | tuple _ | array _ _ | ptr _ | param _ =>
      simp [Consts.toExpr] at h
  | .constructAs params t c ps, e, h => by
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => simp [hps] at h
    | ok es =>
      simp only [hps, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact mapM_toExpr_noControl (fun q hq _ hq' => by
        have : sizeOf q < sizeOf (Generic.Pattern.constructAs params t c ps) := by
          have := List.sizeOf_lt_of_mem hq
          simp [Generic.Pattern.constructAs.sizeOf_spec]; omega
        exact hasNoControl_of_toExpr hq') hps
termination_by p _ _ => sizeOf p

variable [Field F] [DecidableEq F]

mutual

/-- An expression with no `.control` node admits no abrupt `EvalExit`, even if it
evaluates `.global` constants. -/
theorem no_evalExit_of_noControl {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {before after : Heap F} {target : ExitTarget} {result : SourceValue F},
      hasNoControl e = true →
      EvalExit world types locals e before target result after → False
  | _, _, _, _, _, _, _, hnc, .exit _
  | _, _, _, _, _, _, _, hnc, .exitPayload _
  | _, _, _, _, _, _, _, hnc, .fromBlock _ _ => by
    simp [hasNoControl] at hnc
  | _, _, _, _, _, _, _, _, .fromGlobal _ hto body =>
    no_evalExit_of_noControl (hasNoControl_of_toExpr hto) body
  | _, _, _, _, _, _, _, hnc, .fromTuple items
  | _, _, _, _, _, _, _, hnc, .fromArray items
  | _, _, _, _, _, _, _, hnc, .fromBuiltin items
  | _, _, _, _, _, _, _, hnc, .fromUpdate items
  | _, _, _, _, _, _, _, hnc, .fromRecord items
  | _, _, _, _, _, _, _, hnc, .fromConstruct items
  | _, _, _, _, _, _, _, hnc, .fromConstructAs items
  | _, _, _, _, _, _, _, hnc, .fromCall items => by
    simp only [hasNoControl] at hnc
    exact no_evalArgsExit_of_noControl hnc items
  | _, _, _, _, _, _, _, hnc, .fromRepeat h
  | _, _, _, _, _, _, _, hnc, .fromIndex h
  | _, _, _, _, _, _, _, hnc, .fromSlice h
  | _, _, _, _, _, _, _, hnc, .fromMember h
  | _, _, _, _, _, _, _, hnc, .fromProject h
  | _, _, _, _, _, _, _, hnc, .fromStore h
  | _, _, _, _, _, _, _, hnc, .fromLoad h
  | _, _, _, _, _, _, _, hnc, .fromHint h
  | _, _, _, _, _, _, _, hnc, .fromNeg h => by
    simp only [hasNoControl] at hnc
    exact no_evalExit_of_noControl hnc h
  | _, _, _, _, _, _, _, hnc, .fromLetValue h
  | _, _, _, _, _, _, _, hnc, .binaryLeft h => by
    simp only [hasNoControl, Bool.and_eq_true] at hnc
    exact no_evalExit_of_noControl hnc.1 h
  | _, _, _, _, _, _, _, hnc, .letBody _ _ h
  | _, _, _, _, _, _, _, hnc, .binaryRight _ h => by
    simp only [hasNoControl, Bool.and_eq_true] at hnc
    exact no_evalExit_of_noControl hnc.2 h
  | _, _, _, _, _, _, _, hnc, .fromMatchValue h => by
    simp only [hasNoControl, Bool.and_eq_true] at hnc
    exact no_evalExit_of_noControl hnc.1 h
  | _, _, _, _, _, _, _, hnc, .matchBody _ sel h => by
    simp only [hasNoControl, Bool.and_eq_true] at hnc
    obtain ⟨p, hmem⟩ := selectArm_body_mem sel
    exact no_evalExit_of_noControl ((hasNoControlArms_iff.mp hnc.2) (p, _) hmem) h

theorem no_evalArgsExit_of_noControl {world : World F} :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {before after : Heap F} {target : ExitTarget} {result : SourceValue F},
      hasNoControlList es = true →
      EvalArgsExit world types locals es before target result after → False
  | _, _, _, _, _, _, _, hnc, .head h => by
    simp only [hasNoControlList, Bool.and_eq_true] at hnc
    exact no_evalExit_of_noControl hnc.1 h
  | _, _, _, _, _, _, _, hnc, .tail _ h => by
    simp only [hasNoControlList, Bool.and_eq_true] at hnc
    exact no_evalArgsExit_of_noControl hnc.2 h

end

/-- Any `EvalFn` of a control-free function reduces directly to `EvalExpr` on its body. -/
theorem evalFn_noControl_inv {world : World F} {name : String} {paramNames : List String}
    {body : Aiur.Generic.Expr F} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F}
    (hfn : WorldHasFn world name paramNames body) (hnc : hasNoControl body = true)
    (ev : EvalFn world name args h r h') :
    args.length = paramNames.length ∧
    EvalExpr world [] (paramNames.zip args) body h r h' := by
  cases ev with
  | intro prep b =>
    obtain ⟨rfl, hlen, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact ⟨hlen, b⟩
  | returned prep b =>
    obtain ⟨rfl, _, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact False.elim (no_evalExit_of_noControl hnc b)

end NoControl

section EvalHelpers

variable {F : Type} [Field F] [DecidableEq F]

theorem evalExpr_var_eq {world : World F} {types : Types} {locals : Environment F Nat}
    {name : String} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == name) = some (name, v))
    (ev : EvalExpr world types locals (.var name) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
  have heq := Option.some.inj (hl.symm.trans hlook)
  exact ⟨(Prod.mk.inj heq).2, rfl⟩

theorem evalExpr_global_literal_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {name : String} {x : F} {h h' : Heap F} {r : SourceValue F}
    (hconst : world.constant name .field = .ok (.literal x))
    (ev : EvalExpr world types locals (.global name (some .field)) h r h') :
    r = .field x ∧ h' = h := by
  cases ev with
  | global hlook hto hb =>
    simp only [Ty.subst] at hlook
    rw [hconst] at hlook
    cases hlook
    simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at hto
    subst hto
    exact evalExpr_literal_inv hb

theorem evalExpr_repeat_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {n : Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.repeat e n) h r h') :
    ∃ v, EvalExpr world types locals e h v h' ∧ r = .tuple (List.replicate n v) := by
  cases ev with
  | «repeat» hv => exact ⟨_, hv, rfl⟩

theorem evalExpr_load_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.load e) h r h') :
    ∃ p, EvalExpr world types locals e h p h' ∧ loadValue h' p = .ok r := by
  cases ev with
  | load hp hl => exact ⟨_, hp, hl⟩

theorem evalExpr_store_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.store e) h r h') :
    ∃ v hm, EvalExpr world types locals e h v hm ∧
      r = .ptr v.type hm.length ∧ h' = hm ++ [v] := by
  cases ev with
  | store hv => exact ⟨_, _, hv, rfl, rfl⟩

theorem evalExpr_slice_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {start : Nat} {stop : Option Nat} {h h' : Heap F}
    {r : SourceValue F}
    (ev : EvalExpr world types locals (.slice e start stop) h r h') :
    ∃ v, EvalExpr world types locals e h v h' ∧ sliceValue v start stop = .ok r := by
  cases ev with
  | slice hv hs => exact ⟨_, hv, hs⟩

theorem evalExpr_project_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e : Aiur.Generic.Expr F} {idx : Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.project e idx) h r h') :
    ∃ v, EvalExpr world types locals e h v h' ∧ projectValue v idx = .ok r := by
  cases ev with
  | project hv hp => exact ⟨_, hv, hp⟩

theorem evalExpr_ascribe_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {t : Generic.Ty} {e : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.builtin (.ascribe t) [e]) h r h') :
    EvalExpr world types locals e h r h' := by
  cases ev with
  | builtin hargs happ =>
    cases hargs with
    | cons he ht =>
      cases ht
      simp only [Builtin.apply, Except.ok.injEq] at happ
      subst happ
      exact he

theorem evalExpr_update1_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {i n : Nat} {base repl : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.update [[.index i n]] [base, repl]) h r h') :
    ∃ vb vr hm,
      EvalExpr world types locals base h vb hm ∧
      EvalExpr world types locals repl hm vr h' ∧
      Update.value types [[.index i n]] [vb, vr] = .ok r := by
  cases ev with
  | update hargs hup =>
    cases hargs with
    | cons hb ht1 =>
      cases ht1 with
      | cons hr ht2 =>
        cases ht2
        exact ⟨_, _, _, hb, hr, hup⟩

theorem evalExpr_call0_inv {world : World F} {locals : Environment F Nat}
    {name : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) []) h r h') :
    EvalFn world name [] h r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs
  exact hcal

theorem evalExpr_call5_inv {world : World F} {locals : Environment F Nat}
    {name : String} {e0 e1 e2 e3 e4 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [e0, e1, e2, e3, e4]) h r h') :
    ∃ v0 v1 v2 v3 v4 h1 h2 h3 h4 hm,
      EvalExpr world [] locals e0 h v0 h1 ∧
      EvalExpr world [] locals e1 h1 v1 h2 ∧
      EvalExpr world [] locals e2 h2 v2 h3 ∧
      EvalExpr world [] locals e3 h3 v3 h4 ∧
      EvalExpr world [] locals e4 h4 v4 hm ∧
      EvalFn world name [v0, v1, v2, v3, v4] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0 with | cons h1 t1 =>
  cases t1 with | cons h2 t2 =>
  cases t2 with | cons h3 t3 =>
  cases t3 with | cons h4 t4 =>
  cases t4
  exact ⟨_, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, hcal⟩

theorem evalExpr_call6_inv {world : World F} {locals : Environment F Nat}
    {name : String} {e0 e1 e2 e3 e4 e5 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [e0, e1, e2, e3, e4, e5]) h r h') :
    ∃ v0 v1 v2 v3 v4 v5 h1 h2 h3 h4 h5 hm,
      EvalExpr world [] locals e0 h v0 h1 ∧
      EvalExpr world [] locals e1 h1 v1 h2 ∧
      EvalExpr world [] locals e2 h2 v2 h3 ∧
      EvalExpr world [] locals e3 h3 v3 h4 ∧
      EvalExpr world [] locals e4 h4 v4 h5 ∧
      EvalExpr world [] locals e5 h5 v5 hm ∧
      EvalFn world name [v0, v1, v2, v3, v4, v5] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0 with | cons h1 t1 =>
  cases t1 with | cons h2 t2 =>
  cases t2 with | cons h3 t3 =>
  cases t3 with | cons h4 t4 =>
  cases t4 with | cons h5 t5 =>
  cases t5
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, hcal⟩

theorem evalExpr_call7_inv {world : World F} {locals : Environment F Nat}
    {name : String} {e0 e1 e2 e3 e4 e5 e6 : Aiur.Generic.Expr F} {h h' : Heap F}
    {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [e0, e1, e2, e3, e4, e5, e6]) h r h') :
    ∃ v0 v1 v2 v3 v4 v5 v6 h1 h2 h3 h4 h5 h6 hm,
      EvalExpr world [] locals e0 h v0 h1 ∧
      EvalExpr world [] locals e1 h1 v1 h2 ∧
      EvalExpr world [] locals e2 h2 v2 h3 ∧
      EvalExpr world [] locals e3 h3 v3 h4 ∧
      EvalExpr world [] locals e4 h4 v4 h5 ∧
      EvalExpr world [] locals e5 h5 v5 h6 ∧
      EvalExpr world [] locals e6 h6 v6 hm ∧
      EvalFn world name [v0, v1, v2, v3, v4, v5, v6] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with | cons h0 t0 =>
  cases t0 with | cons h1 t1 =>
  cases t1 with | cons h2 t2 =>
  cases t2 with | cons h3 t3 =>
  cases t3 with | cons h4 t4 =>
  cases t4 with | cons h5 t5 =>
  cases t5 with | cons h6 t6 =>
  cases t6
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h0, h1, h2, h3, h4, h5, h6, hcal⟩

theorem evalExpr_construct2_inv {world : World F} {locals : Environment F Nat}
    {en ctor : String} {a b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct en (some []) ctor [a, b]) h r h') :
    ∃ va vb hm,
      EvalExpr world [] locals a h va hm ∧
      EvalExpr world [] locals b hm vb h' ∧
      r = .construct en ctor [va, vb] := by
  cases ev with
  | construct hargs =>
    cases hargs with | cons ha t1 =>
    cases t1 with | cons hb t2 =>
    cases t2
    exact ⟨_, _, _, ha, hb, by simp [instanceName, Instance.symbol]⟩

theorem evalExpr_let_array4_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {x0 x1 x2 x3 : String} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals
      (.letValue (.array [.bind x0, .bind x1, .bind x2, .bind x3]) e b) h r h') :
    ∃ v0 v1 v2 v3 hm,
      EvalExpr world types locals e h (.tuple [v0, v1, v2, v3]) hm ∧
      EvalExpr world types ([(x0, v0), (x1, v1), (x2, v2), (x3, v3)] ++ locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨v0, v1, v2, v3, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

/-- Inversion of `EvalArgs` over a mapped list of heap-preserving expressions. -/
theorem evalArgs_map_inv {α : Type*} {world : World F} {types : Types}
    {locals : Environment F Nat} {f : α → Aiur.Generic.Expr F} {g : α → SourceValue F}
    (xs : List α)
    (heach : ∀ x ∈ xs, ∀ h r h', EvalExpr world types locals (f x) h r h' → r = g x ∧ h' = h)
    {h h' : Heap F} {vs : List (SourceValue F)}
    (ev : EvalArgs world types locals (xs.map f) h vs h') :
    vs = xs.map g ∧ h' = h := by
  induction xs generalizing h vs with
  | nil =>
    cases ev; exact ⟨rfl, rfl⟩
  | cons x tl ih =>
    cases ev with
    | cons hd tlEv =>
      obtain ⟨rfl, rfl⟩ := heach x List.mem_cons_self _ _ _ hd
      obtain ⟨rfl, rfl⟩ := ih (fun y hy => heach y (List.mem_cons_of_mem _ hy)) tlEv
      exact ⟨rfl, rfl⟩

theorem evalExpr_array_map_inv {α : Type*} {world : World F} {types : Types}
    {locals : Environment F Nat} {f : α → Aiur.Generic.Expr F} {g : α → SourceValue F}
    (xs : List α)
    (heach : ∀ x ∈ xs, ∀ h r h', EvalExpr world types locals (f x) h r h' → r = g x ∧ h' = h)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array (xs.map f)) h r h') :
    r = .tuple (xs.map g) ∧ h' = h := by
  cases ev with
  | array hargs =>
    obtain ⟨rfl, rfl⟩ := evalArgs_map_inv xs heach hargs
    exact ⟨rfl, rfl⟩

theorem evalExpr_match_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {scr : Aiur.Generic.Expr F} {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.matchValue scr arms) h r h') :
    ∃ v hm bs body,
      EvalExpr world types locals scr h v hm ∧
      selectArm world types hm v arms = .ok (some (bs, body)) ∧
      EvalExpr world types (bs ++ locals) body hm r h' := by
  cases ev with
  | matchValue hv hsel hb => exact ⟨_, _, _, _, hv, hsel, hb⟩

omit [Field F] in
theorem selectArm_nil_inv {world : World F} {types : Types} {h : Heap F} {v : SourceValue F}
    {bs : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : SourceSemantics.selectArm world types h v [] = .ok (some (bs, body))) : False := by
  simp [SourceSemantics.selectArm, pure, Except.pure] at hsel

omit [Field F] in
theorem selectArm_cons_inv {world : World F} {types : Types} {h : Heap F} {v : SourceValue F}
    {p : Aiur.Generic.Pattern F} {b : Aiur.Generic.Expr F}
    {rest : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {bs : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : SourceSemantics.selectArm world types h v ((p, b) :: rest) = .ok (some (bs, body))) :
    (world.matchPattern types h p v = .ok (some bs) ∧ body = b) ∨
    (world.matchPattern types h p v = .ok none ∧
      SourceSemantics.selectArm world types h v rest = .ok (some (bs, body))) := by
  simp only [SourceSemantics.selectArm, bind, Except.bind] at hsel
  cases hm : world.matchPattern types h p v with
  | error _ => simp [hm] at hsel
  | ok opt =>
    simp only [hm] at hsel
    cases opt with
    | some bs' =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
      exact .inl ⟨by rw [hsel.1], hsel.2.symm⟩
    | none =>
      exact .inr ⟨rfl, hsel⟩

/-- Inversion of `match e { c => b1, _ => b2 }`. -/
theorem evalExpr_match_lit_wild_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {scr b1 b2 : Aiur.Generic.Expr F} {c : F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals
      (.matchValue scr [(.literal c, b1), (.wildcard, b2)]) h r h') :
    ∃ v hm, EvalExpr world types locals scr h v hm ∧
      ((v = .field c ∧ EvalExpr world types locals b1 hm r h') ∨
       (v ≠ .field c ∧ EvalExpr world types locals b2 hm r h')) := by
  obtain ⟨v, hm, bs, body, hscr, hsel, hbody⟩ := evalExpr_match_inv ev
  rcases selectArm_cons_inv hsel with ⟨hmatch, rfl⟩ | ⟨hnomatch, hsel2⟩
  · cases v with
    | field x =>
      simp only [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at hmatch
      split at hmatch
      · next hcx =>
        simp only [Except.ok.injEq, Option.some.injEq] at hmatch
        subst hmatch
        exact ⟨.field x, hm, hscr, .inl ⟨by rw [hcx], by simpa using hbody⟩⟩
      · simp at hmatch
    | tuple _ | ptr _ _ | construct _ _ _ =>
      simp [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at hmatch
  · have hne : v ≠ .field c := by
      intro hveq; subst hveq
      simp [World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at hnomatch
    rcases selectArm_cons_inv hsel2 with ⟨hmatch2, rfl⟩ | ⟨hnomatch2, hsel3⟩
    · simp only [World.matchPattern, matchPatternWith, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at hmatch2
      subst hmatch2
      exact ⟨v, hm, hscr, .inr ⟨hne, by simpa using hbody⟩⟩
    · exact False.elim (selectArm_nil_inv hsel3)

theorem binop_add {x y : F} {r : SourceValue F}
    (h : evalBinOp .add (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x + y) :=
  (Except.ok.inj h).symm

theorem binop_sub {x y : F} {r : SourceValue F}
    (h : evalBinOp .sub (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x - y) :=
  (Except.ok.inj h).symm

theorem binop_mul {x y : F} {r : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x * y) :=
  (Except.ok.inj h).symm

theorem binop_div {x y : F} {r : SourceValue F} (hy : y ≠ 0)
    (h : evalBinOp .div (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x / y) := by
  have e : evalBinOp .div (.field x : SourceValue F) (.field y) = .ok (.field (x / y)) := by
    simp [evalBinOp, hy]
  rw [e] at h
  exact (Except.ok.inj h).symm

end EvalHelpers

/-! ## Section 2: Value Representations, Streams, Layer Stacks, and Field Lemmas -/

section Representations

variable {F : Type} [Field F]

/-- Canonical monomorphized enum name for `Bytes::Stream = Lists::List<UInt8::U8>`. -/
def byteStreamEnum : String :=
  (Aiur.Generic.Instance.mk "Lists::Node" [.field]).symbol

theorem byteStreamEnum_ctor :
    constructorName [] (.named "Lists::Node" [.field]) = byteStreamEnum := by
  simp [constructorName, Generic.Ty.toCore, byteStreamEnum]

theorem byteStreamEnum_inst :
    instanceName [] "Lists::Node" (some [.field]) = byteStreamEnum := by
  simp [instanceName, byteStreamEnum]

/-- A checked byte (`UInt8::U8`) as a source value. -/
abbrev bv (b : UInt8) : SourceValue F := .field (b.toNat : F)

/-- A 32-bit word from its four little-endian bytes (`UInt32::U32 = [U8; 4]`). -/
def w4 (b0 b1 b2 b3 : UInt8) : SourceValue F := .tuple [bv b0, bv b1, bv b2, bv b3]

/-- A 32-bit word as a source value (four little-endian bytes). -/
def wv (w : UInt32) : SourceValue F :=
  w4 (Blake3.Pure.wordBytes w)[0] (Blake3.Pure.wordBytes w)[1]
    (Blake3.Pure.wordBytes w)[2] (Blake3.Pure.wordBytes w)[3]

/-- A vector of 32-bit words (chaining value `[U32; 8]` or block `[U32; 16]`). -/
def vecV {n : Nat} (v : Vector UInt32 n) : SourceValue F :=
  .tuple (List.ofFn fun k : Fin n => wv v[k])

/-- The 32-word list inside `Blake3::compress`'s state `[U32; 32]`. -/
def stateL (s m : Blake3.Pure.Block) : List (SourceValue F) :=
  List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F)) ++
    List.ofFn (fun k : Fin 16 => (wv m[k] : SourceValue F))

/-- `Blake3::compress`'s `[U32; 32]` state: 16 state words followed by 16 message words. -/
def stateV (s m : Blake3.Pure.Block) : SourceValue F := .tuple (stateL s m)

/-- Byte `i` (little-endian) of a 64-bit chunk counter. -/
def u64b (c : UInt64) (i : Nat) : UInt8 := (c.toNat / 256 ^ i).toUInt8

/-- A 64-bit counter (`UInt64::U64 = [U8; 8]`) as a source value. -/
def u64v (c : UInt64) : SourceValue F :=
  .tuple (List.ofFn fun i : Fin 8 => bv (u64b c i))

/-- A 32-byte digest or address (`[U8; 32]`), matching `Aiur.Library.Bytes.RepAddress`. -/
def digestV (d : Vector UInt8 32) : SourceValue F := .tuple (d.toList.map bv)

/-- A `Blake3::MaybeDigest` value. -/
def maybeV : Option Blake3.Pure.CV → SourceValue F
  | none => .construct "Blake3::MaybeDigest" "None" []
  | some d => .construct "Blake3::MaybeDigest" "Some" [vecV d]

/-- The `root` field flag passed to `Blake3::next_layer`. -/
def rootF : Bool → F
  | true => 1
  | false => 0

/-- A byte stream (`Bytes::Stream = &Lists::Node<UInt8::U8>`) holding `bytes` in `h`. -/
abbrev Stream (h : Heap F) (bytes : List UInt8) (ptr : SourceValue F) : Prop :=
  Aiur.Library.Bytes.RepByteStream byteStreamEnum h bytes ptr

/-- The layer stack (`Blake3::Layer = &Blake3::LayerNode`) holding chaining values `st`
(top first: `LayerNode::Push(rest, cv)` represents `cv :: rest`). -/
inductive Stack (h : Heap F) : List Blake3.Pure.CV → SourceValue F → Prop where
  | nil {addr : Nat} (cell : h[addr]? = some (.construct "Blake3::LayerNode" "Nil" [])) :
      Stack h [] (.ptr (.enum "Blake3::LayerNode") addr)
  | push {addr : Nat} {cv : Blake3.Pure.CV} {st : List Blake3.Pure.CV} {p : SourceValue F}
      (cell : h[addr]? = some (.construct "Blake3::LayerNode" "Push" [p, vecV cv]))
      (rest : Stack h st p) : Stack h (cv :: st) (.ptr (.enum "Blake3::LayerNode") addr)

/-! ### Field Compatibility & Bridge Lemmas -/

theorem u32Compat_natCast_inj (hc : U32.Compatible F) {a b : Nat}
    (ha : a < 3 * U32.base) (hb : b < 3 * U32.base) (h : (a : F) = (b : F)) : a = b :=
  hc ha hb h

theorem u32Compat_byte_inj (hc : U32.Compatible F) {a b : Nat}
    (ha : a < 256) (hb : b < 256) (h : (a : F) = (b : F)) : a = b :=
  hc (lt_trans ha (by decide)) (lt_trans hb (by decide)) h

theorem u32Compat_small_inj (hc : U32.Compatible F) {a b : Nat}
    (ha : a < 1024) (hb : b < 1024) (h : (a : F) = (b : F)) : a = b :=
  hc (lt_trans ha (by decide)) (lt_trans hb (by decide)) h

theorem u32Compat_ne_zero (hc : U32.Compatible F) {k : Nat} (hk : k < 1024) (h0 : k ≠ 0) :
    (0 : F) ≠ (k : F) := by
  intro e
  exact h0 (u32Compat_small_inj hc hk (by omega) (by simpa using e.symm))

theorem u32Compat_of_fieldCompatible (fc : FieldCompatible F) : U32.Compatible F := by
  intro a ha b hb h
  exact fc (lt_trans ha (by decide : 3 * U32.base < 2 ^ 57))
    (lt_trans hb (by decide : 3 * U32.base < 2 ^ 57)) h

theorem u32Compat_of_zmod (p : Nat) [Fact (Nat.Prime p)] (hp : 3 * U32.base ≤ p) :
    U32.Compatible (ZMod p) :=
  U32.compatible_of_charP (ZMod p) p hp

theorem toNat_ofNat_lt {x : Nat} (hx : x < 256) : (UInt8.ofNat x).toNat = x := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hx

theorem bv_ofNat {x : Nat} (hx : x < 256) : (bv (UInt8.ofNat x) : SourceValue F) = .field (x : F) := by
  simp only [bv, toNat_ofNat_lt hx]

theorem byte_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

theorem bv_inj (hc : U32.Compatible F) {a b : UInt8} (h : (bv a : SourceValue F) = bv b) : a = b :=
  UInt8.ext (u32Compat_byte_inj hc (byte_lt a) (byte_lt b) (Value.field.inj h))

theorem wv_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    (wv (Aiur.Library.Blake3.wordOfBytes b0 b1 b2 b3) : SourceValue F) = w4 b0 b1 b2 b3 := by
  rw [wv, Aiur.Library.Blake3.wordBytes_wordOfBytes]
  rfl

theorem wv_bytes (w : UInt32) :
    Aiur.Library.Blake3.wordOfBytes (Blake3.Pure.wordBytes w)[0] (Blake3.Pure.wordBytes w)[1]
      (Blake3.Pure.wordBytes w)[2] (Blake3.Pure.wordBytes w)[3] = w :=
  Aiur.Library.Blake3.wordOfBytes_wordBytes w

theorem word_lt (w : UInt32) : w.toNat < U32.base := w.toNat_lt

theorem w4_eq_wv {c0 c1 c2 c3 : UInt8} {w : UInt32}
    (hw : (Aiur.Library.Blake3.wordOfBytes c0 c1 c2 c3).toNat = w.toNat) :
    (w4 c0 c1 c2 c3 : SourceValue F) = wv w := by
  have e : Aiur.Library.Blake3.wordOfBytes c0 c1 c2 c3 = w := UInt32.ext hw
  rw [← e, wv_wordOfBytes]

/-- Bridge between `wv w` and `TypedGadgets.isU32Val w.toNat`. -/
theorem isU32Val_wv (w : UInt32) : isU32Val w.toNat (wv w : SourceValue F) := by
  refine ⟨(Blake3.Pure.wordBytes w)[0].toNat, (Blake3.Pure.wordBytes w)[1].toNat,
    (Blake3.Pure.wordBytes w)[2].toNat, (Blake3.Pure.wordBytes w)[3].toNat,
    byte_lt _, byte_lt _, byte_lt _, byte_lt _, ?_, rfl⟩
  have h := congrArg UInt32.toNat (wv_bytes w)
  rw [Aiur.Library.Blake3.wordOfBytes_toNat] at h
  exact h.symm

/-- Bridge from `TypedGadgets.isU32Val` to `wv`. -/
theorem wv_of_isU32Val {n : Nat} {v : SourceValue F} (hv : isU32Val n v) :
    v = wv (UInt32.ofNat n) := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩ := hv
  have hw : (Aiur.Library.Blake3.wordOfBytes (UInt8.ofNat b0) (UInt8.ofNat b1)
      (UInt8.ofNat b2) (UInt8.ofNat b3)).toNat = (UInt32.ofNat (U32.pack b0 b1 b2 b3)).toNat := by
    rw [Aiur.Library.Blake3.wordOfBytes_toNat, toNat_ofNat_lt h0, toNat_ofNat_lt h1,
      toNat_ofNat_lt h2, toNat_ofNat_lt h3, UInt32.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (U32.pack_lt h0 h1 h2 h3)).symm
  rw [← w4_eq_wv hw, w4, bv_ofNat h0, bv_ofNat h1, bv_ofNat h2, bv_ofNat h3]

theorem u64b_toNat (c : UInt64) (i : Nat) : (u64b c i).toNat = c.toNat / 256 ^ i % 256 := by
  simp [u64b, Nat.toUInt8_eq, UInt8.toNat_ofNat']

theorem u64v_eq (c : UInt64) : (u64v c : SourceValue F) =
    .tuple [bv (u64b c 0), bv (u64b c 1), bv (u64b c 2), bv (u64b c 3),
            bv (u64b c 4), bv (u64b c 5), bv (u64b c 6), bv (u64b c 7)] := rfl

theorem u64_pack (c : UInt64) :
    U64.pack (u64b c 0).toNat (u64b c 1).toNat (u64b c 2).toNat (u64b c 3).toNat
      (u64b c 4).toNat (u64b c 5).toNat (u64b c 6).toNat (u64b c 7).toNat = c.toNat := by
  have hn : c.toNat < 18446744073709551616 := c.toNat_lt
  simp only [u64b_toNat]
  unfold U64.pack
  omega

/-- Bridge between `u64v c` and `Gadgets.isU64Val c.toNat`. -/
theorem isU64Val_u64v (c : UInt64) : isU64Val c.toNat (u64v c : SourceValue F) :=
  ⟨(u64b c 0).toNat, (u64b c 1).toNat, (u64b c 2).toNat, (u64b c 3).toNat,
   (u64b c 4).toNat, (u64b c 5).toNat, (u64b c 6).toNat, (u64b c 7).toNat,
   byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _,
   (u64_pack c).symm, rfl⟩

theorem u64v_zero : (u64v 0 : SourceValue F) = .tuple (List.replicate 8 (.field 0)) := by
  rw [u64v_eq]; simp [u64b, bv]

/-! ### Heap, Stream, and Stack Lemmas -/

omit [Field F] in
@[simp] theorem type_construct (name ctor : String) (args : List (SourceValue F)) :
    (Value.construct name ctor args : SourceValue F).type = .enum name := by
  rw [Value.type]

omit [Field F] in
@[simp] theorem type_tuple (xs : List (SourceValue F)) :
    (Value.tuple xs : SourceValue F).type = .tuple (xs.map Value.type) := by
  rw [Value.type]

omit [Field F] in
theorem load_cell {h : Heap F} {addr : Nat} {name ctor : String} {args : List (SourceValue F)}
    (cell : h[addr]? = some (.construct name ctor args)) :
    loadValue h (.ptr (.enum name) addr) = .ok (.construct name ctor args) := by
  simp [loadValue, cell, bind, Except.bind, pure, Except.pure]

omit [Field F] in
theorem loadValue_snoc (h : Heap F) (v : SourceValue F) :
    loadValue (h ++ [v]) (.ptr v.type h.length) = .ok v := by
  simp [loadValue, bind, Except.bind, pure, Except.pure]

omit [Field F] in
theorem cell_extend {h h' : Heap F} (ext : Heap.Extends h h') {a : Nat} {v : SourceValue F}
    (cell : h[a]? = some v) : h'[a]? = some v := by
  obtain ⟨s, rfl⟩ := ext
  have ha : a < h.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at cell
    cases cell
  rw [List.getElem?_append_left ha, cell]

omit [Field F] in
theorem loadValue_extend {h h' : Heap F} (ext : Heap.Extends h h') {p v : SourceValue F}
    (hl : loadValue h p = .ok v) : loadValue h' p = .ok v := by
  cases p with
  | ptr t a =>
    cases hc : h[a]? with
    | none => simp [loadValue, hc] at hl
    | some w =>
      have hw' := cell_extend ext hc
      simp only [loadValue, hc] at hl
      simp only [loadValue, hw']
      exact hl
  | _ => simp [loadValue] at hl

omit [Field F] in
theorem extends3 (h : Heap F) (a b d : SourceValue F) :
    Heap.Extends h (h ++ [a] ++ [b] ++ [d]) :=
  ⟨[a, b, d], by simp⟩

theorem Stream.mono {h h' : Heap F} (ext : Heap.Extends h h') {bytes : List UInt8}
    {ptr : SourceValue F} (hs : Stream h bytes ptr) : Stream h' bytes ptr :=
  Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext hs

theorem stream_inv {h : Heap F} {bytes : List UInt8} {ptr v : SourceValue F}
    (hs : Stream h bytes ptr) (hl : loadValue h ptr = .ok v) :
    (bytes = [] ∧ v = .construct byteStreamEnum "Nil" []) ∨
    (∃ x xs tail, bytes = x :: xs ∧ v = .construct byteStreamEnum "Cons" [bv x, tail] ∧
      Stream h xs tail) := by
  cases hs with
  | nil cell =>
    rw [load_cell cell] at hl; cases hl; exact .inl ⟨rfl, rfl⟩
  | cons cell headRep tailRep =>
    rw [load_cell cell] at hl; cases hl
    refine .inr ⟨_, _, _, rfl, ?_, tailRep⟩
    rw [headRep]

theorem stream_nil_snoc (h : Heap F) :
    Stream (h ++ [.construct byteStreamEnum "Nil" []]) []
      (.ptr (.enum byteStreamEnum) h.length) :=
  .nil (by simp)

theorem stream_cons_snoc {h : Heap F} {x : UInt8} {xs : List UInt8} {tail : SourceValue F}
    (hs : Stream h xs tail) :
    Stream (h ++ [.construct byteStreamEnum "Cons" [bv x, tail]]) (x :: xs)
      (.ptr (.enum byteStreamEnum) h.length) :=
  .cons (by simp) rfl (hs.mono (Heap.Extends.snoc h _))

theorem Stack.mono {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {st : List Blake3.Pure.CV} {p : SourceValue F}, Stack h st p → Stack h' st p
  | _, _, .nil cell => .nil (cell_extend ext cell)
  | _, _, .push cell rest => .push (cell_extend ext cell) (rest.mono ext)

theorem stack_inv {h : Heap F} {st : List Blake3.Pure.CV} {p v : SourceValue F}
    (hs : Stack h st p) (hl : loadValue h p = .ok v) :
    (st = [] ∧ v = .construct "Blake3::LayerNode" "Nil" []) ∨
    (∃ cv st' q, st = cv :: st' ∧ v = .construct "Blake3::LayerNode" "Push" [q, vecV cv] ∧
      Stack h st' q) := by
  cases hs with
  | nil cell =>
    rw [load_cell cell] at hl; cases hl; exact .inl ⟨rfl, rfl⟩
  | push cell rest =>
    rw [load_cell cell] at hl; cases hl; exact .inr ⟨_, _, _, rfl, rfl, rest⟩

theorem stack_nil_snoc (h : Heap F) :
    Stack (h ++ [.construct "Blake3::LayerNode" "Nil" []]) []
      (.ptr (.enum "Blake3::LayerNode") h.length) :=
  .nil (by simp)

theorem stack_push_snoc {h : Heap F} {cv : Blake3.Pure.CV} {st : List Blake3.Pure.CV}
    {p : SourceValue F} (hs : Stack h st p) :
    Stack (h ++ [.construct "Blake3::LayerNode" "Push" [p, vecV cv]]) (cv :: st)
      (.ptr (.enum "Blake3::LayerNode") h.length) :=
  .push (by simp) (hs.mono (Heap.Extends.snoc h _))

omit [Field F] in
theorem proj_getElem (items : List (SourceValue F)) (i : Nat) (hi : i < items.length) :
    projectValue (.tuple items) i = .ok items[i] := by
  simp [projectValue, List.getElem?_eq_getElem hi]

omit [Field F] in
theorem proj_inv {items : List (SourceValue F)} {i : Nat} {v : SourceValue F}
    (hi : i < items.length) (h : projectValue (.tuple items) i = .ok v) : v = items[i] :=
  (Except.ok.inj ((proj_getElem items i hi).symm.trans h)).symm

theorem proj_vecV {n : Nat} (v : Vector UInt32 n) (i : Nat) (hi : i < n) :
    projectValue (vecV v : SourceValue F) i = .ok (wv v[i]) := by
  have hl : i < (List.ofFn fun k : Fin n => (wv v[k] : SourceValue F)).length := by simpa using hi
  rw [vecV, proj_getElem _ _ hl]
  simp

theorem proj_digestV (d : Vector UInt8 32) (i : Nat) (hi : i < 32) :
    projectValue (digestV d : SourceValue F) i = .ok (bv d[i]) := by
  have hl : i < (d.toList.map bv : List (SourceValue F)).length := by simpa using hi
  rw [digestV, proj_getElem _ _ hl]
  simp

theorem proj_w4_0 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3 : SourceValue F) 0 = .ok (bv b0) := rfl
theorem proj_w4_1 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3 : SourceValue F) 1 = .ok (bv b1) := rfl
theorem proj_w4_2 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3 : SourceValue F) 2 = .ok (bv b2) := rfl
theorem proj_w4_3 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3 : SourceValue F) 3 = .ok (bv b3) := rfl

end Representations

/-! ## Section 3: Static Tables, Elaborated ASTs, `Blake3LibraryWorld`, and `checkBlake3World` -/

section WorldAndChecker

variable {F : Type} [Field F] [DecidableEq F]

/-- The 65,536 byte-pair inputs `(a, b)` for `0 ≤ a, b < 256`. -/
def bytePairInputs : List (Nat × Nat) :=
  (List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)

def byteInputsRows (F : Type) [Field F] : List (Constant F) :=
  (List.range 256).map fun (x : Nat) => .tuple [.field (x : F)]

def byteValuesRows (F : Type) [Field F] : List (Constant F) :=
  (List.range 256).map fun (x : Nat) => .field (x : F)

def pairInputsRows (F : Type) [Field F] : List (Constant F) :=
  bytePairInputs.map fun (a, b) => .tuple [.field (a : F), .field (b : F)]

def pairUnitsRows (F : Type) [Field F] : List (Constant F) :=
  bytePairInputs.map fun _ => .tuple []

def pairXorsRows (F : Type) [Field F] : List (Constant F) :=
  bytePairInputs.map fun (a, b) => .field ((Nat.xor a b : Nat) : F)

def pairXorParts4Rows (F : Type) [Field F] : List (Constant F) :=
  bytePairInputs.map fun (a, b) =>
    .tuple [.field ((Nat.xor a b / 16 : Nat) : F), .field (((Nat.xor a b % 16) * 16 : Nat) : F)]

def pairXorParts7Rows (F : Type) [Field F] : List (Constant F) :=
  bytePairInputs.map fun (a, b) =>
    .tuple [.field ((Nat.xor a b / 128 : Nat) : F), .field (((Nat.xor a b % 128) * 2 : Nat) : F)]

/-- Behavioral contracts for the 5 `UInt8` lookup maps used by `Aiur.Library.Blake3`. -/
structure Blake3MapSpec (world : World F) : Prop where
  from_field : ∀ v h r h',
    EvalFn world "UInt8::from_field" [v] h r h' →
    r = v ∧ h' = h ∧ ∃ x : Nat, x < 256 ∧ v = .field (x : F)
  range_pair : ∀ v1 v2 h r h',
    EvalFn world "UInt8::range_pair" [v1, v2] h r h' →
    r = .tuple [] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)
  raw_xor : ∀ v1 v2 h r h',
    EvalFn world "UInt8::raw_xor" [v1, v2] h r h' →
    h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧
      v1 = .field (a : F) ∧ v2 = .field (b : F) ∧ r = .field ((Nat.xor a b : Nat) : F)
  raw_xor_split4 : ∀ v1 v2 h r h',
    EvalFn world "UInt8::raw_xor_split4" [v1, v2] h r h' →
    h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧
      v1 = .field (a : F) ∧ v2 = .field (b : F) ∧
      r = .tuple [.field ((Nat.xor a b / 16 : Nat) : F),
                  .field (((Nat.xor a b % 16) * 16 : Nat) : F)]
  raw_xor_split7 : ∀ v1 v2 h r h',
    EvalFn world "UInt8::raw_xor_split7" [v1, v2] h r h' →
    h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧
      v1 = .field (a : F) ∧ v2 = .field (b : F) ∧
      r = .tuple [.field ((Nat.xor a b / 128 : Nat) : F),
                  .field (((Nat.xor a b % 128) * 2 : Nat) : F)]

/-- Symbolic table specification for the 5 maps and 7 backing tables used by BLAKE3. -/
structure Blake3TablesMatch (s : Generic.Source F) : Prop where
  noFn_from_field : s.program.sourceFunction? "UInt8::from_field" = none
  noFn_range_pair : s.program.sourceFunction? "UInt8::range_pair" = none
  noFn_raw_xor : s.program.sourceFunction? "UInt8::raw_xor" = none
  noFn_raw_xor_split4 : s.program.sourceFunction? "UInt8::raw_xor_split4" = none
  noFn_raw_xor_split7 : s.program.sourceFunction? "UInt8::raw_xor_split7" = none
  map_from_field : ∃ m, s.tables.findMap? "UInt8::from_field" = some m ∧
    m.input = "UInt8::byte_inputs" ∧ m.output = "UInt8::byte_values"
  map_range_pair : ∃ m, s.tables.findMap? "UInt8::range_pair" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_units"
  map_raw_xor : ∃ m, s.tables.findMap? "UInt8::raw_xor" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_xors"
  map_raw_xor_split4 : ∃ m, s.tables.findMap? "UInt8::raw_xor_split4" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_xor_parts4"
  map_raw_xor_split7 : ∃ m, s.tables.findMap? "UInt8::raw_xor_split7" = some m ∧
    m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_xor_parts7"
  tbl_byte_inputs : ∃ t, s.tables.findTable? "UInt8::byte_inputs" = some t ∧
    t.rows = byteInputsRows F
  tbl_byte_values : ∃ t, s.tables.findTable? "UInt8::byte_values" = some t ∧
    t.rows = byteValuesRows F
  tbl_pair_inputs : ∃ t, s.tables.findTable? "UInt8::pair_inputs" = some t ∧
    t.rows = pairInputsRows F
  tbl_pair_units : ∃ t, s.tables.findTable? "UInt8::pair_units" = some t ∧
    t.rows = pairUnitsRows F
  tbl_pair_xors : ∃ t, s.tables.findTable? "UInt8::pair_xors" = some t ∧
    t.rows = pairXorsRows F
  tbl_pair_xor_parts4 : ∃ t, s.tables.findTable? "UInt8::pair_xor_parts4" = some t ∧
    t.rows = pairXorParts4Rows F
  tbl_pair_xor_parts7 : ∃ t, s.tables.findTable? "UInt8::pair_xor_parts7" = some t ∧
    t.rows = pairXorParts7Rows F

/-- Executable check for the 5 `UInt8` maps and 7 tables required by `Aiur.Library.Blake3`. -/
def checkBlake3Tables (s : Generic.Source F) : Bool :=
  checkNoFunction s "UInt8::from_field" &&
  checkNoFunction s "UInt8::range_pair" &&
  checkNoFunction s "UInt8::raw_xor" &&
  checkNoFunction s "UInt8::raw_xor_split4" &&
  checkNoFunction s "UInt8::raw_xor_split7" &&
  checkMap s "UInt8::from_field" "UInt8::byte_inputs" "UInt8::byte_values" &&
  checkMap s "UInt8::range_pair" "UInt8::pair_inputs" "UInt8::pair_units" &&
  checkMap s "UInt8::raw_xor" "UInt8::pair_inputs" "UInt8::pair_xors" &&
  checkMap s "UInt8::raw_xor_split4" "UInt8::pair_inputs" "UInt8::pair_xor_parts4" &&
  checkMap s "UInt8::raw_xor_split7" "UInt8::pair_inputs" "UInt8::pair_xor_parts7" &&
  checkTable s "UInt8::byte_inputs" (byteInputsRows F) &&
  checkTable s "UInt8::byte_values" (byteValuesRows F) &&
  checkTable s "UInt8::pair_inputs" (pairInputsRows F) &&
  checkTable s "UInt8::pair_units" (pairUnitsRows F) &&
  checkTable s "UInt8::pair_xors" (pairXorsRows F) &&
  checkTable s "UInt8::pair_xor_parts4" (pairXorParts4Rows F) &&
  checkTable s "UInt8::pair_xor_parts7" (pairXorParts7Rows F)

private theorem mem_zip_map_iff {α β γ : Type*} {f : α → β} {g : α → γ} {l : List α}
    {x : β} {y : γ} :
    (x, y) ∈ (l.map f).zip (l.map g) ↔ ∃ a ∈ l, f a = x ∧ g a = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨a, ha, h1, h2⟩)
      · exact ⟨hd, Or.inl rfl, rfl, rfl⟩
      · exact ⟨a, Or.inr ha, h1, h2⟩
    · rintro ⟨a, rfl | ha, h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨a, ha, h1, h2⟩

private theorem evalExpr_constantExpr_inv {world : World F} {types : Types}
    {locals : Environment F Nat} :
    ∀ (c : Constant F) {h h' : Heap F} {r : SourceValue F},
      EvalExpr world types locals (Generic.constantExpr c) h r h' →
      r = c.toValue ∧ h' = h
  | .field _, _, _, _, ev => by
    simp only [Generic.constantExpr] at ev
    cases ev
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩
  | .tuple xs, h, h', _, ev => by
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
        | nil => intro _ _ _ _ ha; cases ha; exact ⟨rfl, rfl⟩
        | cons y yt ih =>
          intro _ _ _ hrec ha
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
  | .construct n ctor xs, h, h', _, ev => by
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
        | nil => intro _ _ _ _ ha; cases ha; exact ⟨rfl, rfl⟩
        | cons y yt ih =>
          intro _ _ _ hrec ha
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
private theorem hasNoControl_constantExpr :
    ∀ (c : Constant F), hasNoControl (Generic.constantExpr c) = true
  | .field _ => by simp [Generic.constantExpr, hasNoControl]
  | .tuple xs => by
    simp only [Generic.constantExpr, hasNoControl, hasNoControlList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.tuple xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.tuple.sizeOf_spec]; omega
    exact hasNoControl_constantExpr y
  | .construct n ctor xs => by
    simp only [Generic.constantExpr, hasNoControl, hasNoControlList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.construct n ctor xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.construct.sizeOf_spec]; omega
    exact hasNoControl_constantExpr y
  | .ptr _ a => Empty.elim a
termination_by c => sizeOf c

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
      exact False.elim (no_evalExit_of_noControl (hasNoControl_constantExpr row) b)

theorem blake3TablesMatch_of_check {s : Generic.Source F} (h : checkBlake3Tables s = true) :
    Blake3TablesMatch s := by
  simp only [checkBlake3Tables, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact
    { noFn_from_field := checkNoFunction_sound h1
      noFn_range_pair := checkNoFunction_sound h2
      noFn_raw_xor := checkNoFunction_sound h3
      noFn_raw_xor_split4 := checkNoFunction_sound h4
      noFn_raw_xor_split7 := checkNoFunction_sound h5
      map_from_field := checkMap_sound h6
      map_range_pair := checkMap_sound h7
      map_raw_xor := checkMap_sound h8
      map_raw_xor_split4 := checkMap_sound h9
      map_raw_xor_split7 := checkMap_sound h10
      tbl_byte_inputs := checkTable_sound h11
      tbl_byte_values := checkTable_sound h12
      tbl_pair_inputs := checkTable_sound h13
      tbl_pair_units := checkTable_sound h14
      tbl_pair_xors := checkTable_sound h15
      tbl_pair_xor_parts4 := checkTable_sound h16
      tbl_pair_xor_parts7 := checkTable_sound h17 }

/-- Symbolic soundness of the 5 `UInt8` maps required by BLAKE3 (zero table expansion). -/
theorem blake3MapSpec_of_source (s : Generic.Source F) (ht : Blake3TablesMatch s) :
    Blake3MapSpec s.world := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_from_field ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_from_field
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_byte_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_byte_values
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows,
      byteInputsRows, byteValuesRows] at hmem
    obtain ⟨x, hx, hkeq, hreq⟩ := (mem_zip_map_iff (l := List.range 256)).mp hmem
    have hxlt : x < 256 := List.mem_range.mp hx
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨by simp [Constant.toValue, Value.mapAddress, hv], rfl, x, hxlt, hv.symm⟩
  · intro v1 v2 h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_range_pair ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_range_pair
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_pair_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_pair_units
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows,
      pairInputsRows, pairUnitsRows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := (mem_zip_map_iff (l := bytePairInputs)).mp hmem
    simp only [bytePairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hab
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
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows,
      pairInputsRows, pairXorsRows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := (mem_zip_map_iff (l := bytePairInputs)).mp hmem
    simp only [bytePairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hab
    obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨rfl, a', b', ha', hb', hv.1.symm, hv.2.symm, by simp [Constant.toValue, Value.mapAddress]⟩
  · intro v1 v2 h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_raw_xor_split4 ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_raw_xor_split4
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_pair_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_pair_xor_parts4
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows,
      pairInputsRows, pairXorParts4Rows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := (mem_zip_map_iff (l := bytePairInputs)).mp hmem
    simp only [bytePairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hab
    obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨rfl, a', b', ha', hb', hv.1.symm, hv.2.symm, by simp [Constant.toValue, Value.mapAddress]⟩
  · intro v1 v2 h r h' ev
    obtain ⟨row, hlook, rfl, rfl⟩ := evalFn_map_inv s ht.noFn_raw_xor_split7 ev
    obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
    obtain ⟨m0, hm0, hin, hout⟩ := ht.map_raw_xor_split7
    rw [hm0, Option.some.injEq] at hfm; subst hfm
    obtain ⟨ti, hti, hti_rows⟩ := ht.tbl_pair_inputs
    obtain ⟨to_, hto, hto_rows⟩ := ht.tbl_pair_xor_parts7
    simp only [Aiur.Program.mapRows, hin, hout, hti, hto, hti_rows, hto_rows,
      pairInputsRows, pairXorParts7Rows] at hmem
    obtain ⟨⟨a, b⟩, hab, hkeq, hreq⟩ := (mem_zip_map_iff (l := bytePairInputs)).mp hmem
    simp only [bytePairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hab
    obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
    subst hkeq hreq
    have hv := Aiur.Value.toConstant_spec hkey
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    exact ⟨rfl, a', b', ha', hb', hv.1.symm, hv.2.symm, by simp [Constant.toValue, Value.mapAddress]⟩

/-! ### Expected Elaborated ASTs for `UInt8`, `UInt32`, `UInt64`, `Fields`, and `Blake3` -/

/-- All byte constant indices referenced in `Blake3` (`BYTE_0` plus the 31 IV byte constants). -/
def ivByteNums : List Nat :=
  [0, 103, 230, 9, 106, 133, 174, 187, 114, 243, 110, 60, 58, 245, 79, 165,
   127, 82, 14, 81, 140, 104, 5, 155, 171, 217, 131, 31, 25, 205, 224, 91]

/-- The 8 little-endian byte quadruples of BLAKE3's `iv()`. -/
def ivWordBytes : List (Nat × Nat × Nat × Nat) :=
  [(103, 230, 9, 106), (133, 174, 103, 187), (114, 243, 110, 60), (58, 245, 79, 165),
   (127, 82, 14, 81), (140, 104, 5, 155), (171, 217, 131, 31), (25, 205, 224, 91)]

private abbrev gByte (n : Nat) : Aiur.Generic.Expr F :=
  .global s!"UInt8::BYTE_{n}" (some .field)

private abbrev u8f (e : Aiur.Generic.Expr F) : Aiur.Generic.Expr F :=
  .call "UInt8::to_field" (some []) [e]

private def u8ToFieldBody : Aiur.Generic.Expr F := .var "byte"

private def u8FromFieldsBody : Aiur.Generic.Expr F :=
  .letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
    (.tuple [.var "a", .var "b"])

private def u8XorBody : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor" (some []) [.var "a", .var "b"]

private def u8XorSplit4Body : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor_split4" (some []) [.var "a", .var "b"]

private def u8XorSplit7Body : Aiur.Generic.Expr F :=
  .call "UInt8::raw_xor_split7" (some []) [.var "a", .var "b"]

private def u8JoinBody : Aiur.Generic.Expr F :=
  .binary .add (.project (.var "high") 0) (.project (.var "low") 1)

private def u32FromBytesBody : Aiur.Generic.Expr F := .var "bytes"
private def u32ToBytesBody : Aiur.Generic.Expr F := .var "word"
private def u32CompactFieldBody : Aiur.Generic.Expr F := .var "word"

private def u32CompactBody : Aiur.Generic.Expr F :=
  .binary .add
    (.binary .add
      (.binary .add (u8f (.index (.var "word") 0))
        (.binary .mul (.literal (256 : F)) (u8f (.index (.var "word") 1))))
      (.binary .mul (.literal (65536 : F)) (u8f (.index (.var "word") 2))))
    (.binary .mul (.literal (16777216 : F)) (u8f (.index (.var "word") 3)))

private def u32FromFieldsBody : Aiur.Generic.Expr F :=
  .letValue (.tuple [.bind "b0", .bind "b1"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 0, .index (.var "raw") 1]) <|
  .letValue (.tuple [.bind "b2", .bind "b3"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 2, .index (.var "raw") 3]) <|
  .array [.var "b0", .var "b1", .var "b2", .var "b3"]

private def u32WordFieldsExpr (v : String) : Aiur.Generic.Expr F :=
  .array [u8f (.index (.var v) 0), u8f (.index (.var v) 1),
          u8f (.index (.var v) 2), u8f (.index (.var v) 3)]

private def u32AddBody : Aiur.Generic.Expr F :=
  .letValue (.bind "raw")
    (.hint (.array .field 4) (.tuple [u32WordFieldsExpr "a", u32WordFieldsExpr "b"]) "u32.add") <|
  .letValue (.bind "result") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue (.bind "carry")
    (.binary .div
      (.binary .sub
        (.binary .add (.call "UInt32::compact" (some []) [.var "a"])
                      (.call "UInt32::compact" (some []) [.var "b"]))
        (.call "UInt32::compact" (some []) [.var "result"]))
      (.literal (4294967296 : F))) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 add carry", runtimeCheck := false })
      [.binary .mul (.var "carry") (.binary .sub (.var "carry") (.literal (1 : F))),
       .literal (0 : F)]) <|
  .var "result"

private def u32Add3Body : Aiur.Generic.Expr F :=
  .letValue (.bind "raw")
    (.hint (.array .field 4)
      (.tuple [u32WordFieldsExpr "a", u32WordFieldsExpr "b", u32WordFieldsExpr "c"]) "u32.add3") <|
  .letValue (.bind "result") (.call "UInt32::from_fields" (some []) [.var "raw"]) <|
  .letValue (.bind "carry")
    (.binary .div
      (.binary .sub
        (.binary .add
          (.binary .add (.call "UInt32::compact" (some []) [.var "a"])
                        (.call "UInt32::compact" (some []) [.var "b"]))
          (.call "UInt32::compact" (some []) [.var "c"]))
        (.call "UInt32::compact" (some []) [.var "result"]))
      (.literal (4294967296 : F))) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "u32 add3 carry", runtimeCheck := false })
      [.binary .mul
         (.binary .mul (.var "carry") (.binary .sub (.var "carry") (.literal (1 : F))))
         (.binary .sub (.var "carry") (.literal (2 : F))),
       .literal (0 : F)]) <|
  .var "result"

private def u32XorBody : Aiur.Generic.Expr F :=
  .array
    [.call "UInt8::xor" (some []) [.index (.var "a") 0, .index (.var "b") 0],
     .call "UInt8::xor" (some []) [.index (.var "a") 1, .index (.var "b") 1],
     .call "UInt8::xor" (some []) [.index (.var "a") 2, .index (.var "b") 2],
     .call "UInt8::xor" (some []) [.index (.var "a") 3, .index (.var "b") 3]]

private def u32Rotr8Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 1, .index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0]

private def u32Rotr16Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0, .index (.var "a") 1]

private def u32XorRotr7Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array
    [.call "UInt8::join7" (some []) [.var "p0", .var "p1"],
     .call "UInt8::join7" (some []) [.var "p1", .var "p2"],
     .call "UInt8::join7" (some []) [.var "p2", .var "p3"],
     .call "UInt8::join7" (some []) [.var "p3", .var "p0"]]

private def u32XorRotr12Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array
    [.call "UInt8::join4" (some []) [.var "p1", .var "p2"],
     .call "UInt8::join4" (some []) [.var "p2", .var "p3"],
     .call "UInt8::join4" (some []) [.var "p3", .var "p0"],
     .call "UInt8::join4" (some []) [.var "p0", .var "p1"]]

private def u64IsZeroBody : Aiur.Generic.Expr F :=
  .matchValue (.var "x")
    [(.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))), .literal (1 : F)),
     (.wildcard, .literal (0 : F))]

private def wrappingSuccArm (i : Nat) : Aiur.Generic.Expr F :=
  .array ((List.range 8).map fun j =>
    if j < i then gByte 0
    else if j == i then
      .call "UInt8::from_field" (some []) [.binary .add (u8f (.var s!"b{i}")) (.literal (1 : F))]
    else .var s!"b{j}")

private def wrappingSuccMatch : Nat → Aiur.Generic.Expr F
  | 0 => .array (List.replicate 8 (gByte 0))
  | k + 1 =>
    let idx := 8 - (k + 1)
    .matchValue (u8f (.var s!"b{idx}"))
      [(.literal (255 : F), wrappingSuccMatch k),
       (.wildcard, wrappingSuccArm idx)]

private def u64WrappingSuccBody : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                     .bind "b4", .bind "b5", .bind "b6", .bind "b7"]) (.var "bytes")
    (wrappingSuccMatch 8)

private def fieldsIsZeroBody : Aiur.Generic.Expr F :=
  .matchValue (.var "x") [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))]

private def blake3IvBody : Aiur.Generic.Expr F :=
  .array (ivWordBytes.map fun (a, b, c, d) =>
    .call "UInt32::from_bytes" (some []) [.array [gByte a, gByte b, gByte c, gByte d]])

private def blake3GFunctionBody : Aiur.Generic.Expr F :=
  .letValue (.bind "a") (.call "UInt32::add3" (some []) [.var "a", .var "b", .var "x"]) <|
  .letValue (.bind "d") (.call "UInt32::rotr16" (some []) [.call "UInt32::xor" (some []) [.var "d", .var "a"]]) <|
  .letValue (.bind "c") (.call "UInt32::add" (some []) [.var "c", .var "d"]) <|
  .letValue (.bind "b") (.call "UInt32::xor_rotr12" (some []) [.var "b", .var "c"]) <|
  .letValue (.bind "a") (.call "UInt32::add3" (some []) [.var "a", .var "b", .var "y"]) <|
  .letValue (.bind "d") (.call "UInt32::rotr8" (some []) [.call "UInt32::xor" (some []) [.var "d", .var "a"]]) <|
  .letValue (.bind "c") (.call "UInt32::add" (some []) [.var "c", .var "d"]) <|
  .letValue (.bind "b") (.call "UInt32::xor_rotr7" (some []) [.var "b", .var "c"]) <|
  .array [.var "a", .var "b", .var "c", .var "d"]

/-- One `g` step inside `Blake3::compress_inner_j`. -/
def gStep (a b c d : Fin 16) (jx jy : Nat) (rest : Aiur.Generic.Expr F) : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "a", .bind "b", .bind "c", .bind "d"])
    (.call "Blake3::g_function" (some [])
      [.index (.var "state") a.val, .index (.var "state") b.val,
       .index (.var "state") c.val, .index (.var "state") d.val,
       .index (.var "state") (16 + jx), .index (.var "state") (16 + jy)]) <|
  .letValue (.bind "state") (.update [[.index a.val 32]] [.var "state", .var "a"]) <|
  .letValue (.bind "state") (.update [[.index b.val 32]] [.var "state", .var "b"]) <|
  .letValue (.bind "state") (.update [[.index c.val 32]] [.var "state", .var "c"]) <|
  .letValue (.bind "state") (.update [[.index d.val 32]] [.var "state", .var "d"]) <|
  rest

private def blake3CijBody : Aiur.Generic.Expr F :=
  gStep 0 4 8 12 0 1 <|
  gStep 1 5 9 13 2 3 <|
  gStep 2 6 10 14 4 5 <|
  gStep 3 7 11 15 6 7 <|
  gStep 0 5 10 15 8 9 <|
  gStep 1 6 11 12 10 11 <|
  gStep 2 7 8 13 12 13 <|
  gStep 3 4 9 14 14 15 <|
  .var "state"

private def blake3CompressInitBody : Aiur.Generic.Expr F :=
  .letValue (.bind "IV") (.call "Blake3::iv" (some []) []) <|
  .letValue (.bind "IV0") (.index (.var "IV") 0) <|
  .letValue (.bind "IV1") (.index (.var "IV") 1) <|
  .letValue (.bind "IV2") (.index (.var "IV") 2) <|
  .letValue (.bind "IV3") (.index (.var "IV") 3) <|
  .letValue (.bind "counter_low")
    (.call "UInt32::from_bytes" (some []) [.slice (.var "counter") 0 (some 4)]) <|
  .letValue (.bind "counter_high")
    (.call "UInt32::from_bytes" (some []) [.slice (.var "counter") 4 (some 8)]) <|
  .letValue (.bind "block_len_u32")
    (.call "UInt32::from_bytes" (some [])
      [.array [.call "UInt8::from_field" (some []) [.var "block_len"], gByte 0, gByte 0, gByte 0]]) <|
  .letValue (.bind "flags_u32")
    (.call "UInt32::from_bytes" (some [])
      [.array [.call "UInt8::from_field" (some []) [.var "flags"], gByte 0, gByte 0, gByte 0]]) <|
  .letValue (.bind "state")
    (.builtin (.ascribe (.array (.array .field 4) 32))
      [.array
        ((List.range 8).map (fun i => .index (.var "chaining_value") i) ++
         [.var "IV0", .var "IV1", .var "IV2", .var "IV3",
          .var "counter_low", .var "counter_high", .var "block_len_u32", .var "flags_u32"] ++
         (List.range 16).map (fun i => .index (.var "block_words") i))]) <|
  .call "Blake3::compress" (some []) [.literal (0 : F), .var "state"]

/-- The 16 message-word permutation index pairs `(dst_slot, src_slot)` in `Blake3::compress`. -/
def permutePairs : List (Fin 16 × Fin 16) :=
  [(0, 2), (1, 6), (2, 3), (3, 10), (4, 7), (5, 0), (6, 4), (7, 13),
   (8, 1), (9, 11), (10, 12), (11, 5), (12, 9), (13, 14), (14, 15), (15, 8)]

private def permuteExpr (dst src : String) :
    List (Fin 16 × Fin 16) → Aiur.Generic.Expr F → Aiur.Generic.Expr F
  | [], rest => rest
  | (i, j) :: ps, rest =>
    .letValue (.bind dst)
      (.update [[.index (16 + i.val) 32]] [.var dst, .index (.var src) (16 + j.val)])
      (permuteExpr dst src ps rest)

private def finalizeOutputsExpr : Nat → Aiur.Generic.Expr F
  | 0 => .array ((List.range 8).map fun i => .var s!"output{i}")
  | k + 1 =>
    let idx := 8 - (k + 1)
    .letValue (.bind s!"output{idx}")
      (.call "UInt32::xor" (some []) [.index (.var "s1") idx, .index (.var "s1") (idx + 8)])
      (finalizeOutputsExpr k)

private def blake3CompressBody : Aiur.Generic.Expr F :=
  .letValue (.bind "s1") (.call "Blake3::compress_inner_j" (some []) [.var "state"]) <|
  .matchValue (.var "stage")
    [(.literal (3 : F), finalizeOutputsExpr 8),
     (.wildcard,
       permuteExpr "s1" "state" permutePairs <|
       .letValue (.bind "s2") (.call "Blake3::compress_inner_j" (some []) [.var "s1"]) <|
       permuteExpr "s2" "s1" permutePairs <|
       .call "Blake3::compress" (some [])
         [.binary .add (.var "stage") (.literal (1 : F)), .var "s2"])]

/-- The 64 byte binder names `b0 .. b63` used in `Blake3::take_block` and `bytes_to_block`. -/
def bNames : List String := (List.range 64).map fun i => s!"b{i}"

/-- Reversed byte binder names `b63 .. b0`. -/
def bNamesRev : List String := bNames.reverse

private def fbCalls : List String → List (Aiur.Generic.Expr F)
  | a :: b :: c :: d :: rest =>
    .call "UInt32::from_bytes" (some []) [.array [.var a, .var b, .var c, .var d]] :: fbCalls rest
  | _ => []

private def nilPat : Aiur.Generic.Pattern F :=
  .construct (.named "Lists::Node" [.field]) "Nil" []

private def consPat (b l : String) : Aiur.Generic.Pattern F :=
  .construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .bind l]

private def conswPat (b : String) : Aiur.Generic.Pattern F :=
  .construct (.named "Lists::Node" [.field]) "Cons" [.bind b, .wildcard]

private def tbFull : Aiur.Generic.Expr F :=
  .construct "Blake3::BlockRead" (some []) "Full" [.array (fbCalls bNames), .var "l"]

private def tbFrom : List String → String → Aiur.Generic.Expr F
  | [], _ => tbFull
  | b :: bs, scr =>
    .matchValue (.load (.var scr))
      [(nilPat, .construct "Blake3::BlockRead" (some []) "Short" []),
       (consPat b "l", tbFrom bs "l")]

private def blake3TakeBlockBody : Aiur.Generic.Expr F := tbFrom bNames "input"

private def bbFrom : List String → String → Aiur.Generic.Expr F
  | [], _ => .array (fbCalls bNames)
  | b :: bs, scr =>
    match bs with
    | [] => .letValue (conswPat b) (.load (.var scr)) (.array (fbCalls bNames))
    | _ :: _ => .letValue (consPat b "l") (.load (.var scr)) (bbFrom bs "l")

private def blake3BytesToBlockBody : Aiur.Generic.Expr F := bbFrom bNamesRev "byte_acc"

private def blake3PadBlockBody : Aiur.Generic.Expr F :=
  .matchValue (.var "n")
    [(.literal (0 : F), .var "acc"),
     (.wildcard,
       .call "Blake3::pad_block" (some [])
         [.store (.construct "Lists::Node" (some [.field]) "Cons" [gByte 0, .var "acc"]),
          .binary .sub (.var "n") (.literal (1 : F))])]

private def blake3FinishArm1 : Aiur.Generic.Expr F :=
  .matchValue (.load (.var "chunk_count"))
    [(.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))),
       .letValue (.bind "flags")
         (.binary .add (.binary .add (.var "ROOT") (.var "CHUNK_START")) (.var "CHUNK_END"))
         (.store (.construct "Blake3::LayerNode" (some []) "Push"
           [.var "layer",
            .call "Blake3::compress_init" (some [])
              [.load (.var "block_digest"),
               .repeat (.global "UInt32::ZERO" (some (.array .field 4))) 16,
               .load (.var "chunk_count"), .literal (0 : F), .var "flags"]]))),
     (.wildcard, .var "layer")]

private def blake3FinishArm2 : Aiur.Generic.Expr F :=
  .store (.construct "Blake3::LayerNode" (some []) "Push"
    [.var "layer", .load (.var "block_digest")])

private def blake3FinishArm3 : Aiur.Generic.Expr F :=
  .letValue (.bind "flags")
    (.binary .add
      (.binary .add (.var "CHUNK_END")
        (.binary .mul (.call "UInt64::is_zero" (some []) [.load (.var "chunk_count")]) (.var "ROOT")))
      (.binary .mul
        (.call "Fields::is_zero" (some []) [.binary .sub (.var "chunk_index") (.var "block_index")])
        (.var "CHUNK_START"))) <|
  .letValue (.bind "block")
    (.call "Blake3::bytes_to_block" (some [])
      [.call "Blake3::pad_block" (some [])
        [.var "byte_acc", .binary .sub (.literal (64 : F)) (.var "block_index")]]) <|
  .store (.construct "Blake3::LayerNode" (some []) "Push"
    [.var "layer",
     .call "Blake3::compress_init" (some [])
       [.load (.var "block_digest"), .var "block", .load (.var "chunk_count"),
        .var "block_index", .var "flags"]])

private def blake3FinishBody : Aiur.Generic.Expr F :=
  .letValue (.bind "CHUNK_START") (.literal (1 : F)) <|
  .letValue (.bind "CHUNK_END") (.literal (2 : F)) <|
  .letValue (.bind "ROOT") (.literal (8 : F)) <|
  .matchValue (.tuple [.var "block_index", .var "chunk_index"])
    [(.tuple [.literal (0 : F), .literal (0 : F)], blake3FinishArm1),
     (.tuple [.literal (0 : F), .wildcard], blake3FinishArm2),
     (.tuple [.wildcard, .wildcard], blake3FinishArm3)]

private def blake3CompressChunksBody : Aiur.Generic.Expr F :=
  .matchValue (.load (.var "input"))
    [(nilPat,
       .call "Blake3::finish" (some [])
         [.var "byte_acc", .var "block_index", .var "chunk_index",
          .var "chunk_count", .var "block_digest", .var "layer"]),
     (consPat "head" "input",
       .letValue (.bind "byte_acc")
         (.store (.construct "Lists::Node" (some [.field]) "Cons" [.var "head", .var "byte_acc"])) <|
       .matchValue (.var "block_index")
         [(.literal (63 : F),
            .call "Blake3::compress_block" (some [])
              [.var "input", .var "byte_acc", .var "chunk_index",
               .var "chunk_count", .var "block_digest", .var "layer"]),
          (.wildcard,
            .call "Blake3::compress_chunks" (some [])
              [.var "input", .var "byte_acc",
               .binary .add (.var "block_index") (.literal (1 : F)),
               .binary .add (.var "chunk_index") (.literal (1 : F)),
               .var "chunk_count", .var "block_digest", .var "layer"])])]

private def blake3HashBlocksBody : Aiur.Generic.Expr F :=
  .matchValue (.call "Blake3::take_block" (some []) [.var "input"])
    [(.construct (.named "Blake3::BlockRead" []) "Short" [],
       .call "Blake3::compress_chunks" (some [])
         [.var "input",
          .store (.construct "Lists::Node" (some [.field]) "Nil" []),
          .literal (0 : F),
          .binary .mul (.literal (64 : F)) (.var "block_no"),
          .var "chunk_count", .var "cv", .var "layer"]),
     (.construct (.named "Blake3::BlockRead" []) "Full" [.bind "block", .bind "rest"],
       .letValue (.bind "CHUNK_START") (.literal (1 : F)) <|
       .letValue (.bind "CHUNK_END") (.literal (2 : F)) <|
       .letValue (.bind "ROOT") (.literal (8 : F)) <|
       .letValue (.bind "empty")
         (.matchValue (.load (.var "rest"))
           [(nilPat, .literal (1 : F)), (.wildcard, .literal (0 : F))]) <|
       .letValue (.bind "at15")
         (.call "Fields::is_zero" (some []) [.binary .sub (.var "block_no") (.literal (15 : F))]) <|
       .letValue (.bind "start_flag")
         (.call "Fields::is_zero" (some []) [.var "block_no"]) <|
       .letValue (.bind "end_flag")
         (.binary .sub (.binary .add (.var "empty") (.var "at15"))
                       (.binary .mul (.var "empty") (.var "at15"))) <|
       .letValue (.bind "root_flag")
         (.binary .mul (.var "empty")
           (.call "UInt64::is_zero" (some []) [.load (.var "chunk_count")])) <|
       .letValue (.bind "flags")
         (.binary .add
           (.binary .add (.binary .mul (.var "CHUNK_START") (.var "start_flag"))
                         (.binary .mul (.var "CHUNK_END") (.var "end_flag")))
           (.binary .mul (.var "ROOT") (.var "root_flag"))) <|
       .letValue (.bind "digest")
         (.call "Blake3::compress_init" (some [])
           [.load (.var "cv"), .var "block", .load (.var "chunk_count"),
            .literal (64 : F), .var "flags"]) <|
       .matchValue (.tuple [.var "empty", .var "at15"])
         [(.tuple [.literal (1 : F), .wildcard],
            .store (.construct "Blake3::LayerNode" (some []) "Push" [.var "layer", .var "digest"])),
          (.tuple [.wildcard, .literal (1 : F)],
            .letValue (.bind "IV") (.call "Blake3::iv" (some []) []) <|
            .call "Blake3::hash_blocks" (some [])
              [.var "rest", .literal (0 : F),
               .store (.call "UInt64::wrapping_succ" (some []) [.load (.var "chunk_count")]),
               .store (.var "IV"),
               .store (.construct "Blake3::LayerNode" (some []) "Push" [.var "layer", .var "digest"])]),
          (.tuple [.wildcard, .wildcard],
            .call "Blake3::hash_blocks" (some [])
              [.var "rest",
               .binary .add (.var "block_no") (.literal (1 : F)),
               .var "chunk_count",
               .store (.var "digest"),
               .var "layer"])])]

private def blake3NextLayerBody : Aiur.Generic.Expr F :=
  .matchValue (.load (.var "layer"))
    [(.construct (.named "Blake3::LayerNode" []) "Nil" [],
       .tuple [.construct "Blake3::MaybeDigest" (some []) "Some" [.var "digest"], .var "layer"]),
     (.construct (.named "Blake3::LayerNode" []) "Push" [.bind "layer", .bind "other"],
       .letValue (.tuple [.bind "last", .bind "new_layer"])
         (.call "Blake3::next_layer" (some []) [.var "layer", .var "other", .literal (0 : F)]) <|
       .matchValue (.var "last")
         [(.construct (.named "Blake3::MaybeDigest" []) "None" [],
            .tuple [.construct "Blake3::MaybeDigest" (some []) "Some" [.var "digest"], .var "new_layer"]),
          (.construct (.named "Blake3::MaybeDigest" []) "Some" [.bind "last"],
            .letValue (.bind "PARENT") (.literal (4 : F)) <|
            .letValue (.bind "ROOT") (.literal (8 : F)) <|
            .letValue (.bind "IV") (.call "Blake3::iv" (some []) []) <|
            .letValue (.array [.bind "x0", .bind "x1", .bind "x2", .bind "x3",
                               .bind "x4", .bind "x5", .bind "x6", .bind "x7"]) (.var "last") <|
            .letValue (.array [.bind "x8", .bind "x9", .bind "x10", .bind "x11",
                               .bind "x12", .bind "x13", .bind "x14", .bind "x15"]) (.var "digest") <|
            .letValue (.bind "blocks")
              (.array ((List.range 16).map fun i => .var s!"x{i}")) <|
            .matchValue (.load (.var "new_layer"))
              [(.construct (.named "Blake3::LayerNode" []) "Nil" [],
                 .letValue (.bind "flags")
                   (.binary .add (.var "PARENT") (.binary .mul (.var "ROOT") (.var "root"))) <|
                 .letValue (.bind "digest")
                   (.call "Blake3::compress_init" (some [])
                     [.var "IV", .var "blocks", .repeat (gByte 0) 8, .literal (64 : F), .var "flags"]) <|
                 .tuple [.construct "Blake3::MaybeDigest" (some []) "None" [],
                         .store (.construct "Blake3::LayerNode" (some []) "Push"
                           [.var "new_layer", .var "digest"])]),
               (.wildcard,
                 .letValue (.bind "flags") (.var "PARENT") <|
                 .letValue (.bind "digest")
                   (.call "Blake3::compress_init" (some [])
                     [.var "IV", .var "blocks", .repeat (gByte 0) 8, .literal (64 : F), .var "flags"]) <|
                 .tuple [.construct "Blake3::MaybeDigest" (some []) "None" [],
                         .store (.construct "Blake3::LayerNode" (some []) "Push"
                           [.var "new_layer", .var "digest"])])])])]

private def blake3CompressLayerBody : Aiur.Generic.Expr F :=
  .letValue (.construct (.named "Blake3::LayerNode" []) "Push" [.bind "rest", .bind "digest"])
    (.load (.var "layer")) <|
  .matchValue (.load (.var "rest"))
    [(.construct (.named "Blake3::LayerNode" []) "Nil" [], .var "digest"),
     (.wildcard,
       .letValue (.tuple [.bind "last", .bind "new_merkle"])
         (.call "Blake3::next_layer" (some []) [.var "rest", .var "digest", .literal (1 : F)]) <|
       .matchValue (.var "last")
         [(.construct (.named "Blake3::MaybeDigest" []) "None" [],
            .call "Blake3::compress_layer" (some []) [.var "new_merkle"]),
          (.construct (.named "Blake3::MaybeDigest" []) "Some" [.bind "last"],
            .call "Blake3::compress_layer" (some [])
              [.store (.construct "Blake3::LayerNode" (some []) "Push"
                [.var "new_merkle", .var "last"])])])]

private def blake3HashBody : Aiur.Generic.Expr F :=
  .letValue (.bind "IV") (.call "Blake3::iv" (some []) []) <|
  .call "Blake3::compress_layer" (some [])
    [.call "Blake3::hash_blocks" (some [])
      [.var "input", .literal (0 : F),
       .store (.repeat (gByte 0) 8),
       .store (.var "IV"),
       .store (.construct "Blake3::LayerNode" (some []) "Nil" [])]]

private def digestBytesGo : Nat → Aiur.Generic.Expr F
  | 0 => .array ((List.range 32).map fun i => .index (.var s!"b{i / 4}") (i % 4))
  | k + 1 =>
    let idx := 8 - (k + 1)
    .letValue (.bind s!"b{idx}")
      (.call "UInt32::to_bytes" (some []) [.index (.var "digest") idx])
      (digestBytesGo k)

private def blake3DigestBytesBody : Aiur.Generic.Expr F := digestBytesGo 8

private def blake3AddressToFieldsBody : Aiur.Generic.Expr F :=
  .array ((List.range 32).map fun i => u8f (.index (.var "bytes") i))

private def addrFromFieldsGo : Nat → Aiur.Generic.Expr F
  | 0 => .array ((List.range 32).map fun i => .var s!"b{i}")
  | k + 1 =>
    let idx := 16 - (k + 1)
    let i0 := 2 * idx
    let i1 := 2 * idx + 1
    .letValue (.tuple [.bind s!"b{i0}", .bind s!"b{i1}"])
      (.call "UInt8::from_fields" (some []) [.index (.var "raw") i0, .index (.var "raw") i1])
      (addrFromFieldsGo k)

private def blake3AddressFromFieldsBody : Aiur.Generic.Expr F := addrFromFieldsGo 16

private def blake3VerifyBytesAgainstBody : Aiur.Generic.Expr F :=
  .letValue (.bind "h") (.call "Blake3::hash" (some []) [.var "bytes"]) <|
  .letValue .wildcard
    (.builtin (.assertEq
      { message := some "hash of the supplied bytes != the address they were fetched under",
        runtimeCheck := true })
      [.call "Blake3::address_to_fields" (some [])
         [.call "Blake3::digest_bytes" (some []) [.var "h"]],
       .call "Blake3::address_to_fields" (some []) [.var "expected"]]) <|
  .tuple []

private def blake3BytesToAddrBody : Aiur.Generic.Expr F :=
  .letValue (.bind "h") (.call "Blake3::hash" (some []) [.var "bytes"]) <|
  .store (.call "Blake3::digest_bytes" (some []) [.var "h"])

private def blake3PackWordBody : Aiur.Generic.Expr F :=
  .call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "w"]]

private def blake3PackDigestBody : Aiur.Generic.Expr F :=
  .array ((List.range 8).map fun i =>
    .call "Blake3::pack_word" (some []) [.index (.var "h") i])

/-- World hypothesis for a Formal Aiur world containing `Aiur.Library.Blake3`
(with its `UInt8`, `UInt32`, `UInt64`, and `Fields` dependencies). -/
structure Blake3LibraryWorld (world : World F) : Prop where
  maps : Blake3MapSpec world
  constDepth_pos : 0 < world.constDepth
  const_bytes : ∀ n ∈ ivByteNums, world.constant s!"UInt8::BYTE_{n}" .field = .ok (.literal (n : F))
  const_u32_zero : world.constant "UInt32::ZERO" (.array .field 4) =
    .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4)
  u8_to_field : WorldHasFn world "UInt8::to_field" ["byte"] u8ToFieldBody
  u8_from_fields : WorldHasFn world "UInt8::from_fields" ["a", "b"] u8FromFieldsBody
  u8_xor : WorldHasFn world "UInt8::xor" ["a", "b"] u8XorBody
  u8_xor_split4 : WorldHasFn world "UInt8::xor_split4" ["a", "b"] u8XorSplit4Body
  u8_xor_split7 : WorldHasFn world "UInt8::xor_split7" ["a", "b"] u8XorSplit7Body
  u8_join4 : WorldHasFn world "UInt8::join4" ["high", "low"] u8JoinBody
  u8_join7 : WorldHasFn world "UInt8::join7" ["high", "low"] u8JoinBody
  u32_from_bytes : WorldHasFn world "UInt32::from_bytes" ["bytes"] u32FromBytesBody
  u32_to_bytes : WorldHasFn world "UInt32::to_bytes" ["word"] u32ToBytesBody
  u32_compact_field : WorldHasFn world "UInt32::compact_field" ["word"] u32CompactFieldBody
  u32_compact : WorldHasFn world "UInt32::compact" ["word"] u32CompactBody
  u32_from_fields : WorldHasFn world "UInt32::from_fields" ["raw"] u32FromFieldsBody
  u32_add : WorldHasFn world "UInt32::add" ["a", "b"] u32AddBody
  u32_add3 : WorldHasFn world "UInt32::add3" ["a", "b", "c"] u32Add3Body
  u32_xor : WorldHasFn world "UInt32::xor" ["a", "b"] u32XorBody
  u32_rotr8 : WorldHasFn world "UInt32::rotr8" ["a"] u32Rotr8Body
  u32_rotr16 : WorldHasFn world "UInt32::rotr16" ["a"] u32Rotr16Body
  u32_xor_rotr7 : WorldHasFn world "UInt32::xor_rotr7" ["a", "b"] u32XorRotr7Body
  u32_xor_rotr12 : WorldHasFn world "UInt32::xor_rotr12" ["a", "b"] u32XorRotr12Body
  u64_is_zero : WorldHasFn world "UInt64::is_zero" ["x"] u64IsZeroBody
  u64_wrapping_succ : WorldHasFn world "UInt64::wrapping_succ" ["bytes"] u64WrappingSuccBody
  fields_is_zero : WorldHasFn world "Fields::is_zero" ["x"] fieldsIsZeroBody
  blake3_iv : WorldHasFn world "Blake3::iv" [] blake3IvBody
  blake3_g_function : WorldHasFn world "Blake3::g_function" ["a", "b", "c", "d", "x", "y"] blake3GFunctionBody
  blake3_compress_inner_j : WorldHasFn world "Blake3::compress_inner_j" ["state"] blake3CijBody
  blake3_compress_init : WorldHasFn world "Blake3::compress_init"
    ["chaining_value", "block_words", "counter", "block_len", "flags"] blake3CompressInitBody
  blake3_compress : WorldHasFn world "Blake3::compress" ["stage", "state"] blake3CompressBody
  blake3_take_block : WorldHasFn world "Blake3::take_block" ["input"] blake3TakeBlockBody
  blake3_bytes_to_block : WorldHasFn world "Blake3::bytes_to_block" ["byte_acc"] blake3BytesToBlockBody
  blake3_pad_block : WorldHasFn world "Blake3::pad_block" ["acc", "n"] blake3PadBlockBody
  blake3_finish : WorldHasFn world "Blake3::finish"
    ["byte_acc", "block_index", "chunk_index", "chunk_count", "block_digest", "layer"] blake3FinishBody
  blake3_compress_chunks : WorldHasFn world "Blake3::compress_chunks"
    ["input", "byte_acc", "block_index", "chunk_index", "chunk_count", "block_digest", "layer"] blake3CompressChunksBody
  blake3_hash_blocks : WorldHasFn world "Blake3::hash_blocks"
    ["input", "block_no", "chunk_count", "cv", "layer"] blake3HashBlocksBody
  blake3_next_layer : WorldHasFn world "Blake3::next_layer"
    ["layer", "digest", "root"] blake3NextLayerBody
  blake3_compress_layer : WorldHasFn world "Blake3::compress_layer" ["layer"] blake3CompressLayerBody
  blake3_hash : WorldHasFn world "Blake3::hash" ["input"] blake3HashBody
  blake3_digest_bytes : WorldHasFn world "Blake3::digest_bytes" ["digest"] blake3DigestBytesBody
  blake3_address_to_fields : WorldHasFn world "Blake3::address_to_fields" ["bytes"] blake3AddressToFieldsBody
  blake3_address_from_fields : WorldHasFn world "Blake3::address_from_fields" ["raw"] blake3AddressFromFieldsBody
  blake3_verify_bytes_against : WorldHasFn world "Blake3::verify_bytes_against"
    ["bytes", "expected"] blake3VerifyBytesAgainstBody
  blake3_bytes_to_addr : WorldHasFn world "Blake3::bytes_to_addr" ["bytes"] blake3BytesToAddrBody
  blake3_pack_word : WorldHasFn world "Blake3::pack_word" ["w"] blake3PackWordBody
  blake3_pack_digest : WorldHasFn world "Blake3::pack_digest" ["h"] blake3PackDigestBody

/-- Computable checker verifying that `s` contains all constants and exact elaborated
functions required by `Blake3LibraryWorld`. -/
def checkBlake3Functions (s : Generic.Source F) : Bool :=
  let checkFn (nm : String) (ps : List String) (body : Aiur.Generic.Expr F) : Bool :=
    match s.program.findFunction? nm with
    | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == ps) && (f.body == body)
    | none => false
  let checkBytes : Bool :=
    ivByteNums.all fun n =>
      match elaborateConst s.program s!"UInt8::BYTE_{n}" .field with
      | .ok p => p == .literal (n : F)
      | .error _ => false
  let checkU32Zero : Bool :=
    match elaborateConst s.program "UInt32::ZERO" (.array .field 4) with
    | .ok p => p == .repeat (.global "UInt8::BYTE_0" (some .field)) 4
    | .error _ => false
  checkBytes && checkU32Zero &&
  checkFn "UInt8::to_field" ["byte"] u8ToFieldBody &&
  checkFn "UInt8::from_fields" ["a", "b"] u8FromFieldsBody &&
  checkFn "UInt8::xor" ["a", "b"] u8XorBody &&
  checkFn "UInt8::xor_split4" ["a", "b"] u8XorSplit4Body &&
  checkFn "UInt8::xor_split7" ["a", "b"] u8XorSplit7Body &&
  checkFn "UInt8::join4" ["high", "low"] u8JoinBody &&
  checkFn "UInt8::join7" ["high", "low"] u8JoinBody &&
  checkFn "UInt32::from_bytes" ["bytes"] u32FromBytesBody &&
  checkFn "UInt32::to_bytes" ["word"] u32ToBytesBody &&
  checkFn "UInt32::compact_field" ["word"] u32CompactFieldBody &&
  checkFn "UInt32::compact" ["word"] u32CompactBody &&
  checkFn "UInt32::from_fields" ["raw"] u32FromFieldsBody &&
  checkFn "UInt32::add" ["a", "b"] u32AddBody &&
  checkFn "UInt32::add3" ["a", "b", "c"] u32Add3Body &&
  checkFn "UInt32::xor" ["a", "b"] u32XorBody &&
  checkFn "UInt32::rotr8" ["a"] u32Rotr8Body &&
  checkFn "UInt32::rotr16" ["a"] u32Rotr16Body &&
  checkFn "UInt32::xor_rotr7" ["a", "b"] u32XorRotr7Body &&
  checkFn "UInt32::xor_rotr12" ["a", "b"] u32XorRotr12Body &&
  checkFn "UInt64::is_zero" ["x"] u64IsZeroBody &&
  checkFn "UInt64::wrapping_succ" ["bytes"] u64WrappingSuccBody &&
  checkFn "Fields::is_zero" ["x"] fieldsIsZeroBody &&
  checkFn "Blake3::iv" [] blake3IvBody &&
  checkFn "Blake3::g_function" ["a", "b", "c", "d", "x", "y"] blake3GFunctionBody &&
  checkFn "Blake3::compress_inner_j" ["state"] blake3CijBody &&
  checkFn "Blake3::compress_init"
    ["chaining_value", "block_words", "counter", "block_len", "flags"] blake3CompressInitBody &&
  checkFn "Blake3::compress" ["stage", "state"] blake3CompressBody &&
  checkFn "Blake3::take_block" ["input"] blake3TakeBlockBody &&
  checkFn "Blake3::bytes_to_block" ["byte_acc"] blake3BytesToBlockBody &&
  checkFn "Blake3::pad_block" ["acc", "n"] blake3PadBlockBody &&
  checkFn "Blake3::finish"
    ["byte_acc", "block_index", "chunk_index", "chunk_count", "block_digest", "layer"] blake3FinishBody &&
  checkFn "Blake3::compress_chunks"
    ["input", "byte_acc", "block_index", "chunk_index", "chunk_count", "block_digest", "layer"] blake3CompressChunksBody &&
  checkFn "Blake3::hash_blocks"
    ["input", "block_no", "chunk_count", "cv", "layer"] blake3HashBlocksBody &&
  checkFn "Blake3::next_layer" ["layer", "digest", "root"] blake3NextLayerBody &&
  checkFn "Blake3::compress_layer" ["layer"] blake3CompressLayerBody &&
  checkFn "Blake3::hash" ["input"] blake3HashBody &&
  checkFn "Blake3::digest_bytes" ["digest"] blake3DigestBytesBody &&
  checkFn "Blake3::address_to_fields" ["bytes"] blake3AddressToFieldsBody &&
  checkFn "Blake3::address_from_fields" ["raw"] blake3AddressFromFieldsBody &&
  checkFn "Blake3::verify_bytes_against" ["bytes", "expected"] blake3VerifyBytesAgainstBody &&
  checkFn "Blake3::bytes_to_addr" ["bytes"] blake3BytesToAddrBody &&
  checkFn "Blake3::pack_word" ["w"] blake3PackWordBody &&
  checkFn "Blake3::pack_digest" ["h"] blake3PackDigestBody

/-- **Complete executable world check for `Aiur.Library.Blake3`**: checks both the
5 `UInt8` static maps / 7 backing tables and all 43 elaborated library functions & constants. -/
def checkBlake3World (s : Generic.Source F) : Bool :=
  checkBlake3Tables s && checkBlake3Functions s

local macro "b3_lib_name" : tactic => `(tactic| first | decide | simp)

/-- **Soundness of `checkBlake3World`**: any prepared `Generic.Source` passing
`checkBlake3World` satisfies `Blake3LibraryWorld s.world`. -/
theorem blake3LibraryWorld_of_check {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3LibraryWorld s.world := by
  simp only [checkBlake3World, Bool.and_eq_true] at h
  obtain ⟨htables, hfuncs⟩ := h
  have tables := blake3TablesMatch_of_check htables
  simp only [checkBlake3Functions, Bool.and_eq_true, and_assoc] at hfuncs
  obtain ⟨hBytes, hU32Z,
    h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33,
    h34, h35, h36, h37, h38, h39, h40, h41, h42, h43⟩ := hfuncs
  have constBytes : ∀ n ∈ ivByteNums,
      s.world.constant s!"UInt8::BYTE_{n}" .field = .ok (.literal (n : F)) := by
    intro n hn
    have hall := List.all_eq_true.mp hBytes n hn
    cases hc : elaborateConst s.program s!"UInt8::BYTE_{n}" .field with
    | error _ => rw [hc] at hall; simp at hall
    | ok p =>
      rw [hc] at hall
      simp only [beq_iff_eq] at hall
      rw [Generic.Source.world, sourceWorld]
      simp only [hc, hall, Except.mapError]
  have constU32Zero : s.world.constant "UInt32::ZERO" (.array .field 4) =
      .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) := by
    cases hc : elaborateConst s.program "UInt32::ZERO" (.array .field 4) with
    | error _ => rw [hc] at hU32Z; simp at hU32Z
    | ok p =>
      rw [hc] at hU32Z
      simp only [beq_iff_eq] at hU32Z
      simp [Generic.Source.world, sourceWorld, hc, hU32Z, Except.mapError]
  exact
    { maps := blake3MapSpec_of_source s tables
      constDepth_pos := Nat.succ_pos _
      const_bytes := constBytes
      const_u32_zero := constU32Zero
      u8_to_field := worldHasFn_of_check s (by b3_lib_name) h1
      u8_from_fields := worldHasFn_of_check s (by b3_lib_name) h2
      u8_xor := worldHasFn_of_check s (by b3_lib_name) h3
      u8_xor_split4 := worldHasFn_of_check s (by b3_lib_name) h4
      u8_xor_split7 := worldHasFn_of_check s (by b3_lib_name) h5
      u8_join4 := worldHasFn_of_check s (by b3_lib_name) h6
      u8_join7 := worldHasFn_of_check s (by b3_lib_name) h7
      u32_from_bytes := worldHasFn_of_check s (by b3_lib_name) h8
      u32_to_bytes := worldHasFn_of_check s (by b3_lib_name) h9
      u32_compact_field := worldHasFn_of_check s (by b3_lib_name) h10
      u32_compact := worldHasFn_of_check s (by b3_lib_name) h11
      u32_from_fields := worldHasFn_of_check s (by b3_lib_name) h12
      u32_add := worldHasFn_of_check s (by b3_lib_name) h13
      u32_add3 := worldHasFn_of_check s (by b3_lib_name) h14
      u32_xor := worldHasFn_of_check s (by b3_lib_name) h15
      u32_rotr8 := worldHasFn_of_check s (by b3_lib_name) h16
      u32_rotr16 := worldHasFn_of_check s (by b3_lib_name) h17
      u32_xor_rotr7 := worldHasFn_of_check s (by b3_lib_name) h18
      u32_xor_rotr12 := worldHasFn_of_check s (by b3_lib_name) h19
      u64_is_zero := worldHasFn_of_check s (by b3_lib_name) h20
      u64_wrapping_succ := worldHasFn_of_check s (by b3_lib_name) h21
      fields_is_zero := worldHasFn_of_check s (by b3_lib_name) h22
      blake3_iv := worldHasFn_of_check s (by b3_lib_name) h23
      blake3_g_function := worldHasFn_of_check s (by b3_lib_name) h24
      blake3_compress_inner_j := worldHasFn_of_check s (by b3_lib_name) h25
      blake3_compress_init := worldHasFn_of_check s (by b3_lib_name) h26
      blake3_compress := worldHasFn_of_check s (by b3_lib_name) h27
      blake3_take_block := worldHasFn_of_check s (by b3_lib_name) h28
      blake3_bytes_to_block := worldHasFn_of_check s (by b3_lib_name) h29
      blake3_pad_block := worldHasFn_of_check s (by b3_lib_name) h30
      blake3_finish := worldHasFn_of_check s (by b3_lib_name) h31
      blake3_compress_chunks := worldHasFn_of_check s (by b3_lib_name) h32
      blake3_hash_blocks := worldHasFn_of_check s (by b3_lib_name) h33
      blake3_next_layer := worldHasFn_of_check s (by b3_lib_name) h34
      blake3_compress_layer := worldHasFn_of_check s (by b3_lib_name) h35
      blake3_hash := worldHasFn_of_check s (by b3_lib_name) h36
      blake3_digest_bytes := worldHasFn_of_check s (by b3_lib_name) h37
      blake3_address_to_fields := worldHasFn_of_check s (by b3_lib_name) h38
      blake3_address_from_fields := worldHasFn_of_check s (by b3_lib_name) h39
      blake3_verify_bytes_against := worldHasFn_of_check s (by b3_lib_name) h40
      blake3_bytes_to_addr := worldHasFn_of_check s (by b3_lib_name) h41
      blake3_pack_word := worldHasFn_of_check s (by b3_lib_name) h42
      blake3_pack_digest := worldHasFn_of_check s (by b3_lib_name) h43 }

end WorldAndChecker

/-! ## Section 4: Operational `EvalFn` Contracts for `UInt8`, `UInt32`, `UInt64`, and `Fields` -/

section Primitives

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F} (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)

private theorem evalExpr_u32WordFields_inv {locals : Environment F Nat} {v : String}
    {w : UInt32} {h h' : Heap F} {r : SourceValue F}
    (lib : Blake3LibraryWorld world)
    (hl : locals.find? (·.1 == v) = some (v, wv w))
    (ev : EvalExpr world [] locals (u32WordFieldsExpr v) h r h') : h' = h := by
  have hu8 : ∀ x r' h1 h2, EvalFn world "UInt8::to_field" [x] h1 r' h2 → r' = x ∧ h2 = h1 := by
    intro x r' h1 h2 e
    obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u8_to_field rfl e
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) b
    exact ⟨rfl, rfl⟩
  have hslot : ∀ (k : Nat) (hk : k < 4) (h1 h2 : Heap F) (rv : SourceValue F),
      EvalExpr world [] locals (u8f (.index (.var v) k)) h1 rv h2 → h2 = h1 := by
    intro k hk h1 h2 rv e
    obtain ⟨vi, _, evi, cal⟩ := evalExpr_call1_inv e
    obtain ⟨vt, evt, _⟩ := evalExpr_index_inv evi
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl evt
    exact (hu8 _ _ _ _ cal).2
  obtain ⟨_, _, _, _, _, _, _, e0, e1, e2, e3, _⟩ := evalExpr_array4_inv ev
  obtain rfl := hslot 0 (by omega) _ _ _ e0
  obtain rfl := hslot 1 (by omega) _ _ _ e1
  obtain rfl := hslot 2 (by omega) _ _ _ e2
  exact hslot 3 (by omega) _ _ _ e3

/-! ### `UInt8` Contracts -/

include lib in
theorem eval_u8_to_field {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::to_field" [v] h r h') : r = v ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u8_to_field rfl ev
  exact evalExpr_var_eq (by simp) b

include lib in
theorem eval_u8_from_field {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::from_field" [v] h r h') :
    ∃ b : UInt8, v = bv b ∧ r = bv b ∧ h' = h := by
  obtain ⟨rfl, rfl, x, hx, rfl⟩ := lib.maps.from_field _ _ _ _ ev
  exact ⟨UInt8.ofNat x, (bv_ofNat hx).symm, (bv_ofNat hx).symm, rfl⟩

include lib in
theorem eval_u8_from_field_lit {x : Nat} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::from_field" [.field (x : F)] h r h') :
    r = .field (x : F) ∧ h' = h := by
  obtain ⟨rfl, rfl, _, _, _⟩ := lib.maps.from_field _ _ _ _ ev
  exact ⟨rfl, rfl⟩

include lib in
theorem eval_u8_from_fields {v1 v2 r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::from_fields" [v1, v2] h r h') :
    ∃ a b : UInt8, v1 = bv a ∧ v2 = bv b ∧ r = .tuple [bv a, bv b] ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u8_from_fields rfl ev
  obtain ⟨_, _, hcall, hret⟩ := evalExpr_let_wildcard_inv b
  obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := lib.maps.range_pair _ _ _ _ _ cal
  obtain ⟨va', vb', _, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  exact ⟨UInt8.ofNat a, UInt8.ofNat b', (bv_ofNat ha).symm, (bv_ofNat hb).symm,
    by rw [bv_ofNat ha, bv_ofNat hb], rfl⟩

include hc lib in
theorem eval_u8_xor {a b : UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::xor" [bv a, bv b] h r h') :
    r = bv (a ^^^ b) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u8_xor rfl ev
  obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor _ _ _ _ _ cal
  have hae := u32Compat_byte_inj hc (byte_lt a) ha' (Value.field.inj haEq)
  have hbe := u32Compat_byte_inj hc (byte_lt b) hb' (Value.field.inj hbEq)
  subst hae hbe
  refine ⟨?_, rfl⟩
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [bv, hx]

include hc lib in
theorem eval_u8_xor_split4 {a b : UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::xor_split4" [bv a, bv b] h r h') :
    r = .tuple [.field (((a ^^^ b).toNat / 16 : Nat) : F),
                .field ((((a ^^^ b).toNat % 16) * 16 : Nat) : F)] ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u8_xor_split4 rfl ev
  obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor_split4 _ _ _ _ _ cal
  have hae := u32Compat_byte_inj hc (byte_lt a) ha' (Value.field.inj haEq)
  have hbe := u32Compat_byte_inj hc (byte_lt b) hb' (Value.field.inj hbEq)
  subst hae hbe
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [hx]

include hc lib in
theorem eval_u8_xor_split7 {a b : UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::xor_split7" [bv a, bv b] h r h') :
    r = .tuple [.field (((a ^^^ b).toNat / 128 : Nat) : F),
                .field ((((a ^^^ b).toNat % 128) * 2 : Nat) : F)] ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u8_xor_split7 rfl ev
  obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨rfl, a', b', ha', hb', haEq, hbEq, rfl⟩ := lib.maps.raw_xor_split7 _ _ _ _ _ cal
  have hae := u32Compat_byte_inj hc (byte_lt a) ha' (Value.field.inj haEq)
  have hbe := u32Compat_byte_inj hc (byte_lt b) hb' (Value.field.inj hbEq)
  subst hae hbe
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [hx]

include lib in
theorem eval_u8_join4 {x0 x1 y0 y1 : F} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::join4"
      [.tuple [.field x0, .field x1], .tuple [.field y0, .field y1]] h r h') :
    r = .field (x0 + y1) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u8_join4 rfl ev
  obtain ⟨vl, vr, _, evl, evr, hop⟩ := evalExpr_binary_inv body
  obtain ⟨vh, evh, prh⟩ := evalExpr_project_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh
  obtain rfl := proj_inv (by simp) prh
  obtain ⟨vlo, evlo, prlo⟩ := evalExpr_project_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlo
  obtain rfl := proj_inv (by simp) prlo
  exact ⟨binop_add hop, rfl⟩

include lib in
theorem eval_u8_join7 {x0 x1 y0 y1 : F} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt8::join7"
      [.tuple [.field x0, .field x1], .tuple [.field y0, .field y1]] h r h') :
    r = .field (x0 + y1) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u8_join7 rfl ev
  obtain ⟨vl, vr, _, evl, evr, hop⟩ := evalExpr_binary_inv body
  obtain ⟨vh, evh, prh⟩ := evalExpr_project_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh
  obtain rfl := proj_inv (by simp) prh
  obtain ⟨vlo, evlo, prlo⟩ := evalExpr_project_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlo
  obtain rfl := proj_inv (by simp) prlo
  exact ⟨binop_add hop, rfl⟩

/-! ### `UInt32` Contracts -/

include lib in
theorem eval_u32_from_bytes {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_bytes" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u32_from_bytes rfl ev
  exact evalExpr_var_eq (by simp) b

include lib in
theorem eval_u32_to_bytes {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::to_bytes" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u32_to_bytes rfl ev
  exact evalExpr_var_eq (by simp) b

include lib in
theorem eval_u32_compact_field {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::compact_field" [x] h r h') : r = x ∧ h' = h := by
  obtain ⟨_, b⟩ := evalFn_noControl_inv lib.u32_compact_field rfl ev
  exact evalExpr_var_eq (by simp) b

include lib in
theorem eval_u32_from_fields {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::from_fields" [x] h r h') :
    ∃ c0 c1 c2 c3 : UInt8, r = w4 c0 c1 c2 c3 ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_from_fields rfl ev
  obtain ⟨vb0, vb1, _, ev1, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨vr0, vr1, _, _, evr0, evr1, cal1⟩ := evalExpr_call2_inv ev1
  obtain ⟨_, evx0, _⟩ := evalExpr_index_inv evr0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx0
  obtain ⟨_, evx1, _⟩ := evalExpr_index_inv evr1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx1
  obtain ⟨c0, c1, _, _, heq1, rfl⟩ := eval_u8_from_fields lib cal1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl⟩ := heq1
  obtain ⟨vb2, vb3, _, ev2, k2⟩ := evalExpr_let_tuple2_inv k1
  obtain ⟨vr2, vr3, _, _, evr2, evr3, cal2⟩ := evalExpr_call2_inv ev2
  obtain ⟨_, evx2, _⟩ := evalExpr_index_inv evr2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx2
  obtain ⟨_, evx3, _⟩ := evalExpr_index_inv evr3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx3
  obtain ⟨c2, c3, _, _, heq2, rfl⟩ := eval_u8_from_fields lib cal2
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl⟩ := heq2
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv k2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  exact ⟨c0, c1, c2, c3, rfl, rfl⟩

include lib in
theorem eval_u32_compact {b0 b1 b2 b3 : UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::compact" [w4 b0 b1 b2 b3] h r h') :
    r = .field ((Aiur.Library.Blake3.wordOfBytes b0 b1 b2 b3).toNat : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_compact rfl ev
  have hbyte : ∀ (i : Nat) (bi : UInt8) (h1 h2 : Heap F) (rv : SourceValue F),
      projectValue (w4 b0 b1 b2 b3 : SourceValue F) i = .ok (bv bi) →
      EvalExpr world [] [("word", w4 b0 b1 b2 b3)] (u8f (.index (.var "word") i)) h1 rv h2 →
      rv = bv bi ∧ h2 = h1 := by
    intro i bi h1 h2 rv hpr e
    obtain ⟨vi, _, evi, cal⟩ := evalExpr_call1_inv e
    obtain ⟨vt, evt, pr⟩ := evalExpr_index_inv evi
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
    obtain rfl := Except.ok.inj (hpr.symm.trans pr)
    exact eval_u8_to_field lib cal
  obtain ⟨va3, vb3, _, eva3, evb3, opAdd3⟩ := evalExpr_binary_inv body
  obtain ⟨va2, vb2, _, eva2, evb2, opAdd2⟩ := evalExpr_binary_inv eva3
  obtain ⟨va1, vb1, _, eva1, evb1, opAdd1⟩ := evalExpr_binary_inv eva2
  obtain ⟨rfl, rfl⟩ := hbyte 0 b0 _ _ _ (proj_w4_0 b0 b1 b2 b3) eva1
  obtain ⟨vc1, vd1, _, evc1, evd1, opMul1⟩ := evalExpr_binary_inv evb1
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc1
  obtain ⟨rfl, rfl⟩ := hbyte 1 b1 _ _ _ (proj_w4_1 b0 b1 b2 b3) evd1
  obtain rfl := binop_mul opMul1
  obtain rfl := binop_add opAdd1
  obtain ⟨vc2, vd2, _, evc2, evd2, opMul2⟩ := evalExpr_binary_inv evb2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc2
  obtain ⟨rfl, rfl⟩ := hbyte 2 b2 _ _ _ (proj_w4_2 b0 b1 b2 b3) evd2
  obtain rfl := binop_mul opMul2
  obtain rfl := binop_add opAdd2
  obtain ⟨vc3, vd3, _, evc3, evd3, opMul3⟩ := evalExpr_binary_inv evb3
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc3
  obtain ⟨rfl, rfl⟩ := hbyte 3 b3 _ _ _ (proj_w4_3 b0 b1 b2 b3) evd3
  obtain rfl := binop_mul opMul3
  obtain rfl := binop_add opAdd3
  refine ⟨?_, rfl⟩
  rw [Aiur.Library.Blake3.wordOfBytes_toNat]
  congr 1
  simp only [U32.pack]
  push_cast
  ring

include lib in
theorem eval_u32_compact_wv {a : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::compact" [wv a] h r h') :
    r = .field (a.toNat : F) ∧ h' = h := by
  have h1 := eval_u32_compact lib (b0 := (Blake3.Pure.wordBytes a)[0])
    (b1 := (Blake3.Pure.wordBytes a)[1]) (b2 := (Blake3.Pure.wordBytes a)[2])
    (b3 := (Blake3.Pure.wordBytes a)[3]) ev
  rwa [wv_bytes] at h1

include hc lib in
theorem eval_u32_add {a b : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::add" [wv a, wv b] h r h') :
    r = wv (a + b) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_add rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  obtain ⟨_, _, _, evKa, evKb, _⟩ := evalExpr_tuple2_inv evKey
  obtain rfl := evalExpr_u32WordFields_inv lib (by simp; rfl) evKa
  obtain rfl := evalExpr_u32WordFields_inv lib (by simp; rfl) evKb
  obtain ⟨vres, _, evRes, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evRes
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
  obtain ⟨c0, c1, c2, c3, rfl, rfl⟩ := eval_u32_from_fields lib calFF
  obtain ⟨vcarry, _, evCarry, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨vnum, vden, _, evNum, evDen, opDiv⟩ := evalExpr_binary_inv evCarry
  obtain ⟨vsum, vcres, _, evSum, evCres, opSub⟩ := evalExpr_binary_inv evNum
  obtain ⟨vca, vcb, _, evCa, evCb, opAdd⟩ := evalExpr_binary_inv evSum
  obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evCa
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calCa
  obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evCb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calCb
  obtain rfl := binop_add opAdd
  obtain ⟨vr', _, evr', calCr⟩ := evalExpr_call1_inv evCres
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
  obtain ⟨rfl, rfl⟩ := eval_u32_compact lib calCr
  obtain rfl := binop_sub opSub
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evDen
  have hbase : (4294967296 : F) ≠ 0 := by
    simpa [U32.base] using U32.base_ne_zero hc
  obtain rfl := binop_div hbase opDiv
  obtain ⟨_, _, evAss, k4⟩ := evalExpr_let_wildcard_inv k3
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vc1, vc2, _, evc1, evc2, opMul⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
  obtain ⟨vc3, v1, _, evc3, ev1, opSub1⟩ := evalExpr_binary_inv evc2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc3
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  obtain rfl := binop_sub opSub1
  obtain rfl := binop_mul opMul
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k4
  refine ⟨?_, rfl⟩
  have hchk := Value.field.inj heq
  have key := (U32.add_words_check_iff hc (word_lt a) (word_lt b)
    (word_lt (Aiur.Library.Blake3.wordOfBytes c0 c1 c2 c3))).1
    (by simpa [U32.base] using hchk)
  apply w4_eq_wv
  rw [key, UInt32.toNat_add]
  rfl

include hc lib in
theorem eval_u32_add3 {a b c : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::add3" [wv a, wv b, wv c] h r h') :
    r = wv (a + b + c) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_add3 rfl ev
  obtain ⟨vraw, _, evHint, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, evKey⟩ := evalExpr_hint_inv evHint
  cases evKey with
  | tuple hargs =>
    cases hargs with | cons evKa t1 =>
    cases t1 with | cons evKb t2 =>
    cases t2 with | cons evKc t3 =>
    cases t3
    obtain rfl := evalExpr_u32WordFields_inv lib (by simp; rfl) evKa
    obtain rfl := evalExpr_u32WordFields_inv lib (by simp; rfl) evKb
    obtain rfl := evalExpr_u32WordFields_inv lib (by simp; rfl) evKc
    obtain ⟨vres, _, evRes, k2⟩ := evalExpr_let_bind_inv k1
    obtain ⟨vraw', _, evRaw', calFF⟩ := evalExpr_call1_inv evRes
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evRaw'
    obtain ⟨c0, c1, c2, c3, rfl, rfl⟩ := eval_u32_from_fields lib calFF
    obtain ⟨vcarry, _, evCarry, k3⟩ := evalExpr_let_bind_inv k2
    obtain ⟨vnum, vden, _, evNum, evDen, opDiv⟩ := evalExpr_binary_inv evCarry
    obtain ⟨vsum3, vcres, _, evSum3, evCres, opSub⟩ := evalExpr_binary_inv evNum
    obtain ⟨vsum2, vcc, _, evSum2, evCc, opAdd2⟩ := evalExpr_binary_inv evSum3
    obtain ⟨vca, vcb, _, evCa, evCb, opAdd1⟩ := evalExpr_binary_inv evSum2
    obtain ⟨va', _, eva', calCa⟩ := evalExpr_call1_inv evCa
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
    obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calCa
    obtain ⟨vb', _, evb', calCb⟩ := evalExpr_call1_inv evCb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
    obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calCb
    obtain rfl := binop_add opAdd1
    obtain ⟨vc', _, evc', calCc⟩ := evalExpr_call1_inv evCc
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc'
    obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calCc
    obtain rfl := binop_add opAdd2
    obtain ⟨vr', _, evr', calCr⟩ := evalExpr_call1_inv evCres
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
    obtain ⟨rfl, rfl⟩ := eval_u32_compact lib calCr
    obtain rfl := binop_sub opSub
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evDen
    have hbase : (4294967296 : F) ≠ 0 := by
      simpa [U32.base] using U32.base_ne_zero hc
    obtain rfl := binop_div hbase opDiv
    obtain ⟨_, _, evAss, k4⟩ := evalExpr_let_wildcard_inv k3
    obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
    obtain ⟨vp1, vp2, _, evp1, evp2, opMul2⟩ := evalExpr_binary_inv evl
    obtain ⟨vc1, vc2, _, evc1, evc2, opMul1⟩ := evalExpr_binary_inv evp1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
    obtain ⟨vc3, v1, _, evc3, ev1, opSub1⟩ := evalExpr_binary_inv evc2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc3
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
    obtain rfl := binop_sub opSub1
    obtain rfl := binop_mul opMul1
    obtain ⟨vc4, v2, _, evc4, ev2, opSub2⟩ := evalExpr_binary_inv evp2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc4
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
    obtain rfl := binop_sub opSub2
    obtain rfl := binop_mul opMul2
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k4
    refine ⟨?_, rfl⟩
    have hchk := Value.field.inj heq
    have key := (U32.add3_words_check_iff hc (word_lt a) (word_lt b) (word_lt c)
      (word_lt (Aiur.Library.Blake3.wordOfBytes c0 c1 c2 c3))).1
      (by simpa [U32.base] using hchk)
    apply w4_eq_wv
    rw [key, UInt32.toNat_add, UInt32.toNat_add]
    simp only [U32.base]
    omega

include hc lib in
theorem eval_u32_xor_w4 {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::xor" [w4 a0 a1 a2 a3, w4 b0 b1 b2 b3] h r h') :
    r = w4 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_xor rfl ev
  have hstep : ∀ (i : Nat) (ai bi : UInt8) (h1 h2 : Heap F) (rv : SourceValue F),
      projectValue (w4 a0 a1 a2 a3 : SourceValue F) i = .ok (bv ai) →
      projectValue (w4 b0 b1 b2 b3 : SourceValue F) i = .ok (bv bi) →
      EvalExpr world [] [("a", w4 a0 a1 a2 a3), ("b", w4 b0 b1 b2 b3)]
        (.call "UInt8::xor" (some []) [.index (.var "a") i, .index (.var "b") i]) h1 rv h2 →
      rv = bv (ai ^^^ bi) ∧ h2 = h1 := by
    intro i ai bi h1 h2 rv hpa hpb e
    obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv e
    obtain ⟨vta, evta, pra⟩ := evalExpr_index_inv eva
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evta
    obtain rfl := Except.ok.inj (hpa.symm.trans pra)
    obtain ⟨vtb, evtb, prb⟩ := evalExpr_index_inv evb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evtb
    obtain rfl := Except.ok.inj (hpb.symm.trans prb)
    exact eval_u8_xor hc lib cal
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  obtain ⟨rfl, rfl⟩ := hstep 0 a0 b0 _ _ _ (proj_w4_0 _ _ _ _) (proj_w4_0 _ _ _ _) e0
  obtain ⟨rfl, rfl⟩ := hstep 1 a1 b1 _ _ _ (proj_w4_1 _ _ _ _) (proj_w4_1 _ _ _ _) e1
  obtain ⟨rfl, rfl⟩ := hstep 2 a2 b2 _ _ _ (proj_w4_2 _ _ _ _) (proj_w4_2 _ _ _ _) e2
  obtain ⟨rfl, rfl⟩ := hstep 3 a3 b3 _ _ _ (proj_w4_3 _ _ _ _) (proj_w4_3 _ _ _ _) e3
  exact ⟨rfl, rfl⟩

include hc lib in
theorem eval_u32_xor {a b : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::xor" [wv a, wv b] h r h') :
    r = wv (a ^^^ b) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_u32_xor_w4 hc lib ev
  refine ⟨?_, rfl⟩
  rw [← wv_wordOfBytes, ← Aiur.Library.Blake3.xor_spec, wv_bytes, wv_bytes]

include lib in
theorem eval_u32_rotr8 {a : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::rotr8" [wv a] h r h') :
    r = wv (Blake3.Pure.rotateRight a 8) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_rotr8 rfl ev
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  obtain ⟨vt0, evt0, pr0⟩ := evalExpr_index_inv e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt0
  obtain rfl := Except.ok.inj ((proj_w4_1 _ _ _ _).symm.trans pr0)
  obtain ⟨vt1, evt1, pr1⟩ := evalExpr_index_inv e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt1
  obtain rfl := Except.ok.inj ((proj_w4_2 _ _ _ _).symm.trans pr1)
  obtain ⟨vt2, evt2, pr2⟩ := evalExpr_index_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt2
  obtain rfl := Except.ok.inj ((proj_w4_3 _ _ _ _).symm.trans pr2)
  obtain ⟨vt3, evt3, pr3⟩ := evalExpr_index_inv e3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt3
  obtain rfl := Except.ok.inj ((proj_w4_0 _ _ _ _).symm.trans pr3)
  refine ⟨?_, rfl⟩
  conv_rhs => rw [← wv_bytes a]
  rw [Aiur.Library.Blake3.rotr8_spec, wv_wordOfBytes]
  rfl

include lib in
theorem eval_u32_rotr16 {a : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::rotr16" [wv a] h r h') :
    r = wv (Blake3.Pure.rotateRight a 16) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_rotr16 rfl ev
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv body
  obtain ⟨vt0, evt0, pr0⟩ := evalExpr_index_inv e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt0
  obtain rfl := Except.ok.inj ((proj_w4_2 _ _ _ _).symm.trans pr0)
  obtain ⟨vt1, evt1, pr1⟩ := evalExpr_index_inv e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt1
  obtain rfl := Except.ok.inj ((proj_w4_3 _ _ _ _).symm.trans pr1)
  obtain ⟨vt2, evt2, pr2⟩ := evalExpr_index_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt2
  obtain rfl := Except.ok.inj ((proj_w4_0 _ _ _ _).symm.trans pr2)
  obtain ⟨vt3, evt3, pr3⟩ := evalExpr_index_inv e3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt3
  obtain rfl := Except.ok.inj ((proj_w4_1 _ _ _ _).symm.trans pr3)
  refine ⟨?_, rfl⟩
  conv_rhs => rw [← wv_bytes a]
  rw [Aiur.Library.Blake3.rotr16_spec, wv_wordOfBytes]
  rfl

include hc lib in
theorem eval_u32_xor_rotr12 {a b : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::xor_rotr12" [wv a, wv b] h r h') :
    r = wv (Blake3.Pure.rotateRight (a ^^^ b) 12) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_xor_rotr12 rfl ev
  have hsp : ∀ {locals : Environment F Nat} (i : Nat) (ai bi : UInt8) (h1 h2 : Heap F)
      (rv : SourceValue F),
      locals.find? (·.1 == "a") = some ("a", wv a) →
      locals.find? (·.1 == "b") = some ("b", wv b) →
      projectValue (wv a : SourceValue F) i = .ok (bv ai) →
      projectValue (wv b : SourceValue F) i = .ok (bv bi) →
      EvalExpr world [] locals
        (.call "UInt8::xor_split4" (some []) [.index (.var "a") i, .index (.var "b") i]) h1 rv h2 →
      rv = .tuple [.field (((ai ^^^ bi).toNat / 16 : Nat) : F),
                   .field ((((ai ^^^ bi).toNat % 16) * 16 : Nat) : F)] ∧ h2 = h1 := by
    intro locals i ai bi h1 h2 rv hla hlb hpa hpb e
    obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv e
    obtain ⟨vta, evta, pra⟩ := evalExpr_index_inv eva
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hla evta
    obtain rfl := Except.ok.inj (hpa.symm.trans pra)
    obtain ⟨vtb, evtb, prb⟩ := evalExpr_index_inv evb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlb evtb
    obtain rfl := Except.ok.inj (hpb.symm.trans prb)
    exact eval_u8_xor_split4 hc lib cal
  obtain ⟨vp0, _, evp0, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := hsp 0 _ _ _ _ _ (by simp) (by simp) (proj_w4_0 _ _ _ _) (proj_w4_0 _ _ _ _) evp0
  obtain ⟨vp1, _, evp1, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨rfl, rfl⟩ := hsp 1 _ _ _ _ _ (by simp) (by simp) (proj_w4_1 _ _ _ _) (proj_w4_1 _ _ _ _) evp1
  obtain ⟨vp2, _, evp2, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨rfl, rfl⟩ := hsp 2 _ _ _ _ _ (by simp) (by simp) (proj_w4_2 _ _ _ _) (proj_w4_2 _ _ _ _) evp2
  obtain ⟨vp3, _, evp3, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨rfl, rfl⟩ := hsp 3 _ _ _ _ _ (by simp) (by simp) (proj_w4_3 _ _ _ _) (proj_w4_3 _ _ _ _) evp3
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv k4
  have hj : ∀ {locals : Environment F Nat} {n1 n2 : String} {x0 x1 y0 y1 : F}
      {h1 h2 : Heap F} {rv : SourceValue F},
      locals.find? (·.1 == n1) = some (n1, .tuple [.field x0, .field x1]) →
      locals.find? (·.1 == n2) = some (n2, .tuple [.field y0, .field y1]) →
      EvalExpr world [] locals (.call "UInt8::join4" (some []) [.var n1, .var n2]) h1 rv h2 →
      rv = .field (x0 + y1) ∧ h2 = h1 := by
    intro locals n1 n2 x0 x1 y0 y1 h1 h2 rv hl1 hl2 e
    obtain ⟨v1, v2, _, _, ev1, ev2, cal⟩ := evalExpr_call2_inv e
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl1 ev1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl2 ev2
    exact eval_u8_join4 lib cal
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e0
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e1
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e2
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e3
  refine ⟨?_, rfl⟩
  have hspec := Aiur.Library.Blake3.xor_rotr12_spec (Blake3.Pure.wordBytes a)[0]
    (Blake3.Pure.wordBytes a)[1] (Blake3.Pure.wordBytes a)[2] (Blake3.Pure.wordBytes a)[3]
    (Blake3.Pure.wordBytes b)[0] (Blake3.Pure.wordBytes b)[1] (Blake3.Pure.wordBytes b)[2]
    (Blake3.Pure.wordBytes b)[3]
  simp only [wv_bytes] at hspec
  rw [hspec, wv_wordOfBytes]
  simp only [w4, bv]
  congr 1
  simp only [List.cons.injEq, Value.field.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [toNat_ofNat_lt (U32.joined_nibbles_lt (byte_lt _) (byte_lt _))]
    simp only [UInt8.toNat_xor]
    push_cast; ring

include hc lib in
theorem eval_u32_xor_rotr7 {a b : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt32::xor_rotr7" [wv a, wv b] h r h') :
    r = wv (Blake3.Pure.rotateRight (a ^^^ b) 7) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u32_xor_rotr7 rfl ev
  have hsp : ∀ {locals : Environment F Nat} (i : Nat) (ai bi : UInt8) (h1 h2 : Heap F)
      (rv : SourceValue F),
      locals.find? (·.1 == "a") = some ("a", wv a) →
      locals.find? (·.1 == "b") = some ("b", wv b) →
      projectValue (wv a : SourceValue F) i = .ok (bv ai) →
      projectValue (wv b : SourceValue F) i = .ok (bv bi) →
      EvalExpr world [] locals
        (.call "UInt8::xor_split7" (some []) [.index (.var "a") i, .index (.var "b") i]) h1 rv h2 →
      rv = .tuple [.field (((ai ^^^ bi).toNat / 128 : Nat) : F),
                   .field ((((ai ^^^ bi).toNat % 128) * 2 : Nat) : F)] ∧ h2 = h1 := by
    intro locals i ai bi h1 h2 rv hla hlb hpa hpb e
    obtain ⟨va, vb, _, _, eva, evb, cal⟩ := evalExpr_call2_inv e
    obtain ⟨vta, evta, pra⟩ := evalExpr_index_inv eva
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hla evta
    obtain rfl := Except.ok.inj (hpa.symm.trans pra)
    obtain ⟨vtb, evtb, prb⟩ := evalExpr_index_inv evb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlb evtb
    obtain rfl := Except.ok.inj (hpb.symm.trans prb)
    exact eval_u8_xor_split7 hc lib cal
  obtain ⟨vp0, _, evp0, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := hsp 0 _ _ _ _ _ (by simp) (by simp) (proj_w4_0 _ _ _ _) (proj_w4_0 _ _ _ _) evp0
  obtain ⟨vp1, _, evp1, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨rfl, rfl⟩ := hsp 1 _ _ _ _ _ (by simp) (by simp) (proj_w4_1 _ _ _ _) (proj_w4_1 _ _ _ _) evp1
  obtain ⟨vp2, _, evp2, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨rfl, rfl⟩ := hsp 2 _ _ _ _ _ (by simp) (by simp) (proj_w4_2 _ _ _ _) (proj_w4_2 _ _ _ _) evp2
  obtain ⟨vp3, _, evp3, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨rfl, rfl⟩ := hsp 3 _ _ _ _ _ (by simp) (by simp) (proj_w4_3 _ _ _ _) (proj_w4_3 _ _ _ _) evp3
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv k4
  have hj : ∀ {locals : Environment F Nat} {n1 n2 : String} {x0 x1 y0 y1 : F}
      {h1 h2 : Heap F} {rv : SourceValue F},
      locals.find? (·.1 == n1) = some (n1, .tuple [.field x0, .field x1]) →
      locals.find? (·.1 == n2) = some (n2, .tuple [.field y0, .field y1]) →
      EvalExpr world [] locals (.call "UInt8::join7" (some []) [.var n1, .var n2]) h1 rv h2 →
      rv = .field (x0 + y1) ∧ h2 = h1 := by
    intro locals n1 n2 x0 x1 y0 y1 h1 h2 rv hl1 hl2 e
    obtain ⟨v1, v2, _, _, ev1, ev2, cal⟩ := evalExpr_call2_inv e
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl1 ev1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl2 ev2
    exact eval_u8_join7 lib cal
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e0
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e1
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e2
  obtain ⟨rfl, rfl⟩ := hj (by simp; exact ⟨rfl, rfl⟩) (by simp; exact ⟨rfl, rfl⟩) e3
  refine ⟨?_, rfl⟩
  have hspec := Aiur.Library.Blake3.xor_rotr7_spec (Blake3.Pure.wordBytes a)[0]
    (Blake3.Pure.wordBytes a)[1] (Blake3.Pure.wordBytes a)[2] (Blake3.Pure.wordBytes a)[3]
    (Blake3.Pure.wordBytes b)[0] (Blake3.Pure.wordBytes b)[1] (Blake3.Pure.wordBytes b)[2]
    (Blake3.Pure.wordBytes b)[3]
  simp only [wv_bytes] at hspec
  rw [hspec, wv_wordOfBytes]
  simp only [w4, bv]
  congr 1
  simp only [List.cons.injEq, Value.field.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [toNat_ofNat_lt (U32.joined_seven_bits_lt (byte_lt _) (byte_lt _))]
    simp only [UInt8.toNat_xor]
    push_cast; ring

/-! ### `Fields` and `UInt64` Contracts -/

include lib in
theorem eval_fields_is_zero_field {x : F} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Fields::is_zero" [.field x] h r h') :
    r = .field (if x = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.fields_is_zero rfl ev
  obtain ⟨v, hm, evx, hbr⟩ := evalExpr_match_lit_wild_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
  rcases hbr with ⟨heq, hb1⟩ | ⟨hne, hb2⟩
  · have hx : x = 0 := Value.field.inj heq
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hb1
    exact ⟨by simp [hx], rfl⟩
  · have hx : x ≠ 0 := fun e => hne (by rw [e])
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hb2
    exact ⟨by simp [hx], rfl⟩

include hc lib in
theorem eval_fields_is_zero {n : Nat} (hn : n < 1024) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Fields::is_zero" [.field (n : F)] h r h') :
    r = .field (if n = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_fields_is_zero_field lib ev
  have hiff : ((n : F) = 0) ↔ n = 0 :=
    ⟨fun h => u32Compat_small_inj hc hn (by omega) (by simpa using h), fun h => by simp [h]⟩
  exact ⟨by simp [hiff], rfl⟩

/-- Matching a byte against `UInt8::BYTE_0` succeeds iff the byte is `0`. -/
theorem match_byte0_bv (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)
    (h : Heap F) (b : UInt8) :
    world.matchPattern [] h (.global "UInt8::BYTE_0" (some .field)) (bv b) =
      .ok (if b = 0 then some [] else none) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp lib.constDepth_pos)
  have hcb : world.constant "UInt8::BYTE_0" .field = .ok (.literal 0) := by
    have h0 := lib.const_bytes 0 (by decide)
    have hnm : s!"UInt8::BYTE_{(0 : Nat)}" = "UInt8::BYTE_0" := rfl
    rw [hnm, Nat.cast_zero] at h0
    exact h0
  unfold World.matchPattern
  rw [hd, matchPatternWith]
  simp only [Generic.Ty.subst, hcb, bind, Except.bind]
  rw [matchPatternWith]
  simp only [Aiur.Pattern.bindings, bv, pure, Except.pure, Except.ok.injEq]
  by_cases hb : b = 0
  · subst hb; simp
  · have hne : ¬ ((0 : F) = (b.toNat : F)) := by
      intro heq
      apply hb
      exact UInt8.ext (u32Compat_byte_inj hc (byte_lt b) (by decide) (by simpa using heq.symm))
    simp [hb, hne]

omit [DecidableEq F] in
private theorem matchListWith_byte0 {α : Type*}
    {f : α → SourceValue F → Except EvalError (Option (Environment F Nat))}
    (hf : ∀ a (b : UInt8), f a (bv b) = .ok (if b = 0 then some [] else none)) :
    ∀ (xs : List α) (bs : List UInt8), xs.length = bs.length →
      matchListWith f xs (bs.map bv) = .ok (if bs.all (· == 0) then some [] else none)
  | [], [], _ => rfl
  | x :: xs, b :: bs, hlen => by
    simp only [List.map_cons, matchListWith, hf, bind, Except.bind, pure, Except.pure, List.all_cons]
    by_cases hb : b = 0
    · subst hb
      simp only [↓reduceIte, beq_self_eq_true, Bool.true_and,
        matchListWith_byte0 hf xs bs (Nat.succ.inj hlen)]
      split_ifs <;> rfl
    · have hbf : (b == 0) = false := beq_false_of_ne hb
      simp [hb, hbf]

/-- Matching `u64v c` against `[UInt8::BYTE_0; 8]` succeeds iff `c = 0`. -/
theorem match_zeros8_u64v (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)
    (h : Heap F) (c : UInt64) :
    world.matchPattern [] h
        (.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field)))) (u64v c) =
      .ok (if c = 0 then some [] else none) := by
  let bs : List UInt8 := (List.range 8).map (u64b c)
  have hu64 : (u64v c : SourceValue F) = .tuple (bs.map bv) := by
    rw [u64v_eq]; rfl
  have hc0_iff : c = 0 ↔ bs.all (· == 0) = true := by
    simp only [bs, List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq]
    constructor
    · rintro rfl j _; simp [u64b]
    · intro hall
      have hp := u64_pack c
      rw [hall 0 (by omega), hall 1 (by omega), hall 2 (by omega), hall 3 (by omega),
          hall 4 (by omega), hall 5 (by omega), hall 6 (by omega), hall 7 (by omega)] at hp
      exact UInt64.toNat_inj.mp (by rw [← hp]; rfl)
  rw [hu64]
  change matchPatternWith world.constant world.constDepth [] h
    (.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field)))) (.tuple (bs.map bv)) = _
  rw [matchPatternWith]
  have hbslen : bs.length = 8 := by simp [bs]
  simp only [List.length_replicate, List.length_map, hbslen, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  rw [matchListWith_byte0 (fun p b => by
    have hp : p.val = .global "UInt8::BYTE_0" (some .field) := List.eq_of_mem_replicate p.property
    rw [hp]; exact match_byte0_bv hc lib h b) _ _ (by simp [hbslen])]
  by_cases h0 : c = 0
  · simp [h0, hc0_iff.mp h0]
  · have hne : ¬ (bs.all (· == 0) = true) := fun h' => h0 (hc0_iff.mpr h')
    simp [h0, hne]

include hc lib in
theorem eval_u64_is_zero {c : UInt64} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt64::is_zero" [u64v c] h r h') :
    r = .field (if c = 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u64_is_zero rfl ev
  obtain ⟨v, hm, bs, armBody, evx, hsel, hbr⟩ := evalExpr_match_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
  rcases selectArm_cons_inv hsel with ⟨hmt, rfl⟩ | ⟨hnm, hsel2⟩
  · rw [match_zeros8_u64v hc lib] at hmt
    by_cases hc0 : c = 0
    · subst hc0
      simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at hmt
      subst hmt
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hbr
      exact ⟨by simp, rfl⟩
    · simp [hc0] at hmt
  · rw [match_zeros8_u64v hc lib] at hnm
    have hc0 : c ≠ 0 := by intro e; subst e; simp at hnm
    rcases selectArm_cons_inv hsel2 with ⟨hmt2, rfl⟩ | ⟨_, hsel3⟩
    · simp only [World.matchPattern, matchPatternWith, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at hmt2
      subst hmt2
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hbr
      exact ⟨by simp [hc0], rfl⟩
    · exact False.elim (selectArm_nil_inv hsel3)

omit [DecidableEq F] in
private theorem u64v_succ (c : UInt64) {r0 r1 r2 r3 r4 r5 r6 r7 : Nat}
    (hr : U64.wrappingSuccBytes (u64b c 0).toNat (u64b c 1).toNat (u64b c 2).toNat
      (u64b c 3).toNat (u64b c 4).toNat (u64b c 5).toNat (u64b c 6).toNat (u64b c 7).toNat =
      (r0, r1, r2, r3, r4, r5, r6, r7)) :
    (u64v (c + 1) : SourceValue F) = .tuple
      [.field (r0 : F), .field (r1 : F), .field (r2 : F), .field (r3 : F),
       .field (r4 : F), .field (r5 : F), .field (r6 : F), .field (r7 : F)] := by
  have sound := U64.wrapping_succ_sound (byte_lt (u64b c 0)) (byte_lt (u64b c 1))
    (byte_lt (u64b c 2)) (byte_lt (u64b c 3)) (byte_lt (u64b c 4)) (byte_lt (u64b c 5))
    (byte_lt (u64b c 6)) (byte_lt (u64b c 7))
  rw [hr] at sound
  simp only at sound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hp⟩ := sound
  rw [u64_pack] at hp
  have hs : (c + 1).toNat = U64.pack r0 r1 r2 r3 r4 r5 r6 r7 := by
    rw [hp]; simp [UInt64.toNat_add, U64.base]
  have hd : ∀ (k : Nat), (u64b (c + 1) k).toNat =
      (U64.pack r0 r1 r2 r3 r4 r5 r6 r7) / 256 ^ k % 256 := fun k => by rw [u64b_toNat, hs]
  have d0 : (u64b (c + 1) 0).toNat = r0 := by rw [hd 0]; unfold U64.pack; omega
  have d1 : (u64b (c + 1) 1).toNat = r1 := by rw [hd 1]; unfold U64.pack; omega
  have d2 : (u64b (c + 1) 2).toNat = r2 := by rw [hd 2]; unfold U64.pack; omega
  have d3 : (u64b (c + 1) 3).toNat = r3 := by rw [hd 3]; unfold U64.pack; omega
  have d4 : (u64b (c + 1) 4).toNat = r4 := by rw [hd 4]; unfold U64.pack; omega
  have d5 : (u64b (c + 1) 5).toNat = r5 := by rw [hd 5]; unfold U64.pack; omega
  have d6 : (u64b (c + 1) 6).toNat = r6 := by rw [hd 6]; unfold U64.pack; omega
  have d7 : (u64b (c + 1) 7).toNat = r7 := by rw [hd 7]; unfold U64.pack; omega
  rw [u64v_eq]
  simp only [bv, d0, d1, d2, d3, d4, d5, d6, d7]

omit [DecidableEq F] in
private theorem hasNoControl_wrappingSuccArm (i : Nat) :
    hasNoControl (wrappingSuccArm (F := F) i) = true := by
  simp only [wrappingSuccArm, hasNoControl, hasNoControlList_iff, List.mem_map]
  rintro _ ⟨j, _, rfl⟩
  split_ifs <;> rfl

omit [DecidableEq F] in
private theorem hasNoControl_wrappingSuccMatch :
    ∀ k, hasNoControl (wrappingSuccMatch (F := F) k) = true
  | 0 => rfl
  | k + 1 => by
    simp only [wrappingSuccMatch, u8f, hasNoControl, hasNoControlList, hasNoControlArms,
      Bool.and_eq_true, Bool.and_true, true_and]
    exact ⟨hasNoControl_wrappingSuccMatch k, hasNoControl_wrappingSuccArm _⟩

private theorem evalExpr_wrappingSuccArm_inv (lib : Blake3LibraryWorld world)
    {locals : Environment F Nat} (c : UInt64)
    (hloc : ∀ j < 8, locals.find? (·.1 == s!"b{j}") = some (s!"b{j}", bv (u64b c j)))
    (i : Nat) (hi : i < 8) {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (wrappingSuccArm i) h r h') :
    r = .tuple ((List.range 8).map fun j =>
      if j < i then (.field (0 : F) : SourceValue F)
      else if j = i then .field (((u64b c i).toNat + 1 : Nat) : F)
      else bv (u64b c j)) ∧ h' = h := by
  unfold wrappingSuccArm at ev
  refine evalExpr_array_map_inv (List.range 8) ?_ ev
  intro j hj h1 rv h2 ej
  have hjlt : j < 8 := List.mem_range.mp hj
  by_cases hlt : j < i
  · simp only [hlt, ↓reduceIte] at ej ⊢
    simpa using evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) ej
  · by_cases heq : j = i
    · subst heq
      simp only [hlt, ↓reduceIte, beq_self_eq_true] at ej
      simp only [hlt, ↓reduceIte]
      obtain ⟨va, _, eva, calFF⟩ := evalExpr_call1_inv ej
      obtain ⟨vl, vr, _, evl, evr, opAdd⟩ := evalExpr_binary_inv eva
      obtain ⟨vb, _, evb, calTF⟩ := evalExpr_call1_inv evl
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (hloc j hjlt) evb
      obtain ⟨rfl, rfl⟩ := eval_u8_to_field lib calTF
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
      obtain rfl := binop_add opAdd
      have hcast : ((u64b c j).toNat : F) + 1 = (((u64b c j).toNat + 1 : Nat) : F) := by push_cast; ring
      rw [hcast] at calFF
      exact eval_u8_from_field_lit lib calFF
    · have hbeq : (j == i) = false := beq_false_of_ne heq
      simp only [hlt, hbeq, ↓reduceIte, Bool.false_eq_true] at ej
      simp only [hlt, heq, ↓reduceIte]
      exact evalExpr_var_eq (hloc j hjlt) ej

private theorem evalExpr_wrappingSuccStep_inv (hc : U32.Compatible F)
    (lib : Blake3LibraryWorld world) {locals : Environment F Nat} (c : UInt64)
    (hloc : ∀ j < 8, locals.find? (·.1 == s!"b{j}") = some (s!"b{j}", bv (u64b c j)))
    {k : Nat} (hk : k < 8) {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (wrappingSuccMatch (k + 1)) h r h') :
    let idx := 8 - (k + 1)
    ((u64b c idx).toNat = 255 ∧ EvalExpr world [] locals (wrappingSuccMatch k) h r h') ∨
    ((u64b c idx).toNat ≠ 255 ∧
      r = .tuple ((List.range 8).map fun j =>
        if j < idx then (.field (0 : F) : SourceValue F)
        else if j = idx then .field (((u64b c idx).toNat + 1 : Nat) : F)
        else bv (u64b c j)) ∧ h' = h) := by
  simp only [wrappingSuccMatch] at ev
  obtain ⟨v, hm, evScr, hbr⟩ := evalExpr_match_lit_wild_inv ev
  obtain ⟨vb, _, evb, calTF⟩ := evalExpr_call1_inv evScr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (hloc (8 - (k + 1)) (by omega)) evb
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field lib calTF
  rcases hbr with ⟨heq, hb1⟩ | ⟨hne, hb2⟩
  · have h255 : (u64b c (8 - (k + 1))).toNat = 255 :=
      u32Compat_byte_inj hc (byte_lt _) (by omega) (by simpa using Value.field.inj heq)
    exact .inl ⟨h255, hb1⟩
  · have hne255 : (u64b c (8 - (k + 1))).toNat ≠ 255 := by
      intro e; apply hne; rw [bv, e]; simp
    obtain ⟨rfl, rfl⟩ := evalExpr_wrappingSuccArm_inv lib c hloc (8 - (k + 1)) (by omega) hb2
    exact .inr ⟨hne255, rfl, rfl⟩

include hc lib in
theorem eval_u64_wrapping_succ {c : UInt64} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "UInt64::wrapping_succ" [u64v c] h r h') :
    r = u64v (c + 1) ∧ h' = h := by
  have hnc : hasNoControl (u64WrappingSuccBody (F := F)) = true := by
    simp [u64WrappingSuccBody, hasNoControl, hasNoControl_wrappingSuccMatch]
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.u64_wrapping_succ hnc ev
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evb, k0⟩ := evalExpr_let_array8_inv body
  obtain ⟨hveq, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  rw [u64v_eq] at hveq
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hveq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hveq
  have hloc : ∀ j < 8,
      ([("b0", bv (u64b c 0)), ("b1", bv (u64b c 1)), ("b2", bv (u64b c 2)),
        ("b3", bv (u64b c 3)), ("b4", bv (u64b c 4)), ("b5", bv (u64b c 5)),
        ("b6", bv (u64b c 6)), ("b7", bv (u64b c 7)),
        ("bytes", u64v c)] : Environment F Nat).find? (·.1 == s!"b{j}") =
      some (s!"b{j}", bv (u64b c j)) := by
    intro j hj; interval_cases j <;> rfl
  rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 7) (by omega) k0 with ⟨e0, k1⟩ | ⟨ne0, rfl, rfl⟩
  · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 6) (by omega) k1 with ⟨e1, k2⟩ | ⟨ne1, rfl, rfl⟩
    · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 5) (by omega) k2 with ⟨e2, k3⟩ | ⟨ne2, rfl, rfl⟩
      · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 4) (by omega) k3 with ⟨e3, k4⟩ | ⟨ne3, rfl, rfl⟩
        · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 3) (by omega) k4 with ⟨e4, k5⟩ | ⟨ne4, rfl, rfl⟩
          · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 2) (by omega) k5 with ⟨e5, k6⟩ | ⟨ne5, rfl, rfl⟩
            · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 1) (by omega) k6 with ⟨e6, k7⟩ | ⟨ne6, rfl, rfl⟩
              · rcases evalExpr_wrappingSuccStep_inv hc lib c hloc (k := 0) (by omega) k7 with ⟨e7, k8⟩ | ⟨ne7, rfl, rfl⟩
                · obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, _, _, _, _, _, _, _,
                    g0, g1, g2, g3, g4, g5, g6, g7, rfl⟩ := evalExpr_array8_inv k8
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g0
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g1
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g2
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g3
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g4
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g5
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g6
                  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) g7
                  refine ⟨?_, rfl⟩
                  rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0)
                    (r6 := 0) (r7 := 0) (by simp [U64.wrappingSuccBytes, e0, e1, e2, e3, e4, e5, e6, e7])]
                · refine ⟨?_, rfl⟩
                  rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0)
                    (r6 := 0) (r7 := (u64b c 7).toNat + 1)
                    (by simp [U64.wrappingSuccBytes, e0, e1, e2, e3, e4, e5, e6, ne7])]
                  simp [List.range_succ, bv]
              · refine ⟨?_, rfl⟩
                rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0)
                  (r6 := (u64b c 6).toNat + 1) (r7 := (u64b c 7).toNat)
                  (by simp [U64.wrappingSuccBytes, e0, e1, e2, e3, e4, e5, ne6])]
                simp [List.range_succ, bv]
            · refine ⟨?_, rfl⟩
              rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0)
                (r5 := (u64b c 5).toNat + 1) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat)
                (by simp [U64.wrappingSuccBytes, e0, e1, e2, e3, e4, ne5])]
              simp [List.range_succ, bv]
          · refine ⟨?_, rfl⟩
            rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0)
              (r4 := (u64b c 4).toNat + 1) (r5 := (u64b c 5).toNat)
              (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat)
              (by simp [U64.wrappingSuccBytes, e0, e1, e2, e3, ne4])]
            simp [List.range_succ, bv]
        · refine ⟨?_, rfl⟩
          rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0)
            (r3 := (u64b c 3).toNat + 1) (r4 := (u64b c 4).toNat)
            (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat)
            (by simp [U64.wrappingSuccBytes, e0, e1, e2, ne3])]
          simp [List.range_succ, bv]
      · refine ⟨?_, rfl⟩
        rw [u64v_succ c (r0 := 0) (r1 := 0)
          (r2 := (u64b c 2).toNat + 1) (r3 := (u64b c 3).toNat) (r4 := (u64b c 4).toNat)
          (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat)
          (by simp [U64.wrappingSuccBytes, e0, e1, ne2])]
        simp [List.range_succ, bv]
    · refine ⟨?_, rfl⟩
      rw [u64v_succ c (r0 := 0)
        (r1 := (u64b c 1).toNat + 1) (r2 := (u64b c 2).toNat) (r3 := (u64b c 3).toNat)
        (r4 := (u64b c 4).toNat) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat)
        (r7 := (u64b c 7).toNat) (by simp [U64.wrappingSuccBytes, e0, ne1])]
      simp [List.range_succ, bv]
  · refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := (u64b c 0).toNat + 1) (r1 := (u64b c 1).toNat)
      (r2 := (u64b c 2).toNat) (r3 := (u64b c 3).toNat) (r4 := (u64b c 4).toNat)
      (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat)
      (by simp [U64.wrappingSuccBytes, ne0])]
    simp [List.range_succ, bv]

end Primitives

/-! ## Section 5: Operational `EvalFn` Contracts for BLAKE3 Compression -/

section Compression

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F} (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)

omit [DecidableEq F] in
private theorem stateL_length (s m : Blake3.Pure.Block) :
    (stateL (F := F) s m).length = 32 := by
  simp [stateL]

omit [DecidableEq F] in
private theorem proj_stateV_lo (s m : Blake3.Pure.Block) (i : Nat) (hi : i < 16) :
    projectValue (stateV (F := F) s m) i = .ok (wv s[i]) := by
  have hl : i < (stateL (F := F) s m).length := by rw [stateL_length]; omega
  have hl' : i < (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F))).length := by
    simpa using hi
  rw [stateV, proj_getElem _ _ hl]
  simp only [stateL]
  rw [List.getElem_append_left hl', List.getElem_ofFn]
  rfl

omit [DecidableEq F] in
private theorem proj_stateV_hi (s m : Blake3.Pure.Block) (j : Nat) (hj : j < 16) :
    projectValue (stateV (F := F) s m) (16 + j) = .ok (wv m[j]) := by
  have hl : 16 + j < (stateL (F := F) s m).length := by rw [stateL_length]; omega
  have hl' : (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F))).length ≤ 16 + j := by
    simp
  rw [stateV, proj_getElem _ _ hl]
  simp only [stateL]
  rw [List.getElem_append_right hl', List.getElem_ofFn]
  simp

private theorem mapM_some_eq {α β : Type} (f : α → Option β) (g : α → β)
    (hfg : ∀ a, f a = some (g a)) : ∀ l : List α, l.mapM f = some (l.map g)
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, hfg, mapM_some_eq f g hfg l]

private theorem zipIdx_map_set {α : Type} (vs : List α) (i : Nat) (x : α) :
    (vs.zipIdx.map fun p => if p.2 == i then x else p.1) = vs.set i x := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

private theorem mapM_zipIdx_set {α : Type} (vs : List α) (i : Nat) (x : α) :
    (vs.zipIdx.mapM fun p => if (p.2 == i) = true then (some x : Option α) else some p.1) =
      some (vs.set i x) := by
  rw [mapM_some_eq _ (fun p => if (p.2 == i) = true then x else p.1)
    (fun p => by by_cases h : (p.2 == i) = true <;> simp [h]), zipIdx_map_set]

omit [Field F] [DecidableEq F] in
private theorem update_index (types : List (String × Aiur.Generic.Ty)) (vs : List (SourceValue F))
    (i n : Nat) (x : SourceValue F) (hn : vs.length = n) :
    Update.value types [[.index i n]] [.tuple vs, x] = .ok (.tuple (vs.set i x)) := by
  subst hn
  simp only [Update.value, Update.apply, Update.replace, Update.unpack, Update.pack,
    UpdateStep.owner, UpdateStep.width, UpdateStep.position, ↓reduceIte, bind, Option.bind, pure]
  erw [mapM_zipIdx_set]

omit [DecidableEq F] in
private theorem ofFn_set (v : Vector UInt32 16) (i : Nat) (hi : i < 16) (w : UInt32) :
    (List.ofFn fun k : Fin 16 => (wv (F := F) v[k])).set i (wv w) =
      List.ofFn fun k : Fin 16 => (wv (F := F) (v.set i w hi)[k]) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_set, List.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
  by_cases h : i = k <;> simp [h]

omit [DecidableEq F] in
private theorem update_stateV_lo (types : List (String × Aiur.Generic.Ty))
    (s m : Blake3.Pure.Block) (i : Fin 16) (w : UInt32) :
    Update.value types [[.index i.val 32]] [stateV (F := F) s m, wv w] =
      .ok (stateV (s.set i w) m) := by
  rw [stateV, update_index types (stateL s m) i.val 32 (wv w) (stateL_length s m), stateV]
  congr 2
  have hi : i.val < (List.ofFn (fun k : Fin 16 => (wv (F := F) s[k]))).length := by simp
  simp only [stateL]
  rw [List.set_append_left i.val (wv w) hi, ofFn_set s i.val i.isLt w]

omit [DecidableEq F] in
private theorem update_stateV_hi (types : List (String × Aiur.Generic.Ty))
    (s m : Blake3.Pure.Block) (j : Fin 16) (w : UInt32) :
    Update.value types [[.index (16 + j.val) 32]] [stateV (F := F) s m, wv w] =
      .ok (stateV s (m.set j w)) := by
  rw [stateV, update_index types (stateL s m) (16 + j.val) 32 (wv w) (stateL_length s m), stateV]
  congr 2
  apply List.ext_getElem (by simp [stateL])
  intro k h1 h2
  simp only [stateL, List.getElem_set]
  by_cases hlt : k < 16
  · have hne : 16 + j.val ≠ k := by omega
    have hl : k < (List.ofFn (fun i : Fin 16 => (wv (F := F) s[i]))).length := by simpa using hlt
    simp only [hne, ↓reduceIte, List.getElem_append_left hl]
  · have hge : (List.ofFn (fun i : Fin 16 => (wv (F := F) s[i]))).length ≤ k := by simp; omega
    rw [List.getElem_append_right hge, List.getElem_append_right hge]
    simp only [List.length_ofFn, List.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
    by_cases heq : 16 + j.val = k
    · subst heq; simp
    · have hj' : j.val ≠ k - 16 := by omega
      simp [heq, hj']

/-! ### `Blake3::iv` -/

include lib in
theorem eval_iv {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::iv" [] h r h') :
    r = vecV Blake3.Pure.iv ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_iv rfl ev
  have heach : ∀ q ∈ ivWordBytes, ∀ h1 rv h2,
      EvalExpr world [] []
        (.call "UInt32::from_bytes" (some [])
          [.array [gByte q.1, gByte q.2.1, gByte q.2.2.1, gByte q.2.2.2]]) h1 rv h2 →
      rv = w4 (UInt8.ofNat q.1) (UInt8.ofNat q.2.1)
              (UInt8.ofNat q.2.2.1) (UInt8.ofNat q.2.2.2) ∧ h2 = h1 := by
    intro ⟨a, b, c, d⟩ hmem h1 rv h2 e
    have hlt : a ∈ ivByteNums ∧ b ∈ ivByteNums ∧ c ∈ ivByteNums ∧ d ∈ ivByteNums ∧
        a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256 := by
      simp only [ivWordBytes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
    obtain ⟨va, _, eva, cal⟩ := evalExpr_call1_inv e
    obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv eva
    obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes a hlt.1) e0
    obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes b hlt.2.1) e1
    obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes c hlt.2.2.1) e2
    obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes d hlt.2.2.2.1) e3
    obtain ⟨rfl, rfl⟩ := eval_u32_from_bytes lib cal
    exact ⟨by simp [w4, bv_ofNat hlt.2.2.2.2.1, bv_ofNat hlt.2.2.2.2.2.1,
      bv_ofNat hlt.2.2.2.2.2.2.1, bv_ofNat hlt.2.2.2.2.2.2.2], rfl⟩
  obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv ivWordBytes heach body
  refine ⟨?_, rfl⟩
  rw [← Aiur.Library.Blake3.iv_spec]
  simp only [vecV, List.ofFn_succ, List.ofFn_zero, ivWordBytes, List.map_cons, List.map_nil,
    Fin.getElem_fin]
  rfl

/-! ### `Blake3::g_function` and `Blake3::compress_inner_j` -/

include hc lib in
theorem eval_g_function {a b c d x y : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::g_function" [wv a, wv b, wv c, wv d, wv x, wv y] h r h') :
    r = vecV (Blake3.Pure.mix a b c d x y) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_g_function rfl ev
  -- a1 = add3(a, b, x)
  obtain ⟨va1, _, eva1, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨u1, u2, u3, _, _, _, e1, e2, e3, cal1⟩ := evalExpr_call3_inv eva1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  obtain ⟨rfl, rfl⟩ := eval_u32_add3 hc lib cal1
  -- d1 = rotr16(xor(d, a1))
  obtain ⟨vd1, _, evd1, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨ux1, _, evx1, calR16⟩ := evalExpr_call1_inv evd1
  obtain ⟨u4, u5, _, _, e4, e5, calX1⟩ := evalExpr_call2_inv evx1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
  obtain ⟨rfl, rfl⟩ := eval_u32_xor hc lib calX1
  obtain ⟨rfl, rfl⟩ := eval_u32_rotr16 lib calR16
  -- c1 = add(c, d1)
  obtain ⟨vc1, _, evc1, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨u6, u7, _, _, e6, e7, calA1⟩ := evalExpr_call2_inv evc1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e7
  obtain ⟨rfl, rfl⟩ := eval_u32_add hc lib calA1
  -- b1 = xor_rotr12(b, c1)
  obtain ⟨vb1, _, evb1, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨u8, u9, _, _, e8, e9, calR12⟩ := evalExpr_call2_inv evb1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e8
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e9
  obtain ⟨rfl, rfl⟩ := eval_u32_xor_rotr12 hc lib calR12
  -- a2 = add3(a1, b1, y)
  obtain ⟨va2, _, eva2, k5⟩ := evalExpr_let_bind_inv k4
  obtain ⟨u10, u11, u12, _, _, _, e10, e11, e12, cal2⟩ := evalExpr_call3_inv eva2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e10
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e11
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e12
  obtain ⟨rfl, rfl⟩ := eval_u32_add3 hc lib cal2
  -- d2 = rotr8(xor(d1, a2))
  obtain ⟨vd2, _, evd2, k6⟩ := evalExpr_let_bind_inv k5
  obtain ⟨ux2, _, evx2, calR8⟩ := evalExpr_call1_inv evd2
  obtain ⟨u13, u14, _, _, e13, e14, calX2⟩ := evalExpr_call2_inv evx2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e13
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e14
  obtain ⟨rfl, rfl⟩ := eval_u32_xor hc lib calX2
  obtain ⟨rfl, rfl⟩ := eval_u32_rotr8 lib calR8
  -- c2 = add(c1, d2)
  obtain ⟨vc2, _, evc2, k7⟩ := evalExpr_let_bind_inv k6
  obtain ⟨u15, u16, _, _, e15, e16, calA2⟩ := evalExpr_call2_inv evc2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e15
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e16
  obtain ⟨rfl, rfl⟩ := eval_u32_add hc lib calA2
  -- b2 = xor_rotr7(b1, c2)
  obtain ⟨vb2, _, evb2, k8⟩ := evalExpr_let_bind_inv k7
  obtain ⟨u17, u18, _, _, e17, e18, calR7⟩ := evalExpr_call2_inv evb2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e17
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e18
  obtain ⟨rfl, rfl⟩ := eval_u32_xor_rotr7 hc lib calR7
  -- [a2, b2, c2, d2]
  obtain ⟨r0, r1, r2, r3, _, _, _, er0, er1, er2, er3, rfl⟩ := evalExpr_array4_inv k8
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) er0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) er1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) er2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) er3
  exact ⟨rfl, rfl⟩

private theorem evalExpr_updStep_inv {locals : Environment F Nat}
    {s m : Blake3.Pure.Block} {i : Fin 16} {n : String} {w : UInt32}
    {rest : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hs : locals.find? (·.1 == "state") = some ("state", stateV s m))
    (hn : locals.find? (·.1 == n) = some (n, wv w))
    (ev : EvalExpr world [] locals
      (.letValue (.bind "state") (.update [[.index i.val 32]] [.var "state", .var n]) rest) h r h') :
    EvalExpr world [] (("state", stateV (s.set i w) m) :: locals) rest h r h' := by
  obtain ⟨v, _, evUp, kb⟩ := evalExpr_let_bind_inv ev
  obtain ⟨vb, vr, _, evb, evr, hup⟩ := evalExpr_update1_inv evUp
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hs evb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hn evr
  rw [update_stateV_lo] at hup
  cases hup
  exact kb

private theorem evalExpr_gStep_inv (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)
    {locals : Environment F Nat} {s m : Blake3.Pure.Block} {a b c d : Fin 16}
    {jx jy : Nat} (hjx : jx < 16) (hjy : jy < 16)
    {rest : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hloc : locals.find? (·.1 == "state") = some ("state", stateV s m))
    (ev : EvalExpr world [] locals (gStep a b c d jx jy rest) h r h') :
    ∃ locals' : Environment F Nat,
      locals'.find? (·.1 == "state") =
        some ("state", stateV (Blake3.Pure.g s a b c d m[jx] m[jy]) m) ∧
      EvalExpr world [] locals' rest h r h' := by
  unfold gStep at ev
  obtain ⟨va, vb, vc, vd, _, evG, kb⟩ := evalExpr_let_array4_inv ev
  obtain ⟨u0, u1, u2, u3, u4, u5, _, _, _, _, _, _, e0, e1, e2, e3, e4, e5, calG⟩ :=
    evalExpr_call6_inv evG
  have hlo : ∀ (idx : Fin 16) {rv : SourceValue F} {h1 h2 : Heap F},
      EvalExpr world [] locals (.index (.var "state") idx.val) h1 rv h2 →
      rv = wv s[idx.val] ∧ h2 = h1 := by
    intro idx rv h1 h2 e
    obtain ⟨vst, evst, pr⟩ := evalExpr_index_inv e
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hloc evst
    exact ⟨(Except.ok.inj ((proj_stateV_lo s m idx.val idx.isLt).symm.trans pr)).symm, rfl⟩
  have hhi : ∀ (idx : Nat) (hidx : idx < 16) {rv : SourceValue F} {h1 h2 : Heap F},
      EvalExpr world [] locals (.index (.var "state") (16 + idx)) h1 rv h2 →
      rv = wv m[idx] ∧ h2 = h1 := by
    intro idx hidx rv h1 h2 e
    obtain ⟨vst, evst, pr⟩ := evalExpr_index_inv e
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hloc evst
    exact ⟨(Except.ok.inj ((proj_stateV_hi s m idx hidx).symm.trans pr)).symm, rfl⟩
  obtain ⟨rfl, rfl⟩ := hlo a e0
  obtain ⟨rfl, rfl⟩ := hlo b e1
  obtain ⟨rfl, rfl⟩ := hlo c e2
  obtain ⟨rfl, rfl⟩ := hlo d e3
  obtain ⟨rfl, rfl⟩ := hhi jx hjx e4
  obtain ⟨rfl, rfl⟩ := hhi jy hjy e5
  obtain ⟨hmix, rfl⟩ := eval_g_function hc lib calG
  set mx := Blake3.Pure.mix s[a.val] s[b.val] s[c.val] s[d.val] m[jx] m[jy]
  have hv4 : (vecV mx : SourceValue F) = .tuple [wv mx[0], wv mx[1], wv mx[2], wv mx[3]] := rfl
  rw [hv4] at hmix
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hmix
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hmix
  have hst0 : ([("a", wv mx[0]), ("b", wv mx[1]), ("c", wv mx[2]), ("d", wv mx[3])] ++ locals).find?
      (·.1 == "state") = some ("state", stateV s m) := by simpa using hloc
  have kb1 := evalExpr_updStep_inv hst0 (by simp; rfl) kb
  have kb2 := evalExpr_updStep_inv (by simp; rfl) (by simp; rfl) kb1
  have kb3 := evalExpr_updStep_inv (by simp; rfl) (by simp; rfl) kb2
  have kb4 := evalExpr_updStep_inv (by simp; rfl) (by simp; rfl) kb3
  exact ⟨_, by simp [Blake3.Pure.g, mx], kb4⟩

include hc lib in
theorem eval_compress_inner_j {s m : Blake3.Pure.Block} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_inner_j" [stateV s m] h r h') :
    r = stateV (Aiur.Library.Blake3.compressInnerJ s m) m ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress_inner_j rfl ev
  obtain ⟨l1, h1, d1⟩ := evalExpr_gStep_inv hc lib (a := 0) (b := 4) (c := 8) (d := 12)
    (jx := 0) (jy := 1) (by decide) (by decide) (by simp; rfl) body
  obtain ⟨l2, h2, d2⟩ := evalExpr_gStep_inv hc lib (a := 1) (b := 5) (c := 9) (d := 13)
    (jx := 2) (jy := 3) (by decide) (by decide) h1 d1
  obtain ⟨l3, h3, d3⟩ := evalExpr_gStep_inv hc lib (a := 2) (b := 6) (c := 10) (d := 14)
    (jx := 4) (jy := 5) (by decide) (by decide) h2 d2
  obtain ⟨l4, h4, d4⟩ := evalExpr_gStep_inv hc lib (a := 3) (b := 7) (c := 11) (d := 15)
    (jx := 6) (jy := 7) (by decide) (by decide) h3 d3
  obtain ⟨l5, h5, d5⟩ := evalExpr_gStep_inv hc lib (a := 0) (b := 5) (c := 10) (d := 15)
    (jx := 8) (jy := 9) (by decide) (by decide) h4 d4
  obtain ⟨l6, h6, d6⟩ := evalExpr_gStep_inv hc lib (a := 1) (b := 6) (c := 11) (d := 12)
    (jx := 10) (jy := 11) (by decide) (by decide) h5 d5
  obtain ⟨l7, h7, d7⟩ := evalExpr_gStep_inv hc lib (a := 2) (b := 7) (c := 8) (d := 13)
    (jx := 12) (jy := 13) (by decide) (by decide) h6 d6
  obtain ⟨l8, h8, d8⟩ := evalExpr_gStep_inv hc lib (a := 3) (b := 4) (c := 9) (d := 14)
    (jx := 14) (jy := 15) (by decide) (by decide) h7 d7
  exact evalExpr_var_eq h8 d8

/-! ### `Blake3::compress` and `Blake3::compress_init` -/

/-- `n` rounds of `Blake3::compress` (each round applies `compressInnerJ` and `permute`). -/
def compressRounds : Nat → Blake3.Pure.Block → Blake3.Pure.Block →
    Blake3.Pure.Block × Blake3.Pure.Block
  | 0, s, m => (s, m)
  | n + 1, s, m =>
    compressRounds n (Aiur.Library.Blake3.compressInnerJ s m) (Aiur.Library.Blake3.permute m)

theorem compressRounds_seven (s m : Blake3.Pure.Block) :
    (compressRounds 7 s m).1 = Aiur.Library.Blake3.compressInnerI s m := rfl

private theorem evalExpr_permuteExpr_inv {dst src : String}
    (hne : dst ≠ src) {sSrc mSrc sDst : Blake3.Pure.Block} :
    ∀ (ps : List (Fin 16 × Fin 16)) (mCur : Blake3.Pure.Block)
      {locals' : Environment F Nat} {rest : Aiur.Generic.Expr F} {h h' : Heap F}
      {r : SourceValue F},
      locals'.find? (·.1 == src) = some (src, stateV sSrc mSrc) →
      locals'.find? (·.1 == dst) = some (dst, stateV sDst mCur) →
      EvalExpr world [] locals' (permuteExpr dst src ps rest) h r h' →
      ∃ locals'' : Environment F Nat,
        locals''.find? (·.1 == dst) =
          some (dst, stateV sDst (ps.foldl (fun acc p => acc.set p.1 mSrc[p.2]) mCur)) ∧
        (∀ nm, nm ≠ dst → locals''.find? (·.1 == nm) = locals'.find? (·.1 == nm)) ∧
        EvalExpr world [] locals'' rest h r h'
  | [], mCur, locals', rest, h, h', r, _, hdst, ev =>
    ⟨locals', hdst, fun _ _ => rfl, ev⟩
  | (i, j) :: ps, mCur, locals', rest, h, h', r, hsrc', hdst, ev => by
    simp only [permuteExpr] at ev
    obtain ⟨v, _, evUp, kb⟩ := evalExpr_let_bind_inv ev
    obtain ⟨vb, vr, _, evb, evr, hup⟩ := evalExpr_update1_inv evUp
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hdst evb
    obtain ⟨vsr, evsr, pr⟩ := evalExpr_index_inv evr
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hsrc' evsr
    obtain rfl := Except.ok.inj ((proj_stateV_hi sSrc mSrc j.val j.isLt).symm.trans pr)
    rw [update_stateV_hi] at hup
    cases hup
    have hsrc'' : ((dst, stateV sDst (mCur.set i mSrc[j])) :: locals').find? (·.1 == src) =
        some (src, stateV sSrc mSrc) := by
      simp [beq_false_of_ne hne, hsrc']
    obtain ⟨locals'', hdst'', hpres, evRest⟩ :=
      evalExpr_permuteExpr_inv hne ps (mCur.set i mSrc[j]) hsrc'' (by simp; rfl) kb
    refine ⟨locals'', hdst'', ?_, evRest⟩
    intro nm hnm
    rw [hpres nm hnm]
    simp [beq_false_of_ne hnm.symm]

private theorem foldl_permutePairs (m : Blake3.Pure.Block) :
    permutePairs.foldl (fun acc p => acc.set p.1 m[p.2]) m = Aiur.Library.Blake3.permute m := by
  apply Vector.ext
  intro i hi
  simp only [permutePairs, List.foldl_cons, List.foldl_nil, Aiur.Library.Blake3.permute,
    Vector.getElem_set]
  interval_cases i <;> simp

private theorem output_ne_s1 (n : Nat) (hn : n < 8) : (s!"output{n}" == "s1") = false := by
  interval_cases n <;> decide

private theorem output_ne_output {m n : Nat} (hm : m < 8) (hn : n < 8) (hne : m ≠ n) :
    (s!"output{m}" == s!"output{n}") = false := by
  interval_cases m <;> interval_cases n <;> first | exact absurd rfl hne | decide

private theorem evalExpr_finalizeOutputs_inv (hc : U32.Compatible F)
    (lib : Blake3LibraryWorld world) {s1 m : Blake3.Pure.Block} :
    ∀ (k : Nat) (hk : k ≤ 8) {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      locals.find? (·.1 == "s1") = some ("s1", stateV s1 m) →
      (∀ i (hi : i < 8 - k), locals.find? (·.1 == s!"output{i}") =
        some (s!"output{i}", wv (s1[i]'(by omega) ^^^ s1[i + 8]'(by omega)))) →
      EvalExpr world [] locals (finalizeOutputsExpr k) h r h' →
      r = vecV (Aiur.Library.Blake3.finalizeState s1) ∧ h' = h
  | 0, _, locals, h, h', r, _, hout, ev => by
    simp only [finalizeOutputsExpr] at ev
    obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv (List.range 8)
      (g := fun i => if hi : i < 8 then wv (s1[i]'(by omega) ^^^ s1[i + 8]'(by omega)) else .tuple [])
      (fun i hi h1 rv h2 ei => by
        have hilt : i < 8 := List.mem_range.mp hi
        simp only [hilt, ↓reduceDIte]
        exact evalExpr_var_eq (hout i (by omega)) ei) ev
    refine ⟨?_, rfl⟩
    simp only [vecV, Aiur.Library.Blake3.finalizeState]
    congr 1
  | k + 1, hk, locals, h, h', r, hs1, hout, ev => by
    simp only [finalizeOutputsExpr] at ev
    set idx := 8 - (k + 1)
    obtain ⟨vo, _, evo, kb⟩ := evalExpr_let_bind_inv ev
    obtain ⟨va, vb, _, _, eva, evb, calX⟩ := evalExpr_call2_inv evo
    obtain ⟨vsa, evsa, pra⟩ := evalExpr_index_inv eva
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hs1 evsa
    obtain rfl := Except.ok.inj ((proj_stateV_lo s1 m idx (by omega)).symm.trans pra)
    obtain ⟨vsb, evsb, prb⟩ := evalExpr_index_inv evb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hs1 evsb
    obtain rfl := Except.ok.inj ((proj_stateV_lo s1 m (idx + 8) (by omega)).symm.trans prb)
    obtain ⟨rfl, rfl⟩ := eval_u32_xor hc lib calX
    have hs1' : ((s!"output{idx}", wv (s1[idx]'(by omega) ^^^ s1[idx + 8]'(by omega))) :: locals).find?
        (·.1 == "s1") = some ("s1", stateV s1 m) := by
      simp only [List.find?_cons, output_ne_s1 idx (by omega), hs1]
    have hout' : ∀ i (hi : i < 8 - k),
        ((s!"output{idx}", wv (s1[idx]'(by omega) ^^^ s1[idx + 8]'(by omega))) :: locals).find?
          (·.1 == s!"output{i}") =
          some (s!"output{i}", wv (s1[i]'(by omega) ^^^ s1[i + 8]'(by omega))) := by
      intro i hi
      by_cases hieq : i = idx
      · subst hieq; simp
      · simp only [List.find?_cons, output_ne_output (by omega) (by omega) (Ne.symm hieq),
          hout i (by omega)]
    exact evalExpr_finalizeOutputs_inv hc lib k (by omega) hs1' hout' kb

include hc lib in
/-- **`Blake3::compress(stage, state)`**: runs 2 rounds per stage for `stage = 0, 1, 2` and the
7th round + finalization at `stage = 3`. -/
theorem eval_compress :
    ∀ (n : Nat) {k : Nat} {s m : Blake3.Pure.Block} {r : SourceValue F} {h h' : Heap F},
      k + n = 3 →
      EvalFn world "Blake3::compress" [.field (k : F), stateV s m] h r h' →
      r = vecV (Aiur.Library.Blake3.finalizeState (compressRounds (2 * n + 1) s m).1) ∧ h' = h
  | 0, k, s, m, r, h, h', hk, ev => by
    have hk3 : k = 3 := by omega
    subst hk3
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress rfl ev
    obtain ⟨vs1, _, evs1, k1⟩ := evalExpr_let_bind_inv body
    obtain ⟨vst, _, evst, calCij⟩ := evalExpr_call1_inv evs1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evst
    obtain ⟨rfl, rfl⟩ := eval_compress_inner_j hc lib calCij
    obtain ⟨vstage, _, evStage, hbr⟩ := evalExpr_match_lit_wild_inv k1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evStage
    rcases hbr with ⟨_, hb3⟩ | ⟨hne, _⟩
    · exact evalExpr_finalizeOutputs_inv hc lib 8 (by omega) (by simp; rfl) (fun i hi => by omega) hb3
    · exact absurd (by simp) hne
  | n + 1, k, s, m, r, h, h', hk, ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress rfl ev
    obtain ⟨vs1, _, evs1, k1⟩ := evalExpr_let_bind_inv body
    obtain ⟨vst, _, evst, calCij1⟩ := evalExpr_call1_inv evs1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evst
    obtain ⟨rfl, rfl⟩ := eval_compress_inner_j hc lib calCij1
    obtain ⟨vstage, _, evStage, hbr⟩ := evalExpr_match_lit_wild_inv k1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evStage
    rcases hbr with ⟨heq3, _⟩ | ⟨_, hbW⟩
    · have hk3 : k = 3 := u32Compat_small_inj hc (by omega) (by omega) (by simpa using Value.field.inj heq3)
      omega
    · obtain ⟨l1, hdst1, hpres1, k2⟩ :=
        evalExpr_permuteExpr_inv (dst := "s1") (src := "state") (by decide)
          permutePairs m (by simp; rfl) (by simp; rfl) hbW
      rw [foldl_permutePairs] at hdst1
      obtain ⟨vs2, _, evs2, k3⟩ := evalExpr_let_bind_inv k2
      obtain ⟨vs1', _, evs1', calCij2⟩ := evalExpr_call1_inv evs2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hdst1 evs1'
      obtain ⟨rfl, rfl⟩ := eval_compress_inner_j hc lib calCij2
      have hs1_in : (("s2", stateV (Aiur.Library.Blake3.compressInnerJ
          (Aiur.Library.Blake3.compressInnerJ s m) (Aiur.Library.Blake3.permute m))
          (Aiur.Library.Blake3.permute m)) :: l1).find? (·.1 == "s1") =
          some ("s1", stateV (Aiur.Library.Blake3.compressInnerJ s m) (Aiur.Library.Blake3.permute m)) := by
        simp [hdst1]
      obtain ⟨l2, hdst2, hpres2, k4⟩ :=
        evalExpr_permuteExpr_inv (dst := "s2") (src := "s1") (by decide)
          permutePairs (Aiur.Library.Blake3.permute m) hs1_in (by simp; rfl) k3
      rw [foldl_permutePairs] at hdst2
      obtain ⟨vNextStage, vNextState, _, _, evNS, evNSt, calRec⟩ := evalExpr_call2_inv k4
      obtain ⟨vk, v1, _, evk, ev1, opAdd⟩ := evalExpr_binary_inv evNS
      have hstage_in : l2.find? (·.1 == "stage") = some ("stage", .field (k : F)) := by
        rw [hpres2 "stage" (by decide)]
        simp only [List.find?_cons, show ("s2" == "stage") = false from by decide]
        rw [hpres1 "stage" (by decide)]
        simp
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hstage_in evk
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
      obtain rfl := binop_add opAdd
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hdst2 evNSt
      have hcast : (k : F) + 1 = ((k + 1 : Nat) : F) := by push_cast; ring
      rw [hcast] at calRec
      have ih := eval_compress n (k := k + 1) (by omega) calRec
      have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [h2]
      exact ih

private theorem lo_word (c : UInt64) :
    Aiur.Library.Blake3.wordOfBytes (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3) = c.toUInt32 := by
  apply UInt32.ext
  rw [Aiur.Library.Blake3.wordOfBytes_toNat, UInt64.toNat_toUInt32]
  simp only [u64b_toNat, U32.pack]
  omega

private theorem hi_word (c : UInt64) :
    Aiur.Library.Blake3.wordOfBytes (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7) =
      (c >>> 32).toUInt32 := by
  apply UInt32.ext
  rw [Aiur.Library.Blake3.wordOfBytes_toNat, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have hshift : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [hshift, Nat.shiftRight_eq_div_pow]
  simp only [u64b_toNat, U32.pack]
  omega

omit [DecidableEq F] in
private theorem small_word {n : Nat} (hn : n < 256) :
    (.tuple [.field (n : F), .field 0, .field 0, .field 0] : SourceValue F) = wv n.toUInt32 := by
  have e : Aiur.Library.Blake3.wordOfBytes (UInt8.ofNat n) 0 0 0 = n.toUInt32 := by
    apply UInt32.ext
    rw [Aiur.Library.Blake3.wordOfBytes_toNat, toNat_ofNat_lt hn, Nat.toUInt32_eq, UInt32.toNat_ofNat']
    simp only [U32.pack, UInt8.toNat_zero]
    omega
  rw [← e, wv_wordOfBytes, w4]
  simp [bv_ofNat hn]

private theorem evalArgs_append_inv {types : Types} {locals : Environment F Nat}
    {xs ys : List (Aiur.Generic.Expr F)} {h h' : Heap F} {vs : List (SourceValue F)}
    (ev : EvalArgs world types locals (xs ++ ys) h vs h') :
    ∃ vxs vys hm, vs = vxs ++ vys ∧
      EvalArgs world types locals xs h vxs hm ∧
      EvalArgs world types locals ys hm vys h' := by
  induction xs generalizing h vs with
  | nil => exact ⟨[], vs, h, rfl, .nil, ev⟩
  | cons x tl ih =>
    cases ev with
    | cons hd tlEv =>
      obtain ⟨vxs, vys, hm, rfl, hxs, hys⟩ := ih tlEv
      exact ⟨_ :: vxs, vys, hm, rfl, .cons hd hxs, hys⟩

include hc lib in
/-- **`Blake3::compress_init`** computes `Blake3.Pure.compress` on its chaining value,
16-word message block, 64-bit counter, byte length (`< 256`), and flags (`< 256`). -/
theorem eval_compress_init {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len fl : Nat} (hlen : len < 256) (hfl : fl < 256) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v c, .field (len : F), .field (fl : F)] h r h') :
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl.toUInt32) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress_init rfl ev
  obtain ⟨viv, _, eviv, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := eval_iv lib (evalExpr_call0_inv eviv)
  obtain ⟨viv0, _, eviv0, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vt0, evt0, pr0⟩ := evalExpr_index_inv eviv0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt0
  obtain rfl := Except.ok.inj ((proj_vecV Blake3.Pure.iv 0 (by decide)).symm.trans pr0)
  obtain ⟨viv1, _, eviv1, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨vt1, evt1, pr1⟩ := evalExpr_index_inv eviv1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt1
  obtain rfl := Except.ok.inj ((proj_vecV Blake3.Pure.iv 1 (by decide)).symm.trans pr1)
  obtain ⟨viv2, _, eviv2, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨vt2, evt2, pr2⟩ := evalExpr_index_inv eviv2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt2
  obtain rfl := Except.ok.inj ((proj_vecV Blake3.Pure.iv 2 (by decide)).symm.trans pr2)
  obtain ⟨viv3, _, eviv3, k5⟩ := evalExpr_let_bind_inv k4
  obtain ⟨vt3, evt3, pr3⟩ := evalExpr_index_inv eviv3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt3
  obtain rfl := Except.ok.inj ((proj_vecV Blake3.Pure.iv 3 (by decide)).symm.trans pr3)
  obtain ⟨vcl, _, evcl, k6⟩ := evalExpr_let_bind_inv k5
  obtain ⟨vsl, _, evsl, calCL⟩ := evalExpr_call1_inv evcl
  obtain ⟨vc1, evc1, hsl1⟩ := evalExpr_slice_inv evsl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
  obtain rfl := Except.ok.inj ((show sliceValue (u64v c : SourceValue F) 0 (some 4) =
    .ok (w4 (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3)) from rfl).symm.trans hsl1)
  obtain ⟨rfl, rfl⟩ := eval_u32_from_bytes lib calCL
  obtain ⟨vch, _, evch, k7⟩ := evalExpr_let_bind_inv k6
  obtain ⟨vsh, _, evsh, calCH⟩ := evalExpr_call1_inv evch
  obtain ⟨vc2, evc2, hsl2⟩ := evalExpr_slice_inv evsh
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
  obtain rfl := Except.ok.inj ((show sliceValue (u64v c : SourceValue F) 4 (some 8) =
    .ok (w4 (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7)) from rfl).symm.trans hsl2)
  obtain ⟨rfl, rfl⟩ := eval_u32_from_bytes lib calCH
  obtain ⟨vlen, _, evlen, k8⟩ := evalExpr_let_bind_inv k7
  obtain ⟨vla, _, evla, calLen⟩ := evalExpr_call1_inv evlen
  obtain ⟨l0, l1, l2, l3, _, _, _, el0, el1, el2, el3, rfl⟩ := evalExpr_array4_inv evla
  obtain ⟨vlf, _, evlf, calLFF⟩ := evalExpr_call1_inv el0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlf
  obtain ⟨rfl, rfl⟩ := eval_u8_from_field_lit lib calLFF
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) el1
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) el2
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) el3
  obtain ⟨rfl, rfl⟩ := eval_u32_from_bytes lib calLen
  obtain ⟨vfl, _, evfl, k9⟩ := evalExpr_let_bind_inv k8
  obtain ⟨vfa, _, evfa, calFl⟩ := evalExpr_call1_inv evfl
  obtain ⟨f0, f1, f2, f3, _, _, _, ef0, ef1, ef2, ef3, rfl⟩ := evalExpr_array4_inv evfa
  obtain ⟨vff, _, evff, calFFF⟩ := evalExpr_call1_inv ef0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evff
  obtain ⟨rfl, rfl⟩ := eval_u8_from_field_lit lib calFFF
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) ef1
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) ef2
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) ef3
  obtain ⟨rfl, rfl⟩ := eval_u32_from_bytes lib calFl
  obtain ⟨vst, _, evstAsc, k10⟩ := evalExpr_let_bind_inv k9
  have evst := evalExpr_ascribe_inv evstAsc
  cases evst with
  | array hargs =>
    obtain ⟨v12, v3, _, rfl, h12, h3⟩ := evalArgs_append_inv hargs
    obtain ⟨v1, v2, _, rfl, h1, h2⟩ := evalArgs_append_inv h12
    obtain ⟨rfl, rfl⟩ := evalArgs_map_inv (List.range 8)
      (g := fun i => if hi : i < 8 then wv cv[i] else .tuple [])
      (fun i hi h1 rv h2 ei => by
        have hilt : i < 8 := List.mem_range.mp hi
        simp only [hilt, ↓reduceDIte]
        obtain ⟨vt, evt, pr⟩ := evalExpr_index_inv ei
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
        exact ⟨(Except.ok.inj ((proj_vecV cv i hilt).symm.trans pr)).symm, rfl⟩) h1
    cases h2 with | cons e20 t20 =>
    cases t20 with | cons e21 t21 =>
    cases t21 with | cons e22 t22 =>
    cases t22 with | cons e23 t23 =>
    cases t23 with | cons e24 t24 =>
    cases t24 with | cons e25 t25 =>
    cases t25 with | cons e26 t26 =>
    cases t26 with | cons e27 t27 =>
    cases t27
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e20
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e21
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e22
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e23
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e24
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e25
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e26
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e27
    obtain ⟨rfl, rfl⟩ := evalArgs_map_inv (List.range 16)
      (g := fun i => if hi : i < 16 then wv m[i] else .tuple [])
      (fun i hi h1 rv h2 ei => by
        have hilt : i < 16 := List.mem_range.mp hi
        simp only [hilt, ↓reduceDIte]
        obtain ⟨vt, evt, pr⟩ := evalExpr_index_inv ei
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
        exact ⟨(Except.ok.inj ((proj_vecV m i hilt).symm.trans pr)).symm, rfl⟩) h3
    obtain ⟨v0, vst', _, _, ev0, evst', calComp⟩ := evalExpr_call2_inv k10
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp only [List.find?_cons, beq_self_eq_true]; rfl) evst'
    have hstEq : Value.tuple
        (((List.range 8).map fun i => if hi : i < 8 then wv (F := F) cv[i] else .tuple []) ++
         [wv Blake3.Pure.iv[0], wv Blake3.Pure.iv[1], wv Blake3.Pure.iv[2], wv Blake3.Pure.iv[3],
          w4 (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3),
          w4 (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7),
          .tuple [.field (len : F), .field 0, .field 0, .field 0],
          .tuple [.field (fl : F), .field 0, .field 0, .field 0]] ++
         ((List.range 16).map fun i => if hi : i < 16 then wv (F := F) m[i] else .tuple [])) =
        stateV (Blake3.Pure.initialWords cv c len.toUInt32 fl.toUInt32) m := by
      rw [small_word hlen, small_word hfl, ← wv_wordOfBytes (u64b c 0), lo_word,
        ← wv_wordOfBytes (u64b c 4), hi_word]
      simp only [stateV, stateL]
      congr 1
    rw [hstEq, show (0 : F) = ((0 : Nat) : F) by simp] at calComp
    obtain ⟨rfl, rfl⟩ := eval_compress hc lib 3 (k := 0) (by rfl) calComp
    rw [compressRounds_seven, Aiur.Library.Blake3.compress_spec]
    exact ⟨rfl, rfl⟩

include hc lib in
/-- `Blake3::compress_init` with flags supplied as a `UInt32` (`fl.toNat < 256`). -/
theorem eval_compress_init' {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len : Nat} {fl : UInt32} (hlen : len < 256) (hfl : fl.toNat < 256) {r : SourceValue F}
    {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v c, .field (len : F), .field (fl.toNat : F)] h r h') :
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init hc lib hlen hfl ev
  exact ⟨by rw [show fl.toNat.toUInt32 = fl from UInt32.ofNat_toNat], rfl⟩

end Compression

/-! ## Section 6: Operational `EvalFn` Contracts for Streams and the Block Loop -/

section StreamsAndLoop

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F} (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)

/-! ### Constructor, Tuple, and Pattern-Matching Helpers -/

private theorem node_ctor : constructorName [] (.named "Lists::Node" [.field]) = byteStreamEnum := by
  decide +kernel

private theorem node_inst : instanceName [] "Lists::Node" (some [.field]) = byteStreamEnum := by
  decide +kernel

private theorem blockRead_ctor :
    constructorName [] (.named "Blake3::BlockRead" []) = "Blake3::BlockRead" := by
  decide +kernel

private theorem layerNode_ctor :
    constructorName [] (.named "Blake3::LayerNode" []) = "Blake3::LayerNode" := by
  decide +kernel

private theorem maybeDigest_ctor :
    constructorName [] (.named "Blake3::MaybeDigest" []) = "Blake3::MaybeDigest" := by
  decide +kernel

private theorem evalExpr_construct0_inv {locals : Environment F Nat} {en ctor : String}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct en (some []) ctor []) h r h') :
    r = .construct en ctor [] ∧ h' = h := by
  cases ev with
  | construct hargs =>
    cases hargs
    exact ⟨by simp [instanceName, Instance.symbol], rfl⟩

private theorem evalExpr_construct1_inv {locals : Environment F Nat} {en ctor : String}
    {a : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct en (some []) ctor [a]) h r h') :
    ∃ va, EvalExpr world [] locals a h va h' ∧ r = .construct en ctor [va] := by
  cases ev with
  | construct hargs =>
    cases hargs with | cons ha t1 =>
    cases t1
    exact ⟨_, ha, by simp [instanceName, Instance.symbol]⟩

private theorem evalExpr_construct_stream0_inv {locals : Environment F Nat} {ctor : String}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct "Lists::Node" (some [.field]) ctor []) h r h') :
    r = .construct byteStreamEnum ctor [] ∧ h' = h := by
  cases ev with
  | construct hargs =>
    cases hargs
    exact ⟨by rw [node_inst], rfl⟩

private theorem evalExpr_construct_stream2_inv {locals : Environment F Nat} {ctor : String}
    {a b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.construct "Lists::Node" (some [.field]) ctor [a, b]) h r h') :
    ∃ va vb hm,
      EvalExpr world [] locals a h va hm ∧
      EvalExpr world [] locals b hm vb h' ∧
      r = .construct byteStreamEnum ctor [va, vb] := by
  cases ev with
  | construct hargs =>
    cases hargs with | cons ha t1 =>
    cases t1 with | cons hb t2 =>
    cases t2
    exact ⟨_, _, _, ha, hb, by rw [node_inst]⟩

private theorem evalExpr_let_inv {locals : Environment F Nat}
    {p : Aiur.Generic.Pattern F} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.letValue p e b) h r h') :
    ∃ v hm bs,
      EvalExpr world [] locals e h v hm ∧
      world.matchPattern [] hm p v = .ok (some bs) ∧
      EvalExpr world [] (bs ++ locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb => exact ⟨_, _, _, hv, hm, hb⟩

omit [Field F] in
private theorem match_construct0_same (world : World F) (h : Heap F) {t : Generic.Ty} {nm c : String}
    (ht : constructorName [] t = nm) :
    world.matchPattern [] h (.construct t c []) (.construct nm c []) = .ok (some []) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp [ht, matchListWith]

omit [Field F] in
private theorem match_construct_ne_ctor (world : World F) (h : Heap F) {t : Generic.Ty}
    {nm c c' : String} {ps : List (Aiur.Generic.Pattern F)} {vs : List (SourceValue F)}
    (hne : c' ≠ c) :
    world.matchPattern [] h (.construct t c ps) (.construct nm c' vs) = .ok none := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp [bne_iff_ne, hne]

omit [Field F] in
private theorem match_construct1_bind (world : World F) (h : Heap F) {t : Generic.Ty}
    {nm c x : String} {v : SourceValue F} (ht : constructorName [] t = nm) :
    world.matchPattern [] h (.construct t c [.bind x]) (.construct nm c [v]) =
      .ok (some [(x, v)]) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [ht, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, List.length_nil, List.attach_cons, List.attach_nil, List.map_nil,
    matchListWith, bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith]
  rfl

omit [Field F] in
private theorem match_construct2_bind (world : World F) (h : Heap F) {t : Generic.Ty}
    {nm c x y : String} {u v : SourceValue F} (ht : constructorName [] t = nm) :
    world.matchPattern [] h (.construct t c [.bind x, .bind y]) (.construct nm c [u, v]) =
      .ok (some [(x, u), (y, v)]) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [ht, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, List.length_nil, List.attach_cons, List.attach_nil, List.map_cons,
    List.map_nil, matchListWith, bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  rfl

omit [Field F] in
private theorem match_construct2_bind_wild (world : World F) (h : Heap F) {t : Generic.Ty}
    {nm c x : String} {u v : SourceValue F} (ht : constructorName [] t = nm) :
    world.matchPattern [] h (.construct t c [.bind x, .wildcard]) (.construct nm c [u, v]) =
      .ok (some [(x, u)]) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [ht, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, List.length_nil, List.attach_cons, List.attach_nil, List.map_cons,
    List.map_nil, matchListWith, bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  rfl

omit [Field F] in
private theorem match_tuple2_ll (world : World F) (h : Heap F) (a b x y : F) :
    world.matchPattern [] h (.tuple [.literal a, .literal b]) (.tuple [.field x, .field y]) =
      .ok (if a = x ∧ b = y then some [] else none) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, matchListWith,
    bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  simp only [Aiur.Pattern.bindings, pure, Except.pure]
  by_cases ha : a = x <;> by_cases hb : b = y <;> simp [ha, hb]

omit [Field F] in
private theorem match_tuple2_lw (world : World F) (h : Heap F) (a x : F) (y : SourceValue F) :
    world.matchPattern [] h (.tuple [.literal a, .wildcard]) (.tuple [.field x, y]) =
      .ok (if a = x then some [] else none) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, matchListWith,
    bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  simp only [Aiur.Pattern.bindings, pure, Except.pure]
  by_cases ha : a = x <;> simp [ha]

omit [Field F] in
private theorem match_tuple2_wl (world : World F) (h : Heap F) (b y : F) (x : SourceValue F) :
    world.matchPattern [] h (.tuple [.wildcard, .literal b]) (.tuple [x, .field y]) =
      .ok (if b = y then some [] else none) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, matchListWith,
    bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  simp only [Aiur.Pattern.bindings, pure, Except.pure]
  by_cases hb : b = y <;> simp [hb]

omit [Field F] in
private theorem match_tuple2_ww (world : World F) (h : Heap F) (x y : SourceValue F) :
    world.matchPattern [] h (.tuple [.wildcard, .wildcard]) (.tuple [x, y]) = .ok (some []) := by
  change matchPatternWith world.constant world.constDepth [] h _ _ = _
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, matchListWith,
    bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith, matchPatternWith]
  rfl

omit [Field F] in
private theorem match_wildcard (world : World F) (h : Heap F) (v : SourceValue F) :
    world.matchPattern [] h .wildcard v = .ok (some []) := by
  change matchPatternWith world.constant world.constDepth [] h .wildcard v = _
  rw [matchPatternWith]
  rfl

/-! ### `Blake3::take_block` and `Blake3::bytes_to_block` -/

private theorem bNames_length : bNames.length = 64 := rfl

private theorem bNames_nodup : bNames.Nodup := by decide

private theorem l_notMem : "l" ∉ bNames := by decide

private theorem bNamesRev_eq : bNamesRev = bNames.reverse := rfl

private theorem bNames_eq_rev : bNamesRev.reverse = bNames := by
  rw [bNamesRev_eq, List.reverse_reverse]

private theorem mem_bNames_of_rev {pre bs : List String} {b : String}
    (h : pre.reverse ++ b :: bs = bNamesRev) : b ∈ bNames := by
  rw [← bNames_eq_rev, ← h]
  simp

private abbrev Bound (locals : Environment F Nat) (names : List String) (xs : List UInt8) : Prop :=
  List.Forall₂ (fun n x => locals.find? (·.1 == n) = some (n, bv x)) names xs

omit [DecidableEq F] in
private theorem bound_skip {locals : Environment F Nat} {names : List String} {xs : List UInt8}
    (pre : Environment F Nat) (hpre : ∀ n ∈ names, ∀ e ∈ pre, e.1 ≠ n)
    (hb : Bound locals names xs) : Bound (pre ++ locals) names xs := by
  induction hb with
  | nil => exact .nil
  | @cons n x ns xs' hx _ ih =>
    refine .cons ?_ (ih (fun n' hn' e he => hpre n' (List.mem_cons_of_mem _ hn') e he))
    rw [List.find?_append]
    have hnone : pre.find? (·.1 == n) = none :=
      List.find?_eq_none.mpr (fun e he => by simpa using hpre n List.mem_cons_self e he)
    rw [hnone]
    simpa using hx

private def words4 : List UInt8 → List (SourceValue F)
  | a :: b :: c :: d :: rest => w4 a b c d :: words4 rest
  | _ => []

omit [DecidableEq F] in
private theorem words4_length : ∀ (xs : List UInt8), (words4 (F := F) xs).length = xs.length / 4
  | a :: b :: c :: d :: rest => by simp [words4, words4_length rest]; omega
  | [] => by simp [words4]
  | [_] => by simp [words4]
  | [_, _] => by simp [words4]
  | [_, _, _] => by simp [words4]

omit [DecidableEq F] in
private theorem words4_length_getElem : ∀ (xs : List UInt8) (k : Nat) (h : k * 4 + 3 < xs.length),
    ∃ hk : k < (words4 (F := F) xs).length,
      (words4 (F := F) xs)[k] = w4 xs[k * 4] xs[k * 4 + 1] xs[k * 4 + 2] xs[k * 4 + 3]
  | a :: b :: c :: d :: rest, 0, _ => ⟨by simp [words4], rfl⟩
  | a :: b :: c :: d :: rest, k + 1, h => by
    obtain ⟨hk, e⟩ := words4_length_getElem rest k (by simp at h; omega)
    refine ⟨by simp [words4]; omega, ?_⟩
    simp only [words4]
    rw [List.getElem_cons_succ, e]
    have h0 : (a :: b :: c :: d :: rest)[(k + 1) * 4]'(by omega) = rest[k * 4]'(by simp at h; omega) := by
      simp [show (k + 1) * 4 = k * 4 + 4 by omega]
    have h1 : (a :: b :: c :: d :: rest)[(k + 1) * 4 + 1]'(by omega) = rest[k * 4 + 1]'(by simp at h; omega) := by
      simp [show (k + 1) * 4 + 1 = k * 4 + 5 by omega]
    have h2 : (a :: b :: c :: d :: rest)[(k + 1) * 4 + 2]'(by omega) = rest[k * 4 + 2]'(by simp at h; omega) := by
      simp [show (k + 1) * 4 + 2 = k * 4 + 6 by omega]
    have h3 : (a :: b :: c :: d :: rest)[(k + 1) * 4 + 3]'(by omega) = rest[k * 4 + 3]'(by simp at h; omega) := by
      simp [show (k + 1) * 4 + 3 = k * 4 + 7 by omega]
    rw [h0, h1, h2, h3]
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h

private theorem bytesWord_four (xs : List UInt8) (k : Nat) (hk : k * 4 + 3 < xs.length) :
    Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => xs.toArray[k * 4 + b.val]?.getD 0) =
      Aiur.Library.Blake3.wordOfBytes xs[k * 4] xs[k * 4 + 1] xs[k * 4 + 2] xs[k * 4 + 3] := by
  rw [← Aiur.Library.Blake3.bytesWord_eq_wordOfBytes]
  congr 1
  ext b hb
  simp only [Vector.getElem_ofFn]
  interval_cases b
  · simp [List.getElem?_eq_getElem (show k * 4 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 1 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 2 < xs.length by omega)]
  · simp [List.getElem?_eq_getElem (show k * 4 + 3 < xs.length by omega)]

omit [DecidableEq F] in
private theorem words4_eq (xs : List UInt8) (hx : xs.length = 64) :
    (.tuple (words4 xs) : SourceValue F) = vecV (Blake3.Pure.blockWords xs) := by
  rw [vecV]
  congr 1
  apply List.ext_getElem (by simp [words4_length, hx])
  intro k h1 h2
  have hk : k * 4 + 3 < xs.length := by rw [words4_length, hx] at h1; omega
  obtain ⟨_, e⟩ := words4_length_getElem (F := F) xs k hk
  rw [e, List.getElem_ofFn]
  simp only [Blake3.Pure.blockWords, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [bytesWord_four xs k hk, wv_wordOfBytes]

omit [Field F] [DecidableEq F] in
private theorem hasNoControl_fbCalls : ∀ ns, hasNoControlList (fbCalls (F := F) ns) = true
  | [] | [_] | [_, _] | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: rest => by
    simp only [fbCalls, hasNoControlList, hasNoControl, Bool.and_true, Bool.true_and]
    exact hasNoControl_fbCalls rest

omit [Field F] [DecidableEq F] in
private theorem hasNoControl_tbFrom : ∀ bs scr, hasNoControl (tbFrom (F := F) bs scr) = true
  | [], _ => by
    simp only [tbFrom, tbFull, hasNoControl, hasNoControlList, Bool.and_true]
    exact hasNoControl_fbCalls bNames
  | _ :: bs, _ => by
    simp only [tbFrom, hasNoControl, hasNoControlList, hasNoControlArms, Bool.and_true, Bool.true_and]
    exact hasNoControl_tbFrom bs "l"

omit [Field F] [DecidableEq F] in
private theorem hasNoControl_bbFrom : ∀ bs scr, hasNoControl (bbFrom (F := F) bs scr) = true
  | [], _ => by
    simp only [bbFrom, hasNoControl]
    exact hasNoControl_fbCalls bNames
  | _ :: [], _ => by
    simp only [bbFrom, hasNoControl, Bool.true_and]
    exact hasNoControl_fbCalls bNames
  | _ :: c :: bs, _ => by
    simp only [bbFrom, hasNoControl, Bool.true_and]
    exact hasNoControl_bbFrom (c :: bs) "l"

private theorem fbCall_inv (lib : Blake3LibraryWorld world) {locals : Environment F Nat}
    {a b c d : String} {x0 x1 x2 x3 : UInt8}
    (h0 : locals.find? (·.1 == a) = some (a, bv x0))
    (h1 : locals.find? (·.1 == b) = some (b, bv x1))
    (h2 : locals.find? (·.1 == c) = some (c, bv x2))
    (h3 : locals.find? (·.1 == d) = some (d, bv x3))
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals
      (.call "UInt32::from_bytes" (some []) [.array [.var a, .var b, .var c, .var d]]) h r h') :
    r = w4 x0 x1 x2 x3 ∧ h' = h := by
  obtain ⟨va, _, eva, cal⟩ := evalExpr_call1_inv ev
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq h0 e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq h1 e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq h2 e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq h3 e3
  exact eval_u32_from_bytes lib cal

private theorem fbCalls_inv (lib : Blake3LibraryWorld world) :
    ∀ (names : List String) (xs : List UInt8) {locals : Environment F Nat},
      Bound locals names xs → ∀ {h h' : Heap F} {vs : List (SourceValue F)},
        EvalArgs world [] locals (fbCalls names) h vs h' →
        vs = words4 xs ∧ h' = h
  | [], _, _, hb, _, _, _, ev => by
    cases hb; cases ev; exact ⟨rfl, rfl⟩
  | [_], _, _, hb, _, _, _, ev => by
    cases ev; rcases hb with _ | ⟨_, hb⟩; rcases hb with ⟨⟩; exact ⟨rfl, rfl⟩
  | [_, _], _, _, hb, _, _, _, ev => by
    cases ev; rcases hb with _ | ⟨_, hb⟩; rcases hb with _ | ⟨_, hb⟩; rcases hb with ⟨⟩
    exact ⟨rfl, rfl⟩
  | [_, _, _], _, _, hb, _, _, _, ev => by
    cases ev; rcases hb with _ | ⟨_, hb⟩; rcases hb with _ | ⟨_, hb⟩
    rcases hb with _ | ⟨_, hb⟩; rcases hb with ⟨⟩; exact ⟨rfl, rfl⟩
  | _ :: _ :: _ :: _ :: rest, _, _, hb, _, _, _, ev => by
    rcases hb with _ | ⟨h0, hb⟩
    rcases hb with _ | ⟨h1, hb⟩
    rcases hb with _ | ⟨h2, hb⟩
    rcases hb with _ | ⟨h3, hb⟩
    cases ev with
    | cons dv av =>
      obtain ⟨rfl, rfl⟩ := fbCall_inv lib h0 h1 h2 h3 dv
      obtain ⟨rfl, rfl⟩ := fbCalls_inv lib rest _ hb av
      exact ⟨rfl, rfl⟩

private theorem tbLevel_inv {locals : Environment F Nat} {scr b : String} {bs : List String}
    {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F}
    (hscr : locals.find? (·.1 == scr) = some (scr, ptr))
    (hrep : Stream h bytes ptr)
    (ev : EvalExpr world [] locals (tbFrom (b :: bs) scr) h r h') :
    (bytes = [] ∧ r = .construct "Blake3::BlockRead" "Short" [] ∧ h' = h) ∨
    (∃ x xs tail, bytes = x :: xs ∧ Stream h xs tail ∧
      EvalExpr world [] ([(b, bv x), ("l", tail)] ++ locals) (tbFrom bs "l") h r h') := by
  simp only [tbFrom] at ev
  obtain ⟨v, _, bnd, body, dx, sel, db⟩ := evalExpr_match_inv ev
  obtain ⟨p, dp, ld⟩ := evalExpr_load_inv dx
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hscr dp
  rcases stream_inv hrep ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, htail⟩
  · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
    · rw [nilPat, match_construct0_same _ _ node_ctor] at mt
      cases mt
      obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv db
      exact .inl ⟨rfl, rfl, rfl⟩
    · rw [nilPat, match_construct0_same _ _ node_ctor] at nm
      cases nm
  · rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
    · rw [nilPat, match_construct_ne_ctor _ _ (by decide)] at mt
      cases mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
      · rw [consPat, match_construct2_bind _ _ node_ctor] at mt2
        cases mt2
        exact .inr ⟨x, xs, tail, rfl, htail, db⟩
      · exact False.elim (selectArm_nil_inv sel3)

private theorem tbFull_inv (lib : Blake3LibraryWorld world) {locals : Environment F Nat}
    {xs : List UInt8} (hb : Bound locals bNames xs)
    {ptr : SourceValue F} (hl : locals.find? (·.1 == "l") = some ("l", ptr))
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals tbFull h r h') :
    r = .construct "Blake3::BlockRead" "Full" [.tuple (words4 xs), ptr] ∧ h' = h := by
  obtain ⟨v1, v2, _, d1, d2, rfl⟩ := evalExpr_construct2_inv ev
  cases d1 with
  | array aw =>
    obtain ⟨rfl, rfl⟩ := fbCalls_inv lib bNames xs hb aw
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl d2
    exact ⟨rfl, rfl⟩

private theorem tbFrom_inv (lib : Blake3LibraryWorld world) :
    ∀ (bs pre : List String) (ys : List UInt8) {locals : Environment F Nat}
      {scr : String} {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F},
      pre.reverse ++ bs = bNames → (bs = [] → scr = "l") → Bound locals pre ys →
      locals.find? (·.1 == scr) = some (scr, ptr) → Stream h bytes ptr →
      EvalExpr world [] locals (tbFrom bs scr) h r h' →
      h' = h ∧ ((bytes.length < bs.length ∧ r = .construct "Blake3::BlockRead" "Short" []) ∨
        (bs.length ≤ bytes.length ∧ ∃ tail,
          r = .construct "Blake3::BlockRead" "Full"
            [.tuple (words4 (ys.reverse ++ bytes.take bs.length)), tail] ∧
          Stream h (bytes.drop bs.length) tail))
  | [], pre, ys, locals, scr, ptr, bytes, h, h', r, hpre, hscr, hb, hl, hs, ev => by
    obtain rfl := hscr rfl
    simp only [List.append_nil] at hpre
    have hb' : Bound locals bNames ys.reverse := by
      rw [← hpre]; exact List.forall₂_reverse_iff.mpr hb
    simp only [tbFrom] at ev
    obtain ⟨rfl, rfl⟩ := tbFull_inv lib hb' hl ev
    exact ⟨rfl, .inr ⟨by simp, ptr, by simp, by simpa using hs⟩⟩
  | b :: bs, pre, ys, locals, scr, ptr, bytes, h, h', r, hpre, _, hb, hl, hs, ev => by
    rcases tbLevel_inv hl hs ev with ⟨rfl, rfl, rfl⟩ | ⟨x, xs, tail, rfl, htail, db⟩
    · exact ⟨rfl, .inl ⟨by simp, rfl⟩⟩
    · have hnd : (pre.reverse ++ b :: bs).Nodup := by rw [hpre]; exact bNames_nodup
      have hbpre : b ∉ pre := fun hm =>
        (List.nodup_append.mp hnd).2.2 b (List.mem_reverse.mpr hm) b List.mem_cons_self rfl
      have hbmem : b ∈ bNames := by rw [← hpre]; simp
      have hbl : b ≠ "l" := fun e => l_notMem (e ▸ hbmem)
      have hlpre : "l" ∉ pre := fun hm => by
        apply l_notMem; rw [← hpre]; exact List.mem_append_left _ (List.mem_reverse.mpr hm)
      have hb2 : Bound ([(b, bv x), ("l", tail)] ++ locals) (b :: pre) (x :: ys) := by
        refine .cons (by simp) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · intro e'; simp only at e'; exact hbpre (e' ▸ hn)
        · intro e'; simp only at e'; exact hlpre (e' ▸ hn)
      obtain ⟨rfl, hres⟩ := tbFrom_inv lib bs (b :: pre) (x :: ys) (by simpa using hpre)
        (fun _ => rfl) hb2 (by simp [hbl]) htail db
      refine ⟨rfl, ?_⟩
      rcases hres with ⟨hlt, rfl⟩ | ⟨hle, tl, rfl, htl⟩
      · exact .inl ⟨by simp; omega, rfl⟩
      · exact .inr ⟨by simp; omega, tl, by simp, by simpa using htl⟩

include lib in
/-- **`Blake3::take_block`**: reads the first 64 bytes as `blockWords` and returns the remaining
stream, or `Short` when fewer than 64 bytes remain. -/
theorem eval_take_block {inp r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    (hs : Stream h bytes inp) (ev : EvalFn world "Blake3::take_block" [inp] h r h') :
    h' = h ∧ ((bytes.length < 64 ∧ r = .construct "Blake3::BlockRead" "Short" []) ∨
      (64 ≤ bytes.length ∧ ∃ tail,
        r = .construct "Blake3::BlockRead" "Full"
          [vecV (Blake3.Pure.blockWords (bytes.take 64)), tail] ∧
        Stream h (bytes.drop 64) tail)) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_take_block (hasNoControl_tbFrom bNames "input") ev
  obtain ⟨rfl, hres⟩ := tbFrom_inv lib bNames [] [] (by rfl) (by simp [bNames]) .nil (by simp) hs body
  refine ⟨rfl, ?_⟩
  rw [bNames_length] at hres
  rcases hres with ⟨hlt, rfl⟩ | ⟨hle, tl, rfl, htl⟩
  · exact .inl ⟨hlt, rfl⟩
  · refine .inr ⟨hle, tl, ?_, htl⟩
    rw [List.reverse_nil, List.nil_append, words4_eq (bytes.take 64) (by simp; omega)]

private theorem bbFrom_inv (lib : Blake3LibraryWorld world) :
    ∀ (bs pre : List String) (ys : List UInt8) {locals : Environment F Nat}
      {scr : String} {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F},
      bs ≠ [] → pre.reverse ++ bs = bNamesRev → Bound locals pre ys →
      locals.find? (·.1 == scr) = some (scr, ptr) → Stream h bytes ptr →
      EvalExpr world [] locals (bbFrom bs scr) h r h' →
      h' = h ∧ bs.length ≤ bytes.length ∧
        r = .tuple (words4 ((bytes.take bs.length).reverse ++ ys))
  | [], _, _, _, _, _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [b], pre, ys, locals, scr, ptr, bytes, h, h', r, _, hpre, hb, hl, hs, ev => by
    simp only [bbFrom] at ev
    obtain ⟨v, _, bnd, dx, mt, db⟩ := evalExpr_let_inv ev
    obtain ⟨p, dp, ld⟩ := evalExpr_load_inv dx
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl dp
    rcases stream_inv hs ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, _⟩
    · rw [conswPat, match_construct_ne_ctor _ _ (by decide)] at mt
      cases mt
    · rw [conswPat, match_construct2_bind_wild _ _ node_ctor] at mt
      cases mt
      have hpre' : b :: pre = bNames := by rw [← bNames_eq_rev, ← hpre]; simp
      have hbpre : b ∉ pre := (List.nodup_cons.mp (by rw [hpre']; exact bNames_nodup)).1
      have hb2 : Bound ([(b, bv x)] ++ locals) bNames (x :: ys) := by
        rw [← hpre']
        refine .cons (by simp) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        intro e'; simp only at e'; exact hbpre (e' ▸ hn)
      cases db with
      | array aw =>
        obtain ⟨rfl, rfl⟩ := fbCalls_inv lib bNames (x :: ys) hb2 aw
        exact ⟨rfl, by simp, by simp⟩
  | b :: c :: bs, pre, ys, locals, scr, ptr, bytes, h, h', r, _, hpre, hb, hl, hs, ev => by
    simp only [bbFrom] at ev
    obtain ⟨v, _, bnd, dx, mt, db⟩ := evalExpr_let_inv ev
    obtain ⟨p, dp, ld⟩ := evalExpr_load_inv dx
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl dp
    rcases stream_inv hs ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, htail⟩
    · rw [consPat, match_construct_ne_ctor _ _ (by decide)] at mt
      cases mt
    · rw [consPat, match_construct2_bind _ _ node_ctor] at mt
      cases mt
      have hnd : (pre.reverse ++ b :: c :: bs).Nodup := by
        rw [hpre, bNamesRev_eq]; exact List.nodup_reverse.mpr bNames_nodup
      have hbpre : b ∉ pre := fun hm =>
        (List.nodup_append.mp hnd).2.2 b (List.mem_reverse.mpr hm) b List.mem_cons_self rfl
      have hbmem : b ∈ bNames := mem_bNames_of_rev hpre
      have hbl : b ≠ "l" := fun e => l_notMem (e ▸ hbmem)
      have hlpre : "l" ∉ pre := fun hm => by
        apply l_notMem; rw [← bNames_eq_rev, ← hpre]; simp [hm]
      have hb2 : Bound ([(b, bv x), ("l", tail)] ++ locals) (b :: pre) (x :: ys) := by
        refine .cons (by simp) (bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · intro e'; simp only at e'; exact hbpre (e' ▸ hn)
        · intro e'; simp only at e'; exact hlpre (e' ▸ hn)
      obtain ⟨rfl, hle, rfl⟩ := bbFrom_inv lib (c :: bs) (b :: pre) (x :: ys) (by simp)
        (by simpa using hpre) hb2 (by simp [hbl]) htail db
      exact ⟨rfl, by simp at hle ⊢; omega, by simp⟩

include lib in
/-- **`Blake3::bytes_to_block`**: converts the first 64 bytes of a reversed byte accumulator
stream into `Blake3.Pure.blockWords`. -/
theorem eval_bytes_to_block {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
    (hs : Stream h bytes acc) (ev : EvalFn world "Blake3::bytes_to_block" [acc] h r h') :
    h' = h ∧ 64 ≤ bytes.length ∧ r = vecV (Blake3.Pure.blockWords (bytes.take 64).reverse) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_bytes_to_block
    (hasNoControl_bbFrom bNamesRev "byte_acc") ev
  obtain ⟨rfl, hle, rfl⟩ := bbFrom_inv lib bNamesRev [] [] (by simp [bNamesRev, bNames]) (by rfl)
    .nil (by simp) hs body
  have hlen : bNamesRev.length = 64 := rfl
  rw [hlen] at hle ⊢
  refine ⟨rfl, hle, ?_⟩
  rw [List.append_nil, words4_eq (bytes.take 64).reverse (by simp; omega)]

/-! ### `Blake3::pad_block` -/

include hc lib in
/-- **`Blake3::pad_block(acc, n)`**: prepends `n` zero bytes onto `acc` (for `n < 1024`). -/
theorem eval_pad_block :
    ∀ (n : Nat) {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F},
      n < 1024 → Stream h bytes acc →
      EvalFn world "Blake3::pad_block" [acc, .field (n : F)] h r h' →
      Heap.Extends h h' ∧ Stream h' (List.replicate n 0 ++ bytes) r
  | 0, acc, r, bytes, h, h', _, hs, ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_pad_block rfl ev
    obtain ⟨vn, _, evn, hbr⟩ := evalExpr_match_lit_wild_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn
    rcases hbr with ⟨_, hb0⟩ | ⟨hne, _⟩
    · obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hb0
      exact ⟨Heap.Extends.refl _, by simpa using hs⟩
    · exact absurd (by simp) hne
  | n + 1, acc, r, bytes, h, h', hn, hs, ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_pad_block rfl ev
    obtain ⟨vn, _, evn, hbr⟩ := evalExpr_match_lit_wild_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn
    rcases hbr with ⟨heq0, _⟩ | ⟨_, hbW⟩
    · have h0 : n + 1 = 0 :=
        u32Compat_small_inj hc hn (by omega) (by push_cast; exact Value.field.inj heq0)
      omega
    · obtain ⟨v1, v2, _, _, ev1, ev2, calRec⟩ := evalExpr_call2_inv hbW
      obtain ⟨vc, _, evc, rfl, rfl⟩ := evalExpr_store_inv ev1
      obtain ⟨vb0, vacc, _, evb0, evacc, rfl⟩ := evalExpr_construct_stream2_inv evc
      obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) evb0
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evacc
      obtain ⟨vn', v1', _, evn', ev1', opSub⟩ := evalExpr_binary_inv ev2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn'
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1'
      obtain rfl := binop_sub opSub
      have hcast : (n : F) + 1 - 1 = (n : F) := by ring
      have hbv0 : (Value.field ((0 : Nat) : F) : SourceValue F) = bv 0 := by simp [bv]
      rw [type_construct, hbv0, hcast] at calRec
      obtain ⟨ext, hr⟩ := eval_pad_block n (by omega) (stream_cons_snoc (x := 0) hs) calRec
      refine ⟨(Heap.Extends.snoc _ _).trans ext, ?_⟩
      simpa [List.replicate_succ'] using hr

/-! ### `Blake3::finish`, `Blake3::compress_chunks`, and `Blake3::hash_blocks` -/

private theorem evalExpr_zeroBlock_inv (lib : Blake3LibraryWorld world)
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals
      (.repeat (.global "UInt32::ZERO" (some (.array .field 4))) 16) h r h') :
    r = vecV (Vector.replicate 16 (0 : UInt32)) ∧ h' = h := by
  obtain ⟨v, evg, rfl⟩ := evalExpr_repeat_inv ev
  cases evg with
  | global hlook hto hb =>
    simp only [Generic.Ty.subst] at hlook
    rw [lib.const_u32_zero] at hlook
    cases hlook
    have hto' : Consts.toExpr (.repeat (.global "UInt8::BYTE_0" (some .field)) 4 : Aiur.Generic.Pattern F) =
        .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) := by
      rw [Consts.toExpr, Consts.toExpr]; rfl
    rw [hto'] at hto
    cases hto
    obtain ⟨b, evb, rfl⟩ := evalExpr_repeat_inv hb
    obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) evb
    refine ⟨?_, rfl⟩
    rfl

private theorem evalExpr_zeroU64_inv (lib : Blake3LibraryWorld world)
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.repeat (gByte 0) 8) h r h') :
    r = u64v 0 ∧ h' = h := by
  obtain ⟨b, evb, rfl⟩ := evalExpr_repeat_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv (lib.const_bytes 0 (by decide)) evb
  exact ⟨by rw [u64v_zero]; simp, rfl⟩

private theorem flags_nat (s e r : Bool) :
    (Aiur.Library.Blake3.blockFlags s e r).toNat =
      (if s then 1 else 0) + 2 * (if e then 1 else 0) + 8 * (if r then 1 else 0) := by
  cases s <;> cases e <;> cases r <;> decide

omit [DecidableEq F] in
private theorem flags_general (s e r : Bool) :
    ((Aiur.Library.Blake3.blockFlags s e r).toNat : F) =
      (if s then 1 else 0) + 2 * (if e then 1 else 0) + 8 * (if r then 1 else 0) := by
  rw [flags_nat]
  cases s <;> cases e <;> cases r <;> norm_num

omit [DecidableEq F] in
private theorem flags_field (s r : Bool) :
    ((Aiur.Library.Blake3.blockFlags s true r).toNat : F) =
      (2 : F) + (if r then 1 else 0) * 8 + (if s then 1 else 0) * 1 := by
  rw [flags_general]
  cases s <;> cases r <;> norm_num

private theorem flags_lt (s e r : Bool) : (Aiur.Library.Blake3.blockFlags s e r).toNat < 256 := by
  cases s <;> cases e <;> cases r <;> decide

private theorem padded_block (acc : List UInt8) (k : Nat) (hacc : acc.length = k) (hk : k ≤ 64) :
    Blake3.Pure.blockWords ((List.replicate (64 - k) 0 ++ acc).take 64).reverse =
      Blake3.Pure.blockWords acc.reverse := by
  have hlen : (List.replicate (64 - k) (0 : UInt8) ++ acc).length = 64 := by simp; omega
  rw [List.take_of_length_le (by omega), List.reverse_append, List.reverse_replicate]
  have h := Aiur.Library.Blake3.bytes_to_block_spec acc.reverse (by simp; omega)
  rwa [List.length_reverse, hacc] at h

include hc lib in
/-- **`Blake3::finish`**: finalizes the trailing byte accumulator, pushing the final chunk
chaining value onto the layer stack as modeled by `Aiur.Library.Blake3.finish`. -/
theorem eval_finish {acc : List UInt8} {k j : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {accp ccp cvp lp r : SourceValue F} {h h' : Heap F}
    (hk : k ≤ 63) (hj : j < 1024) (hkj : k ≤ j) (hacc : acc.length = k)
    (hs : Stream h acc accp) (hcc : loadValue h ccp = .ok (u64v c))
    (hcv : loadValue h cvp = .ok (vecV cv)) (hl : Stack h layer.reverse lp)
    (ev : EvalFn world "Blake3::finish" [accp, .field (k : F), .field (j : F), ccp, cvp, lp] h r h') :
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.finish acc k j c cv layer).reverse r := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_finish rfl ev
  obtain ⟨vCS, _, evCS, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evCS
  obtain ⟨vCE, _, evCE, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evCE
  obtain ⟨vRT, _, evRT, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evRT
  obtain ⟨sv, _, bs, armBody, evSc, sel, db⟩ := evalExpr_match_inv k3
  obtain ⟨vk, vj, _, evk, evj, rfl⟩ := evalExpr_tuple2_inv evSc
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evj
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.cast_zero] at sel
    by_cases hj0 : j = 0
    · subst hj0
      simp only [Nat.cast_zero] at sel
      rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
      · rw [match_tuple2_ll] at mt
        simp only [and_self, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at mt
        subst mt
        -- Arm 1: k = 0, j = 0 (empty input iff c = 0)
        simp only [List.nil_append, blake3FinishArm1] at db
        obtain ⟨vcc, _, bs1, arm1, evCC, sel1, db1⟩ := evalExpr_match_inv db
        obtain ⟨pcc, evpcc, ldcc⟩ := evalExpr_load_inv evCC
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpcc
        obtain rfl := Except.ok.inj (hcc.symm.trans ldcc)
        rcases selectArm_cons_inv sel1 with ⟨mt1, rfl⟩ | ⟨nm1, sel2⟩
        · rw [match_zeros8_u64v hc lib] at mt1
          by_cases hc0 : c = 0
          · subst hc0
            simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at mt1
            subst mt1
            simp only [List.nil_append] at db1
            obtain ⟨vfl, _, evfl, k4⟩ := evalExpr_let_bind_inv db1
            obtain ⟨vf1, vf2, _, evf1, evf2, opA2⟩ := evalExpr_binary_inv evfl
            obtain ⟨vf3, vf4, _, evf3, evf4, opA1⟩ := evalExpr_binary_inv evf1
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evf3
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evf4
            obtain rfl := binop_add opA1
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evf2
            obtain rfl := binop_add opA2
            obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv k4
            obtain ⟨vlp, vci, _, evlp, evci, rfl⟩ := evalExpr_construct2_inv evcell
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlp
            obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, eg0, eg1, eg2, eg3, eg4, calCI⟩ :=
              evalExpr_call5_inv evci
            obtain ⟨pg0, epg0, ldg0⟩ := evalExpr_load_inv eg0
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg0
            obtain rfl := Except.ok.inj (hcv.symm.trans ldg0)
            obtain ⟨rfl, rfl⟩ := evalExpr_zeroBlock_inv lib eg1
            obtain ⟨pg2, epg2, ldg2⟩ := evalExpr_load_inv eg2
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg2
            obtain rfl := Except.ok.inj (hcc.symm.trans ldg2)
            obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv eg3
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg4
            have hfl : (8 : F) + 1 + 2 = ((Aiur.Library.Blake3.blockFlags true true true).toNat : F) := by
              rw [flags_general]; norm_num
            rw [hfl, show (0 : F) = ((0 : Nat) : F) by simp] at calCI
            obtain ⟨rfl, rfl⟩ := eval_compress_init' hc lib (len := 0) (by omega) (flags_lt _ _ _) calCI
            refine ⟨Heap.Extends.snoc _ _, ?_⟩
            rw [type_construct]
            have hmodel : Aiur.Library.Blake3.finish acc 0 0 0 cv layer =
                layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords []) 0 0
                  (Aiur.Library.Blake3.blockFlags true true true)] := by
              simp [Aiur.Library.Blake3.finish]
            rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append,
              Aiur.Library.Blake3.blockWords_nil]
            exact stack_push_snoc hl
          · simp [hc0] at mt1
        · rw [match_zeros8_u64v hc lib] at nm1
          have hc0 : c ≠ 0 := fun e => by subst e; simp at nm1
          rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
          · rw [match_wildcard] at mt2
            cases mt2
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) db1
            exact ⟨Heap.Extends.refl _, by simpa [Aiur.Library.Blake3.finish, hc0] using hl⟩
          · exact False.elim (selectArm_nil_inv sel3)
      · rw [match_tuple2_ll] at nm; simp at nm
    · -- Arm 2: k = 0, j ≠ 0
      have hjne : (0 : F) ≠ (j : F) := u32Compat_ne_zero hc hj hj0
      rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
      · rw [match_tuple2_ll] at mt; simp [hjne] at mt
      · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨nm2, _⟩
        · rw [match_tuple2_lw] at mt2
          simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at mt2
          subst mt2
          simp only [List.nil_append, blake3FinishArm2] at db
          obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv db
          obtain ⟨vlp, vcv, _, evlp, evcv, rfl⟩ := evalExpr_construct2_inv evcell
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlp
          obtain ⟨pcv, evpcv, ldcv⟩ := evalExpr_load_inv evcv
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpcv
          obtain rfl := Except.ok.inj (hcv.symm.trans ldcv)
          refine ⟨Heap.Extends.snoc _ _, ?_⟩
          rw [type_construct]
          have hmodel : Aiur.Library.Blake3.finish acc 0 j c cv layer = layer ++ [cv] := by
            simp [Aiur.Library.Blake3.finish, hj0]
          rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append]
          exact stack_push_snoc hl
        · rw [match_tuple2_lw] at nm2; simp at nm2
  · -- Arm 3: k ≠ 0 (partial block padded to 64 bytes)
    have hkne : (0 : F) ≠ (k : F) := u32Compat_ne_zero hc (by omega) hk0
    rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
    · rw [match_tuple2_ll] at mt; simp [hkne] at mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, _⟩ | ⟨_, sel3⟩
      · rw [match_tuple2_lw] at mt2; simp [hkne] at mt2
      · rcases selectArm_cons_inv sel3 with ⟨mt3, rfl⟩ | ⟨_, sel4⟩
        · rw [match_tuple2_ww] at mt3
          cases mt3
          simp only [List.nil_append, blake3FinishArm3] at db
          obtain ⟨vfl, _, evfl, k4⟩ := evalExpr_let_bind_inv db
          obtain ⟨vf1, vf2, _, evf1, evf2, opA2⟩ := evalExpr_binary_inv evfl
          obtain ⟨vfce, vfrt, _, evfce, evfrt, opA1⟩ := evalExpr_binary_inv evf1
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evfce
          obtain ⟨vciz, vrt, _, evciz, evrt, opM1⟩ := evalExpr_binary_inv evfrt
          obtain ⟨vcc, _, evcc, calCIZ⟩ := evalExpr_call1_inv evciz
          obtain ⟨pcc, epcc, ldcc⟩ := evalExpr_load_inv evcc
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epcc
          obtain rfl := Except.ok.inj (hcc.symm.trans ldcc)
          obtain ⟨rfl, rfl⟩ := eval_u64_is_zero hc lib calCIZ
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evrt
          obtain rfl := binop_mul opM1
          obtain rfl := binop_add opA1
          obtain ⟨vfiz, vcs, _, evfiz, evcs, opM2⟩ := evalExpr_binary_inv evf2
          obtain ⟨vdiff, _, evdiff, calFIZ⟩ := evalExpr_call1_inv evfiz
          obtain ⟨vj', vk', _, evj', evk', opSub1⟩ := evalExpr_binary_inv evdiff
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evj'
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk'
          obtain rfl := binop_sub opSub1
          rw [show (j : F) - (k : F) = ((j - k : Nat) : F) by
            push_cast [Nat.cast_sub hkj]; ring] at calFIZ
          obtain ⟨rfl, rfl⟩ := eval_fields_is_zero hc lib (by omega) calFIZ
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evcs
          obtain rfl := binop_mul opM2
          obtain rfl := binop_add opA2
          obtain ⟨vblk, _, evblk, k5⟩ := evalExpr_let_bind_inv k4
          obtain ⟨vpad, _, evpad, calB2B⟩ := evalExpr_call1_inv evblk
          obtain ⟨vacc, v64k, _, _, evacc, ev64k, calPad⟩ := evalExpr_call2_inv evpad
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evacc
          obtain ⟨v64, vk'', _, ev64, evk'', opSub2⟩ := evalExpr_binary_inv ev64k
          obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev64
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk''
          obtain rfl := binop_sub opSub2
          rw [show (64 : F) - (k : F) = ((64 - k : Nat) : F) by
            push_cast [Nat.cast_sub (by omega : k ≤ 64)]; ring] at calPad
          obtain ⟨ext1, hpad⟩ := eval_pad_block hc lib (64 - k) (by omega) hs calPad
          obtain ⟨rfl, _, rfl⟩ := eval_bytes_to_block lib hpad calB2B
          obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv k5
          obtain ⟨vlp, vci, _, evlp, evci, rfl⟩ := evalExpr_construct2_inv evcell
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlp
          obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, eg0, eg1, eg2, eg3, eg4, calCI⟩ :=
            evalExpr_call5_inv evci
          obtain ⟨pg0, epg0, ldg0⟩ := evalExpr_load_inv eg0
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg0
          obtain rfl := Except.ok.inj ((loadValue_extend ext1 hcv).symm.trans ldg0)
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg1
          obtain ⟨pg2, epg2, ldg2⟩ := evalExpr_load_inv eg2
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg2
          obtain rfl := Except.ok.inj ((loadValue_extend ext1 hcc).symm.trans ldg2)
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg3
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg4
          have hfl : ((2 : F) + if c = 0 then 8 else 0) + (if j - k = 0 then 1 else 0) =
              ((Aiur.Library.Blake3.blockFlags (decide (j - k = 0)) true (decide (c = 0))).toNat : F) := by
            rw [flags_field]
            by_cases hc0 : c = 0 <;> by_cases hjk : j - k = 0 <;> simp [hc0, hjk]
          rw [hfl] at calCI
          obtain ⟨rfl, rfl⟩ := eval_compress_init' hc lib (len := k) (by omega) (flags_lt _ _ _) calCI
          refine ⟨ext1.trans (Heap.Extends.snoc _ _), ?_⟩
          rw [type_construct]
          have hmodel : Aiur.Library.Blake3.finish acc k j c cv layer =
              layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords acc.reverse) c k.toUInt32
                (Aiur.Library.Blake3.blockFlags (decide (j - k = 0)) true (decide (c = 0)))] := by
            simp [Aiur.Library.Blake3.finish, hk0]
          rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append,
            ← padded_block acc k hacc (by omega)]
          exact stack_push_snoc (hl.mono ext1)
        · exact False.elim (selectArm_nil_inv sel4)

include hc lib in
/-- **`Blake3::compress_chunks`** on fewer bytes than remain in the current 64-byte block
(the tail reached by `Blake3::hash_blocks`). -/
theorem eval_compress_chunks (bytes acc : List UInt8) {k j : Nat} {c : UInt64}
    {cv : Blake3.Pure.CV} {layer : List Blake3.Pure.CV}
    {inp accp ccp cvp lp r : SourceValue F} {h h' : Heap F}
    (hk : k + bytes.length ≤ 63) (hj : j + bytes.length < 1024) (hkj : k ≤ j)
    (hacc : acc.length = k)
    (hs : Stream h bytes inp) (hsa : Stream h acc accp) (hcc : loadValue h ccp = .ok (u64v c))
    (hcv : loadValue h cvp = .ok (vecV cv)) (hl : Stack h layer.reverse lp)
    (ev : EvalFn world "Blake3::compress_chunks"
      [inp, accp, .field (k : F), .field (j : F), ccp, cvp, lp] h r h') :
    Heap.Extends h h' ∧
      Stack h' (Aiur.Library.Blake3.finish (bytes.reverse ++ acc)
        (k + bytes.length) (j + bytes.length) c cv layer).reverse r := by
  induction bytes generalizing acc k j inp accp ccp cvp lp r h h' with
  | nil =>
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress_chunks rfl ev
    obtain ⟨v, _, bs, armBody, evLd, sel, db⟩ := evalExpr_match_inv body
    obtain ⟨p, evp, ld⟩ := evalExpr_load_inv evLd
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp
    rcases stream_inv hs ld with ⟨_, rfl⟩ | ⟨_, _, _, he, _, _⟩
    · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
      · rw [nilPat, match_construct0_same _ _ node_ctor] at mt
        cases mt
        simp only [List.nil_append] at db
        obtain ⟨a0, a1, a2, a3, a4, a5, _, _, _, _, _, _, e0, e1, e2, e3, e4, e5, calFin⟩ :=
          evalExpr_call6_inv db
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
        simpa using eval_finish hc lib (by simp at hk; omega) (by simp at hj; omega)
          hkj hacc hsa hcc hcv hl calFin
      · rw [nilPat, match_construct0_same _ _ node_ctor] at nm; cases nm
    · cases he
  | cons x xs ih =>
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress_chunks rfl ev
    obtain ⟨v, _, bs, armBody, evLd, sel, db⟩ := evalExpr_match_inv body
    obtain ⟨p, evp, ld⟩ := evalExpr_load_inv evLd
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp
    rcases stream_inv hs ld with ⟨he, _⟩ | ⟨x', xs', tail, he, rfl, htail⟩
    · cases he
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
      · rw [nilPat, match_construct_ne_ctor _ _ (by decide)] at mt; cases mt
      · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
        · rw [consPat, match_construct2_bind _ _ node_ctor] at mt2
          cases mt2
          obtain ⟨vacc', _, evSt, k1⟩ := evalExpr_let_bind_inv db
          obtain ⟨vnode, _, evnode, rfl, rfl⟩ := evalExpr_store_inv evSt
          obtain ⟨vh, va, _, evh, eva, rfl⟩ := evalExpr_construct_stream2_inv evnode
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
          obtain ⟨vk', _, evk', hbr⟩ := evalExpr_match_lit_wild_inv k1
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk'
          rcases hbr with ⟨heq63, _⟩ | ⟨_, hbW⟩
          · have hk63 : k = 63 := u32Compat_small_inj hc (by simp at hk; omega) (by omega)
              (by rw [Nat.cast_ofNat]; exact Value.field.inj heq63)
            simp at hk; omega
          · obtain ⟨g0, g1, g2, g3, g4, g5, g6, _, _, _, _, _, _, _,
              e0, e1, e2, e3, e4, e5, e6, calRec⟩ := evalExpr_call7_inv hbW
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
            obtain ⟨vk1, v1, _, evk1, ev1, opK⟩ := evalExpr_binary_inv e2
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk1
            obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
            obtain rfl := binop_add opK
            obtain ⟨vj1, v2, _, evj1, ev2, opJ⟩ := evalExpr_binary_inv e3
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evj1
            obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
            obtain rfl := binop_add opJ
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e6
            rw [show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring,
              show (j : F) + 1 = ((j + 1 : Nat) : F) by push_cast; ring] at calRec
            obtain ⟨ext2, hst⟩ := ih (x :: acc) (k := k + 1) (j := j + 1)
              (by simp at hk; omega) (by simp at hj; omega) (by omega) (by simp [hacc])
              (htail.mono (Heap.Extends.snoc _ _)) (stream_cons_snoc hsa)
              (loadValue_extend (Heap.Extends.snoc _ _) hcc)
              (loadValue_extend (Heap.Extends.snoc _ _) hcv)
              (hl.mono (Heap.Extends.snoc _ _)) calRec
            refine ⟨(Heap.Extends.snoc _ _).trans ext2, ?_⟩
            have e1 : (x :: xs).reverse ++ acc = xs.reverse ++ x :: acc := by simp
            have e2 : k + (x :: xs).length = k + 1 + xs.length := by simp; omega
            have e3 : j + (x :: xs).length = j + 1 + xs.length := by simp; omega
            rw [e1, e2, e3]
            exact hst
        · exact False.elim (selectArm_nil_inv sel3)

private theorem evalExpr_isEmptyStream_inv {locals : Environment F Nat}
    {ptr : SourceValue F} {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F}
    (hl : locals.find? (·.1 == "rest") = some ("rest", ptr))
    (hs : Stream h bytes ptr)
    (ev : EvalExpr world [] locals
      (.matchValue (.load (.var "rest")) [(nilPat, .literal 1), (.wildcard, .literal 0)]) h r h') :
    r = .field (if bytes = [] then 1 else 0) ∧ h' = h := by
  obtain ⟨v, _, bs, armBody, evLd, sel, db⟩ := evalExpr_match_inv ev
  obtain ⟨p, evp, ld⟩ := evalExpr_load_inv evLd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl evp
  rcases stream_inv hs ld with ⟨rfl, rfl⟩ | ⟨x, xs, tail, rfl, rfl, _⟩
  · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
    · rw [nilPat, match_construct0_same _ _ node_ctor] at mt
      cases mt
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv db
      exact ⟨by simp, rfl⟩
    · rw [nilPat, match_construct0_same _ _ node_ctor] at nm; cases nm
  · rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
    · rw [nilPat, match_construct_ne_ctor _ _ (by decide)] at mt; cases mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
      · rw [match_wildcard] at mt2
        cases mt2
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv db
        exact ⟨by simp, rfl⟩
      · exact False.elim (selectArm_nil_inv sel3)

omit [DecidableEq F] in
private theorem sub15_eq_zero (hc : U32.Compatible F) {n : Nat} (hn : n < 1024) :
    ((n : F) - 15 = 0) ↔ n = 15 := by
  rw [sub_eq_zero]
  exact ⟨fun e => u32Compat_small_inj hc hn (by omega) (by simpa using e),
    fun e => by subst e; simp⟩

private def HBSpec (world : World F) (bytes : List UInt8) : Prop :=
  ∀ {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV} {layer : List Blake3.Pure.CV}
    {inp ccp cvp lp r : SourceValue F} {h h' : Heap F},
    n ≤ 15 → Stream h bytes inp → loadValue h ccp = .ok (u64v c) →
    loadValue h cvp = .ok (vecV cv) → Stack h layer.reverse lp →
    EvalFn world "Blake3::hash_blocks" [inp, .field (n : F), ccp, cvp, lp] h r h' →
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r

private theorem hb_core (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)
    (bytes : List UInt8) (ih : ∀ b : List UInt8, b.length < bytes.length → HBSpec world b) :
    HBSpec world bytes := by
  intro n c cv layer inp ccp cvp lp r h h' hn hs hcc hcv hl ev
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_hash_blocks rfl ev
  obtain ⟨vtb, _, bs, armBody, evTB, sel, db⟩ := evalExpr_match_inv body
  obtain ⟨vinp, _, evinp, calTB⟩ := evalExpr_call1_inv evTB
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evinp
  obtain ⟨rfl, htb⟩ := eval_take_block lib hs calTB
  rcases htb with ⟨hlt, rfl⟩ | ⟨hle, tail, rfl, htail⟩
  · -- Short path: fewer than 64 bytes left -> `compress_chunks`
    rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
    · rw [match_construct0_same _ _ blockRead_ctor] at mt
      cases mt
      simp only [List.nil_append] at db
      obtain ⟨g0, g1, g2, g3, g4, g5, g6, _, _, _, _, _, _, _,
          e0, e1, e2, e3, e4, e5, e6, calCC⟩ := evalExpr_call7_inv db
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
      obtain ⟨vnil, _, evnil, rfl, rfl⟩ := evalExpr_store_inv e1
      obtain ⟨rfl, rfl⟩ := evalExpr_construct_stream0_inv evnil
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e2
      obtain ⟨v64, vn', _, ev64, evn', opMul⟩ := evalExpr_binary_inv e3
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev64
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn'
      obtain rfl := binop_mul opMul
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e6
      rw [type_construct, show (0 : F) = ((0 : Nat) : F) by simp,
        show (64 : F) * (n : F) = ((64 * n : Nat) : F) by push_cast; ring] at calCC
      obtain ⟨ext2, hst⟩ := eval_compress_chunks hc lib bytes [] (k := 0) (j := 64 * n)
        (c := c) (cv := cv) (layer := layer) (by omega) (by omega) (by omega) rfl
        (hs.mono (Heap.Extends.snoc _ _)) (stream_nil_snoc _)
        (loadValue_extend (Heap.Extends.snoc _ _) hcc)
        (loadValue_extend (Heap.Extends.snoc _ _) hcv)
        (hl.mono (Heap.Extends.snoc _ _)) calCC
      refine ⟨(Heap.Extends.snoc _ _).trans ext2, ?_⟩
      rw [Aiur.Library.Blake3.hashBlocks_short bytes n c cv layer hlt,
        Aiur.Library.Blake3.compressChunks_tail c cv layer bytes [] 0 (64 * n) (by omega)]
      exact hst
    · rw [match_construct0_same _ _ blockRead_ctor] at nm
      cases nm
  · -- Full path: ≥ 64 bytes left
    rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
    · rw [match_construct_ne_ctor _ _ (by decide)] at mt; cases mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
      · rw [match_construct2_bind _ _ blockRead_ctor] at mt2
        cases mt2
        obtain ⟨vCS, _, evCS, k1⟩ := evalExpr_let_bind_inv db
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evCS
        obtain ⟨vCE, _, evCE, k2⟩ := evalExpr_let_bind_inv k1
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evCE
        obtain ⟨vRT, _, evRT, k3⟩ := evalExpr_let_bind_inv k2
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evRT
        obtain ⟨vEm, _, evEm, k4⟩ := evalExpr_let_bind_inv k3
        obtain ⟨rfl, rfl⟩ := evalExpr_isEmptyStream_inv (by simp) htail evEm
        obtain ⟨vAt, _, evAt, k5⟩ := evalExpr_let_bind_inv k4
        obtain ⟨vSub, _, evSub, calAt⟩ := evalExpr_call1_inv evAt
        obtain ⟨vn1, v15, _, evn1, ev15, opSub⟩ := evalExpr_binary_inv evSub
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn1
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev15
        obtain rfl := binop_sub opSub
        obtain ⟨rfl, rfl⟩ := eval_fields_is_zero_field lib calAt
        simp only [sub15_eq_zero hc (by omega : n < 1024)] at k5
        obtain ⟨vSt, _, evSt, k6⟩ := evalExpr_let_bind_inv k5
        obtain ⟨vn2, _, evn2, calSt⟩ := evalExpr_call1_inv evSt
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn2
        obtain ⟨rfl, rfl⟩ := eval_fields_is_zero hc lib (by omega) calSt
        obtain ⟨vEn, _, evEn, k7⟩ := evalExpr_let_bind_inv k6
        obtain ⟨vea, vem, _, evea, evem, opSubE⟩ := evalExpr_binary_inv evEn
        obtain ⟨ve1, va1, _, eve1, eva1, opAddE⟩ := evalExpr_binary_inv evea
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eve1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva1
        obtain rfl := binop_add opAddE
        obtain ⟨ve2, va2, _, eve2, eva2, opMulE⟩ := evalExpr_binary_inv evem
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eve2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva2
        obtain rfl := binop_mul opMulE
        obtain rfl := binop_sub opSubE
        obtain ⟨vRo, _, evRo, k8⟩ := evalExpr_let_bind_inv k7
        obtain ⟨ve3, vciz, _, eve3, evciz, opMulR⟩ := evalExpr_binary_inv evRo
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eve3
        obtain ⟨vcc1, _, evcc1, calCIZ⟩ := evalExpr_call1_inv evciz
        obtain ⟨pcc1, epcc1, ldcc1⟩ := evalExpr_load_inv evcc1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epcc1
        obtain rfl := Except.ok.inj (hcc.symm.trans ldcc1)
        obtain ⟨rfl, rfl⟩ := eval_u64_is_zero hc lib calCIZ
        obtain rfl := binop_mul opMulR
        obtain ⟨vFl, _, evFl, k9⟩ := evalExpr_let_bind_inv k8
        obtain ⟨vf12, vf3, _, evf12, evf3, opAddF2⟩ := evalExpr_binary_inv evFl
        obtain ⟨vf1, vf2, _, evf1, evf2, opAddF1⟩ := evalExpr_binary_inv evf12
        obtain ⟨vc1, vs1, _, evc1, evs1, opM1⟩ := evalExpr_binary_inv evf1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evs1
        obtain rfl := binop_mul opM1
        obtain ⟨vc2, ve4, _, evc2, eve4, opM2⟩ := evalExpr_binary_inv evf2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eve4
        obtain rfl := binop_mul opM2
        obtain rfl := binop_add opAddF1
        obtain ⟨vc3, vr1, _, evc3, evr1, opM3⟩ := evalExpr_binary_inv evf3
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc3
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr1
        obtain rfl := binop_mul opM3
        obtain rfl := binop_add opAddF2
        obtain ⟨vDig, _, evDig, k10⟩ := evalExpr_let_bind_inv k9
        obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, eg0, eg1, eg2, eg3, eg4, calCI⟩ :=
          evalExpr_call5_inv evDig
        obtain ⟨pg0, epg0, ldg0⟩ := evalExpr_load_inv eg0
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg0
        obtain rfl := Except.ok.inj (hcv.symm.trans ldg0)
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg1
        obtain ⟨pg2, epg2, ldg2⟩ := evalExpr_load_inv eg2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epg2
        obtain rfl := Except.ok.inj (hcc.symm.trans ldg2)
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv eg3
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eg4
        set bEmpty : Bool := decide (bytes.length ≤ 64)
        have hFlEq : ((if n = 0 then (1 : F) else 0) +
            2 * (((if bytes.length ≤ 64 then 1 else 0) + if n = 15 then 1 else 0) -
                  if n = 15 then if bytes.length ≤ 64 then 1 else 0 else 0) +
            if c = 0 then if bytes.length ≤ 64 then 8 else 0 else 0) =
            ((Aiur.Library.Blake3.blockFlags (decide (n = 0)) (bEmpty || decide (n = 15))
               (bEmpty && decide (c = 0))).toNat : F) := by
          rw [flags_general]
          by_cases hle64 : bytes.length ≤ 64 <;> by_cases hn0 : n = 0 <;>
            by_cases hn15 : n = 15 <;> by_cases hc0 : c = 0 <;>
            simp [bEmpty, hle64, hn0, hn15, hc0]
        rw [hFlEq, show (64 : F) = ((64 : Nat) : F) by simp] at calCI
        obtain ⟨rfl, rfl⟩ := eval_compress_init' hc lib (len := 64) (by omega) (flags_lt _ _ _) calCI
        set dig := Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c (Nat.toUInt32 64)
          (Aiur.Library.Blake3.blockFlags (decide (n = 0)) (bEmpty || decide (n = 15))
            (bEmpty && decide (c = 0)))
        -- Now match (empty, at15)
        obtain ⟨vsc, _, bsc, armC, evSc, selC, dbC⟩ := evalExpr_match_inv k10
        obtain ⟨vem', vat', _, evem', evat', rfl⟩ := evalExpr_tuple2_inv evSc
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evem'
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evat'
        by_cases hempty : bytes.length ≤ 64
        · -- Sub-arm 1: last block (bytes.length = 64)
          have hlen : bytes.length = 64 := by omega
          have hbE : bEmpty = true := by simp [bEmpty, hempty]
          simp only [hempty, ↓reduceIte] at selC
          rcases selectArm_cons_inv selC with ⟨mtc, rfl⟩ | ⟨nmc, _⟩
          · rw [match_tuple2_lw] at mtc
            simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at mtc
            subst mtc
            simp only [List.nil_append] at dbC
            obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv dbC
            obtain ⟨vlp, vdg, _, evlp, evdg, rfl⟩ := evalExpr_construct2_inv evcell
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlp
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evdg
            refine ⟨Heap.Extends.snoc _ _, ?_⟩
            rw [type_construct, Aiur.Library.Blake3.hashBlocks_last_block bytes n c cv layer hlen,
              List.reverse_append, List.reverse_singleton, List.singleton_append]
            have hdigEq : dig = Blake3.Pure.compress cv (Blake3.Pure.blockWords bytes) c
                64 (Aiur.Library.Blake3.blockFlags (decide (n = 0)) true (decide (c = 0))) := by
              simp only [dig, hbE, Bool.true_or, Bool.true_and,
                List.take_of_length_le (by omega : bytes.length ≤ 64)]
              rfl
            rw [← hdigEq]
            exact stack_push_snoc hl
          · rw [match_tuple2_lw] at nmc; simp at nmc
        · -- More bytes remain: 64 < bytes.length
          have hlong : 64 < bytes.length := by omega
          have hbE : bEmpty = false := by simp [bEmpty, hempty]
          simp only [hempty, ↓reduceIte] at selC
          have h10 : (1 : F) ≠ 0 := one_ne_zero
          rcases selectArm_cons_inv selC with ⟨mtc, _⟩ | ⟨_, selC2⟩
          · rw [match_tuple2_lw] at mtc; simp [h10] at mtc
          · by_cases hn15 : n = 15
            · -- Sub-arm 2: chunk end (n = 15)
              simp only [hn15, ↓reduceIte] at selC2
              rcases selectArm_cons_inv selC2 with ⟨mtc2, rfl⟩ | ⟨nmc2, _⟩
              · rw [match_tuple2_wl] at mtc2
                simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at mtc2
                subst mtc2
                simp only [List.nil_append] at dbC
                obtain ⟨viv, _, eviv, k11⟩ := evalExpr_let_bind_inv dbC
                obtain ⟨rfl, rfl⟩ := eval_iv lib (evalExpr_call0_inv eviv)
                obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, e0, e1, e2, e3, e4, calRec⟩ :=
                  evalExpr_call5_inv k11
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
                obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
                obtain ⟨vsucc, _, evsucc, rfl, rfl⟩ := evalExpr_store_inv e2
                obtain ⟨vcc2, _, evcc2, calSucc⟩ := evalExpr_call1_inv evsucc
                obtain ⟨pcc2, epcc2, ldcc2⟩ := evalExpr_load_inv evcc2
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epcc2
                obtain rfl := Except.ok.inj (hcc.symm.trans ldcc2)
                obtain ⟨rfl, rfl⟩ := eval_u64_wrapping_succ hc lib calSucc
                obtain ⟨viv', _, eviv', rfl, rfl⟩ := evalExpr_store_inv e3
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eviv'
                obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv e4
                obtain ⟨vlp, vdg, _, evlp, evdg, rfl⟩ := evalExpr_construct2_inv evcell
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlp
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evdg
                rw [type_construct, show (0 : F) = ((0 : Nat) : F) by simp] at calRec
                have hdigEq : dig = Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c
                    (Nat.toUInt32 64) (Aiur.Library.Blake3.blockFlags false true false) := by
                  simp [dig, hbE, hn15]
                rw [hdigEq] at calRec
                obtain ⟨ext2, hres⟩ := ih (bytes.drop 64) (by rw [List.length_drop]; omega)
                  (n := 0) (c := c + 1) (cv := Blake3.Pure.iv)
                  (layer := layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c
                    (Nat.toUInt32 64) (Aiur.Library.Blake3.blockFlags false true false)])
                  (by omega)
                  (htail.mono (extends3 _ _ _ _))
                  (loadValue_extend ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))
                    (loadValue_snoc _ _))
                  (loadValue_extend (Heap.Extends.snoc _ _) (loadValue_snoc _ _))
                  (by
                    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
                    exact stack_push_snoc
                      (hl.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))))
                  calRec
                refine ⟨(extends3 _ _ _ _).trans ext2, ?_⟩
                subst hn15
                rw [Aiur.Library.Blake3.hashBlocks_chunk_end bytes c cv layer hlong]
                exact hres
              · rw [match_tuple2_wl] at nmc2; simp at nmc2
            · -- Sub-arm 3: interior block of a chunk (n ≠ 15)
              simp only [hn15, ↓reduceIte] at selC2
              rcases selectArm_cons_inv selC2 with ⟨mtc2, _⟩ | ⟨_, selC3⟩
              · rw [match_tuple2_wl] at mtc2; simp [h10] at mtc2
              · rcases selectArm_cons_inv selC3 with ⟨mtc3, rfl⟩ | ⟨_, selC4⟩
                · rw [match_tuple2_ww] at mtc3
                  cases mtc3
                  simp only [List.nil_append] at dbC
                  obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, e0, e1, e2, e3, e4, calRec⟩ :=
                    evalExpr_call5_inv dbC
                  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
                  obtain ⟨vn', v1, _, evn', ev1, opAdd⟩ := evalExpr_binary_inv e1
                  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evn'
                  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
                  obtain rfl := binop_add opAdd
                  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
                  obtain ⟨vdg, _, evdg, rfl, rfl⟩ := evalExpr_store_inv e3
                  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evdg
                  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
                  have hdigEq : dig = Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c
                      (Nat.toUInt32 64) (Aiur.Library.Blake3.blockFlags (decide (n = 0)) false false) := by
                    simp [dig, hbE, hn15]
                  rw [hdigEq, show (n : F) + 1 = ((n + 1 : Nat) : F) by push_cast; ring] at calRec
                  obtain ⟨ext2, hres⟩ := ih (bytes.drop 64) (by rw [List.length_drop]; omega)
                    (n := n + 1) (c := c)
                    (cv := Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c
                      (Nat.toUInt32 64) (Aiur.Library.Blake3.blockFlags (decide (n = 0)) false false))
                    (layer := layer) (by omega)
                    (htail.mono (Heap.Extends.snoc _ _))
                    (loadValue_extend (Heap.Extends.snoc _ _) hcc)
                    (loadValue_snoc _ _)
                    (hl.mono (Heap.Extends.snoc _ _))
                    calRec
                  refine ⟨(Heap.Extends.snoc _ _).trans ext2, ?_⟩
                  rw [Aiur.Library.Blake3.hashBlocks_step bytes n c cv layer hlong hn15]
                  exact hres
                · exact False.elim (selectArm_nil_inv selC4)
      · exact False.elim (selectArm_nil_inv sel3)

private theorem eval_hash_blocks_le (hc : U32.Compatible F) (lib : Blake3LibraryWorld world) :
    ∀ (N : Nat) (bytes : List UInt8), bytes.length ≤ N → HBSpec world bytes
  | 0, bytes, h => hb_core hc lib bytes (fun _ hlt => absurd hlt (by omega))
  | N + 1, bytes, h => hb_core hc lib bytes (fun b hlt => eval_hash_blocks_le hc lib N b (by omega))

include hc lib in
/-- **`Blake3::hash_blocks`**: processes 64-byte blocks and finishes the trailing chunk, pushing
every chunk chaining value onto the layer stack as modeled by `Aiur.Library.Blake3.hashBlocks`. -/
theorem eval_hash_blocks (bytes : List UInt8) {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {inp ccp cvp lp r : SourceValue F} {h h' : Heap F}
    (hn : n ≤ 15) (hs : Stream h bytes inp) (hcc : loadValue h ccp = .ok (u64v c))
    (hcv : loadValue h cvp = .ok (vecV cv)) (hl : Stack h layer.reverse lp)
    (ev : EvalFn world "Blake3::hash_blocks" [inp, .field (n : F), ccp, cvp, lp] h r h') :
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r :=
  eval_hash_blocks_le hc lib bytes.length bytes (Nat.le_refl _) hn hs hcc hcv hl ev

end StreamsAndLoop

/-! ## Section 7: Operational `EvalFn` Contracts for the Merkle Tree and Exported API -/

section MerkleAndAPI

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F} (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)

/-! ### Pure Merkle Layer Model -/

/-- Parent node flags: `PARENT` (4), plus `ROOT` (8) for the root parent (12). -/
def parentFlags (root : Bool) : UInt32 := if root then 12 else 4

/-- Parent node chaining value: `compress(IV, left ++ right, 0, 64, parentFlags root)`. -/
def parentCV (root : Bool) (l r : Blake3.Pure.CV) : Blake3.Pure.CV :=
  Blake3.Pure.compress Blake3.Pure.iv (l ++ r) 0 64 (parentFlags root)

/-- Pure model of `Blake3::next_layer(layer, digest, root)` on a top-first stack `st`. -/
def nlM (root : Bool) : List Blake3.Pure.CV → Blake3.Pure.CV →
    Option Blake3.Pure.CV × List Blake3.Pure.CV
  | [], d => (some d, [])
  | other :: rest, d =>
    match nlM false rest other with
    | (none, nl) => (some d, nl)
    | (some last, nl) => (none, parentCV (root && nl.isEmpty) last d :: nl)

/-- Next stack passed to `compress_layer` after `next_layer` returns `(pending, nl)`. -/
def resM : Option Blake3.Pure.CV × List Blake3.Pure.CV → List Blake3.Pure.CV
  | (none, nl) => nl
  | (some x, nl) => x :: nl

private theorem nlM_none_eq {root : Bool} {other d : Blake3.Pure.CV}
    {rest nl : List Blake3.Pure.CV} (hr : nlM false rest other = (none, nl)) :
    nlM root (other :: rest) d = (some d, nl) := by
  simp only [nlM, hr]

private theorem nlM_some_eq {root : Bool} {other d last : Blake3.Pure.CV}
    {rest nl : List Blake3.Pure.CV} (hr : nlM false rest other = (some last, nl)) :
    nlM root (other :: rest) d = (none, parentCV (root && nl.isEmpty) last d :: nl) := by
  simp only [nlM, hr]

private theorem nlM_shape : ∀ (st : List Blake3.Pure.CV) (d : Blake3.Pure.CV) (root : Bool),
    ((nlM root st d).1 = none ↔ st.length % 2 = 1) ∧
      (nlM root st d).2.length = (st.length + 1) / 2
  | [], _, _ => by simp [nlM]
  | other :: rest, d, root => by
    have ih := nlM_shape rest other false
    rcases hr : nlM false rest other with ⟨_ | last, nl⟩
    · rw [hr] at ih; rw [nlM_none_eq hr]
      simp only [List.length_cons] at ih ⊢; simp at ih ⊢; omega
    · rw [hr] at ih; rw [nlM_some_eq hr]
      simp only [List.length_cons] at ih ⊢; simp at ih ⊢; omega

private theorem nextLayer_append : ∀ (Z W : List Blake3.Pure.CV), Z.length % 2 = 0 →
    Aiur.Library.Blake3.nextLayer (Z ++ W) =
      Aiur.Library.Blake3.nextLayer Z ++ Aiur.Library.Blake3.nextLayer W
  | [], _, _ => by simp [Aiur.Library.Blake3.nextLayer]
  | [_], _, hz => by simp at hz
  | a :: b :: Z, W, hz => by
    have ih := nextLayer_append Z W (by simp at hz; omega)
    simp only [List.cons_append, Aiur.Library.Blake3.nextLayer, ih]

private theorem nextLayer_single (x : Blake3.Pure.CV) :
    Aiur.Library.Blake3.nextLayer [x] = [x] := by
  simp [Aiur.Library.Blake3.nextLayer]

private theorem nextLayer_pair (l r : Blake3.Pure.CV) :
    Aiur.Library.Blake3.nextLayer [l, r] = [parentCV false l r] := by
  rw [Aiur.Library.Blake3.next_layer_pair_spec]; rfl

private theorem nlM_false_spec : ∀ (st : List Blake3.Pure.CV) (d : Blake3.Pure.CV),
    (resM (nlM false st d)).reverse = Aiur.Library.Blake3.nextLayer (st.reverse ++ [d])
  | [], d => by simp [nlM, resM, Aiur.Library.Blake3.nextLayer]
  | other :: rest, d => by
    have ih := nlM_false_spec rest other
    have sh := (nlM_shape rest other false).1
    rcases hr : nlM false rest other with ⟨_ | last, nl⟩
    · rw [hr] at ih sh
      have hodd : rest.length % 2 = 1 := sh.mp rfl
      rw [nlM_none_eq hr]
      have ih' : nl.reverse = Aiur.Library.Blake3.nextLayer (rest.reverse ++ [other]) := by
        simpa [resM] using ih
      show (d :: nl).reverse = _
      simp only [List.reverse_cons]
      rw [ih', nextLayer_append (rest.reverse ++ [other]) [d] (by simp; omega), nextLayer_single]
    · rw [hr] at ih sh
      have heven : rest.length % 2 = 0 := by simp at sh; omega
      rw [nlM_some_eq hr, Bool.false_and]
      show (parentCV false last d :: nl).reverse = _
      have h2 : Aiur.Library.Blake3.nextLayer (rest.reverse ++ [other]) =
          Aiur.Library.Blake3.nextLayer rest.reverse ++ [other] := by
        rw [nextLayer_append _ _ (by simp; omega), nextLayer_single]
      have ih' : nl.reverse ++ [last] = Aiur.Library.Blake3.nextLayer rest.reverse ++ [other] := by
        rw [← h2, ← ih]; simp [resM]
      obtain ⟨e1, e2⟩ := List.append_inj' ih' rfl
      obtain rfl : last = other := by simpa using e2
      simp only [List.reverse_cons]
      rw [e1, List.append_assoc, List.singleton_append,
        nextLayer_append _ [last, d] (by simp; omega), nextLayer_pair]

private theorem nlM_root (other : Blake3.Pure.CV) (rest : List Blake3.Pure.CV)
    (d : Blake3.Pure.CV) (hne : rest ≠ []) :
    nlM true (other :: rest) d = nlM false (other :: rest) d := by
  have sh := (nlM_shape rest other false).2
  rcases hr : nlM false rest other with ⟨_ | last, nl⟩
  · rw [nlM_none_eq hr, nlM_none_eq hr]
  · have hnl : nl ≠ [] := by
      rw [hr] at sh; rintro rfl
      have := List.length_pos_iff.mpr hne; simp at sh; omega
    simp only [nlM_some_eq hr, List.isEmpty_eq_false_iff.mpr hnl, Bool.and_false]

private theorem compressLayer_step (d : Blake3.Pure.CV) (rest : List Blake3.Pure.CV)
    (hne : rest ≠ []) :
    Aiur.Library.Blake3.compressLayer (resM (nlM true rest d)).reverse =
      Aiur.Library.Blake3.compressLayer (d :: rest).reverse := by
  match rest, hne with
  | [], hne => exact absurd rfl hne
  | [l], _ =>
    have e : nlM true [l] d = (none, [parentCV true l d]) := by simp [nlM]
    rw [e]
    show Aiur.Library.Blake3.compressLayer [parentCV true l d].reverse =
      Aiur.Library.Blake3.compressLayer [d, l].reverse
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      Aiur.Library.Blake3.compressLayer]
    rfl
  | l :: m :: tl, _ =>
    rw [nlM_root l (m :: tl) d (by simp), nlM_false_spec,
      show (d :: l :: m :: tl).reverse = (l :: m :: tl).reverse ++ [d] from List.reverse_cons]
    have hlen : 3 ≤ ((l :: m :: tl).reverse ++ [d]).length := by simp
    generalize ((l :: m :: tl).reverse ++ [d]) = X at hlen ⊢
    rcases X with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · exact (Aiur.Library.Blake3.compress_layer_step_spec a b c t).symm

omit [DecidableEq F] in
private theorem maybeV_none {p : Option Blake3.Pure.CV}
    (h : maybeV p = (.construct "Blake3::MaybeDigest" "None" [] : SourceValue F)) : p = none := by
  cases p with
  | none => rfl
  | some _ => simp [maybeV] at h

omit [DecidableEq F] in
private theorem maybeV_some {p : Option Blake3.Pure.CV} {x : SourceValue F}
    (h : maybeV p = .construct "Blake3::MaybeDigest" "Some" [x]) :
    ∃ d, p = some d ∧ x = vecV d := by
  cases p with
  | none => simp [maybeV] at h
  | some d =>
    simp only [maybeV, Value.construct.injEq, List.cons.injEq, and_true, true_and] at h
    exact ⟨d, rfl, h.symm⟩

omit [DecidableEq F] in
private theorem parentFlags_field (root : Bool) :
    (((parentFlags root).toNat : Nat) : F) = 4 + 8 * rootF root := by
  cases root
  · show (((4 : UInt32).toNat : Nat) : F) = 4 + 8 * 0; norm_num
  · show (((12 : UInt32).toNat : Nat) : F) = 4 + 8 * 1; norm_num

private theorem parentFlags_lt (root : Bool) : (parentFlags root).toNat < 256 := by
  cases root <;> decide

omit [DecidableEq F] in
private theorem vecV_eight (a : Vector UInt32 8) :
    (vecV a : SourceValue F) =
      .tuple [wv a[0], wv a[1], wv a[2], wv a[3], wv a[4], wv a[5], wv a[6], wv a[7]] := rfl

omit [DecidableEq F] in
private theorem vecV_toList {n : Nat} (v : Vector UInt32 n) :
    (vecV v : SourceValue F) = .tuple (v.toList.map wv) := by
  unfold vecV; congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

omit [DecidableEq F] in
private theorem vecV_append8 (a b : Vector UInt32 8) :
    (vecV (a ++ b) : SourceValue F) =
      .tuple [wv a[0], wv a[1], wv a[2], wv a[3], wv a[4], wv a[5], wv a[6], wv a[7],
              wv b[0], wv b[1], wv b[2], wv b[3], wv b[4], wv b[5], wv b[6], wv b[7]] := by
  have ea : (a.toList.map wv : List (SourceValue F)) =
      [wv a[0], wv a[1], wv a[2], wv a[3], wv a[4], wv a[5], wv a[6], wv a[7]] :=
    Value.tuple.inj ((vecV_toList a).symm.trans (vecV_eight a))
  have eb : (b.toList.map wv : List (SourceValue F)) =
      [wv b[0], wv b[1], wv b[2], wv b[3], wv b[4], wv b[5], wv b[6], wv b[7]] :=
    Value.tuple.inj ((vecV_toList b).symm.trans (vecV_eight b))
  simp only [vecV_toList, Vector.toList_append, List.map_append, ea, eb, List.cons_append,
    List.nil_append]

/-! ### `Blake3::next_layer` and `Blake3::compress_layer` -/

set_option maxHeartbeats 800000 in
include hc lib in
/-- **`Blake3::next_layer`**: pairs chaining values on the stack from bottom to top,
returning `(maybe_pending, new_layer)` as modeled by `nlM`. -/
theorem eval_next_layer (st : List Blake3.Pure.CV) {d : Blake3.Pure.CV} {root : Bool}
    {p r : SourceValue F} {h h' : Heap F}
    (hs : Stack h st p)
    (ev : EvalFn world "Blake3::next_layer" [p, vecV d, .field (rootF root)] h r h') :
    Heap.Extends h h' ∧ ∃ q, r = .tuple [maybeV (nlM root st d).1, q] ∧
      Stack h' (nlM root st d).2 q := by
  induction st generalizing d root p r h h' with
  | nil =>
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_next_layer rfl ev
    obtain ⟨v, _, bs, armBody, evLd, sel, db⟩ := evalExpr_match_inv body
    obtain ⟨pl, evpl, ld⟩ := evalExpr_load_inv evLd
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpl
    rcases stack_inv hs ld with ⟨_, rfl⟩ | ⟨_, _, _, he, _, _⟩
    · rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, _⟩
      · rw [match_construct0_same _ _ layerNode_ctor] at mt
        cases mt
        simp only [List.nil_append] at db
        obtain ⟨v1, v2, _, ev1, ev2, rfl⟩ := evalExpr_tuple2_inv db
        obtain ⟨vd, evd, rfl⟩ := evalExpr_construct1_inv ev1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evd
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2
        exact ⟨Heap.Extends.refl _, _, rfl, hs⟩
      · rw [match_construct0_same _ _ layerNode_ctor] at nm; cases nm
    · cases he
  | cons other rest ih =>
    obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_next_layer rfl ev
    obtain ⟨v, _, bs, armBody, evLd, sel, db⟩ := evalExpr_match_inv body
    obtain ⟨pl, evpl, ld⟩ := evalExpr_load_inv evLd
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpl
    rcases stack_inv hs ld with ⟨he, _⟩ | ⟨other', rest', q0, he, rfl, hq0⟩
    · cases he
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rcases selectArm_cons_inv sel with ⟨mt, _⟩ | ⟨_, sel2⟩
      · rw [match_construct_ne_ctor _ _ (by decide)] at mt; cases mt
      · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
        · rw [match_construct2_bind _ _ layerNode_ctor] at mt2
          cases mt2
          obtain ⟨vLast, vNL, _, evRec, k1⟩ := evalExpr_let_tuple2_inv db
          obtain ⟨a0, a1, a2, _, _, _, e0, e1, e2, calRec⟩ := evalExpr_call3_inv evRec
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
          obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e2
          rw [show (0 : F) = rootF false from rfl] at calRec
          obtain ⟨ext1, q', hq', hst'⟩ :=
            ih (d := other) (root := false) hq0 calRec
          rcases hr : nlM false rest other with ⟨pend, nl⟩
          rw [hr] at hq' hst'
          simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
          obtain ⟨rfl, rfl⟩ := hq'
          obtain ⟨vL, _, bsL, armL, evL, selL, dbL⟩ := evalExpr_match_inv k1
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evL
          cases pend with
          | none =>
            -- Nothing pending below -> d becomes pending
            simp only [maybeV] at selL
            rcases selectArm_cons_inv selL with ⟨mtL, rfl⟩ | ⟨nmL, _⟩
            · rw [match_construct0_same _ _ maybeDigest_ctor] at mtL
              cases mtL
              simp only [List.nil_append] at dbL
              obtain ⟨u1, u2, _, eu1, eu2, rfl⟩ := evalExpr_tuple2_inv dbL
              obtain ⟨vd, evd, rfl⟩ := evalExpr_construct1_inv eu1
              obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evd
              obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eu2
              rw [nlM_none_eq hr]
              exact ⟨ext1, _, rfl, hst'⟩
            · rw [match_construct0_same _ _ maybeDigest_ctor] at nmL; cases nmL
          | some last =>
            -- `last` pending below -> compress parent `(last ++ d)`
            simp only [maybeV] at selL
            rcases selectArm_cons_inv selL with ⟨mtL, _⟩ | ⟨_, selL2⟩
            · rw [match_construct_ne_ctor _ _ (by decide)] at mtL; cases mtL
            · rcases selectArm_cons_inv selL2 with ⟨mtL2, rfl⟩ | ⟨_, selL3⟩
              · rw [match_construct1_bind _ _ maybeDigest_ctor] at mtL2
                cases mtL2
                obtain ⟨vP, _, evP, k2⟩ := evalExpr_let_bind_inv dbL
                obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evP
                obtain ⟨vR, _, evR, k3⟩ := evalExpr_let_bind_inv k2
                obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evR
                obtain ⟨vIV, _, evIV, k4⟩ := evalExpr_let_bind_inv k3
                obtain ⟨rfl, rfl⟩ := eval_iv lib (evalExpr_call0_inv evIV)
                obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, _, evX0, k5⟩ := evalExpr_let_array8_inv k4
                obtain ⟨hlEq, rfl⟩ := evalExpr_var_eq (by simp; rfl) evX0
                rw [vecV_eight] at hlEq
                simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlEq
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hlEq
                obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15, _, evX8, k6⟩ := evalExpr_let_array8_inv k5
                obtain ⟨hdEq, rfl⟩ := evalExpr_var_eq (by simp; rfl) evX8
                rw [vecV_eight] at hdEq
                simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdEq
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hdEq
                obtain ⟨vBlk, _, evBlk, k7⟩ := evalExpr_let_bind_inv k6
                have hloc : ∀ (tailEnv : Environment F Nat) (i : Nat), i < 16 →
                    (([("x8", wv (F := F) d[0]), ("x9", wv d[1]), ("x10", wv d[2]), ("x11", wv d[3]),
                       ("x12", wv d[4]), ("x13", wv d[5]), ("x14", wv d[6]), ("x15", wv d[7])] ++
                      ([("x0", wv last[0]), ("x1", wv last[1]), ("x2", wv last[2]), ("x3", wv last[3]),
                        ("x4", wv last[4]), ("x5", wv last[5]), ("x6", wv last[6]), ("x7", wv last[7])] ++
                       tailEnv)) : Environment F Nat).find? (·.1 == s!"x{i}") =
                    some (s!"x{i}", if h8 : i < 8 then wv last[i] else if h16 : i < 16 then wv d[i - 8] else .tuple []) := by
                  intro tailEnv i hi; interval_cases i <;> rfl
                obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv (List.range 16)
                  (g := fun i => if h8 : i < 8 then wv (F := F) last[i]
                                 else if h16 : i < 16 then wv d[i - 8] else .tuple [])
                  (fun i hi _ _ _ ei => evalExpr_var_eq (hloc _ i (List.mem_range.mp hi)) ei) evBlk
                have hblkEq : Value.tuple ((List.range 16).map fun i =>
                    if h8 : i < 8 then wv (F := F) last[i]
                    else if h16 : i < 16 then wv d[i - 8] else .tuple []) = vecV (last ++ d) := by
                  rw [vecV_append8]; rfl
                rw [hblkEq] at k7
                obtain ⟨vN, _, bsN, armN, evN, selN, dbN⟩ := evalExpr_match_inv k7
                obtain ⟨pN, epN, ldN⟩ := evalExpr_load_inv evN
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epN
                rcases stack_inv hst' ldN with ⟨rfl, rfl⟩ | ⟨cvTop, nlTail, qTop, rfl, rfl, _⟩
                · -- `new_layer` is `Nil`: propagate `root`
                  rcases selectArm_cons_inv selN with ⟨mtN, rfl⟩ | ⟨nmN, _⟩
                  · rw [match_construct0_same _ _ layerNode_ctor] at mtN
                    cases mtN
                    simp only [List.nil_append] at dbN
                    obtain ⟨vFl, _, evFl, k8⟩ := evalExpr_let_bind_inv dbN
                    obtain ⟨vp', vm', _, evp', evm', opAdd⟩ := evalExpr_binary_inv evFl
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp'
                    obtain ⟨vr1, vr2, _, evr1, evr2, opMul⟩ := evalExpr_binary_inv evm'
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr1
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr2
                    obtain rfl := binop_mul opMul
                    obtain rfl := binop_add opAdd
                    obtain ⟨vDig, _, evDig, k9⟩ := evalExpr_let_bind_inv k8
                    obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, e0, e1, e2, e3, e4, calCI⟩ :=
                      evalExpr_call5_inv evDig
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
                    obtain ⟨rfl, rfl⟩ := evalExpr_zeroU64_inv lib e2
                    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e3
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
                    rw [← parentFlags_field root, show (64 : F) = ((64 : Nat) : F) by simp] at calCI
                    obtain ⟨rfl, rfl⟩ := eval_compress_init' hc lib (len := 64) (by omega)
                      (parentFlags_lt root) calCI
                    obtain ⟨u1, u2, _, eu1, eu2, rfl⟩ := evalExpr_tuple2_inv k9
                    obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv eu1
                    obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv eu2
                    obtain ⟨vq', vdg', _, evq', evdg', rfl⟩ := evalExpr_construct2_inv evcell
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
                    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evdg'
                    rw [nlM_some_eq hr, List.isEmpty_nil, Bool.and_true, type_construct]
                    exact ⟨ext1.trans (Heap.Extends.snoc _ _), _, rfl, stack_push_snoc hst'⟩
                  · rw [match_construct0_same _ _ layerNode_ctor] at nmN; cases nmN
                · -- `new_layer` is non-empty: not root (`flags = PARENT`)
                  rcases selectArm_cons_inv selN with ⟨mtN, _⟩ | ⟨_, selN2⟩
                  · rw [match_construct_ne_ctor _ _ (by decide)] at mtN; cases mtN
                  · rcases selectArm_cons_inv selN2 with ⟨mtN2, rfl⟩ | ⟨_, selN3⟩
                    · rw [match_wildcard] at mtN2
                      cases mtN2
                      simp only [List.nil_append] at dbN
                      obtain ⟨vFl, _, evFl, k8⟩ := evalExpr_let_bind_inv dbN
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evFl
                      obtain ⟨vDig, _, evDig, k9⟩ := evalExpr_let_bind_inv k8
                      obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, e0, e1, e2, e3, e4, calCI⟩ :=
                        evalExpr_call5_inv evDig
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
                      obtain ⟨rfl, rfl⟩ := evalExpr_zeroU64_inv lib e2
                      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e3
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
                      have h4 : (4 : F) = ((parentFlags false).toNat : F) := by
                        rw [parentFlags_field]; simp [rootF]
                      rw [h4, show (64 : F) = ((64 : Nat) : F) by simp] at calCI
                      obtain ⟨rfl, rfl⟩ := eval_compress_init' hc lib (len := 64) (by omega)
                        (parentFlags_lt false) calCI
                      obtain ⟨u1, u2, _, eu1, eu2, rfl⟩ := evalExpr_tuple2_inv k9
                      obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv eu1
                      obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv eu2
                      obtain ⟨vq', vdg', _, evq', evdg', rfl⟩ := evalExpr_construct2_inv evcell
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
                      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evdg'
                      rw [nlM_some_eq hr, List.isEmpty_cons, Bool.and_false, type_construct]
                      exact ⟨ext1.trans (Heap.Extends.snoc _ _), _, rfl, stack_push_snoc hst'⟩
                    · exact False.elim (selectArm_nil_inv selN3)
              · exact False.elim (selectArm_nil_inv selL3)
        · exact False.elim (selectArm_nil_inv sel3)

private def CLSpec (world : World F) (st : List Blake3.Pure.CV) : Prop :=
  ∀ {p r : SourceValue F} {h h' : Heap F},
    Stack h st p → EvalFn world "Blake3::compress_layer" [p] h r h' →
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.compressLayer st.reverse)

private theorem resM_none {p : Option Blake3.Pure.CV × List Blake3.Pure.CV} (h : p.1 = none) :
    resM p = p.2 := by
  rcases p with ⟨_ | _, _⟩
  · rfl
  · simp at h

private theorem resM_some {p : Option Blake3.Pure.CV × List Blake3.Pure.CV} {x : Blake3.Pure.CV}
    (h : p.1 = some x) : resM p = x :: p.2 := by
  rcases p with ⟨_ | _, _⟩
  · simp at h
  · simp at h; subst h; rfl

private theorem cl_core (hc : U32.Compatible F) (lib : Blake3LibraryWorld world)
    (st : List Blake3.Pure.CV)
    (ih : ∀ st' : List Blake3.Pure.CV, st'.length < st.length → CLSpec world st') :
    CLSpec world st := by
  intro p r h h' hs ev
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_compress_layer rfl ev
  obtain ⟨vTop, _, bsTop, evTop, mtTop, k1⟩ := evalExpr_let_inv body
  obtain ⟨pl, evpl, ldTop⟩ := evalExpr_load_inv evTop
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpl
  rcases stack_inv hs ldTop with ⟨rfl, rfl⟩ | ⟨d, rest, qRest, rfl, rfl, hrest⟩
  · rw [match_construct_ne_ctor _ _ (by decide)] at mtTop; cases mtTop
  · rw [match_construct2_bind _ _ layerNode_ctor] at mtTop
    cases mtTop
    obtain ⟨vR, _, bsR, armR, evR, selR, dbR⟩ := evalExpr_match_inv k1
    obtain ⟨pR, evpR, ldR⟩ := evalExpr_load_inv evR
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpR
    rcases stack_inv hrest ldR with ⟨rfl, rfl⟩ | ⟨cv2, rest2, q2, rfl, rfl, _⟩
    · -- Single chaining value: it is the root
      rcases selectArm_cons_inv selR with ⟨mtR, rfl⟩ | ⟨nmR, _⟩
      · rw [match_construct0_same _ _ layerNode_ctor] at mtR
        cases mtR
        simp only [List.nil_append] at dbR
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) dbR
        refine ⟨Heap.Extends.refl _, ?_⟩
        rw [List.reverse_singleton, Aiur.Library.Blake3.compress_layer_singleton]
      · rw [match_construct0_same _ _ layerNode_ctor] at nmR; cases nmR
    · -- At least 2 chaining values: run `next_layer` and recurse
      rcases selectArm_cons_inv selR with ⟨mtR, _⟩ | ⟨_, selR2⟩
      · rw [match_construct_ne_ctor _ _ (by decide)] at mtR; cases mtR
      · rcases selectArm_cons_inv selR2 with ⟨mtR2, rfl⟩ | ⟨_, selR3⟩
        · rw [match_wildcard] at mtR2
          cases mtR2
          simp only [List.nil_append] at dbR
          obtain ⟨vLast, vNM, _, evNL, k2⟩ := evalExpr_let_tuple2_inv dbR
          obtain ⟨a0, a1, a2, _, _, _, e0, e1, e2, calNL⟩ := evalExpr_call3_inv evNL
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
          obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e2
          rw [show (1 : F) = rootF true from rfl] at calNL
          obtain ⟨ext1, q', hq', hst'⟩ :=
            eval_next_layer hc lib (cv2 :: rest2) (d := d) (root := true) hrest calNL
          simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hq'
          obtain ⟨rfl, rfl⟩ := hq'
          obtain ⟨vL, _, bsL, armL, evL, selL, dbL⟩ := evalExpr_match_inv k2
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evL
          have hsh := nlM_shape (cv2 :: rest2) d true
          rcases hr : nlM true (cv2 :: rest2) d with ⟨pend, nl⟩
          rw [hr] at selL hst' hsh
          cases pend with
          | none =>
            simp only [maybeV] at selL
            rcases selectArm_cons_inv selL with ⟨mtL, rfl⟩ | ⟨nmL, _⟩
            · rw [match_construct0_same _ _ maybeDigest_ctor] at mtL
              cases mtL
              simp only [List.nil_append] at dbL
              obtain ⟨vq, _, evq, calRec⟩ := evalExpr_call1_inv dbL
              obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq
              obtain ⟨ext2, rfl⟩ := ih nl (by simp only [List.length_cons] at hsh ⊢; omega) hst' calRec
              refine ⟨ext1.trans ext2, ?_⟩
              rw [← compressLayer_step d (cv2 :: rest2) (by simp),
                resM_none (by rw [hr]), hr]
            · rw [match_construct0_same _ _ maybeDigest_ctor] at nmL; cases nmL
          | some last =>
            simp only [maybeV] at selL
            rcases selectArm_cons_inv selL with ⟨mtL, _⟩ | ⟨_, selL2⟩
            · rw [match_construct_ne_ctor _ _ (by decide)] at mtL; cases mtL
            · rcases selectArm_cons_inv selL2 with ⟨mtL2, rfl⟩ | ⟨_, selL3⟩
              · rw [match_construct1_bind _ _ maybeDigest_ctor] at mtL2
                cases mtL2
                obtain ⟨vp', _, evp', calRec⟩ := evalExpr_call1_inv dbL
                obtain ⟨vcell, _, evcell, rfl, rfl⟩ := evalExpr_store_inv evp'
                obtain ⟨vq', vl', _, evq', evl', rfl⟩ := evalExpr_construct2_inv evcell
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
                obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evl'
                rw [type_construct] at calRec
                have heven : (cv2 :: rest2).length % 2 = 0 := by
                  have h1 := hsh.1; simp at h1; omega
                obtain ⟨ext2, rfl⟩ :=
                  ih (last :: nl) (by simp only [List.length_cons] at hsh heven ⊢; omega)
                    (stack_push_snoc hst') calRec
                refine ⟨ext1.trans ((Heap.Extends.snoc _ _).trans ext2), ?_⟩
                rw [← compressLayer_step d (cv2 :: rest2) (by simp),
                  resM_some (x := last) (by rw [hr]), hr]
              · exact False.elim (selectArm_nil_inv selL3)
        · exact False.elim (selectArm_nil_inv selR3)

private theorem eval_compress_layer_le (hc : U32.Compatible F) (lib : Blake3LibraryWorld world) :
    ∀ (N : Nat) (st : List Blake3.Pure.CV), st.length ≤ N → CLSpec world st
  | 0, st, h => cl_core hc lib st (fun _ hlt => absurd hlt (by omega))
  | N + 1, st, h => cl_core hc lib st (fun st' hlt => eval_compress_layer_le hc lib N st' (by omega))

include hc lib in
/-- **`Blake3::compress_layer`**: reduces a layer stack to its root chaining value as modeled by
`Aiur.Library.Blake3.compressLayer`. -/
theorem eval_compress_layer (st : List Blake3.Pure.CV) {p r : SourceValue F} {h h' : Heap F}
    (hs : Stack h st p) (ev : EvalFn world "Blake3::compress_layer" [p] h r h') :
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.compressLayer st.reverse) :=
  eval_compress_layer_le hc lib st.length st (Nat.le_refl _) hs ev

/-! ### `Blake3::hash` -/

include hc lib in
/-- **`Blake3::hash`**: hashes any heap-allocated byte stream to `Aiur.Library.Blake3.hashModel`. -/
theorem eval_hash {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (ev : EvalFn world "Blake3::hash" [inp] h r h') :
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.hashModel bytes) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_hash rfl ev
  obtain ⟨viv, _, eviv, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := eval_iv lib (evalExpr_call0_inv eviv)
  obtain ⟨vlay, _, evlay, calCL⟩ := evalExpr_call1_inv k1
  obtain ⟨g0, g1, g2, g3, g4, _, _, _, _, _, e0, e1, e2, e3, e4, calHB⟩ :=
    evalExpr_call5_inv evlay
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
  obtain ⟨vcc, _, evcc, rfl, rfl⟩ := evalExpr_store_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_zeroU64_inv lib evcc
  obtain ⟨viv', _, eviv', rfl, rfl⟩ := evalExpr_store_inv e3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eviv'
  obtain ⟨vnil, _, evnil, rfl, rfl⟩ := evalExpr_store_inv e4
  obtain ⟨rfl, rfl⟩ := evalExpr_construct0_inv evnil
  rw [type_construct, show (0 : F) = ((0 : Nat) : F) by simp] at calHB
  obtain ⟨ext1, hst⟩ := eval_hash_blocks hc lib bytes (n := 0) (c := 0) (cv := Blake3.Pure.iv)
    (layer := []) (by omega)
    (hs.mono (extends3 _ _ _ _))
    (loadValue_extend ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)) (loadValue_snoc _ _))
    (loadValue_extend (Heap.Extends.snoc _ _) (loadValue_snoc _ _))
    (stack_nil_snoc _)
    calHB
  obtain ⟨ext2, rfl⟩ := eval_compress_layer hc lib _ hst calCL
  refine ⟨(extends3 _ _ _ _).trans (ext1.trans ext2), ?_⟩
  rw [List.reverse_reverse]
  rfl

include hc lib in
/-- **`Blake3::hash` computes BLAKE3**: on any native input (`bytes.length < 2^64`), the bytes
of `Blake3::hash`'s returned chaining value equal `Blake3.Pure.digest bytes`. -/
theorem eval_hash_digest {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (native : Blake3.Pure.NativeInput bytes)
    (ev : EvalFn world "Blake3::hash" [inp] h r h') :
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.hashModel bytes) ∧
      Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes) = Blake3.Pure.digest bytes :=
  ⟨(eval_hash hc lib hs ev).1, (eval_hash hc lib hs ev).2,
    Aiur.Library.Blake3.hash_model_spec bytes native⟩

/-! ### `Blake3::digest_bytes`, `address_to_fields`, `address_from_fields`, `verify_bytes_against`, `bytes_to_addr`, `pack_word`, `pack_digest` -/

private theorem bIdx_ne_digest (n : Nat) (hn : n < 8) : (s!"b{n}" == "digest") = false := by
  have hall : ((List.range 8).all fun i => !(s!"b{i}" == "digest")) = true := by decide
  have := List.all_eq_true.mp hall n (List.mem_range.mpr hn)
  simpa using this

private theorem bIdx_ne_raw (n : Nat) (hn : n < 32) : (s!"b{n}" == "raw") = false := by
  have hall : ((List.range 32).all fun i => !(s!"b{i}" == "raw")) = true := by decide
  have := List.all_eq_true.mp hall n (List.mem_range.mpr hn)
  simpa using this

private theorem bIdx_ne_bIdx {m n : Nat} (hm : m < 32) (hn : n < 32) (hne : m ≠ n) :
    (s!"b{m}" == s!"b{n}") = false := by
  have hall : ((List.range 32).all fun i =>
      (List.range 32).all fun j => (i == j) || !(s!"b{i}" == s!"b{j}")) = true := by decide
  have h1 := List.all_eq_true.mp hall m (List.mem_range.mpr hm)
  have h2 := List.all_eq_true.mp h1 n (List.mem_range.mpr hn)
  simp only [beq_false_of_ne hne, Bool.false_or, Bool.not_eq_true'] at h2
  exact h2

omit [DecidableEq F] in
private theorem proj_wv (w : UInt32) (j : Nat) (hj : j < 4) :
    projectValue (wv (F := F) w) j = .ok (bv (Blake3.Pure.wordBytes w)[j]) := by
  interval_cases j <;> rfl

private theorem evalExpr_digestBytesGo_inv (lib : Blake3LibraryWorld world) {cv : Blake3.Pure.CV} :
    ∀ (k : Nat) (hk : k ≤ 8) {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      locals.find? (·.1 == "digest") = some ("digest", vecV cv) →
      (∀ i (hi : i < 8 - k), locals.find? (·.1 == s!"b{i}") = some (s!"b{i}", wv cv[i])) →
      EvalExpr world [] locals (digestBytesGo k) h r h' →
      r = digestV (Blake3.Pure.cvBytes cv) ∧ h' = h
  | 0, _, locals, h, h', r, _, hb, ev => by
    simp only [digestBytesGo] at ev
    obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv (List.range 32)
      (g := fun i => if hi : i < 32 then bv (Blake3.Pure.wordBytes cv[i / 4])[i % 4] else .tuple [])
      (fun i hi h1 rv h2 ei => by
        have hilt : i < 32 := List.mem_range.mp hi
        simp only [hilt, ↓reduceDIte]
        obtain ⟨vb, evb, pr⟩ := evalExpr_index_inv ei
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (hb (i / 4) (by omega)) evb
        exact ⟨(Except.ok.inj ((proj_wv cv[i / 4] (i % 4) (Nat.mod_lt i (by omega))).symm.trans pr)).symm, rfl⟩) ev
    refine ⟨?_, rfl⟩
    unfold digestV
    exact congrArg Value.tuple (List.ext_getElem (by simp) fun i h1 _ => by
      simp only [List.length_map, List.length_range] at h1
      simp [h1, Blake3.Pure.cvBytes])
  | k + 1, hk, locals, h, h', r, hdig, hb, ev => by
    simp only [digestBytesGo] at ev
    set idx := 8 - (k + 1)
    obtain ⟨vb, _, evb, kb⟩ := evalExpr_let_bind_inv ev
    obtain ⟨vw, _, evw, calTB⟩ := evalExpr_call1_inv evb
    obtain ⟨vd, evd, pr⟩ := evalExpr_index_inv evw
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hdig evd
    obtain rfl := Except.ok.inj ((proj_vecV cv idx (by omega)).symm.trans pr)
    obtain ⟨rfl, rfl⟩ := eval_u32_to_bytes lib calTB
    have hdig' : ((s!"b{idx}", wv (cv[idx]'(by omega))) :: locals).find? (·.1 == "digest") =
        some ("digest", vecV cv) := by
      simp only [List.find?_cons, bIdx_ne_digest idx (by omega), hdig]
    have hb' : ∀ i (hi : i < 8 - k),
        ((s!"b{idx}", wv (cv[idx]'(by omega))) :: locals).find? (·.1 == s!"b{i}") =
          some (s!"b{i}", wv cv[i]) := by
      intro i hi
      by_cases heq : i = idx
      · subst heq; simp
      · simp only [List.find?_cons, bIdx_ne_bIdx (by omega) (by omega) (Ne.symm heq),
          hb i (by omega)]
    exact evalExpr_digestBytesGo_inv lib k (by omega) hdig' hb' kb

include lib in
/-- **`Blake3::digest_bytes`**: unpacks an 8-word chaining value into its 32 little-endian bytes
(`Blake3.Pure.cvBytes`). -/
theorem eval_digest_bytes {cv : Blake3.Pure.CV} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::digest_bytes" [vecV cv] h r h') :
    r = digestV (Blake3.Pure.cvBytes cv) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_digest_bytes rfl ev
  exact evalExpr_digestBytesGo_inv lib 8 (by omega) (by simp) (fun _ hi => by omega) body

private theorem evalArgs_map_exists {α : Type*} {locals : Environment F Nat}
    {f : α → Aiur.Generic.Expr F} {P : α → SourceValue F → Prop}
    (xs : List α)
    (heach : ∀ x ∈ xs, ∀ h r h', EvalExpr world [] locals (f x) h r h' → P x r ∧ h' = h)
    {h h' : Heap F} {vs : List (SourceValue F)}
    (ev : EvalArgs world [] locals (xs.map f) h vs h') :
    List.Forall₂ P xs vs ∧ h' = h := by
  induction xs generalizing h vs with
  | nil => cases ev; exact ⟨.nil, rfl⟩
  | cons x tl ih =>
    cases ev with
    | cons hd tlEv =>
      obtain ⟨hx, rfl⟩ := heach x List.mem_cons_self _ _ _ hd
      obtain ⟨htl, rfl⟩ := ih (fun y hy => heach y (List.mem_cons_of_mem _ hy)) tlEv
      exact ⟨.cons hx htl, rfl⟩

include lib in
/-- **`Blake3::address_to_fields`**: reads the 32 entries of its input as field elements
(`UInt8::to_field` is the identity on a byte value). -/
theorem eval_address_to_fields {x r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::address_to_fields" [x] h r h') :
    h' = h ∧ ∃ (l : List (SourceValue F)) (hl : l.length = 32), r = .tuple l ∧
      ∀ i (hi : i < 32), projectValue x i = .ok (l[i]'(hl ▸ hi)) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_address_to_fields rfl ev
  cases body with
  | array hargs =>
    obtain ⟨hrel, rfl⟩ := evalArgs_map_exists (List.range 32)
      (P := fun i v => projectValue x i = .ok v)
      (fun i _ h1 rv h2 ei => by
        obtain ⟨vi, _, evi, cal⟩ := evalExpr_call1_inv ei
        obtain ⟨vt, evt, pr⟩ := evalExpr_index_inv evi
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
        obtain ⟨rfl, rfl⟩ := eval_u8_to_field lib cal
        exact ⟨pr, rfl⟩) hargs
    have hlen : _ = 32 := (List.forall₂_iff_get.mp hrel).1.symm.trans (List.length_range (n := 32))
    refine ⟨rfl, _, hlen, rfl, ?_⟩
    intro i hi
    have hget := (List.forall₂_iff_get.mp hrel).2 i (by simp [hi]) (by omega)
    simpa [List.getElem_range] using hget

include lib in
/-- **`Blake3::address_to_fields` on a represented 32-byte digest**: equals
`Aiur.Library.Blake3.addressToFields F addr`. -/
theorem eval_address_to_fields_digestV {addr : Blake3.Pure.Digest} {r : SourceValue F}
    {h h' : Heap F} (ev : EvalFn world "Blake3::address_to_fields" [digestV addr] h r h') :
    r = .tuple ((Aiur.Library.Blake3.addressToFields F addr).toList.map .field) ∧ h' = h := by
  obtain ⟨rfl, l, hlen, rfl, hproj⟩ := eval_address_to_fields lib ev
  refine ⟨?_, rfl⟩
  exact congrArg Value.tuple (List.ext_getElem (by simp [hlen]) fun i h1 _ => by
    have hi : i < 32 := by omega
    have hli : l[i] = bv addr[i] :=
      (Except.ok.inj ((proj_digestV addr i hi).symm.trans (hproj i hi))).symm
    rw [hli]
    simp [bv, Aiur.Library.Blake3.addressToFields])

private theorem evalExpr_addrFromFieldsGo_inv (lib : Blake3LibraryWorld world)
    {raw : SourceValue F} :
    ∀ (k : Nat) (hk : k ≤ 16) (acc : List UInt8),
      acc.length = 2 * (16 - k) →
      (∀ i (hi : i < acc.length), projectValue raw i = .ok (bv acc[i])) →
      ∀ {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
        locals.find? (·.1 == "raw") = some ("raw", raw) →
        (∀ i (hi : i < acc.length), locals.find? (·.1 == s!"b{i}") = some (s!"b{i}", bv acc[i])) →
        EvalExpr world [] locals (addrFromFieldsGo k) h r h' →
        ∃ d : Blake3.Pure.Digest, r = digestV d ∧
          (∀ i (hi : i < 32), projectValue raw i = .ok (bv d[i])) ∧ h' = h
  | 0, _, acc, hlen, hpr, locals, h, h', r, _, hb, ev => by
    simp only [addrFromFieldsGo] at ev
    have h32 : acc.length = 32 := by omega
    let d : Blake3.Pure.Digest := Vector.ofFn fun i : Fin 32 => acc[i.val]'(by omega)
    obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv (List.range 32)
      (g := fun i => if hi : i < 32 then bv d[i] else .tuple [])
      (fun i hi _ _ _ ei => by
        have hilt : i < 32 := List.mem_range.mp hi
        simp only [hilt, ↓reduceDIte, d, Vector.getElem_ofFn]
        exact evalExpr_var_eq (hb i (by omega)) ei) ev
    refine ⟨d, ?_, ?_, rfl⟩
    · unfold digestV
      exact congrArg Value.tuple (List.ext_getElem (by simp) fun i h1 _ => by
        simp only [List.length_map, List.length_range] at h1
        simp [h1])
    · intro i hi
      simp only [d, Vector.getElem_ofFn]
      exact hpr i (by omega)
  | k + 1, hk, acc, hlen, hpr, locals, h, h', r, hraw, hb, ev => by
    simp only [addrFromFieldsGo] at ev
    set idx := 16 - (k + 1)
    set i0 := 2 * idx
    set i1 := 2 * idx + 1
    obtain ⟨vb0, vb1, _, evPair, kb⟩ := evalExpr_let_tuple2_inv ev
    obtain ⟨v0, v1, _, _, ev0, ev1, calFF⟩ := evalExpr_call2_inv evPair
    obtain ⟨vr0, evr0, pr0⟩ := evalExpr_index_inv ev0
    obtain ⟨he0, rfl⟩ := evalExpr_var_eq hraw evr0
    rw [he0] at pr0
    obtain ⟨vr1, evr1, pr1⟩ := evalExpr_index_inv ev1
    obtain ⟨he1, rfl⟩ := evalExpr_var_eq hraw evr1
    rw [he1] at pr1
    obtain ⟨c0, c1, rfl, rfl, hpair, rfl⟩ := eval_u8_from_fields lib calFF
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hlen' : (acc ++ [c0, c1]).length = 2 * (16 - k) := by simp [hlen]; omega
    have hpr' : ∀ i (hi : i < (acc ++ [c0, c1]).length),
        projectValue raw i = .ok (bv (acc ++ [c0, c1])[i]) := by
      intro i hi
      by_cases hlt : i < acc.length
      · rw [List.getElem_append_left hlt]; exact hpr i hlt
      · rw [List.getElem_append_right (by omega)]
        by_cases h0 : i = i0
        · subst h0
          have he0 : i0 - acc.length = 0 := by omega
          simpa [he0] using pr0
        · have h1 : i = i1 := by simp [hlen] at hi; omega
          subst h1
          have he1 : i1 - acc.length = 1 := by omega
          simpa [he1] using pr1
    have hraw' : ((s!"b{i0}", bv (F := F) c0) :: (s!"b{i1}", bv c1) :: locals).find? (·.1 == "raw") =
        some ("raw", raw) := by
      simp only [List.find?_cons, bIdx_ne_raw i0 (by omega), bIdx_ne_raw i1 (by omega), hraw]
    have hb' : ∀ i (hi : i < (acc ++ [c0, c1]).length),
        ((s!"b{i0}", bv (F := F) c0) :: (s!"b{i1}", bv c1) :: locals).find? (·.1 == s!"b{i}") =
          some (s!"b{i}", bv (acc ++ [c0, c1])[i]) := by
      intro i hi
      by_cases h0 : i = i0
      · subst h0
        have he0 : (acc ++ [c0, c1])[i0]'(by omega) = c0 := by
          rw [List.getElem_append_right (by omega)]; simp [show i0 - acc.length = 0 by omega]
        simp [he0]
      · by_cases h1 : i = i1
        · subst h1
          have he1 : (acc ++ [c0, c1])[i1]'(by omega) = c1 := by
            rw [List.getElem_append_right (by omega)]; simp [show i1 - acc.length = 1 by omega]
          simp only [List.find?_cons, bIdx_ne_bIdx (by omega) (by omega) (Ne.symm h0),
            beq_self_eq_true, he1]
        · have hlt : i < acc.length := by simp [hlen] at hi; omega
          rw [List.getElem_append_left hlt]
          simp only [List.find?_cons,
            bIdx_ne_bIdx (by omega) (by omega) (Ne.symm h0),
            bIdx_ne_bIdx (by omega) (by omega) (Ne.symm h1),
            hb i hlt]
    exact evalExpr_addrFromFieldsGo_inv lib k (by omega) (acc ++ [c0, c1]) hlen' hpr' hraw' hb' kb

include lib in
/-- **`Blake3::address_from_fields`**: range-checks 32 raw field elements into bytes and returns
the represented 32-byte digest `digestV d`. -/
theorem eval_address_from_fields {raw r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::address_from_fields" [raw] h r h') :
    ∃ d : Blake3.Pure.Digest, r = digestV d ∧
      (∀ i (hi : i < 32), projectValue raw i = .ok (bv d[i])) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_address_from_fields rfl ev
  exact evalExpr_addrFromFieldsGo_inv lib 16 (by omega) [] (by simp) (fun _ hi => by simp at hi)
    (by simp) (fun _ hi => by simp at hi) body

include hc lib in
/-- **`Blake3::verify_bytes_against` (model level)**: asserts that the 32 entries of `expected`
equal the bytes of `Aiur.Library.Blake3.hashModel bytes`, returning unit. -/
theorem eval_verify_bytes_against_model {bytes : List UInt8} {inp expected r : SourceValue F}
    {h h' : Heap F} (hs : Stream h bytes inp)
    (ev : EvalFn world "Blake3::verify_bytes_against" [inp, expected] h r h') :
    Heap.Extends h h' ∧ r = .tuple [] ∧
      ∀ i (hi : i < 32),
        projectValue expected i = .ok (bv (Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes))[i]) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_verify_bytes_against rfl ev
  obtain ⟨vh, _, evh, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨vinp, _, evinp, calHash⟩ := evalExpr_call1_inv evh
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evinp
  obtain ⟨ext1, rfl⟩ := eval_hash hc lib hs calHash
  obtain ⟨_, _, evAss, k2⟩ := evalExpr_let_wildcard_inv k1
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv evAss
  obtain ⟨vdb, _, evdb, calAF1⟩ := evalExpr_call1_inv evl
  obtain ⟨vh', _, evh', calDB⟩ := evalExpr_call1_inv evdb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh'
  obtain ⟨rfl, rfl⟩ := eval_digest_bytes lib calDB
  obtain ⟨rfl, l1, hl1len, rfl, hl1⟩ := eval_address_to_fields lib calAF1
  obtain ⟨vexp, _, evexp, calAF2⟩ := evalExpr_call1_inv evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evexp
  obtain ⟨rfl, l2, hl2len, rfl, hl2⟩ := eval_address_to_fields lib calAF2
  have hlEq : l1 = l2 := Value.tuple.inj heq
  subst hlEq
  cases k2 with
  | tuple hargs =>
    cases hargs
    refine ⟨ext1, rfl, ?_⟩
    intro i hi
    rw [hl2 i hi, ← hl1 i hi, proj_digestV _ i hi]

omit [DecidableEq F] in
private theorem digest_eq_of_proj (hc : U32.Compatible F) {addr d : Blake3.Pure.Digest}
    {expected : SourceValue F} (ha : expected = digestV addr)
    (hp : ∀ i (hi : i < 32), projectValue expected i = .ok (bv d[i])) : d = addr := by
  subst ha
  apply Vector.ext
  intro i hi
  exact (bv_inj hc (Except.ok.inj ((proj_digestV addr i hi).symm.trans (hp i hi)))).symm

include hc lib in
/-- **`Blake3::verify_bytes_against`**: on any native input (`bytes.length < 2^64`) and
represented address `expected` (`Aiur.Library.Bytes.RepAddress h addr expected`), an accepting
derivation proves `Blake3.Pure.digest bytes = addr`. -/
theorem eval_verify_bytes_against {bytes : List UInt8} {addr : Blake3.Pure.Digest}
    {inp expected r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (ha : Aiur.Library.Bytes.RepAddress h addr expected)
    (native : Blake3.Pure.NativeInput bytes)
    (ev : EvalFn world "Blake3::verify_bytes_against" [inp, expected] h r h') :
    Heap.Extends h h' ∧ r = .tuple [] ∧ Blake3.Pure.digest bytes = addr := by
  obtain ⟨ext, rfl, hproj⟩ := eval_verify_bytes_against_model hc lib hs ev
  refine ⟨ext, rfl, ?_⟩
  rw [← Aiur.Library.Blake3.hash_model_spec bytes native]
  exact digest_eq_of_proj hc ha hproj

include hc lib in
/-- **`Blake3::bytes_to_addr`**: hashes `bytes` and stores its 32-byte digest
`cvBytes (hashModel bytes)` on the heap, returning a pointer to it. -/
theorem eval_bytes_to_addr {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (ev : EvalFn world "Blake3::bytes_to_addr" [inp] h r h') :
    Heap.Extends h h' ∧
      loadValue h' r = .ok (digestV (Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes))) := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_bytes_to_addr rfl ev
  obtain ⟨vh, _, evh, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨vinp, _, evinp, calHash⟩ := evalExpr_call1_inv evh
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evinp
  obtain ⟨ext1, rfl⟩ := eval_hash hc lib hs calHash
  obtain ⟨vdb, _, evdb, rfl, rfl⟩ := evalExpr_store_inv k1
  obtain ⟨vh', _, evh', calDB⟩ := evalExpr_call1_inv evdb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh'
  obtain ⟨rfl, rfl⟩ := eval_digest_bytes lib calDB
  exact ⟨ext1.trans (Heap.Extends.snoc _ _), loadValue_snoc _ _⟩

include hc lib in
/-- **`Blake3::bytes_to_addr` on a native input**: stores `Blake3.Pure.digest bytes` on the heap
and returns a pointer to it. -/
theorem eval_bytes_to_addr_digest {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (native : Blake3.Pure.NativeInput bytes)
    (ev : EvalFn world "Blake3::bytes_to_addr" [inp] h r h') :
    Heap.Extends h h' ∧ loadValue h' r = .ok (digestV (Blake3.Pure.digest bytes)) := by
  obtain ⟨ext, hld⟩ := eval_bytes_to_addr hc lib hs ev
  rw [Aiur.Library.Blake3.hash_model_spec bytes native] at hld
  exact ⟨ext, hld⟩

include lib in
/-- **`Blake3::pack_word`**: compacts a 32-bit word into its scalar field value. -/
theorem eval_pack_word {w : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::pack_word" [wv w] h r h') :
    r = .field (w.toNat : F) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_pack_word rfl ev
  obtain ⟨vc, _, evc, calCF⟩ := evalExpr_call1_inv body
  obtain ⟨vw, _, evw, calC⟩ := evalExpr_call1_inv evc
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evw
  obtain ⟨rfl, rfl⟩ := eval_u32_compact_wv lib calC
  exact eval_u32_compact_field lib calCF

include lib in
/-- **`Blake3::pack_digest`**: packs an 8-word chaining value into 8 field elements, matching
`Aiur.Library.Blake3.packDigest F cv`. -/
theorem eval_pack_digest {cv : Blake3.Pure.CV} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::pack_digest" [vecV cv] h r h') :
    r = .tuple ((Aiur.Library.Blake3.packDigest F cv).toList.map .field) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_inv lib.blake3_pack_digest rfl ev
  obtain ⟨rfl, rfl⟩ := evalExpr_array_map_inv (List.range 8)
    (g := fun i => if hi : i < 8 then .field (cv[i].toNat : F) else .tuple [])
    (fun i hi _ _ _ ei => by
      have hilt : i < 8 := List.mem_range.mp hi
      simp only [hilt, ↓reduceDIte]
      obtain ⟨vw, _, evw, calPW⟩ := evalExpr_call1_inv ei
      obtain ⟨vh, evh, pr⟩ := evalExpr_index_inv evw
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evh
      obtain rfl := Except.ok.inj ((proj_vecV cv i hilt).symm.trans pr)
      exact eval_pack_word lib calPW) body
  refine ⟨?_, rfl⟩
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [h1, Aiur.Library.Blake3.packDigest]

end MerkleAndAPI

/-! ## Section 8: Bundled `Blake3Contracts`, Field Instantiations, and Smoke Verification -/

section BundledContracts

variable {F : Type} [Field F] [DecidableEq F]

/-- **Tier-1 certified operational `EvalFn` contract bundle for `Aiur.Library.Blake3`**.

Any compiler pass or program-refinement proof in `IxCCAiur` that calls `Aiur.Library.Blake3`
functions can depend solely on `Blake3Contracts world` (obtained directly from the computable
checker `checkBlake3World s = true` plus `U32.Compatible F`), without ever importing `IxVM` or
`IxVMRefinement`. -/
structure Blake3Contracts (world : World F) : Prop where
  iv : ∀ {r h h'}, EvalFn world "Blake3::iv" [] h r h' →
    r = vecV Blake3.Pure.iv ∧ h' = h
  g_function : ∀ {a b c d x y : UInt32} {r h h'},
    EvalFn world "Blake3::g_function" [wv a, wv b, wv c, wv d, wv x, wv y] h r h' →
    r = vecV (Blake3.Pure.mix a b c d x y) ∧ h' = h
  compress_inner_j : ∀ {s m : Blake3.Pure.Block} {r h h'},
    EvalFn world "Blake3::compress_inner_j" [stateV s m] h r h' →
    r = stateV (Aiur.Library.Blake3.compressInnerJ s m) m ∧ h' = h
  compress : ∀ (n : Nat) {k : Nat} {s m : Blake3.Pure.Block} {r h h'},
    k + n = 3 →
    EvalFn world "Blake3::compress" [.field (k : F), stateV s m] h r h' →
    r = vecV (Aiur.Library.Blake3.finalizeState (compressRounds (2 * n + 1) s m).1) ∧ h' = h
  compress_init : ∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len fl : Nat}, len < 256 → fl < 256 → ∀ {r h h'},
    EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v c, .field (len : F), .field (fl : F)] h r h' →
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl.toUInt32) ∧ h' = h
  compress_init' : ∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len : Nat} {fl : UInt32}, len < 256 → fl.toNat < 256 → ∀ {r h h'},
    EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v c, .field (len : F), .field (fl.toNat : F)] h r h' →
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl) ∧ h' = h
  take_block : ∀ {inp r : SourceValue F} {bytes : List UInt8} {h h' : Heap F},
    Stream h bytes inp → EvalFn world "Blake3::take_block" [inp] h r h' →
    h' = h ∧ ((bytes.length < 64 ∧ r = .construct "Blake3::BlockRead" "Short" []) ∨
      (64 ≤ bytes.length ∧ ∃ tail,
        r = .construct "Blake3::BlockRead" "Full"
          [vecV (Blake3.Pure.blockWords (bytes.take 64)), tail] ∧
        Stream h (bytes.drop 64) tail))
  bytes_to_block : ∀ {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F},
    Stream h bytes acc → EvalFn world "Blake3::bytes_to_block" [acc] h r h' →
    h' = h ∧ 64 ≤ bytes.length ∧ r = vecV (Blake3.Pure.blockWords (bytes.take 64).reverse)
  pad_block : ∀ (n : Nat) {acc r : SourceValue F} {bytes : List UInt8} {h h' : Heap F},
    n < 1024 → Stream h bytes acc →
    EvalFn world "Blake3::pad_block" [acc, .field (n : F)] h r h' →
    Heap.Extends h h' ∧ Stream h' (List.replicate n 0 ++ bytes) r
  hash_blocks : ∀ (bytes : List UInt8) {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {inp ccp cvp lp r : SourceValue F} {h h' : Heap F},
    n ≤ 15 → Stream h bytes inp → loadValue h ccp = .ok (u64v c) →
    loadValue h cvp = .ok (vecV cv) → Stack h layer.reverse lp →
    EvalFn world "Blake3::hash_blocks" [inp, .field (n : F), ccp, cvp, lp] h r h' →
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r
  next_layer : ∀ (st : List Blake3.Pure.CV) {d : Blake3.Pure.CV} {root : Bool}
    {p r : SourceValue F} {h h' : Heap F},
    Stack h st p → EvalFn world "Blake3::next_layer" [p, vecV d, .field (rootF root)] h r h' →
    Heap.Extends h h' ∧ ∃ q, r = .tuple [maybeV (nlM root st d).1, q] ∧
      Stack h' (nlM root st d).2 q
  compress_layer : ∀ (st : List Blake3.Pure.CV) {p r : SourceValue F} {h h' : Heap F},
    Stack h st p → EvalFn world "Blake3::compress_layer" [p] h r h' →
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.compressLayer st.reverse)
  hash : ∀ {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F},
    Stream h bytes inp → EvalFn world "Blake3::hash" [inp] h r h' →
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.hashModel bytes)
  hash_digest : ∀ {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F},
    Stream h bytes inp → Blake3.Pure.NativeInput bytes →
    EvalFn world "Blake3::hash" [inp] h r h' →
    Heap.Extends h h' ∧ r = vecV (Aiur.Library.Blake3.hashModel bytes) ∧
      Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes) = Blake3.Pure.digest bytes
  digest_bytes : ∀ {cv : Blake3.Pure.CV} {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::digest_bytes" [vecV cv] h r h' →
    r = digestV (Blake3.Pure.cvBytes cv) ∧ h' = h
  address_to_fields : ∀ {x r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::address_to_fields" [x] h r h' →
    h' = h ∧ ∃ (l : List (SourceValue F)) (hl : l.length = 32), r = .tuple l ∧
      ∀ i (hi : i < 32), projectValue x i = .ok (l[i]'(hl ▸ hi))
  address_to_fields_digestV : ∀ {addr : Blake3.Pure.Digest} {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::address_to_fields" [digestV addr] h r h' →
    r = .tuple ((Aiur.Library.Blake3.addressToFields F addr).toList.map .field) ∧ h' = h
  address_from_fields : ∀ {raw r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::address_from_fields" [raw] h r h' →
    ∃ d : Blake3.Pure.Digest, r = digestV d ∧
      (∀ i (hi : i < 32), projectValue raw i = .ok (bv d[i])) ∧ h' = h
  verify_bytes_against_model : ∀ {bytes : List UInt8} {inp expected r : SourceValue F}
    {h h' : Heap F}, Stream h bytes inp →
    EvalFn world "Blake3::verify_bytes_against" [inp, expected] h r h' →
    Heap.Extends h h' ∧ r = .tuple [] ∧
      ∀ i (hi : i < 32),
        projectValue expected i = .ok (bv (Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes))[i])
  verify_bytes_against : ∀ {bytes : List UInt8} {addr : Blake3.Pure.Digest}
    {inp expected r : SourceValue F} {h h' : Heap F},
    Stream h bytes inp → Aiur.Library.Bytes.RepAddress h addr expected →
    Blake3.Pure.NativeInput bytes →
    EvalFn world "Blake3::verify_bytes_against" [inp, expected] h r h' →
    Heap.Extends h h' ∧ r = .tuple [] ∧ Blake3.Pure.digest bytes = addr
  bytes_to_addr : ∀ {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F},
    Stream h bytes inp → EvalFn world "Blake3::bytes_to_addr" [inp] h r h' →
    Heap.Extends h h' ∧
      loadValue h' r = .ok (digestV (Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes)))
  bytes_to_addr_digest : ∀ {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F},
    Stream h bytes inp → Blake3.Pure.NativeInput bytes →
    EvalFn world "Blake3::bytes_to_addr" [inp] h r h' →
    Heap.Extends h h' ∧ loadValue h' r = .ok (digestV (Blake3.Pure.digest bytes))
  pack_word : ∀ {w : UInt32} {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::pack_word" [wv w] h r h' →
    r = .field (w.toNat : F) ∧ h' = h
  pack_digest : ∀ {cv : Blake3.Pure.CV} {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::pack_digest" [vecV cv] h r h' →
    r = .tuple ((Aiur.Library.Blake3.packDigest F cv).toList.map .field) ∧ h' = h

/-- Construct `Blake3Contracts world` from `U32.Compatible F` and `Blake3LibraryWorld world`. -/
theorem Blake3Contracts.ofLibraryWorld {world : World F}
    (hc : U32.Compatible F) (lib : Blake3LibraryWorld world) : Blake3Contracts world where
  iv := eval_iv lib
  g_function := eval_g_function hc lib
  compress_inner_j := eval_compress_inner_j hc lib
  compress := eval_compress hc lib
  compress_init := eval_compress_init hc lib
  compress_init' := eval_compress_init' hc lib
  take_block := eval_take_block lib
  bytes_to_block := eval_bytes_to_block lib
  pad_block := eval_pad_block hc lib
  hash_blocks := eval_hash_blocks hc lib
  next_layer := eval_next_layer hc lib
  compress_layer := eval_compress_layer hc lib
  hash := eval_hash hc lib
  hash_digest := eval_hash_digest hc lib
  digest_bytes := eval_digest_bytes lib
  address_to_fields := eval_address_to_fields lib
  address_to_fields_digestV := eval_address_to_fields_digestV lib
  address_from_fields := eval_address_from_fields lib
  verify_bytes_against_model := eval_verify_bytes_against_model hc lib
  verify_bytes_against := eval_verify_bytes_against hc lib
  bytes_to_addr := eval_bytes_to_addr hc lib
  bytes_to_addr_digest := eval_bytes_to_addr_digest hc lib
  pack_word := eval_pack_word lib
  pack_digest := eval_pack_digest lib

/-- Construct `Blake3Contracts s.world` directly from `checkBlake3World s = true` over any
`U32.Compatible F` field. -/
theorem Blake3Contracts.ofCheck (hc : U32.Compatible F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofLibraryWorld hc (blake3LibraryWorld_of_check h)

/-- Construct `Blake3Contracts s.world` from `FieldCompatible64 F` (matching `TypedWorld`). -/
theorem Blake3Contracts.ofCheck64 (fc : FieldCompatible64 F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck fc.toU32Compatible h

/-- Construct `Blake3Contracts s.world` from `FieldCompatible F` (matching `World`). -/
theorem Blake3Contracts.ofCheckFieldCompatible (fc : FieldCompatible F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck (u32Compat_of_fieldCompatible fc) h

/-- Construct `Blake3Contracts s.world` over any prime field `ZMod p` with `3 * 2^32 ≤ p`. -/
theorem Blake3Contracts.ofCheckZMod (p : Nat) [Fact (Nat.Prime p)] (hp : 3 * U32.base ≤ p)
    {s : Generic.Source (ZMod p)} (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck (u32Compat_of_zmod p hp) h

/-- Construct `Blake3Contracts s.world` over the Goldilocks field `ZMod (2^64 - 2^32 + 1)`. -/
theorem Blake3Contracts.ofCheckGoldilocks
    {s : Generic.Source Aiur.Library.U32.Goldilocks.F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck Aiur.Library.U32.Goldilocks.compatible h

/-! ### Concrete Smoke Check & Axiom Audit -/

/-- End-to-end Goldilocks smoke theorem: any prepared Goldilocks `Generic.Source` passing
`checkBlake3World` yields certified `EvalFn` contracts for `Blake3::hash`,
`Blake3::digest_bytes`, `Blake3::verify_bytes_against`, and `Blake3::compress_init`. -/
theorem goldilocks_blake3_smoke
    (s : Generic.Source Aiur.Library.U32.Goldilocks.F)
    (hchk : checkBlake3World s = true)
    (bytes : List UInt8) (native : Blake3.Pure.NativeInput bytes)
    (inp rHash rDig : SourceValue Aiur.Library.U32.Goldilocks.F)
    (h h1 h2 : Heap Aiur.Library.U32.Goldilocks.F)
    (hs : Stream h bytes inp)
    (evHash : EvalFn s.world "Blake3::hash" [inp] h rHash h1)
    (evDig : EvalFn s.world "Blake3::digest_bytes" [rHash] h1 rDig h2) :
    Heap.Extends h h2 ∧ rDig = digestV (Blake3.Pure.digest bytes) := by
  have c := Blake3Contracts.ofCheckGoldilocks hchk
  obtain ⟨ext, rfl, hdig⟩ := c.hash_digest hs native evHash
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  exact ⟨ext, by rw [hdig]⟩

end BundledContracts

#print axioms blake3LibraryWorld_of_check
#print axioms eval_compress
#print axioms eval_compress_init
#print axioms eval_hash
#print axioms eval_hash_digest
#print axioms eval_digest_bytes
#print axioms eval_address_to_fields
#print axioms eval_address_from_fields
#print axioms eval_verify_bytes_against
#print axioms eval_bytes_to_addr
#print axioms eval_pack_digest
#print axioms Blake3Contracts.ofCheck
#print axioms Blake3Contracts.ofCheck64
#print axioms Blake3Contracts.ofCheckZMod
#print axioms Blake3Contracts.ofCheckGoldilocks
#print axioms goldilocks_blake3_smoke

end IxCC.AiurBackend.Blake3Spec
