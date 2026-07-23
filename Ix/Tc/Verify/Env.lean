import Ix.Tc.Verify.Trans
import Ix.Tc.Const
import Ix.Tc.Env

/-!
# Environment translation: `KEnv` ↔ `VEnv` (M3)

Upstream `TrEnv'` (Verify/Environment/Basic.lean:105) re-keyed for the
content-addressed environment. The structural divergences:

- **Address-keyed constants, ghost names.** `KEnv.consts` keys by
  `KId` (Blake3 address); the Theory's `VEnv` keys by `Name`, and anon
  constants carry no names at all. The assignment
  `nameOf : Address → Option Lean.Name` is ghost specification data
  (the SAME parameter the translation relation `TrKExprS` reads at
  `const`/`prj` nodes): each translating log step pins
  `nameOf id.addr = some ci'.name`, and name-injectivity across the
  env comes free from `addConst` freshness along the log.
- **Positional levels.** `TrKConstant`'s uvar link is just
  `c.lvls.toNat = ci'.uvars` — no levelParams-name-list translation
  (our `KUniv` is positional like `VLevel` already).
- **Safety via `skip` steps.** Ingress admits constants of every
  safety into `KEnv` unconditionally (Ingress.lean:371,389,406), so
  the log takes a `safety` parameter and out-of-safety constants enter
  by a `skip` step — inserted in the map with NO Theory-side step
  (upstream `Aligned.ignoreConst`'s role; upstream `TrEnv'` itself
  pins every logged constant in-safety, which cannot describe real
  anon KEnvs). The venv holds exactly the in-safety fragment, so
  lookups translate only under a `safety ≤ c.safety` hypothesis —
  discharged at reference sites by the `checkNoUnsafeRefs`
  (Check.lean:43-76) verification in M6/M7. The v1 headline
  instantiates `safety := .safe`.
- **Remaining slice-2 debts** (roadmap): the `quot` step, the
  `thm`/`opaque` kind refinement of `defn` (it currently registers the
  defeq for every kind), and `AddKInduct` — an EMPTY inductive (exact
  upstream parity: their `AddInduct` is an empty `-- TODO`), so the
  relation is uninhabited for envs containing inductives until M8
  supplies the block translation. M5/M6 consume `TrKEnv` as a
  hypothesis, so their lemmas are unaffected.
-/

namespace Ix.DefinitionSafety

/-- The safety lattice order, `unsaf < part < safe`:
`callerSafety ≤ ref.safety` says a `ref.safety`-level constant may be
referenced from a `callerSafety`-level subject — exactly what
`checkNoUnsafeRefs` (Check.lean:43-76) enforces at reference time
(safe subjects reference only safe constants; partial subjects may
also reference partial; unsafe subjects reference anything). Upstream
keys `TrConstant` by the same `safety ≤ ci.safety` (their hand-rolled
`DefinitionSafety.compare`, Verify/Expr.lean:29 — hand-rolled here too
because the derived `Ord` uses the declaration order
`unsaf < safe < part`, which is NOT the lattice). -/
protected def le : Ix.DefinitionSafety → Ix.DefinitionSafety → Bool
  | .unsaf, _ => true
  | _, .safe => true
  | .part, .part => true
  | _, _ => false

instance : LE Ix.DefinitionSafety := ⟨fun a b => a.le b⟩

instance (a b : Ix.DefinitionSafety) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = true))

theorem le_trans {a b c : Ix.DefinitionSafety} :
    a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> decide

theorem le_rfl {a : Ix.DefinitionSafety} : a ≤ a := by
  cases a <;> rfl

theorem unsaf_le {a : Ix.DefinitionSafety} : unsaf ≤ a := by
  cases a <;> rfl

theorem le_safe {a : Ix.DefinitionSafety} : a ≤ safe := by
  cases a <;> rfl

theorem le_antisymm {a b : Ix.DefinitionSafety} :
    a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> decide

end Ix.DefinitionSafety

namespace Ix.Tc

open Std (HashMap)
open Lean4Lean (VExpr VLevel VEnv VConstant VConstVal VDefVal VDecl
  VInductDecl)

/-! ### Env-extension monotonicity of the translation

The environment only grows during a run (lazy ingress); every
translation fact transports along `VEnv.LE` (upstream
`TrExprS.mono`). `trProj` never mentions the env, so its facts
transport for free. -/

theorem TrKExprS.mono {env env' : VEnv} (henv : env ≤ env')
    {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {m : Mode} {Δ : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj Δ e e') :
    TrKExprS env' uvars nameOf trProj Δ e e' := by
  induction H with
  | var h1 => exact .var h1
  | fvar h1 => exact .fvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 h4 => exact .const h1 (henv.1 h2) h3 h4
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.mono henv) (h2.mono henv) ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.mono henv) ih1 ih2
  | all h1 h2 _ _ ih1 ih2 =>
    exact .all (h1.mono henv) (h2.mono henv) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.mono henv) ih1 ih2 ih3
  | prj h1 _ h3 ih => exact .prj h1 ih h3
  | nat h1 => exact .nat (h1.mono henv)
  | str h1 => exact .str (h1.mono henv)

/-! ### Constant safety -/

/-- The safety level of a constant (upstream `ConstantInfo.safety`,
    Verify/Environment/Basic.lean:14): `defn` carries it; `axio`/
    `recr`/`indc`/`ctor` fold their `isUnsafe` flag (those kinds have
    no partial variant); `quot` is kernel-generated and safe. -/
def KConst.safety {m : Mode} : KConst m → Ix.DefinitionSafety
  | .defn (safety := s) .. => s
  | .recr (isUnsafe := u) .. => if u then .unsaf else .safe
  | .axio (isUnsafe := u) .. => if u then .unsaf else .safe
  | .quot .. => .safe
  | .indc (isUnsafe := u) .. => if u then .unsaf else .safe
  | .ctor (isUnsafe := u) .. => if u then .unsaf else .safe

/-! ### Per-constant translation (upstream `TrConstant` tower) -/

variable (safety : Ix.DefinitionSafety) (env : VEnv)
    (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The constant is in-safety and its type translates in the empty
    context, with the positional uvar counts linked (upstream
    `TrConstant`, minus the levelParams-list translation ours doesn't
    need). -/
def TrKConstant (c : KConst .anon) (ci' : VConstant) : Prop :=
  safety ≤ c.safety ∧ c.lvls.toNat = ci'.uvars ∧
  TrKExprS env ci'.uvars nameOf trProj [] c.ty ci'.type

variable (safety : Ix.DefinitionSafety) (env : VEnv)
    (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- `TrKConstant` plus the ghost name link (upstream `TrConstVal`;
    the name comes from `nameOf`, not the constant — anon constants
    are nameless). -/
def TrKConstVal (addr : Address) (c : KConst .anon) (ci' : VConstVal) :
    Prop :=
  TrKConstant safety env nameOf trProj c ci'.toVConstant ∧
  nameOf addr = some ci'.name

variable (safety : Ix.DefinitionSafety) (env : VEnv)
    (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- `TrKConstVal` plus the value translation (upstream `TrDefVal`). -/
def TrKDefVal (addr : Address) (c : KConst .anon) (val : KExpr .anon)
    (ci' : VDefVal) : Prop :=
  TrKConstVal safety env nameOf trProj addr c ci'.toVConstVal ∧
  TrKExprS env c.lvls.toNat nameOf trProj [] val ci'.value

/-! ### Monotonicity of the tower
(upstream Verify/Environment/Lemmas.lean:8-22) -/

theorem TrKConstant.sf_mono {safety safety' : Ix.DefinitionSafety}
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {c : KConst .anon} {ci' : VConstant} (hsf : safety ≤ safety')
    (H : TrKConstant safety' env nameOf trProj c ci') :
    TrKConstant safety env nameOf trProj c ci' :=
  ⟨Ix.DefinitionSafety.le_trans hsf H.1, H.2⟩

theorem TrKConstant.mono {safety : Ix.DefinitionSafety}
    {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {c : KConst .anon} {ci' : VConstant}
    (H : TrKConstant safety env nameOf trProj c ci') :
    TrKConstant safety env' nameOf trProj c ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrKConstVal.mono {safety : Ix.DefinitionSafety}
    {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {addr : Address} {c : KConst .anon} {ci' : VConstVal}
    (H : TrKConstVal safety env nameOf trProj addr c ci') :
    TrKConstVal safety env' nameOf trProj addr c ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrKDefVal.mono {safety : Ix.DefinitionSafety}
    {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {addr : Address} {c : KConst .anon} {val : KExpr .anon}
    {ci' : VDefVal}
    (H : TrKDefVal safety env nameOf trProj addr c val ci') :
    TrKDefVal safety env' nameOf trProj addr c val ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

/-! ### The environment log -/

/-- Block-level inductive translation — upstream-parity STUB (their
    `AddInduct` is an empty inductive pending the `addInduct` spec).
    M8 fills this; until then `TrKEnv'` is uninhabited for
    environments containing inductives, exactly like upstream. -/
inductive AddKInduct :
    HashMap (KId .anon) (KConst .anon) → VEnv → VInductDecl →
    HashMap (KId .anon) (KConst .anon) → VEnv → Prop

theorem AddKInduct.to_addInduct
    {C₁ : HashMap (KId .anon) (KConst .anon)} {env₁ : VEnv}
    {decl : VInductDecl} {C₂ env₂}
    (H : AddKInduct C₁ env₁ decl C₂ env₂) :
    env₁.addInduct decl = some env₂ := nomatch H

variable (safety : Ix.DefinitionSafety)
    (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The environment translation as an event log (upstream `TrEnv'`
    fused with upstream `Aligned`'s skip steps): each translating step
    checks the declaration against the pre-`VEnv`, requires
    address-freshness, and performs the Theory-side `addConst`/
    `addDefEq` step; a `skip` step inserts an out-of-safety constant
    with the `VEnv` unmoved (and no ghost-name obligation), so the
    `VEnv` holds exactly the in-safety fragment. The `Bool` tracks
    quotient initialization (vestigial until the slice-2 `quot`
    step). -/
inductive TrKEnv' :
    HashMap (KId .anon) (KConst .anon) → Bool → VEnv → Prop
  | empty : TrKEnv' {} false .empty
  | skip {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env : VEnv} {id : KId .anon} {c : KConst .anon} :
    ¬safety ≤ c.safety →
    C[id]? = none →
    TrKEnv' C Q env →
    TrKEnv' (C.insert id c) Q env
  | axio {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env env' : VEnv} {id : KId .anon} {nm : Mode.anon.F Name}
      {lps : Mode.anon.F (Array Name)} {isUnsafe : Bool}
      {lvls : UInt64} {ty : KExpr .anon} {ci' : VConstVal} :
    TrKConstVal safety env nameOf trProj id.addr
      (.axio nm lps isUnsafe lvls ty) ci' →
    C[id]? = none →
    ci'.WF env →
    env.addConst ci'.name ci'.toVConstant = some env' →
    TrKEnv' C Q env →
    TrKEnv' (C.insert id (.axio nm lps isUnsafe lvls ty)) Q env'
  | defn {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env env' : VEnv} {id : KId .anon} {nm : Mode.anon.F Name}
      {lps : Mode.anon.F (Array Name)} {kind : Ix.DefKind}
      {dsafety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {lvls : UInt64}
      {ty val : KExpr .anon} {leanAll : Mode.anon.F (Array (KId .anon))}
      {block : KId .anon} {ci' : VDefVal} :
    TrKDefVal safety env nameOf trProj id.addr
      (.defn nm lps kind dsafety hints lvls ty val leanAll block) val
      ci' →
    C[id]? = none →
    ci'.WF env →
    env.addConst ci'.name ci'.toVConstant = some env' →
    TrKEnv' C Q env →
    TrKEnv' (C.insert id (.defn nm lps kind dsafety hints lvls ty val
      leanAll block)) Q (env'.addDefEq ci'.toDefEq)
  | induct {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env : VEnv} {decl : VInductDecl}
      {C' : HashMap (KId .anon) (KConst .anon)} {env' : VEnv} :
    decl.WF env →
    AddKInduct C env decl C' env' →
    TrKEnv' C Q env →
    TrKEnv' C' Q env'

/-- The environment translation (upstream `TrEnv`), quotient flag
    packaged. -/
def TrKEnv (safety : Ix.DefinitionSafety)
    (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop)
    (kenv : KEnv .anon) (venv : VEnv) : Prop :=
  ∃ Q, TrKEnv' safety nameOf trProj kenv.consts Q venv

/-- The translated environment is well-formed — the log replays as
    `VEnv.WF'` declaration steps, with `skip` steps invisible
    (upstream `TrEnv'.wf`). -/
theorem TrKEnv'.wf {safety : Ix.DefinitionSafety}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool} {venv : VEnv}
    (H : TrKEnv' safety nameOf trProj C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | skip _ _ _ ih => exact ih
  | axio h1 h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom h3 h4⟩
  | defn h1 h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .def h3 h4⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.to_addInduct⟩

theorem TrKEnv.wf {safety : Ix.DefinitionSafety}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {kenv : KEnv .anon} {venv : VEnv}
    (H : TrKEnv safety nameOf trProj kenv venv) : venv.WF :=
  let ⟨_, H⟩ := H
  H.wf

/-! ### Reading the log: in-safety lookups translate

Anon `KId` equality is lawful (address `==` is lawful by
Verify/Expr.lean's `LawfulBEq Address`; the name component is `Unit`),
which unlocks the `Std.HashMap` lemma library for the constant map. -/

instance : LawfulBEq (KId .anon) where
  eq_of_beq {a b} h := by
    cases a with | mk addr₁ name₁ =>
    cases b with | mk addr₂ name₂ =>
    have h1 : addr₁ = addr₂ :=
      eq_of_beq (Bool.and_eq_true_iff.mp h).1
    cases name₁
    cases name₂
    cases h1
    rfl
  rfl {a} := by
    cases a with | mk addr name =>
    show (addr == addr && Mode.F.beq name name) = true
    rw [Bool.and_eq_true_iff]
    exact ⟨beq_self_eq_true addr, rfl⟩

instance : LawfulHashable (KId .anon) where
  hash_eq a b h := by rw [eq_of_beq h]

/-- Successful in-safety lookups translate: the resolved constant has
    a ghost name, a Theory-side constant at that name, and the
    translation — transported to the FINAL `VEnv` along the log's
    extension order (upstream `Aligned.find?`, address-keyed). The
    `hs` hypothesis is discharged at reference sites by the
    `checkNoUnsafeRefs` verification: skipped constants resolve in the
    map but have no Theory-side image. -/
theorem TrKEnv'.find? {safety : Ix.DefinitionSafety}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool} {venv : VEnv}
    (H : TrKEnv' safety nameOf trProj C Q venv)
    {j : KId .anon} {c : KConst .anon} (h : C[j]? = some c)
    (hs : safety ≤ c.safety) :
    ∃ n ci', nameOf j.addr = some n ∧ venv.constants n = some ci' ∧
      TrKConstant safety venv nameOf trProj c ci' := by
  induction H with
  | empty => simp at h
  | skip h1 _ _ ih =>
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · cases h
      exact absurd hs h1
    · exact ih h
  | @axio C Q env env' id nm lps isUnsafe lvls ty ci' h1 h2 h3 h4 _
      ih =>
    have le := VEnv.addConst_le h4
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next heq =>
      cases h
      have hij : id = j := eq_of_beq heq
      subst hij
      exact ⟨_, _, h1.2, VEnv.addConst_self h4, h1.1.mono le⟩
    · obtain ⟨n, ci₀, hn, hc, htr⟩ := ih h
      exact ⟨n, ci₀, hn, le.1 hc, htr.mono le⟩
  | @defn C Q env env' id nm lps kind dsafety hints lvls ty val
      leanAll block ci' h1 h2 h3 h4 _ ih =>
    have le : env ≤ env'.addDefEq ci'.toDefEq :=
      (VEnv.addConst_le h4).trans VEnv.addDefEq_le
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next heq =>
      cases h
      have hij : id = j := eq_of_beq heq
      subst hij
      exact ⟨_, _, h1.1.2, VEnv.addDefEq_le.1 (VEnv.addConst_self h4),
        h1.1.1.mono le⟩
    · obtain ⟨n, ci₀, hn, hc, htr⟩ := ih h
      exact ⟨n, ci₀, hn, le.1 hc, htr.mono le⟩
  | induct _ h2 => cases h2

/-- `TrKEnv.find?` at the `KEnv` API (`KEnv.get?` is the map lookup). -/
theorem TrKEnv.find? {safety : Ix.DefinitionSafety}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {kenv : KEnv .anon} {venv : VEnv}
    (H : TrKEnv safety nameOf trProj kenv venv)
    {j : KId .anon} {c : KConst .anon} (h : kenv.get? j = some c)
    (hs : safety ≤ c.safety) :
    ∃ n ci', nameOf j.addr = some n ∧ venv.constants n = some ci' ∧
      TrKConstant safety venv nameOf trProj c ci' :=
  let ⟨_, H⟩ := H
  H.find? h hs

end Ix.Tc
