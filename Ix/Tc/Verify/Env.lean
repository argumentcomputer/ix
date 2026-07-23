import Ix.Tc.Verify.Trans
import Ix.Tc.Const
import Ix.Tc.Env

/-!
# Environment translation: `KEnv` ↔ `VEnv` (M3 opening)

Upstream `TrEnv'` (Verify/Environment/Basic.lean:105) re-keyed for the
content-addressed environment. The structural divergences:

- **Address-keyed constants, ghost names.** `KEnv.consts` keys by
  `KId` (Blake3 address); the Theory's `VEnv` keys by `Name`, and anon
  constants carry no names at all. The assignment
  `nameOf : Address → Option Lean.Name` is ghost specification data
  (the SAME parameter the translation relation `TrKExprS` reads at
  `const`/`prj` nodes): each log step pins `nameOf id.addr =
  some ci'.name`, and name-injectivity across the env comes free from
  `addConst` freshness along the log.
- **Positional levels.** `TrKConstant`'s uvar link is just
  `c.lvls.toNat = ci'.uvars` — no levelParams-name-list translation
  (our `KUniv` is positional like `VLevel` already).
- **Slice-1 scope** (recorded in the roadmap): `axio` pins
  `isUnsafe = false` and `defn` pins `.safe` (the safety parameter +
  `VDecl.block` name-reservation for unsafe decls is a slice-2 debt);
  the `quot` step and `thm`/`opaque` kind refinements are slice-2;
  `AddKInduct` is an EMPTY inductive — exact upstream parity (their
  `AddInduct` is an empty `-- TODO`), so the relation is uninhabited
  for envs containing inductives until M8 supplies the block
  translation. M5/M6 consume `TrKEnv` as a hypothesis, so their
  lemmas are unaffected.
-/

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

/-! ### Per-constant translation (upstream `TrConstant` tower) -/

variable (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The constant's type translates in the empty context, with the
    positional uvar counts linked (upstream `TrConstant`, minus the
    levelParams-list translation ours doesn't need). -/
def TrKConstant (c : KConst .anon) (ci' : VConstant) : Prop :=
  c.lvls.toNat = ci'.uvars ∧
  TrKExprS env ci'.uvars nameOf trProj [] c.ty ci'.type

variable (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- `TrKConstant` plus the ghost name link (upstream `TrConstVal`;
    the name comes from `nameOf`, not the constant — anon constants
    are nameless). -/
def TrKConstVal (addr : Address) (c : KConst .anon) (ci' : VConstVal) :
    Prop :=
  TrKConstant env nameOf trProj c ci'.toVConstant ∧
  nameOf addr = some ci'.name

variable (env : VEnv) (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- `TrKConstVal` plus the value translation (upstream `TrDefVal`). -/
def TrKDefVal (addr : Address) (c : KConst .anon) (val : KExpr .anon)
    (ci' : VDefVal) : Prop :=
  TrKConstVal env nameOf trProj addr c ci'.toVConstVal ∧
  TrKExprS env c.lvls.toNat nameOf trProj [] val ci'.value

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

variable (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop) in
/-- The environment translation as an event log (upstream `TrEnv'`):
    each step translates one declaration against the pre-`VEnv`,
    requires address- and name-freshness, and performs the Theory-side
    `addConst`/`addDefEq` step. The `Bool` tracks quotient
    initialization (vestigial until the slice-2 `quot` step). -/
inductive TrKEnv' :
    HashMap (KId .anon) (KConst .anon) → Bool → VEnv → Prop
  | empty : TrKEnv' {} false .empty
  | axio {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env env' : VEnv} {id : KId .anon} {nm : Mode.anon.F Name}
      {lps : Mode.anon.F (Array Name)} {lvls : UInt64}
      {ty : KExpr .anon} {ci' : VConstVal} :
    TrKConstVal env nameOf trProj id.addr (.axio nm lps false lvls ty)
      ci' →
    C[id]? = none →
    ci'.WF env →
    env.addConst ci'.name ci'.toVConstant = some env' →
    TrKEnv' C Q env →
    TrKEnv' (C.insert id (.axio nm lps false lvls ty)) Q env'
  | defn {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool}
      {env env' : VEnv} {id : KId .anon} {nm : Mode.anon.F Name}
      {lps : Mode.anon.F (Array Name)} {kind : Ix.DefKind}
      {hints : Lean.ReducibilityHints} {lvls : UInt64}
      {ty val : KExpr .anon} {leanAll : Mode.anon.F (Array (KId .anon))}
      {block : KId .anon} {ci' : VDefVal} :
    TrKDefVal env nameOf trProj id.addr
      (.defn nm lps kind .safe hints lvls ty val leanAll block) val
      ci' →
    C[id]? = none →
    ci'.WF env →
    env.addConst ci'.name ci'.toVConstant = some env' →
    TrKEnv' C Q env →
    TrKEnv' (C.insert id (.defn nm lps kind .safe hints lvls ty val
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
def TrKEnv (nameOf : Address → Option Lean.Name)
    (trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop)
    (kenv : KEnv .anon) (venv : VEnv) : Prop :=
  ∃ Q, TrKEnv' nameOf trProj kenv.consts Q venv

/-- The translated environment is well-formed — the log replays as
    `VEnv.WF'` declaration steps (upstream `TrEnv'.wf`). -/
theorem TrKEnv'.wf {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool} {venv : VEnv}
    (H : TrKEnv' nameOf trProj C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | axio h1 h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom h3 h4⟩
  | defn h1 h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .def h3 h4⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.to_addInduct⟩

theorem TrKEnv.wf {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {kenv : KEnv .anon} {venv : VEnv}
    (H : TrKEnv nameOf trProj kenv venv) : venv.WF :=
  let ⟨_, H⟩ := H
  H.wf

/-! ### Reading the log: lookups translate

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

/-- Successful lookups translate: the resolved constant has a ghost
    name, a Theory-side constant at that name, and the translation —
    transported to the FINAL `VEnv` along the log's extension order
    (upstream `TrEnv.find?` / `Aligned.find?`, address-keyed). This is
    the lemma that discharges the `TrKExprS.const` premises at
    `checkConst` read sites. -/
theorem TrKEnv'.find? {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {C : HashMap (KId .anon) (KConst .anon)} {Q : Bool} {venv : VEnv}
    (H : TrKEnv' nameOf trProj C Q venv)
    {j : KId .anon} {c : KConst .anon} (h : C[j]? = some c) :
    ∃ n ci', nameOf j.addr = some n ∧ venv.constants n = some ci' ∧
      TrKConstant venv nameOf trProj c ci' := by
  induction H with
  | empty => simp at h
  | @axio C Q env env' id nm lps lvls ty ci' h1 h2 h3 h4 _ ih =>
    have le := VEnv.addConst_le h4
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next heq =>
      cases h
      have hij : id = j := eq_of_beq heq
      subst hij
      have hname := h1.2
      have hlv := h1.1.1
      have hty := h1.1.2
      exact ⟨_, _, hname, VEnv.addConst_self h4, hlv, hty.mono le⟩
    · obtain ⟨n, ci₀, hn, hc, htr⟩ := ih h
      exact ⟨n, ci₀, hn, le.1 hc, htr.1, htr.2.mono le⟩
  | @defn C Q env env' id nm lps kind hints lvls ty val leanAll block
      ci' h1 h2 h3 h4 _ ih =>
    have le : env ≤ env'.addDefEq ci'.toDefEq :=
      (VEnv.addConst_le h4).trans VEnv.addDefEq_le
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next heq =>
      cases h
      have hij : id = j := eq_of_beq heq
      subst hij
      have hname := h1.1.2
      have hlv := h1.1.1.1
      have hty := h1.1.1.2
      exact ⟨_, _, hname, VEnv.addDefEq_le.1 (VEnv.addConst_self h4),
        hlv, hty.mono le⟩
    · obtain ⟨n, ci₀, hn, hc, htr⟩ := ih h
      exact ⟨n, ci₀, hn, le.1 hc, htr.1, htr.2.mono le⟩
  | induct _ h2 => cases h2

/-- `TrKEnv.find?` at the `KEnv` API (`KEnv.get?` is the map lookup). -/
theorem TrKEnv.find? {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {kenv : KEnv .anon} {venv : VEnv}
    (H : TrKEnv nameOf trProj kenv venv)
    {j : KId .anon} {c : KConst .anon} (h : kenv.get? j = some c) :
    ∃ n ci', nameOf j.addr = some n ∧ venv.constants n = some ci' ∧
      TrKConstant venv nameOf trProj c ci' :=
  let ⟨_, H⟩ := H
  H.find? h

end Ix.Tc
