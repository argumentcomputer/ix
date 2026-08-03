import Ix.Tc.Verify.Trans
import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Inductive
import Ix.Tc.Const
import Ix.Tc.Env

/-!
# Environment translation: `KEnv` ↔ `VEnv`

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
  (Check.lean:43-76) verification at the infer/checkConst soundness
  layers. The v1 headline
  instantiates `safety := .safe`.
- **Remaining legacy debts**: the `quot` step, the `thm`/`opaque` kind
  refinement of `defn` (it currently registers the defeq for every kind),
  and `AddKInduct` — an EMPTY inductive (exact upstream parity: their
  `AddInduct` is an empty `-- TODO`). Thus this legacy relation remains
  uninhabited for envs containing inductives. The trusted-world path below
  does not use it: `TrustedCatalogLog.ambient` admits an explicit
  `InductiveOracle`. G2b removes the legacy relation from the remaining
  C1--C3 consumer interfaces; E2 eventually replaces the oracle with checked
  block construction.
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

/-- Block-level inductive translation in the legacy whole-`KEnv` relation —
    upstream-parity STUB (their `AddInduct` is an empty inductive pending the
    `addInduct` spec). `TrustedCatalogLog.ambient` below is the live G2 path;
    this constructor remains only as a quarantined compatibility interface. -/
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

/-! ## G1c: trusted-catalog log

The legacy `TrKEnv'` above indexes its semantic log by the entire concrete
hash map, forcing pending declarations to be WF before `checkConst` runs.
`TrustedCatalogLog` instead indexes only the ghost trusted predicate.  The
immutable catalog is consulted at each admission step, but pending and
unrelated catalog entries never occur in the log and therefore carry no WF
obligation.

This relation is kept as an explicit proof object over `VerifyWorld` rather
than a field of the structure.  That preserves the acyclic dependency
`World -> Decl -> Env`: `RawDeclRel` needs `VerifyWorld` for pending status,
while the trusted log needs `RawDeclRel`.  `Verify/State.lean` conjoins this
relation with loaded-catalog and intern-table coherence.
-/

/-- Add one id to a trusted predicate. -/
def TrustInsert (trusted : KId .anon → Prop) (id : KId .anon) :
    KId .anon → Prop :=
  fun target => target = id ∨ trusted target

namespace TrustInsert

theorem self {trusted : KId .anon → Prop} {id : KId .anon} :
    TrustInsert trusted id id :=
  Or.inl rfl

theorem old {trusted : KId .anon → Prop} {id target : KId .anon}
    (h : trusted target) : TrustInsert trusted id target :=
  Or.inr h

end TrustInsert

/-! ### Trusted entry provenance -/

/-- Provenance for one trusted catalog id.  Standalone entries retain their
actual declaration-WF transition.  Ambient inductive-family entries retain
the oracle's raw translation, exact Theory lookup, constant-WF fact, and every
registered recursor-rule and exact iota-pattern witnesses.  Keeping both here
is important: `TrustedCatalogLog.find` is the consumer path from an admission
event to WHNF, so dropping either at this boundary would make the oracle's
rule semantics unusable after admission. -/
inductive TrustedCatalogEntry (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (env : VEnv)
    (id : KId .anon) : Prop
  | standalone {c : KConst .anon} {d : VDecl} {before after : VEnv} :
    catalog id = some c →
    RawDeclRel env nameOf trProj id c d →
    VDecl.WF before d after →
    after ≤ env →
    TrustedCatalogEntry trProj catalog nameOf env id
  | ambient {c : KConst .anon} {name : Lean.Name} {ci : VConstant} :
    catalog id = some c →
    RawInductiveConstRel env nameOf trProj id c name ci →
    env.constants name = some ci →
    ci.WF env →
    (∀ ⦃rule⦄, c.HasRecursorRule rule →
      RawRecursorRuleRel env nameOf trProj id c rule) →
    (∀ ⦃ruleIndex rule⦄, c.RecursorRuleAt ruleIndex rule →
      ∃ pattern,
        RawRecursorRulePatternRel env catalog nameOf id c rule pattern ∧
          pattern.ruleIndex = ruleIndex) →
    TrustedCatalogEntry trProj catalog nameOf env id

namespace TrustedCatalogEntry

theorem mono {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {env env' : VEnv}
    {id : KId .anon} (henv : env ≤ env')
    (h : TrustedCatalogEntry trProj catalog nameOf env id) :
    TrustedCatalogEntry trProj catalog nameOf env' id := by
  cases h with
  | standalone hcat hraw hwf hinstalled =>
    exact .standalone hcat (hraw.mono henv) hwf (hinstalled.trans henv)
  | ambient hcat hraw hlookup hwf hrules hpatterns =>
    exact .ambient hcat (hraw.mono henv) (henv.constants hlookup)
      (hwf.mono henv) (fun _ hrule => (hrules hrule).mono henv)
      (fun {_ _} hrule => by
        obtain ⟨pattern, hpattern, hindex⟩ := hpatterns hrule
        exact ⟨pattern, hpattern.mono henv, hindex⟩)

/-- Both provenance cases expose the exact catalog/name/Theory lookup needed
by expression translation. -/
theorem lookup {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {env : VEnv}
    {id : KId .anon} (h : TrustedCatalogEntry trProj catalog nameOf env id) :
    ∃ c name ci,
      catalog id = some c ∧
      nameOf id.addr = some name ∧
      env.constants name = some ci := by
  cases h with
  | @standalone c d before after hcat hraw hwf hinstalled =>
    cases hraw with
    | «axiom» hname hty =>
      cases hwf with
      | «axiom» _ hadd =>
        exact ⟨_, _, _, hcat, hname,
          hinstalled.constants (VEnv.addConst_self hadd)⟩
    | defn hname hty hval hkind =>
      cases hkind with
      | defn =>
        cases hwf with
        | «def» _ hadd =>
          exact ⟨_, _, _, hcat, hname,
            hinstalled.constants
              (VEnv.addDefEq_le.constants (VEnv.addConst_self hadd))⟩
      | opaq | thm =>
        cases hwf with
        | «opaque» _ hadd =>
          exact ⟨_, _, _, hcat, hname,
            hinstalled.constants (VEnv.addConst_self hadd)⟩
  | ambient hcat hraw hlookup hwf hrules hpatterns =>
    exact ⟨_, _, _, hcat, hraw.nameEq, hlookup⟩

/-- Recover the registered Theory equation for any concrete recursor rule
carried by this trusted entry.  Standalone promotion cannot produce a
recursor declaration, so only an ambient inductive admission inhabits the
positive case. -/
theorem recursorRule {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {env : VEnv}
    {id : KId .anon} (h : TrustedCatalogEntry trProj catalog nameOf env id)
    {c : KConst .anon} {rule : RecRule .anon}
    (hcatalog : catalog id = some c) (hrule : c.HasRecursorRule rule) :
    RawRecursorRuleRel env nameOf trProj id c rule := by
  cases h with
  | @standalone c' d before after hcatalog' hraw hwf hinstalled =>
      have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
      subst c'
      cases hraw <;> exact False.elim hrule
  | @ambient c' name ci hcatalog' hraw hlookup hwf hrules hpatterns =>
      have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
      subst c'
      exact hrules hrule

/-- Recover the exact Lean4Lean iota-pattern witness associated with a
trusted concrete recursor rule. -/
theorem recursorPattern {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {env : VEnv}
    {id : KId .anon} (h : TrustedCatalogEntry trProj catalog nameOf env id)
    {c : KConst .anon} {ruleIndex : Nat} {rule : RecRule .anon}
    (hcatalog : catalog id = some c)
    (hrule : c.RecursorRuleAt ruleIndex rule) :
    ∃ pattern,
      RawRecursorRulePatternRel env catalog nameOf id c rule pattern ∧
        pattern.ruleIndex = ruleIndex := by
  cases h with
  | @standalone c' d before after hcatalog' hraw hwf hinstalled =>
      have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
      subst c'
      cases hraw <;> exact False.elim hrule
  | @ambient c' name ci hcatalog' hraw hlookup hwf hrules hpatterns =>
      have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
      subst c'
      exact hpatterns hrule

end TrustedCatalogEntry

/-! ### Unified trusted-constant view -/

/-- Consumer-facing provenance for one exact concrete constant.

Unlike legacy `TrKConstant`, this relation does not require a translation log
over the whole concrete `KEnv`.  It states only what C1--C3 consumers need at
a trusted lookup: the immutable catalog entry is exactly `c`; its assigned
Theory constant is installed and well-formed; universe arities agree; and the
concrete type has a raw translation to that Theory type.  Both standalone
promotion and ambient inductive admission construct the same relation.
Definition-safety authorization remains a per-reference `checkNoUnsafeRefs`
obligation; this relation supplies semantic resolution, not that operational
check. -/
structure TrustedConstRel (trProj : RawProjRel) (world : VerifyWorld)
    (id : KId .anon) (c : KConst .anon) (name : Lean.Name)
    (ci : VConstant) : Prop where
  catalog : world.catalog id = some c
  trusted : world.trusted id
  nameEq : world.nameOf id.addr = some name
  lookup : world.venv.constants name = some ci
  uvars : c.lvls.toNat = ci.uvars
  type : RawExprRel world.venv world.nameOf trProj [] c.ty ci.type
  wf : ci.WF world.venv

namespace TrustedConstRel

/-- Trusted-constant provenance transports along world extension. -/
theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after) {id : KId .anon} {c : KConst .anon}
    {name : Lean.Name} {ci : VConstant}
    (h : TrustedConstRel trProj before id c name ci) :
    TrustedConstRel trProj after id c name ci := by
  refine ⟨?_, hle.trusted h.trusted, ?_, hle.venv.constants h.lookup,
    h.uvars, ?_, h.wf.mono hle.venv⟩
  · rw [← hle.catalog]
    exact h.catalog
  · rw [← hle.nameOf]
    exact h.nameEq
  · rw [← hle.nameOf]
    exact h.type.mono hle.venv

/-- A resolved trusted constant supplies the constant-expression constructor
used by whnf/infer/checking consumers.  The caller contributes only the
per-occurrence universe-level WF and the checker's arity equality. -/
theorem trKExprS_const {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {c : KConst .anon} {name : Lean.Name}
    {ci : VConstant} (h : TrustedConstRel trProj world id c name ci)
    {us : Array (KUniv .anon)} {info : ExprInfo .anon} {ctx : KVLCtx}
    (hlevels : ∀ u ∈ us, u.toVLevel.WF ci.uvars)
    (harity : us.size = c.lvls.toNat) :
    TrKExprS world.venv ci.uvars world.nameOf trProj ctx
      (.const id us info)
      (.const name (us.toList.map KUniv.toVLevel)) :=
  .const h.nameEq h.lookup hlevels (harity.trans h.uvars)

end TrustedConstRel

/-- Event log for exactly the declarations admitted to the Theory world.

The `promote` constructor is the only way to grow the trusted set.  Its final
premise is the new declaration-WF evidence supplied by successful checking;
neither catalog membership nor raw correspondence can synthesize it. -/
inductive TrustedCatalogLog (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) :
    (KId .anon → Prop) → VEnv → Prop
  | empty :
    TrustedCatalogLog trProj catalog nameOf (fun _ => False) .empty
  | promote {trusted : KId .anon → Prop} {env env' : VEnv}
      {id : KId .anon} {c : KConst .anon} {d : VDecl} :
    TrustedCatalogLog trProj catalog nameOf trusted env →
    catalog id = some c →
    RawDeclRel env nameOf trProj id c d →
    CatalogClosed catalog c →
    ¬trusted id →
    VDecl.WF env d env' →
    TrustedCatalogLog trProj catalog nameOf (TrustInsert trusted id) env'
  | ambient {trusted : KId .anon → Prop} {env : VEnv}
      (oracle : InductiveOracle trProj catalog nameOf trusted env) :
    TrustedCatalogLog trProj catalog nameOf trusted env →
    TrustedCatalogLog trProj catalog nameOf oracle.TrustBlock oracle.after

namespace TrustedCatalogLog

/-- Replaying the trusted log constructs a well-formed Theory environment. -/
theorem wf {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {env : VEnv}
    (h : TrustedCatalogLog trProj catalog nameOf trusted env) : env.WF := by
  induction h with
  | empty => exact ⟨[], .empty⟩
  | promote _ _ _ _ _ hwf ih =>
    obtain ⟨ds, hds⟩ := ih
    exact ⟨_, .decl hwf hds⟩
  | ambient oracle _ _ => exact oracle.blockWF

/-- Every trusted id is committed by the immutable catalog. -/
theorem catalogued {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {env : VEnv}
    (h : TrustedCatalogLog trProj catalog nameOf trusted env)
    {id : KId .anon} (htrusted : trusted id) :
    Catalog.Contains catalog id := by
  induction h with
  | empty => exact False.elim htrusted
  | @promote trusted env env' newId c d hlog hcat hraw hclosed huntrusted hwf ih =>
    change id = newId ∨ trusted id at htrusted
    rcases htrusted with hnew | hold
    · subst id
      exact ⟨c, hcat⟩
    · exact ih hold
  | @ambient trusted env oracle hlog ih =>
    change oracle.members id ∨ trusted id at htrusted
    rcases htrusted with hnew | hold
    · exact oracle.catalogued hnew
    · exact ih hold

/-- Read a trusted log entry.  The raw relation is transported to the final
environment, while the original WF transition and its installed prefix are
retained. -/
theorem find {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {env : VEnv}
    (h : TrustedCatalogLog trProj catalog nameOf trusted env)
    {id : KId .anon} (htrusted : trusted id) :
    TrustedCatalogEntry trProj catalog nameOf env id := by
  induction h with
  | empty => exact False.elim htrusted
  | @promote trusted env env' newId c d hlog hcat hraw hclosed huntrusted hwf ih =>
    have hle : env ≤ env' := RawDeclRel.wf_le hraw hwf
    change id = newId ∨ trusted id at htrusted
    rcases htrusted with hnew | hold
    · subst id
      exact .standalone hcat (hraw.mono hle) hwf VEnv.LE.rfl
    · exact (ih hold).mono hle
  | @ambient trusted env oracle hlog ih =>
    change oracle.members id ∨ trusted id at htrusted
    rcases htrusted with hnew | hold
    · obtain ⟨c, name, ci, hcat, hraw, hlookup, hwf⟩ :=
        oracle.translateBlock hnew
      exact .ambient hcat hraw hlookup hwf
        (fun rule hrule => oracle.recursorFacts hnew hcat hrule)
        fun {_ _} hrule => oracle.recursorPatterns hnew hcat hrule
    · exact (ih hold).mono oracle.envLE

end TrustedCatalogLog

/-- A `VerifyWorld` is semantically justified by a trusted-only event log.
This is independent of the concrete lazy-load `KEnv`. -/
def TrustedCatalogRel (trProj : RawProjRel) (world : VerifyWorld) : Prop :=
  TrustedCatalogLog trProj world.catalog world.nameOf world.trusted world.venv

namespace TrustedCatalogRel

/-- Every arbitrary catalog starts with an empty trusted semantic log; no
catalog declaration is required to be WF. -/
theorem ofCatalog (catalog : Catalog) {trProj : RawProjRel} :
    TrustedCatalogRel trProj (VerifyWorld.ofCatalog catalog) :=
  TrustedCatalogLog.empty

/-- The log justifies the `VerifyWorld` well-formedness field independently. -/
theorem wf {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) : world.venv.WF :=
  TrustedCatalogLog.wf h

/-- Trusted lookup yields provenance for either a standalone WF transition or
an oracle-backed ambient inductive member. -/
theorem find {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) {id : KId .anon}
    (htrusted : world.trusted id) :
    TrustedCatalogEntry trProj world.catalog world.nameOf world.venv id :=
  TrustedCatalogLog.find h htrusted

/-- Resolve a concrete rule of a trusted recursor to the well-formed Theory
equation recorded when its ambient inductive block was admitted. -/
theorem recursorRule {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) {id : KId .anon}
    {c : KConst .anon} {rule : RecRule .anon}
    (htrusted : world.trusted id) (hcatalog : world.catalog id = some c)
    (hrule : c.HasRecursorRule rule) :
    RawRecursorRuleRel world.venv world.nameOf trProj id c rule :=
  (h.find htrusted).recursorRule hcatalog hrule

/-- Resolve the exact iota-pattern semantics retained for a trusted concrete
recursor rule. -/
theorem recursorPattern {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) {id : KId .anon}
    {c : KConst .anon} {ruleIndex : Nat} {rule : RecRule .anon}
    (htrusted : world.trusted id) (hcatalog : world.catalog id = some c)
    (hrule : c.RecursorRuleAt ruleIndex rule) :
    ∃ pattern,
      RawRecursorRulePatternRel world.venv world.catalog world.nameOf
        id c rule pattern ∧ pattern.ruleIndex = ruleIndex :=
  (h.find htrusted).recursorPattern hcatalog hrule

/-- Resolve an exact catalog constant through either standalone or ambient
trusted provenance.  This is the whole-`KEnv`-free replacement for the
consumer use of `TrKEnv.find?`. -/
theorem resolve {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) {id : KId .anon}
    {c : KConst .anon} (htrusted : world.trusted id)
    (hcatalog : world.catalog id = some c) :
    ∃ name ci, TrustedConstRel trProj world id c name ci := by
  have hordered := h.wf.ordered
  cases h.find htrusted with
  | @standalone c' d before after hcatalog' hraw hwf hinstalled =>
    have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
    subst c'
    cases hraw with
    | «axiom» hname htype =>
      cases hwf with
      | «axiom» _ hadd =>
        have hlookup := hinstalled.constants (VEnv.addConst_self hadd)
        exact ⟨_, _, hcatalog, htrusted, hname, hlookup, rfl, htype,
          hordered.constWF hlookup⟩
    | defn hname htype hvalue hkind =>
      cases hkind with
      | defn =>
        cases hwf with
        | «def» _ hadd =>
          have hlookup := hinstalled.constants
            (VEnv.addDefEq_le.constants (VEnv.addConst_self hadd))
          exact ⟨_, _, hcatalog, htrusted, hname, hlookup, rfl, htype,
            hordered.constWF hlookup⟩
      | opaq | thm =>
        cases hwf with
        | «opaque» _ hadd =>
          have hlookup := hinstalled.constants (VEnv.addConst_self hadd)
          exact ⟨_, _, hcatalog, htrusted, hname, hlookup, rfl, htype,
            hordered.constWF hlookup⟩
  | @ambient c' name ci hcatalog' hraw hlookup hwf hrules hpatterns =>
    have hc : c' = c := Option.some.inj (hcatalog'.symm.trans hcatalog)
    subst c'
    exact ⟨name, ci, hcatalog, htrusted, hraw.nameEq, hlookup,
      hraw.uvars, hraw.type, hwf⟩

/-- Operational trusted lookup: the id's assigned Theory name resolves to
the exact constant supplied by its recorded provenance. -/
theorem lookup {trProj : RawProjRel} {world : VerifyWorld}
    (h : TrustedCatalogRel trProj world) {id : KId .anon}
    (htrusted : world.trusted id) :
    ∃ c name ci,
      world.catalog id = some c ∧
      world.nameOf id.addr = some name ∧
      world.venv.constants name = some ci := by
  exact (TrustedCatalogRel.find h htrusted).lookup

end TrustedCatalogRel

/-! ### Ghost promotion -/

/-- World promotion keeps immutable ghost input fixed, grows the trusted set
and Theory environment, and includes every requested id. -/
def Promotes (before : VerifyWorld) (ids : KId .anon → Prop)
    (after : VerifyWorld) : Prop :=
  before ≤ after ∧ ∀ ⦃id⦄, ids id → after.trusted id

namespace Promotes

theorem catalog {before after : VerifyWorld} {ids : KId .anon → Prop}
    (h : Promotes before ids after) : before.catalog = after.catalog :=
  h.1.catalog

theorem nameOf {before after : VerifyWorld} {ids : KId .anon → Prop}
    (h : Promotes before ids after) : before.nameOf = after.nameOf :=
  h.1.nameOf

theorem trusted {before after : VerifyWorld} {ids : KId .anon → Prop}
    (h : Promotes before ids after) {id : KId .anon}
    (hid : ids id) : after.trusted id :=
  h.2 hid

theorem trans {a b c : VerifyWorld} {ids ids' : KId .anon → Prop}
    (hab : Promotes a ids b) (hbc : Promotes b ids' c) :
    Promotes a (fun id => ids id ∨ ids' id) c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro id hid
  rcases hid with hid | hid
  · exact hbc.1.trusted (hab.2 hid)
  · exact hbc.2 hid

end Promotes

/-- Admit one pending standalone declaration.  The declaration-WF argument is
unavoidable and explicit: it is the new fact supplied by checker success.
The concrete `KEnv` is not mutated. -/
theorem TrustedCatalogRel.promote
    {trProj : RawProjRel} {world : VerifyWorld} {id : KId .anon}
    {d : VDecl} {venv' : VEnv}
    (hrel : TrustedCatalogRel trProj world)
    (hpending : PendingDecl trProj world id d)
    (hwf : VDecl.WF world.venv d venv') :
    ∃ world',
      Promotes world (fun target => target = id) world' ∧
      TrustedCatalogRel trProj world' ∧
      TrustedDecl trProj world' id d := by
  obtain ⟨c, hcat, hraw, huntrusted, hclosed, hfresh⟩ := hpending
  have hle : world.venv ≤ venv' := RawDeclRel.wf_le hraw hwf
  let world' : VerifyWorld :=
    { catalog := world.catalog
      trusted := TrustInsert world.trusted id
      venv := venv'
      nameOf := world.nameOf
      venvWF := by
        obtain ⟨ds, hds⟩ := world.venvWF
        exact ⟨_, .decl hwf hds⟩
      trustedCatalogued := by
        intro target htrusted
        change target = id ∨ world.trusted target at htrusted
        rcases htrusted with hnew | hold
        · subst target
          exact ⟨c, hcat⟩
        · exact world.trustedCatalogued hold }
  refine ⟨world', ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, rfl, ?_, hle⟩, ?_⟩
    · intro target hold
      exact TrustInsert.old hold
    · intro target htarget
      subst target
      exact TrustInsert.self
  · exact TrustedCatalogLog.promote hrel hcat hraw hclosed huntrusted hwf
  · exact ⟨c, world.venv, venv', hcat, hraw.mono hle,
      TrustInsert.self, hwf, VEnv.LE.rfl⟩

/-- The G1b ill-typed pending world already satisfies the G1c trusted-log
invariant: its catalog entry remains completely outside the empty log. -/
theorem IllTypedPending.trustedCatalogRel :
    TrustedCatalogRel RawProjRel.none IllTypedPending.world :=
  TrustedCatalogLog.empty

/-! ### Executable-shape promotion fixture -/

namespace WellTypedPromotion

def targetName : Lean.Name := `Ix.Tc.Verify.wellTypedPromotion

def fixtureAddress : Address :=
  ⟨⟨Array.replicate 32 1⟩⟩

def targetId : KId .anon := ⟨fixtureAddress, ()⟩

def level : KUniv .anon := .zero fixtureAddress

def exprInfo : ExprInfo .anon where
  addr := fixtureAddress
  lbr := 0
  count0 := 0
  hasFVars := false
  mdata := ()
  metaAddr := ()

def sourceType : KExpr .anon := .sort level exprInfo

def concrete : KConst .anon := .axio () () false 0 sourceType

def theoryConstant : VConstVal where
  name := targetName
  uvars := 0
  type := .sort .zero

def theoryDecl : VDecl := .axiom theoryConstant

def catalog : Catalog := fun _ => some concrete

def world : VerifyWorld where
  catalog := catalog
  trusted := fun _ => False
  venv := .empty
  nameOf := fun _ => some targetName
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} h => False.elim h

def promotedVEnv : VEnv where
  constants := fun name =>
    if targetName = name then some theoryConstant.toVConstant else none
  defeqs := fun _ => False

theorem raw : RawDeclRel world.venv world.nameOf RawProjRel.none
    targetId concrete theoryDecl := by
  apply RawDeclRel.axiom rfl
  exact RawExprRel.sort

theorem pending : PendingDecl RawProjRel.none world targetId theoryDecl := by
  refine ⟨concrete, rfl, raw, (fun h => h), ?_, ?_⟩
  · intro id href
    exact ⟨concrete, rfl⟩
  · intro name hname
    rfl

theorem theoryConstant_wf :
    theoryConstant.toVConstant.WF world.venv := by
  exact ⟨.succ .zero, Lean4Lean.VEnv.HasType.sort (l := .zero) trivial⟩

theorem addConst :
    world.venv.addConst targetName theoryConstant.toVConstant =
      some promotedVEnv := by
  rfl

theorem declWF : VDecl.WF world.venv theoryDecl promotedVEnv :=
  .axiom theoryConstant_wf addConst

theorem trustedCatalogRel :
    TrustedCatalogRel RawProjRel.none world :=
  TrustedCatalogLog.empty

/-- Positive G1c fixture: supplying the new WF derivation promotes exactly
the pending id and immediately yields trusted lookup evidence. -/
theorem promotes :
    ∃ world',
      Promotes world (fun target => target = targetId) world' ∧
      TrustedCatalogRel RawProjRel.none world' ∧
      TrustedDecl RawProjRel.none world' targetId theoryDecl :=
  TrustedCatalogRel.promote trustedCatalogRel pending declWF

end WellTypedPromotion

end Ix.Tc
