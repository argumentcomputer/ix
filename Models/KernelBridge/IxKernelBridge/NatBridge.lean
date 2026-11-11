import IxCK.Kernel.Rules.Derived
import IxCK.Kernel.BasisA
import IxCK.Kernel.Model.Capstone
import IxCK.Kernel.Model.Rules.Sound
import IxCK.Kernel.Model.Denotes
import IxCK.Kernel.Verify.Cached.MainC
import IxCC.Src.Semantics
import IxCC.Recheck.Proof.Soundness
import IxCC.CompileClaim.Proof

/-!
# A conditional simulation lemma between `Src.run` and kernel `Red` (`IxKernelBridge.NatBridge`)

This module proves a simulation lemma between `IxCC`'s source evaluator (`Src.eval` /
`Src.run`) and `IxCK`'s kernel reduction (`Ix.Kernel.Rules.Red`), relative to a relation
`constSpec` that the user supplies, and composes it with set-theoretic denotation
(`Ix.Kernel.Denotes` in `Model.ofEnvModelM mp`) and with IxCC's own soundness theorems. It is
not a source-adequacy theorem for compiled claims: source adequacy against the kernel model
(the roadmap's target theorem, open item S8 of
`IxCC/docs/certification-design.md`) remains open. `Models/KernelBridge/README.md`
states the scope in full.

What a user must supply:
- a kernel environment `env` with `natBasisStored env = true` (no lemma derives this from
  `checkDecls`);
- `constSpec : Levels → CId → Expr md → Prop` with
  `hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e`. For each related
  definition, equation, csimp or opaque constant this asks for a proof of `Red env 0 e kbody`
  and a `RelTerm` image `kbody` of its Src body that mirrors it node for node, type arguments
  and motives included (only `sort` and `pi` positions are unconstrained); for each related
  primitive, the per-operation agreement premise of `RelHead.primBinNat`;
- a related, closed root `eRoot` (`constSpec [] root eRoot`);
- for the denotation layers, that the applied root is readable in the model (`denoteMeta`) and
  graded (`Graded`, or an `Infer` derivation).

What is not connected: the Layer 3 theorems take `env` from any `checkDecls`-accepted
declaration stream and `eRoot` from any closed term related to the Src root. Neither is derived
from the compile claim's `env` bytes or its `target`, and the root index is not tied to
`claim.target`; the theorems are conjunctions that share only the checked Src program.

The relation can be built only for a small fragment: `RelTerm.app` relates an application only
if its argument is related, whatever its relevance; constants are related only through
`constSpec`, whose `RelConstStep` has no case for an inductive type (such as `Nat` itself), an
axiom or a theorem; there is no rule for `.proj` or string literals; and `RelHead`/`RelVal`
know only the `Nat` constructors, `Nat.rec` and `Nat.casesOn`. So type arguments, numerals,
typeclass operations, `match` and recursion as Lean elaborates them are outside it. Recursion
is blocked independently: kernel `Red` is weak-head, so a related recursive constant reduces
only to its stored recursor form (`Nat.brecOn`, `WellFounded.fix`), never to the equation body
`RelConstStep.eqn` asks it to mirror. `IxKernelBridge.Examples` gives instances that do work.

## Layers

1. **Layer 1 (`srcRun_to_red`)**:
   - Simultaneous de Bruijn substitution (`subst`) commuting with `Expr.instantiate1`
     (`instantiate1_subst`, `subst_instantiate1_closed`, `red_betaGate_subst`).
   - Kernel environment predicate `natBasisStored` and multi-step `Red` lemmas for
     δ-unfolding (`red_delta_const`), `Nat.rec` ι-reduction (`red_natRec_zero`,
     `red_natRec_succ`), and `Nat.casesOn` δ+β+ι reduction (`red_natCasesOn_zero`,
     `red_natCasesOn_succ`).
   - Relations between Src and kernel terms, heads, constants and values (`RelTerm`,
     `RelHead`, `RelConstStep`, `RelVal`, `RelSlot`, `RelSlots`). They have cases for variables,
     `Nat` literals, sorts and Π-types (unconstrained), λ-abstractions, `.strict`/`.byName`/
     irrelevant applications (argument related in every mode), both β-redex and ζ-reduct `let`
     forms, constants resolved as definitions, equations, csimp or allowlisted opaques (each
     with a user-supplied `Red` step), `Nat.zero`/`Nat.succ`, binary `Nat` primitives (with a
     user-supplied agreement premise: `IxCC.Src.PrimOp` has 14 binary operations; the premise
     holds for 11 and is false for `pow`, `beq` and `ble`, see `IxKernelBridge.Examples`), and
     `Nat.rec`/`Nat.casesOn`. The unary `pred` has no case.
   - Fuel-strong induction (`sim_all`: `eval_sim`, `apply_sim`, `force_sim`, `fire_sim`,
     `headValue_sim`, `evalConst_sim`) culminating in `srcRun_to_red`.

2. **Layer 2 (`red_to_denotes_nat`, `infer_red_to_denotes_nat`)**:
   - Composes `RulesInputs.ofSem mp φ`, `red_sound`, `infer_sound`, `Denotes_of_denoteMeta`,
     and `Denotes.natLit` to translate closed `Red env 0 e w` with `rawNatLit? w = some out`
     into set-theoretic denotation in `Model.ofEnvModelM mp`, given `denoteMeta` and `Graded`
     (or `Infer`) for `e`.

3. **Layer 3 (`srcRun_to_denotes_nat`, `srcRun_infer_to_denotes_nat`,
   `checkDecls_srcRun_denotes_nat`, `checkDecls_recheck_x86_denotes_nat`,
   `checkDecls_verifyBytes_immortal_denotes_nat`)**:
   - Conjunctions of Layers 1 and 2 with `Ix.Kernel.Cached.checkDecls_sound`,
     `IxCC.Recheck.sound_nat` and `IxCC.CompileClaim.verifyBytes_immortal_sound`, under the
     premises above. All of them use only the standard three axioms
     (`IxKernelBridge.Audit`).
-/

namespace IxKernelBridge

open Ix.Kernel Ix.Kernel.Rules Ix.Kernel.Model Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics

def subst (σ : List (Expr md)) (d : Nat) : Expr md → Expr md
  | .bvar i =>
    if i < d then .bvar i
    else match σ[i - d]? with
      | some v => v
      | none => .bvar (i - σ.length)
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (subst σ d f) (subst σ d a)
  | .lam ty body bi => .lam (subst σ d ty) (subst σ (d + 1) body) bi
  | .forallE ty body bi => .forallE (subst σ d ty) (subst σ (d + 1) body) bi
  | .letE ty val body lmeta =>
    .letE (subst σ d ty) (subst σ d val) (subst σ (d + 1) body) lmeta
  | .lit l => .lit l
  | .proj s i e => .proj s i (subst σ d e)

theorem subst_nil : ∀ (e : Expr md) (d : Nat), subst [] d e = e := by
  intro e
  induction e <;> intro d <;> simp [subst, *]

theorem subst_of_bvarBound_le (σ : List (Expr md)) :
    ∀ (e : Expr md) (d : Nat), e.bvarBound ≤ d → subst σ d e = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp [subst, show i < d by omega]
  | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro d _; rfl
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [subst, ihf d h.1, iha d h.2]
  | lam ty body bi iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [subst, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty body bi iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [subst, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty val body lmeta iht ihv ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [subst, iht d h.1.1, ihv d h.1.2, ihb (d + 1) (by omega)]
  | proj s i sub ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp [subst, ih d h]

theorem instantiate1_subst (σ : List (Expr md)) (a : Expr md)
    (hσ : ∀ x ∈ σ, x.bvarBound = 0) :
    ∀ (e : Expr md) (d : Nat),
      (subst σ (d + 1) e).instantiate1 a d = subst (a :: σ) d e := by
  intro e
  induction e with
  | bvar i =>
    intro d
    simp only [subst]
    by_cases hlt : i < d
    · have hlt1 : i < d + 1 := by omega
      simp [hlt, hlt1, show ¬(i = d) by omega, show ¬(i > d) by omega]
    · by_cases heq : i = d
      · subst heq
        simp
      · have hgt : ¬(i < d + 1) := by omega
        have hpos : i - d = (i - (d + 1)) + 1 := by omega
        simp only [hlt, hgt, ↓reduceIte, hpos, List.getElem?_cons_succ]
        cases hget : σ[i - (d + 1)]? with
        | some v =>
          have hv : v.bvarBound = 0 := hσ v (List.mem_of_getElem? hget)
          exact Expr.instantiate1_of_bvarBound_le v a d (by omega)
        | none =>
          have hge : σ.length ≤ i - (d + 1) := List.getElem?_eq_none_iff.mp hget
          have hne : ¬(i - σ.length = d) := by omega
          have hgt2 : i - σ.length > d := by omega
          simp [Expr.instantiate1, hne, hgt2]
          omega
  | fvar idx ty | sort u | const n us | lit l =>
    intro d
    simp [subst, Expr.instantiate1]
  | app f b ihf ihb =>
    intro d
    simp [subst, ihf d, ihb d]
  | lam ty body bi iht ihb =>
    intro d
    simp [subst, iht d, ihb (d + 1)]
  | forallE ty body bi iht ihb =>
    intro d
    simp [subst, iht d, ihb (d + 1)]
  | letE ty val body lmeta iht ihv ihb =>
    intro d
    simp [subst, Expr.instantiate1, iht d, ihv d, ihb (d + 1)]
  | proj s i sub ih =>
    intro d
    simp [subst, Expr.instantiate1, ih d]

theorem subst_instantiate1_closed (σ : List (Expr md)) (a : Expr md)
    (ha : a.bvarBound = 0) :
    ∀ (e : Expr md) (d : Nat),
      subst σ d (e.instantiate1 a d) = subst (a :: σ) d e := by
  intro e
  induction e with
  | bvar i =>
    intro d
    simp only [Expr.instantiate1, subst]
    by_cases hlt : i < d
    · simp [hlt, show ¬(i = d) by omega, show ¬(i > d) by omega, subst]
    · by_cases heq : i = d
      · subst heq
        simp [subst_of_bvarBound_le σ a i (by omega)]
      · have hgt : i > d := by omega
        have hlt2 : ¬(i - 1 < d) := by omega
        have hsub : i - d = (i - 1 - d) + 1 := by omega
        have hlen : i - 1 - σ.length = i - (σ.length + 1) := by omega
        simp [hlt, heq, hgt, subst, hlt2, hsub, hlen]
  | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro d; rfl
  | app f b ihf ihb =>
    intro d
    simp [Expr.instantiate1, subst, ihf d, ihb d]
  | lam ty body bi iht ihb =>
    intro d
    simp [Expr.instantiate1, subst, iht d, ihb (d + 1)]
  | forallE ty body bi iht ihb =>
    intro d
    simp [Expr.instantiate1, subst, iht d, ihb (d + 1)]
  | letE ty val body lmeta iht ihv ihb =>
    intro d
    simp [Expr.instantiate1, subst, iht d, ihv d, ihb (d + 1)]
  | proj s i sub ih =>
    intro d
    simp [Expr.instantiate1, subst, ih d]

theorem bvarBound_subst_le {σ : List (Expr md)}
    (hσ : ∀ x ∈ σ, x.bvarBound = 0) :
    ∀ (e : Expr md) (d : Nat),
      e.bvarBound ≤ d + σ.length → (subst σ d e).bvarBound ≤ d := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [subst]
    split
    · simp [Expr.bvarBound]; omega
    · cases hget : σ[i - d]? with
      | some v =>
        dsimp only
        have hvb := hσ v (List.mem_of_getElem? hget)
        omega
      | none =>
        dsimp only [Expr.bvarBound]
        have hge := List.getElem?_eq_none_iff.mp hget
        omega
  | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro d _
    simp [subst, Expr.bvarBound]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [subst, Expr.bvarBound, Nat.max_le]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty body bi iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [subst, Expr.bvarBound, Nat.max_le]
    refine ⟨iht d h.1, ?_⟩
    have := ihb (d + 1) (by omega)
    omega
  | forallE ty body bi iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [subst, Expr.bvarBound, Nat.max_le]
    refine ⟨iht d h.1, ?_⟩
    have := ihb (d + 1) (by omega)
    omega
  | letE ty val body lmeta iht ihv ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [subst, Expr.bvarBound, Nat.max_le]
    refine ⟨⟨iht d h.1.1, ihv d h.1.2⟩, ?_⟩
    have := ihb (d + 1) (by omega)
    omega
  | proj s i sub ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [subst, Expr.bvarBound]
    exact ih d h

theorem bvarBound_instantiate1_le {a : Expr md} (ha : a.bvarBound = 0) :
    ∀ (e : Expr md) (c d : Nat), e.bvarBound ≤ c + d + 1 → (e.instantiate1 a c).bvarBound ≤ c + d := by
  intro e
  induction e with
  | bvar i =>
    intro c d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1]
    split
    · omega
    · split
      · simp [Expr.bvarBound]; omega
      · simp [Expr.bvarBound]; omega
  | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro c d _; simp [Expr.instantiate1, Expr.bvarBound]
  | app f b ihf ihb =>
    intro c d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.instantiate1, Expr.bvarBound, Nat.max_le]
    exact ⟨ihf c d h.1, ihb c d h.2⟩
  | lam ty body bi iht ihb =>
    intro c d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.instantiate1, Expr.bvarBound, Nat.max_le]
    refine ⟨iht c d h.1, ?_⟩
    have := ihb (c + 1) d (by omega)
    omega
  | forallE ty body bi iht ihb =>
    intro c d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.instantiate1, Expr.bvarBound, Nat.max_le]
    refine ⟨iht c d h.1, ?_⟩
    have := ihb (c + 1) d (by omega)
    omega
  | letE ty val body lmeta iht ihv ihb =>
    intro c d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.instantiate1, Expr.bvarBound, Nat.max_le]
    refine ⟨⟨iht c d h.1.1, ihv c d h.1.2⟩, ?_⟩
    have := ihb (c + 1) d (by omega)
    omega
  | proj s i sub ih =>
    intro c d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1, Expr.bvarBound]
    exact ih c d h

theorem mkAppN_append : ∀ (es1 es2 : List (Expr md)) (f : Expr md),
    Expr.mkAppN f (es1 ++ es2) = Expr.mkAppN (Expr.mkAppN f es1) es2
  | [], es2, f => rfl
  | a :: as, es2, f => by
    simp only [List.cons_append, Expr.mkAppN]
    exact mkAppN_append as es2 (.app f a)

theorem red_mkAppN_fn {env : Env md} {d : Nat} :
    ∀ (es : List (Expr md)) {f f' : Expr md},
      Red env d f f' → Red env d (Expr.mkAppN f es) (Expr.mkAppN f' es)
  | [], _, _, h => h
  | _ :: as, _, _, h => red_mkAppN_fn as (Red.appFn h)

theorem red_betaGate_subst {env : Env md} {d : Nat}
    {σ : List (Expr md)} {ty body a : Expr md} {mb : BinderMeta}
    (hσ : ∀ x ∈ σ, x.bvarBound = 0)
    (hmb : mb.pw.isNever = true) :
    Red env d (.app (subst σ 0 (.lam ty body mb)) a) (subst (a :: σ) 0 body) := by
  simpa [subst, instantiate1_subst σ a hσ body 0] using
    (Red.betaGate (env := env) (d := d) (ty := subst σ 0 ty) (body := subst σ 1 body) (a := a) hmb)

def natBasisStored (env : Env md) : Bool :=
  env.find? natName == some natA &&
  env.find? natZeroName == some natZeroA &&
  env.find? natSuccName == some natSuccA &&
  env.find? natRecName == some natRecA

theorem natLitSupported_of_natBasisStored {env : Env md}
    (h : natBasisStored env = true) : natLitSupported env = true := by
  simp only [natBasisStored, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, _⟩
  simp [natLitSupported, h1, h2, h3, natIndOk, natZeroOk, natSuccOk, natA, natZeroA, natSuccA]

def natRecRules : List (RecRule md) :=
  match (natRecA : ConstantInfo md) with
  | .recInfo _ _ _ rules => rules
  | _ => []

def natRecZeroRule : RecRule md := (natRecRules (md := md)).getD 0 default
def natRecSuccRule : RecRule md := (natRecRules (md := md)).getD 1 default

theorem red_delta_const {env : Env md} {d : Nat} {c : Key md} {us : List Level}
    {cv : ConstantVal md} {value : Expr md} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv value hint))
    (hlen : us.length = cv.levelParams.length) :
    Red env d (.const c us) (value.instantiateLevelParams cv.levelParams us) := by
  refine Red.delta ?_
  simp [unfoldDefinition, Expr.getAppFn, Expr.getAppArgs, Expr.mkAppN, hf, hlen]

theorem red_natRec_zero {env : Env md} {d : Nat} {u' : Level}
    {motive z s major w : Expr md}
    (hbasis : natBasisStored env = true)
    (hz : z.bvarBound = 0)
    (hmaj : Red env d major w)
    (hw : rawNatLit? w = some 0) :
    Red env d
      (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) major)
      z := by
  have hsup := natLitSupported_of_natBasisStored hbasis
  have hmaj0 : Red env d major (.const natZeroName []) := by
    cases w with
    | lit l =>
      cases l with
      | natVal k =>
        simp only [rawNatLit?, Option.some.injEq] at hw
        subst hw
        exact Red.trans hmaj (Red.natLit hsup)
      | strVal _ => simp [rawNatLit?] at hw
    | const c us =>
      cases us with
      | nil =>
        simp only [rawNatLit?] at hw
        split at hw
        · rename_i hc
          subst hc
          exact hmaj
        · cases hw
      | cons _ _ => simp [rawNatLit?] at hw
    | _ => simp [rawNatLit?] at hw
  simp only [natBasisStored, Bool.and_eq_true, beq_iff_eq] at hbasis
  rcases hbasis with ⟨⟨⟨hNat, hZero⟩, hSucc⟩, hRec⟩
  have hiota : Red env d
      (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) major)
      (Expr.mkAppN (natRecZeroRule.rhs.instantiateLevelParams [BasisDSL.uN] [.succ u'])
        [motive, z, s]) := by
    refine Red.iota (c := natRecName) (us := [.succ u'])
      (mI := 3) (rP := 3) (major := .const natZeroName [])
      (cj := natZeroName) (usj := []) (rl := natRecZeroRule)
      (residual := .const natName [])
      rfl hRec rfl rfl hmaj0 rfl hZero rfl rfl nofun rfl
      (fun h => by cases h) ?_ .nil (fun h => absurd rfl h) (fun h => absurd rfl h)
    refine .skip rfl rfl (.skip rfl rfl (.skip rfl rfl (.skip rfl rfl .nil)))
  have hbeta1 : Red env d
      (Expr.mkAppN (natRecZeroRule.rhs.instantiateLevelParams [BasisDSL.uN] [.succ u'])
        [motive, z, s])
      z := by
    refine Red.trans (Red.appFn (Red.appFn (Red.betaGate rfl))) ?_
    refine Red.trans (Red.appFn (Red.betaGate rfl)) ?_
    refine Red.trans (Red.betaGate rfl) ?_
    change Red env d (z.instantiate1 s 0) z
    rw [Expr.instantiate1_of_bvarBound_le z s 0 (by omega)]
    exact Red.refl
  exact Red.trans hiota hbeta1

theorem red_natRec_succ {env : Env md} {d : Nat} {u' : Level}
    {motive z s major w : Expr md} {m : Nat}
    (hbasis : natBasisStored env = true)
    (hmot : motive.bvarBound = 0)
    (hz : z.bvarBound = 0)
    (hs : s.bvarBound = 0)
    (hmaj : Red env d major w)
    (hw : rawNatLit? w = some (m + 1)) :
    Red env d
      (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) major)
      (.app (.app s (.lit (.natVal m)))
        (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) (.lit (.natVal m)))) := by
  have hsup := natLitSupported_of_natBasisStored hbasis
  have hmajS : Red env d major (.app (.const natSuccName []) (.lit (.natVal m))) := by
    cases w with
    | lit l =>
      cases l with
      | natVal k =>
        simp only [rawNatLit?, Option.some.injEq] at hw
        subst hw
        exact Red.trans hmaj (Red.natLit hsup)
      | strVal _ => simp [rawNatLit?] at hw
    | const c us =>
      cases us with
      | nil =>
        simp only [rawNatLit?] at hw
        split at hw <;> cases hw
      | cons _ _ => simp [rawNatLit?] at hw
    | _ => simp [rawNatLit?] at hw
  simp only [natBasisStored, Bool.and_eq_true, beq_iff_eq] at hbasis
  rcases hbasis with ⟨⟨⟨hNat, hZero⟩, hSucc⟩, hRec⟩
  have hiota : Red env d
      (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) major)
      (Expr.mkAppN (natRecSuccRule.rhs.instantiateLevelParams [BasisDSL.uN] [.succ u'])
        [motive, z, s, .lit (.natVal m)]) := by
    refine Red.iota (c := natRecName) (us := [.succ u'])
      (mI := 3) (rP := 3) (major := .app (.const natSuccName []) (.lit (.natVal m)))
      (cj := natSuccName) (usj := []) (rl := natRecSuccRule)
      (residual := .const natName [])
      rfl hRec rfl rfl hmajS rfl hSucc rfl rfl nofun rfl
      (fun h => by cases h) ?_ (.skip rfl rfl .nil)
      (fun h => absurd rfl h) (fun h => absurd rfl h)
    refine .skip rfl rfl (.skip rfl rfl (.skip rfl rfl (.skip rfl rfl .nil)))
  have hbeta1 : Red env d
      (Expr.mkAppN (natRecSuccRule.rhs.instantiateLevelParams [BasisDSL.uN] [.succ u'])
        [motive, z, s, .lit (.natVal m)])
      (.app (.app s (.lit (.natVal m)))
        (.app (.app (.app (.app (.const natRecName [.succ u']) motive) z) s) (.lit (.natVal m)))) := by
    refine Red.trans (Red.appFn (Red.appFn (Red.appFn (Red.betaGate rfl)))) ?_
    refine Red.trans (Red.appFn (Red.appFn (Red.betaGate rfl))) ?_
    refine Red.trans (Red.appFn (Red.betaGate rfl)) ?_
    refine Red.trans (Red.betaGate rfl) ?_
    change Red env d
      (let e0 : Expr md :=
         .app (.app (.bvar 1) (.bvar 0))
           (.app (.app (.app (.app (.const natRecName [.succ u']) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))
       (((e0.instantiate1 motive 3).instantiate1 z 2).instantiate1 s 1).instantiate1 (.lit (.natVal m)) 0)
      _
    simp only [Expr.instantiate1, ↓reduceIte,
      show ¬(1 = 3) by decide, show ¬(1 > 3) by decide,
      show ¬(0 = 3) by decide, show ¬(0 > 3) by decide,
      show ¬(2 = 3) by decide, show ¬(2 > 3) by decide,
      show ¬(1 = 2) by decide, show ¬(1 > 2) by decide,
      show ¬(0 = 2) by decide, show ¬(0 > 2) by decide,
      show ¬(0 = 1) by decide, show ¬(0 > 1) by decide,
      Expr.instantiate1_of_bvarBound_le motive z 2 (by omega),
      Expr.instantiate1_of_bvarBound_le motive s 1 (by omega),
      Expr.instantiate1_of_bvarBound_le motive (.lit (.natVal m)) 0 (by omega),
      Expr.instantiate1_of_bvarBound_le z s 1 (by omega),
      Expr.instantiate1_of_bvarBound_le z (.lit (.natVal m)) 0 (by omega),
      Expr.instantiate1_of_bvarBound_le s (.lit (.natVal m)) 0 (by omega)]
    exact Red.refl
  exact Red.trans hiota hbeta1

def natCasesOnValue (uParam : LevelParam) (motTy tTy zTy sTy mTy ihTy : Expr md)
    (b0 b1 b2 b3 b4 b5 : BinderMeta) : Expr md :=
  .lam motTy
    (.lam tTy
      (.lam zTy
        (.lam sTy
          (.app (.app (.app (.app (.const natRecName [.param uParam]) (.bvar 3)) (.bvar 1))
            (.lam mTy (.lam ihTy (.app (.bvar 2) (.bvar 1)) b5) b4))
            (.bvar 2))
          b3)
        b2)
      b1)
    b0

theorem red_natCasesOn_zero {env : Env md} {d : Nat} {casesKey : Key md} {u' : Level}
    {cv : ConstantVal md} {hint : ReducibilityHint}
    {uParam : LevelParam} {motTy tTy zTy sTy mTy ihTy : Expr md}
    {b0 b1 b2 b3 b4 b5 : BinderMeta}
    {motive major z s w : Expr md}
    (hbasis : natBasisStored env = true)
    (hfind : env.find? casesKey = some (.defnInfo cv
      (natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5) hint))
    (hlp : cv.levelParams = [uParam])
    (hb0 : (Level.substPW [uParam] [.succ u'] b0.pw).isNever = true)
    (hb1 : (Level.substPW [uParam] [.succ u'] b1.pw).isNever = true)
    (hb2 : (Level.substPW [uParam] [.succ u'] b2.pw).isNever = true)
    (hb3 : (Level.substPW [uParam] [.succ u'] b3.pw).isNever = true)
    (hmot : motive.bvarBound = 0)
    (hmajB : major.bvarBound = 0)
    (hz : z.bvarBound = 0)
    (hmaj : Red env d major w)
    (hw : rawNatLit? w = some 0) :
    Red env d
      (.app (.app (.app (.app (.const casesKey [.succ u']) motive) major) z) s)
      z := by
  have hdelta : Red env d (.const casesKey [.succ u'])
      ((natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5).instantiateLevelParams
        cv.levelParams [.succ u']) :=
    red_delta_const hfind (by simp [hlp])
  rw [hlp, ← subst_nil ((natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5).instantiateLevelParams [uParam] [.succ u']) 0] at hdelta
  refine Red.trans (Red.appFn (Red.appFn (Red.appFn (Red.appFn hdelta)))) ?_
  dsimp only [natCasesOnValue, Expr.instantiateLevelParams, List.map, Level.subst, Level.subst.go,
    ↓reduceIte]
  have h0 : ∀ x ∈ ([] : List (Expr md)), x.bvarBound = 0 := by intro _ h; cases h
  have h1 : ∀ x ∈ [motive], x.bvarBound = 0 := by simp [hmot]
  have h2 : ∀ x ∈ [major, motive], x.bvarBound = 0 := by simp [hmajB, hmot]
  have h3 : ∀ x ∈ [z, major, motive], x.bvarBound = 0 := by simp [hz, hmajB, hmot]
  refine Red.trans (Red.appFn (Red.appFn (Red.appFn (red_betaGate_subst h0 hb0)))) ?_
  refine Red.trans (Red.appFn (Red.appFn (red_betaGate_subst h1 hb1))) ?_
  refine Red.trans (Red.appFn (red_betaGate_subst h2 hb2)) ?_
  refine Red.trans (red_betaGate_subst h3 hb3) ?_
  simpa [subst] using red_natRec_zero hbasis hz hmaj hw

theorem red_natCasesOn_succ {env : Env md} {d : Nat} {casesKey : Key md} {u' : Level}
    {cv : ConstantVal md} {hint : ReducibilityHint}
    {uParam : LevelParam} {motTy tTy zTy sTy mTy ihTy : Expr md}
    {b0 b1 b2 b3 b4 b5 : BinderMeta}
    {motive major z s w : Expr md} {m : Nat}
    (hbasis : natBasisStored env = true)
    (hfind : env.find? casesKey = some (.defnInfo cv
      (natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5) hint))
    (hlp : cv.levelParams = [uParam])
    (hb0 : (Level.substPW [uParam] [.succ u'] b0.pw).isNever = true)
    (hb1 : (Level.substPW [uParam] [.succ u'] b1.pw).isNever = true)
    (hb2 : (Level.substPW [uParam] [.succ u'] b2.pw).isNever = true)
    (hb3 : (Level.substPW [uParam] [.succ u'] b3.pw).isNever = true)
    (hb4 : (Level.substPW [uParam] [.succ u'] b4.pw).isNever = true)
    (hb5 : (Level.substPW [uParam] [.succ u'] b5.pw).isNever = true)
    (hmTy : (mTy.instantiateLevelParams [uParam] [.succ u']).bvarBound ≤ 4)
    (hihTy : (ihTy.instantiateLevelParams [uParam] [.succ u']).bvarBound ≤ 5)
    (hmot : motive.bvarBound = 0)
    (hmajB : major.bvarBound = 0)
    (hz : z.bvarBound = 0)
    (hs : s.bvarBound = 0)
    (hmaj : Red env d major w)
    (hw : rawNatLit? w = some (m + 1)) :
    Red env d
      (.app (.app (.app (.app (.const casesKey [.succ u']) motive) major) z) s)
      (.app s (.lit (.natVal m))) := by
  have hdelta : Red env d (.const casesKey [.succ u'])
      ((natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5).instantiateLevelParams
        cv.levelParams [.succ u']) :=
    red_delta_const hfind (by simp [hlp])
  rw [hlp, ← subst_nil ((natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy b0 b1 b2 b3 b4 b5).instantiateLevelParams [uParam] [.succ u']) 0] at hdelta
  refine Red.trans (Red.appFn (Red.appFn (Red.appFn (Red.appFn hdelta)))) ?_
  dsimp only [natCasesOnValue, Expr.instantiateLevelParams, List.map, Level.subst, Level.subst.go,
    ↓reduceIte]
  have h0 : ∀ x ∈ ([] : List (Expr md)), x.bvarBound = 0 := by intro _ h; cases h
  have h1 : ∀ x ∈ [motive], x.bvarBound = 0 := by simp [hmot]
  have h2 : ∀ x ∈ [major, motive], x.bvarBound = 0 := by simp [hmajB, hmot]
  have h3 : ∀ x ∈ [z, major, motive], x.bvarBound = 0 := by simp [hz, hmajB, hmot]
  have h4 : ∀ x ∈ [s, z, major, motive], x.bvarBound = 0 := by simp [hs, hz, hmajB, hmot]
  refine Red.trans (Red.appFn (Red.appFn (Red.appFn (red_betaGate_subst h0 hb0)))) ?_
  refine Red.trans (Red.appFn (Red.appFn (red_betaGate_subst h1 hb1))) ?_
  refine Red.trans (Red.appFn (red_betaGate_subst h2 hb2)) ?_
  refine Red.trans (red_betaGate_subst h3 hb3) ?_
  have hwB : (subst [s, z, major, motive] 0
      (.lam (mTy.instantiateLevelParams [uParam] [.succ u'])
        (.lam (ihTy.instantiateLevelParams [uParam] [.succ u']) (.app (.bvar 2) (.bvar 1))
          { b5 with pw := Level.substPW [uParam] [.succ u'] b5.pw })
        { b4 with pw := Level.substPW [uParam] [.succ u'] b4.pw })).bvarBound = 0 := by
    have := bvarBound_subst_le h4
      (.lam (mTy.instantiateLevelParams [uParam] [.succ u'])
        (.lam (ihTy.instantiateLevelParams [uParam] [.succ u']) (.app (.bvar 2) (.bvar 1))
          { b5 with pw := Level.substPW [uParam] [.succ u'] b5.pw })
        { b4 with pw := Level.substPW [uParam] [.succ u'] b4.pw }) 0
    simp only [Expr.bvarBound, List.length_cons, List.length_nil, Nat.zero_add] at this
    omega
  refine Red.trans (by simpa [subst] using red_natRec_succ hbasis hmot hz hwB hmaj hw) ?_
  refine Red.trans (Red.appFn (Red.betaGate hb4)) ?_
  dsimp only [Expr.instantiate1]
  refine Red.trans (Red.betaGate hb5) ?_
  dsimp only [Expr.instantiate1]
  simp only [↓reduceIte,
    Expr.instantiate1_of_bvarBound_le s (.lit (.natVal m)) 1 (by omega),
    Expr.instantiate1_of_bvarBound_le s _ 0 (by omega)]
  exact Red.refl

inductive RelTerm (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop)
    (ls : IxCC.Src.Levels) : Nat → IxCC.Src.Term → Expr md → Prop where
  | var {d i : Nat} :
      i < d →
      RelTerm p env constSpec ls d (.var i) (.bvar i)
  | natLit {d n : Nat} :
      RelTerm p env constSpec ls d (.natLit n) (.lit (.natVal n))
  | sort {d : Nat} {u : IxCC.Ixon.Univ} {kt : Expr md} :
      kt.bvarBound ≤ d →
      RelTerm p env constSpec ls d (.sort u) kt
  | pi {d : Nat} {b : IxCC.Src.Binder} {rc : IxCC.Ixon.V3.ValueContract}
      {dom body : IxCC.Src.Term} {kt : Expr md} :
      kt.bvarBound ≤ d →
      RelTerm p env constSpec ls d (.pi b rc dom body) kt
  | lam {d : Nat} {b : IxCC.Src.Binder} {dom body : IxCC.Src.Term}
      {kty kbody : Expr md} {mb : BinderMeta} :
      kty.bvarBound ≤ d →
      (b.propWhen.allowsBeta ls = true → mb.pw.isNever = true) →
      RelTerm p env constSpec ls (d + 1) body kbody →
      RelTerm p env constSpec ls d (.lam b dom body) (.lam kty kbody mb)
  | app {d : Nat} {f a : IxCC.Src.Term} {m : IxCC.Src.Mode}
      {r : IxCC.Src.Rel} {kf ka : Expr md} :
      RelTerm p env constSpec ls d f kf →
      RelTerm p env constSpec ls d a ka →
      RelTerm p env constSpec ls d (.app f a m r) (.app kf ka)
  | letBeta {d : Nat} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v body : IxCC.Src.Term} {kty kv kbody : Expr md} {mb : BinderMeta} :
      mb.pw.isNever = true →
      kty.bvarBound ≤ d →
      RelTerm p env constSpec ls d v kv →
      RelTerm p env constSpec ls (d + 1) body kbody →
      RelTerm p env constSpec ls d (.letE c r ty v body) (.app (.lam kty kbody mb) kv)
  | letZeta {d : Nat} {c : IxCC.Ixon.V3.LetContract} {r : IxCC.Src.Rel}
      {ty v body : IxCC.Src.Term} {kv kbody : Expr md} :
      kv.bvarBound = 0 →
      RelTerm p env constSpec ls d v kv →
      RelTerm p env constSpec ls (d + 1) body kbody →
      RelTerm p env constSpec ls d (.letE c r ty v body) (kbody.instantiate1 kv 0)
  | const {d : Nat} {c : IxCC.Src.CId} {us : List IxCC.Ixon.Univ}
      {kt : Expr md} :
      kt.bvarBound = 0 →
      constSpec (us.map (IxCC.Src.evalUniv ls)) c kt →
      RelTerm p env constSpec ls d (.const c us) kt

theorem RelTerm.bvarBound_le {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {ls : IxCC.Src.Levels} {d : Nat} {t : IxCC.Src.Term} {kt : Expr md}
    (ht : RelTerm p env constSpec ls d t kt) : kt.bvarBound ≤ d := by
  induction ht with
  | var h => simp [Expr.bvarBound]; omega
  | natLit => simp [Expr.bvarBound]
  | sort h => exact h
  | pi h => exact h
  | lam hty _ _ ih =>
    simp only [Expr.bvarBound, Nat.max_le]
    exact ⟨hty, by omega⟩
  | app _ _ ihf iha =>
    simp only [Expr.bvarBound, Nat.max_le]
    exact ⟨ihf, iha⟩
  | letBeta _ hty _ _ ihv ihb =>
    simp only [Expr.bvarBound, Nat.max_le]
    exact ⟨⟨hty, by omega⟩, ihv⟩
  | letZeta hkv _ _ _ ihb =>
    simpa using bvarBound_instantiate1_le hkv _ 0 _ (by simpa using ihb)
  | const h _ => omega

inductive RelHead (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) :
    IxCC.Src.Head → IxCC.Src.Levels → Expr md → Prop where
  | natZero {c : IxCC.Src.CId} {ls : IxCC.Src.Levels}
      {b1 : Bool} {lvls ind cidx : Nat} {cty : IxCC.Src.Term} :
      p.decl? c = some (.ctor b1 lvls ind cidx 0 0 cty) →
      some c = p.known.natZero →
      RelHead p env constSpec (.ctor c) ls (.const natZeroName [])
  | natSucc {c : IxCC.Src.CId} {ls : IxCC.Src.Levels}
      {b1 : Bool} {lvls ind cidx : Nat} {cty : IxCC.Src.Term} :
      p.decl? c = some (.ctor b1 lvls ind cidx 0 1 cty) →
      some c = p.known.natSucc →
      some c ≠ p.known.natZero →
      RelHead p env constSpec (.ctor c) ls (.const natSuccName [])
  | primBinNat {op : IxCC.Src.PrimOp} {ls : IxCC.Src.Levels} {opKey : Key md} :
      op.arity = 2 →
      opKey ∈ natBinOpNames →
      natOpStored env opKey = true →
      (∀ n0 n1 res, op.evalLits [n0, n1] = some res →
        ∃ out, res = .nat out ∧ natOpResult opKey n0 n1 = some (.lit (.natVal out))) →
      RelHead p env constSpec (.prim op) ls (.const opKey [])
  | natRec {r : IxCC.Src.CId} {ls : IxCC.Src.Levels} {u' : Level}
      {b1 b2 : Bool} {rl ind : Nat} {r0 r1 : IxCC.Src.Rule} {rty b0 b1t : IxCC.Src.Term} :
      p.decl? r = some (.recr b1 b2 rl 0 1 2 0 ind [r0, r1] rty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
      some ind = p.known.nat →
      IxCC.Src.peelLams 3 r0.rhs = some b0 →
      RelTerm p env constSpec ls 3 b0 (.bvar 1) →
      IxCC.Src.peelLams 4 r1.rhs = some b1t →
      RelTerm p env constSpec ls 4 b1t
        (.app (.app (.bvar 1) (.bvar 0))
          (.app (.app (.app (.app (.const natRecName [.succ u']) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))) →
      RelHead p env constSpec (.recr r) ls (.const natRecName [.succ u'])
  | natCases {c r : IxCC.Src.CId} {ls : IxCC.Src.Levels} {casesKey : Key md} {u' : Level}
      {b1 b2 : Bool} {rl ind : Nat} {rules : List IxCC.Src.Rule} {rty : IxCC.Src.Term}
      {cv : ConstantVal md} {hint : ReducibilityHint}
      {uParam : LevelParam} {motTy tTy zTy sTy mTy ihTy : Expr md}
      {mb0 mb1 mb2 mb3 mb4 mb5 : BinderMeta} :
      p.table.resolveOf c = some (.case r) →
      p.decl? r = some (.recr b1 b2 rl 0 1 2 0 ind rules rty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
      some ind = p.known.nat →
      env.find? casesKey = some (.defnInfo cv
        (natCasesOnValue uParam motTy tTy zTy sTy mTy ihTy mb0 mb1 mb2 mb3 mb4 mb5) hint) →
      cv.levelParams = [uParam] →
      (Level.substPW [uParam] [.succ u'] mb0.pw).isNever = true →
      (Level.substPW [uParam] [.succ u'] mb1.pw).isNever = true →
      (Level.substPW [uParam] [.succ u'] mb2.pw).isNever = true →
      (Level.substPW [uParam] [.succ u'] mb3.pw).isNever = true →
      (Level.substPW [uParam] [.succ u'] mb4.pw).isNever = true →
      (Level.substPW [uParam] [.succ u'] mb5.pw).isNever = true →
      (mTy.instantiateLevelParams [uParam] [.succ u']).bvarBound ≤ 4 →
      (ihTy.instantiateLevelParams [uParam] [.succ u']).bvarBound ≤ 5 →
      RelHead p env constSpec (.cases c) ls (.const casesKey [.succ u'])

theorem RelHead.bvarBound_zero {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {h : IxCC.Src.Head} {ls : IxCC.Src.Levels} {e : Expr md}
    (hr : RelHead p env constSpec h ls e) : e.bvarBound = 0 := by
  cases hr <;> rfl

inductive RelConstStep (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop)
    (ls : IxCC.Src.Levels) (c : IxCC.Src.CId) (e : Expr md) : Prop where
  | prim {op : IxCC.Src.PrimOp} :
      p.table.resolveOf c = some (.prim op) →
      RelHead p env constSpec (.prim op) ls e →
      RelConstStep p env constSpec ls c e
  | csimp {g thm : IxCC.Src.CId} {vs : List IxCC.Ixon.Univ} {kg : Expr md} :
      p.table.resolveOf c = some (.csimp g vs thm) →
      Red env 0 e kg →
      RelTerm p env constSpec ls 0 (.const g vs) kg →
      RelConstStep p env constSpec ls c e
  | eqn {thm : IxCC.Src.CId} {body : IxCC.Src.Term} {kbody : Expr md} :
      p.table.resolveOf c = some (.eqn thm body) →
      Red env 0 e kbody →
      RelTerm p env constSpec ls 0 body kbody →
      RelConstStep p env constSpec ls c e
  | cases {r : IxCC.Src.CId} :
      p.table.resolveOf c = some (.case r) →
      RelHead p env constSpec (.cases c) ls e →
      RelConstStep p env constSpec ls c e
  | ctor {b1 : Bool} {lvls ind cidx np nf : Nat} {cty : IxCC.Src.Term} :
      p.table.resolveOf c = none →
      p.decl? c = some (.ctor b1 lvls ind cidx np nf cty) →
      RelHead p env constSpec (.ctor c) ls e →
      RelConstStep p env constSpec ls c e
  | recr {b1 b2 : Bool} {rl np nmot nmin ni ind : Nat}
      {rules : List IxCC.Src.Rule} {rty : IxCC.Src.Term} :
      p.table.resolveOf c = none →
      p.decl? c = some (.recr b1 b2 rl np nmot nmin ni ind rules rty) →
      RelHead p env constSpec (.recr c) ls e →
      RelConstStep p env constSpec ls c e
  | defn {lvls : Nat} {ty body : IxCC.Src.Term} {kbody : Expr md} :
      p.table.resolveOf c = none →
      p.decl? c = some (.defn .defn .safe lvls ty body) →
      Red env 0 e kbody →
      RelTerm p env constSpec ls 0 body kbody →
      RelConstStep p env constSpec ls c e
  | opaq {lvls : Nat} {ty body : IxCC.Src.Term} {kbody : Expr md} :
      p.table.resolveOf c = none →
      p.decl? c = some (.defn .opaq .safe lvls ty body) →
      p.table.isOpaqueByValue c = true →
      Red env 0 e kbody →
      RelTerm p env constSpec ls 0 body kbody →
      RelConstStep p env constSpec ls c e

mutual

inductive RelVal (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) :
    IxCC.Src.Value → Expr md → Prop where
  | lit {n : Nat} {w : Expr md} :
      w.bvarBound = 0 →
      rawNatLit? w = some n →
      RelVal p env constSpec (.lit n) w
  | irr {t : Option IxCC.Src.Term} {ρ : List IxCC.Src.Slot} {ls : IxCC.Src.Levels} {w : Expr md} :
      w.bvarBound = 0 →
      RelVal p env constSpec (.irr t ρ ls) w
  | clo {b : IxCC.Src.Binder} {dom body : IxCC.Src.Term} {ρ : List IxCC.Src.Slot}
      {ls : IxCC.Src.Levels} {σ : List (Expr md)} {kty kbody : Expr md} {mb : BinderMeta} :
      (subst σ 0 (.lam kty kbody mb)).bvarBound = 0 →
      kty.bvarBound ≤ σ.length →
      (b.propWhen.allowsBeta ls = true → mb.pw.isNever = true) →
      RelSlots p env constSpec ρ σ →
      RelTerm p env constSpec ls (σ.length + 1) body kbody →
      RelVal p env constSpec (.clo b dom body ρ ls) (subst σ 0 (.lam kty kbody mb))
  | pap {h : IxCC.Src.Head} {ls : IxCC.Src.Levels} {args : List IxCC.Src.Slot}
      {eHead : Expr md} {eArgs : List (Expr md)} :
      (Expr.mkAppN eHead eArgs).bvarBound = 0 →
      RelHead p env constSpec h ls eHead →
      RelSlots p env constSpec args eArgs →
      RelVal p env constSpec (.pap h ls args) (Expr.mkAppN eHead eArgs)

inductive RelSlot (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) :
    IxCC.Src.Slot → Expr md → Prop where
  | val {v : IxCC.Src.Value} {e w : Expr md} :
      e.bvarBound = 0 →
      Red env 0 e w →
      RelVal p env constSpec v w →
      RelSlot p env constSpec (.val v) e
  | name {t : IxCC.Src.Term} {ρ : List IxCC.Src.Slot} {ls : IxCC.Src.Levels}
      {σ : List (Expr md)} {kt : Expr md} :
      (subst σ 0 kt).bvarBound = 0 →
      RelSlots p env constSpec ρ σ →
      RelTerm p env constSpec ls σ.length t kt →
      RelSlot p env constSpec (.name t ρ ls) (subst σ 0 kt)

inductive RelSlots (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) :
    List IxCC.Src.Slot → List (Expr md) → Prop where
  | nil : RelSlots p env constSpec [] []
  | cons {s : IxCC.Src.Slot} {e : Expr md} {ss : List IxCC.Src.Slot} {es : List (Expr md)} :
      RelSlot p env constSpec s e →
      RelSlots p env constSpec ss es →
      RelSlots p env constSpec (s :: ss) (e :: es)

end

theorem RelVal.bvarBound_zero {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {v : IxCC.Src.Value} {w : Expr md}
    (h : RelVal p env constSpec v w) : w.bvarBound = 0 := by
  cases h <;> assumption

theorem RelSlot.bvarBound_zero {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {s : IxCC.Src.Slot} {e : Expr md}
    (h : RelSlot p env constSpec s e) : e.bvarBound = 0 := by
  cases h <;> assumption

theorem RelSlots.length_eq {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} :
    ∀ {ρ : List IxCC.Src.Slot} {σ : List (Expr md)},
      RelSlots p env constSpec ρ σ → ρ.length = σ.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hrest => by simp [RelSlots.length_eq hrest]

theorem RelSlots.bvarBound_zero {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} :
    ∀ {ρ : List IxCC.Src.Slot} {σ : List (Expr md)},
      RelSlots p env constSpec ρ σ → ∀ x ∈ σ, x.bvarBound = 0
  | [], [], .nil => by intro _ hx; cases hx
  | _ :: _, _ :: _, .cons hs hrest => by
    intro x hx
    cases hx with
    | head => exact hs.bvarBound_zero
    | tail _ hmem => exact RelSlots.bvarBound_zero hrest x hmem

theorem RelSlots.getElem?_some {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} :
    ∀ {ρ : List IxCC.Src.Slot} {σ : List (Expr md)},
      RelSlots p env constSpec ρ σ →
      ∀ (i : Nat) (s : IxCC.Src.Slot),
        ρ[i]? = some s → ∃ e, σ[i]? = some e ∧ RelSlot p env constSpec s e
  | [], [], .nil => by intro i s hs; cases hs
  | _ :: _, _ :: _, .cons hs hrest => by
    intro i s hget
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      exact ⟨_, rfl, hs⟩
    | succ i' =>
      simp only [List.getElem?_cons_succ] at hget
      exact RelSlots.getElem?_some hrest i' s hget

theorem RelSlots.append {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} :
    ∀ {ρ1 ρ2 : List IxCC.Src.Slot} {σ1 σ2 : List (Expr md)},
      RelSlots p env constSpec ρ1 σ1 →
      RelSlots p env constSpec ρ2 σ2 →
      RelSlots p env constSpec (ρ1 ++ ρ2) (σ1 ++ σ2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, _, _ :: _, _, .cons hs hrest, h2 => .cons hs (RelSlots.append hrest h2)

theorem RelSlots.len0 {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {args : List IxCC.Src.Slot} {eArgs : List (Expr md)}
    (h : RelSlots p env constSpec args eArgs) (hlen : args.length = 0) :
    args = [] ∧ eArgs = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ => simp at hlen

theorem RelSlots.len1 {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {args : List IxCC.Src.Slot} {eArgs : List (Expr md)}
    (h : RelSlots p env constSpec args eArgs) (hlen : args.length = 1) :
    ∃ s0 e0, args = [s0] ∧ eArgs = [e0] ∧ RelSlot p env constSpec s0 e0 := by
  cases h with
  | nil => simp at hlen
  | cons hs0 hrest =>
    cases hrest with
    | nil => exact ⟨_, _, rfl, rfl, hs0⟩
    | cons _ _ => simp at hlen

theorem RelSlots.len2 {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {args : List IxCC.Src.Slot} {eArgs : List (Expr md)}
    (h : RelSlots p env constSpec args eArgs) (hlen : args.length = 2) :
    ∃ s0 s1 e0 e1, args = [s0, s1] ∧ eArgs = [e0, e1] ∧
      RelSlot p env constSpec s0 e0 ∧ RelSlot p env constSpec s1 e1 := by
  cases h with
  | nil => simp at hlen
  | cons hs0 h1 =>
    cases h1 with
    | nil => simp at hlen
    | cons hs1 h2 =>
      cases h2 with
      | nil => exact ⟨_, _, _, _, rfl, rfl, hs0, hs1⟩
      | cons _ _ => simp at hlen

theorem RelSlots.len4 {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    {args : List IxCC.Src.Slot} {eArgs : List (Expr md)}
    (h : RelSlots p env constSpec args eArgs) (hlen : args.length = 4) :
    ∃ s0 s1 s2 s3 e0 e1 e2 e3,
      args = [s0, s1, s2, s3] ∧ eArgs = [e0, e1, e2, e3] ∧
      RelSlot p env constSpec s0 e0 ∧ RelSlot p env constSpec s1 e1 ∧
      RelSlot p env constSpec s2 e2 ∧ RelSlot p env constSpec s3 e3 := by
  cases h with
  | nil => simp at hlen
  | cons hs0 h1 =>
    cases h1 with
    | nil => simp at hlen
    | cons hs1 h2 =>
      cases h2 with
      | nil => simp at hlen
      | cons hs2 h3 =>
        cases h3 with
        | nil => simp at hlen
        | cons hs3 h4 =>
          cases h4 with
          | nil => exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, hs0, hs1, hs2, hs3⟩
          | cons _ _ => simp at hlen

def EvalSim (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) (k : Nat) : Prop :=
  ∀ {ls : IxCC.Src.Levels} {ρ : List IxCC.Src.Slot} {σ : List (Expr md)}
    {t : IxCC.Src.Term} {kt : Expr md} {v : IxCC.Src.Value},
    RelSlots p env constSpec ρ σ →
    RelTerm p env constSpec ls σ.length t kt →
    IxCC.Src.eval p k ls ρ t = .ok v →
    ∃ w : Expr md, Red env 0 (subst σ 0 kt) w ∧ RelVal p env constSpec v w

def ApplySim (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) (k : Nat) : Prop :=
  ∀ {fv : IxCC.Src.Value} {wf : Expr md} {s : IxCC.Src.Slot} {ea : Expr md}
    {v : IxCC.Src.Value},
    RelVal p env constSpec fv wf →
    RelSlot p env constSpec s ea →
    IxCC.Src.apply p k fv s = .ok v →
    ∃ w : Expr md, Red env 0 (.app wf ea) w ∧ RelVal p env constSpec v w

def ForceSim (p : IxCC.Src.Program) (env : Env md)
    (constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop) (k : Nat) : Prop :=
  ∀ {s : IxCC.Src.Slot} {e : Expr md} {v : IxCC.Src.Value},
    RelSlot p env constSpec s e →
    IxCC.Src.force p k s = .ok v →
    ∃ w : Expr md, Red env 0 e w ∧ RelVal p env constSpec v w

theorem force_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k') :
    ForceSim p env constSpec k := by
  intro s e v hs hforce
  cases hs with
  | val _ hred hval =>
    simp only [IxCC.Src.force, IxCC.Sem.Result.ok.injEq] at hforce
    subst hforce
    exact ⟨_, hred, hval⟩
  | name _ hσ hterm =>
    cases k with
    | zero => simp [IxCC.Src.force] at hforce
    | succ k' =>
      simp only [IxCC.Src.force] at hforce
      exact (ih k' (Nat.lt_succ_self k')).1 hσ hterm hforce

theorem fire_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k')
    {h : IxCC.Src.Head} {ls : IxCC.Src.Levels} {eHead : Expr md}
    {args : List IxCC.Src.Slot} {eArgs : List (Expr md)} {v : IxCC.Src.Value}
    (hHead : RelHead p env constSpec h ls eHead)
    (hSlots : RelSlots p env constSpec args eArgs)
    (hArity : args.length = p.headArity h)
    (hFire : IxCC.Src.fire p k h ls args = .ok v) :
    ∃ w : Expr md, Red env 0 (Expr.mkAppN eHead eArgs) w ∧ RelVal p env constSpec v w := by
  cases hHead with
  | natZero hdecl hzero =>
    simp only [IxCC.Src.Program.headArity, hdecl] at hArity
    obtain ⟨rfl, rfl⟩ := hSlots.len0 hArity
    simp only [IxCC.Src.fire, hdecl, List.drop, IxCC.Src.forceAll, ← hzero, beq_self_eq_true,
      ↓reduceIte, IxCC.Sem.Result.ok.injEq] at hFire
    subst hFire
    exact ⟨.const natZeroName [], Red.refl, .lit rfl (by simp [rawNatLit?])⟩
  | natSucc hdecl hsucc hne =>
    simp only [IxCC.Src.Program.headArity, hdecl] at hArity
    obtain ⟨s0, e0, rfl, rfl, hs0⟩ := hSlots.len1 hArity
    simp only [IxCC.Src.fire, hdecl, List.drop, IxCC.Src.forceAll] at hFire
    cases hf0 : IxCC.Src.force p k s0 with
    | ok v0 =>
      simp only [hf0] at hFire
      obtain ⟨w0, hred0, hv0⟩ := force_sim ih hs0 hf0
      have hneB : (some _ == p.known.natZero) = false := beq_false_of_ne hne
      simp only [hneB, Bool.false_eq_true, ↓reduceIte, ← hsucc, beq_self_eq_true] at hFire
      cases hv0 with
      | lit _ hw0 =>
        simp only [IxCC.Sem.Result.ok.injEq] at hFire
        subst hFire
        exact ⟨.lit (.natVal (_ + 1)),
          Red.natSucc (natLitSupported_of_natBasisStored hbasis) hred0 hw0,
          .lit rfl rfl⟩
      | irr _ | clo _ _ _ _ _ | pap _ _ _ => simp at hFire
    | _ => simp [hf0] at hFire
  | primBinNat harity hmem hstored heval =>
    simp only [IxCC.Src.Program.headArity, harity] at hArity
    obtain ⟨s0, s1, e0, e1, rfl, rfl, hs0, hs1⟩ := hSlots.len2 hArity
    unfold IxCC.Src.fire at hFire
    unfold IxCC.Src.forceAll at hFire
    cases hf0 : IxCC.Src.force p k s0 with
    | ok v0 =>
      rw [hf0] at hFire
      dsimp only at hFire
      unfold IxCC.Src.forceAll at hFire
      cases hf1 : IxCC.Src.force p k s1 with
      | ok v1 =>
        rw [hf1] at hFire
        dsimp only at hFire
        unfold IxCC.Src.forceAll at hFire
        obtain ⟨w0, hred0, hv0⟩ := force_sim ih hs0 hf0
        obtain ⟨w1, hred1, hv1⟩ := force_sim ih hs1 hf1
        cases hv0 with
        | lit _ hw0 =>
          cases hv1 with
          | lit _ hw1 =>
            dsimp only [IxCC.Src.litArgs, Option.map] at hFire
            cases hev : IxCC.Src.PrimOp.evalLits _ [_, _] with
            | some res =>
              rw [hev] at hFire
              obtain ⟨out, rfl, hres⟩ := heval _ _ res hev
              simp only [IxCC.Sem.Result.ok.injEq] at hFire
              subst hFire
              exact ⟨.lit (.natVal out), Red.natOp hmem hstored hred0 hw0 hred1 hw1 hres, .lit rfl rfl⟩
            | none => simp [hev] at hFire
          | irr _ | clo _ _ _ _ _ | pap _ _ _ => simp [IxCC.Src.litArgs] at hFire
        | irr _ | clo _ _ _ _ _ | pap _ _ _ => simp [IxCC.Src.litArgs] at hFire
      | _ => simp [hf1] at hFire
    | _ => simp [hf0] at hFire
  | natRec hdecl hkind hnat hpeel0 hb0 hpeel1 hb1 =>
    simp only [IxCC.Src.Program.headArity, hdecl, Option.bind, IxCC.Src.Decl.recArity,
      Option.getD] at hArity
    obtain ⟨s0, s1, s2, s3, e0, e1, e2, e3, rfl, rfl, hs0, hs1, hs2, hs3⟩ := hSlots.len4 hArity
    cases k with
    | zero => simp [IxCC.Src.fire] at hFire
    | succ k' =>
      simp only [IxCC.Src.fire, hdecl, hkind, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD] at hFire
      cases hf3 : IxCC.Src.force p k' s3 with
      | ok major =>
        simp only [hf3] at hFire
        obtain ⟨w3, hred3, hmaj⟩ := (ih k' (Nat.lt_succ_self k')).2.2 hs3 hf3
        cases hmaj with
        | @lit n _ _ hw3 =>
          simp only [IxCC.Src.Program.selectRule, ← hnat, beq_self_eq_true, ↓reduceIte] at hFire
          cases n with
          | zero =>
            simp only [IxCC.Sem.Result.ofOption, List.getElem?_cons_zero, List.take,
              List.append_nil, List.length_cons, List.length_nil, hpeel0, List.reverse,
              List.reverseAux] at hFire
            have henv : RelSlots p env constSpec [s2, s1, s0] [e2, e1, e0] :=
              .cons hs2 (.cons hs1 (.cons hs0 .nil))
            obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 henv hb0 hFire
            exact ⟨w, Red.trans (red_natRec_zero hbasis hs1.bvarBound_zero hred3 hw3) hredE, hval⟩
          | succ m =>
            simp only [IxCC.Sem.Result.ofOption, List.getElem?_cons_succ, List.getElem?_cons_zero,
              List.take, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
              hpeel1, List.reverse, List.reverseAux] at hFire
            have hlitSlot : RelSlot p env constSpec (.val (.lit m)) (.lit (.natVal m)) :=
              .val rfl Red.refl (.lit rfl rfl)
            have henv : RelSlots p env constSpec [.val (.lit m), s2, s1, s0]
                [.lit (.natVal m), e2, e1, e0] :=
              .cons hlitSlot (.cons hs2 (.cons hs1 (.cons hs0 .nil)))
            obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 henv hb1 hFire
            exact ⟨w, Red.trans (red_natRec_succ hbasis hs0.bvarBound_zero hs1.bvarBound_zero
              hs2.bvarBound_zero hred3 hw3) hredE, hval⟩
        | irr _ | clo _ _ _ _ _ | pap _ _ _ =>
          simp [IxCC.Src.Program.selectRule, IxCC.Sem.Result.ofOption] at hFire
      | _ => simp [hf3] at hFire
  | natCases hres hdecl hkind hnat hfind hlp hmb0 hmb1 hmb2 hmb3 hmb4 hmb5 hmTy hihTy =>
    simp only [IxCC.Src.Program.headArity, hres, hdecl] at hArity
    obtain ⟨s0, s1, s2, s3, e0, e1, e2, e3, rfl, rfl, hs0, hs1, hs2, hs3⟩ := hSlots.len4 hArity
    cases k with
    | zero => simp [IxCC.Src.fire] at hFire
    | succ k' =>
      simp only [IxCC.Src.fire, hres, hdecl, hkind, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD] at hFire
      cases hf1 : IxCC.Src.force p k' s1 with
      | ok major =>
        simp only [hf1] at hFire
        obtain ⟨w1, hred1, hmaj⟩ := (ih k' (Nat.lt_succ_self k')).2.2 hs1 hf1
        cases hmaj with
        | @lit n _ _ hw1 =>
          simp only [IxCC.Src.Program.selectRule, ← hnat, beq_self_eq_true, ↓reduceIte] at hFire
          cases n with
          | zero =>
            simp only [IxCC.Sem.Result.ofOption, List.getElem?_cons_succ, List.getElem?_cons_zero] at hFire
            cases hf2 : IxCC.Src.force p k' s2 with
            | ok minor =>
              simp only [hf2, IxCC.Src.applyAll, IxCC.Sem.Result.ok.injEq] at hFire
              subst hFire
              obtain ⟨w2, hred2, hval⟩ := (ih k' (Nat.lt_succ_self k')).2.2 hs2 hf2
              have hredC := red_natCasesOn_zero hbasis hfind hlp hmb0 hmb1 hmb2 hmb3
                hs0.bvarBound_zero hs1.bvarBound_zero hs2.bvarBound_zero hred1 hw1 (s := e3)
              exact ⟨w2, Red.trans hredC hred2, hval⟩
            | _ => simp [hf2] at hFire
          | succ m =>
            simp only [IxCC.Sem.Result.ofOption, List.getElem?_cons_succ, List.getElem?_cons_zero] at hFire
            cases hf3 : IxCC.Src.force p k' s3 with
            | ok minor =>
              simp only [hf3, IxCC.Src.applyAll] at hFire
              cases hap : IxCC.Src.apply p k' minor (.val (.lit m)) with
              | ok v' =>
                simp only [hap, IxCC.Sem.Result.ok.injEq] at hFire
                subst hFire
                obtain ⟨w3, hred3, hminor⟩ := (ih k' (Nat.lt_succ_self k')).2.2 hs3 hf3
                have hlitSlot : RelSlot p env constSpec (.val (.lit m)) (.lit (.natVal m)) :=
                  .val rfl Red.refl (.lit rfl rfl)
                obtain ⟨w, hredAp, hval⟩ := (ih k' (Nat.lt_succ_self k')).2.1 hminor hlitSlot hap
                have hredC := red_natCasesOn_succ hbasis hfind hlp hmb0 hmb1 hmb2 hmb3 hmb4 hmb5
                  hmTy hihTy hs0.bvarBound_zero hs1.bvarBound_zero hs2.bvarBound_zero
                  hs3.bvarBound_zero hred1 hw1
                exact ⟨w, Red.trans hredC (Red.trans (Red.appFn hred3) hredAp), hval⟩
              | _ => simp [hap] at hFire
            | _ => simp [hf3] at hFire
        | irr _ | clo _ _ _ _ _ | pap _ _ _ =>
          simp [IxCC.Src.Program.selectRule, IxCC.Sem.Result.ofOption] at hFire
      | _ => simp [hf1] at hFire

theorem headValue_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k')
    {ls : IxCC.Src.Levels} {h : IxCC.Src.Head} {eHead : Expr md} {v : IxCC.Src.Value}
    (hHead : RelHead p env constSpec h ls eHead)
    (hHV : IxCC.Src.headValue p k ls h = .ok v) :
    ∃ w : Expr md, Red env 0 eHead w ∧ RelVal p env constSpec v w := by
  simp only [IxCC.Src.headValue] at hHV
  by_cases har : (p.headArity h == 0) = true
  · simp only [har, ↓reduceIte] at hHV
    have har0 : ([] : List IxCC.Src.Slot).length = p.headArity h := by
      simp [beq_iff_eq.mp har]
    simpa [Expr.mkAppN] using fire_sim hbasis ih hHead .nil har0 hHV
  · simp only [har, Bool.false_eq_true, ↓reduceIte, IxCC.Sem.Result.ok.injEq] at hHV
    subst hHV
    exact ⟨eHead, Red.refl,
      .pap (args := []) (eHead := eHead) (eArgs := []) hHead.bvarBound_zero hHead .nil⟩

theorem apply_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k') :
    ApplySim p env constSpec k := by
  intro fv wf s ea v hfv hs hap
  cases hfv with
  | lit _ _ | irr _ => simp [IxCC.Src.apply] at hap
  | @clo b dom body ρ ls σ kty kbody mb hlamB hty hbeta hσ hbody =>
    unfold IxCC.Src.apply at hap
    by_cases hall : b.propWhen.allowsBeta ls = true
    · simp only [hall, ↓reduceIte] at hap
      cases k with
      | zero => simp at hap
      | succ k' =>
        have henv : RelSlots p env constSpec (s :: ρ) (ea :: σ) := .cons hs hσ
        obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 henv hbody hap
        have hredB := red_betaGate_subst (env := env) (d := 0) (a := ea)
          hσ.bvarBound_zero (hbeta hall) (ty := kty) (body := kbody)
        exact ⟨w, Red.trans hredB hredE, hval⟩
    · simp [hall] at hap
  | @pap h ls args eHead eArgs hpapB hHead hArgs =>
    unfold IxCC.Src.apply at hap
    dsimp only at hap
    have hArgs' : RelSlots p env constSpec (args ++ [s]) (eArgs ++ [ea]) :=
      hArgs.append (.cons hs .nil)
    have hmk : Expr.mkAppN eHead (eArgs ++ [ea]) = Expr.app (Expr.mkAppN eHead eArgs) ea := by
      rw [mkAppN_append, Expr.mkAppN, Expr.mkAppN]
    by_cases heq : ((args ++ [s]).length == p.headArity h) = true
    · simp only [heq, ↓reduceIte] at hap
      obtain ⟨w, hredF, hval⟩ := fire_sim hbasis ih hHead hArgs' (beq_iff_eq.mp heq) hap
      rw [hmk] at hredF
      exact ⟨w, hredF, hval⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hap
      by_cases hlt : (args ++ [s]).length < p.headArity h
      · simp only [hlt, ↓reduceIte, IxCC.Sem.Result.ok.injEq] at hap
        subst hap
        have hb' : (Expr.mkAppN eHead (eArgs ++ [ea])).bvarBound = 0 := by
          rw [hmk]
          simp [Expr.bvarBound, hpapB, hs.bvarBound_zero]
        refine ⟨_, Red.refl, ?_⟩
        rw [← hmk]
        exact .pap hb' hHead hArgs'
      · simp only [hlt, ↓reduceIte] at hap
        nomatch hap

theorem applyAll_sim_of_apply {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hApply : ApplySim p env constSpec k) :
    ∀ {ss : List IxCC.Src.Slot} {es : List (Expr md)} {fv : IxCC.Src.Value}
      {wf : Expr md} {v : IxCC.Src.Value},
      RelSlots p env constSpec ss es →
      RelVal p env constSpec fv wf →
      IxCC.Src.applyAll p k fv ss = .ok v →
      ∃ w : Expr md, Red env 0 (Expr.mkAppN wf es) w ∧ RelVal p env constSpec v w
  | [], [], _, wf, _, .nil, hfv, hap => by
    simp only [IxCC.Src.applyAll, IxCC.Sem.Result.ok.injEq] at hap
    subst hap
    exact ⟨wf, Red.refl, hfv⟩
  | s :: rest, e :: erest, fv, wf, v, .cons hs hrest, hfv, hap => by
    unfold IxCC.Src.applyAll at hap
    cases hap1 : IxCC.Src.apply p k fv s with
    | ok v1 =>
      rw [hap1] at hap
      obtain ⟨w1, hred1, hv1⟩ := hApply hfv hs hap1
      obtain ⟨w, hredRest, hv⟩ := applyAll_sim_of_apply hApply hrest hv1 hap
      exact ⟨w, Red.trans (red_mkAppN_fn erest hred1) hredRest, hv⟩
    | _ => simp [hap1] at hap

theorem evalConst_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k')
    {ls : IxCC.Src.Levels} {c : IxCC.Src.CId} {e : Expr md} {v : IxCC.Src.Value}
    (hcs : constSpec ls c e)
    (hev : IxCC.Src.evalConst p k ls c = .ok v) :
    ∃ w : Expr md, Red env 0 e w ∧ RelVal p env constSpec v w := by
  cases hconst ls c e hcs with
  | prim hres hHead =>
    unfold IxCC.Src.evalConst at hev
    rw [hres] at hev
    exact headValue_sim hbasis ih hHead hev
  | csimp hres hred hterm =>
    unfold IxCC.Src.evalConst at hev
    rw [hres] at hev
    cases k with
    | zero => simp at hev
    | succ k' =>
      obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 .nil hterm hev
      rw [subst_nil] at hredE
      exact ⟨w, Red.trans hred hredE, hval⟩
  | eqn hres hred hterm =>
    unfold IxCC.Src.evalConst at hev
    rw [hres] at hev
    cases k with
    | zero => simp at hev
    | succ k' =>
      obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 .nil hterm hev
      rw [subst_nil] at hredE
      exact ⟨w, Red.trans hred hredE, hval⟩
  | cases hres hHead =>
    unfold IxCC.Src.evalConst at hev
    rw [hres] at hev
    exact headValue_sim hbasis ih hHead hev
  | ctor hres hdecl hHead =>
    unfold IxCC.Src.evalConst at hev
    rw [hres, hdecl] at hev
    exact headValue_sim hbasis ih hHead hev
  | recr hres hdecl hHead =>
    unfold IxCC.Src.evalConst at hev
    rw [hres, hdecl] at hev
    exact headValue_sim hbasis ih hHead hev
  | defn hres hdecl hred hterm =>
    unfold IxCC.Src.evalConst at hev
    rw [hres, hdecl] at hev
    cases k with
    | zero => simp at hev
    | succ k' =>
      obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 .nil hterm hev
      rw [subst_nil] at hredE
      exact ⟨w, Red.trans hred hredE, hval⟩
  | opaq hres hdecl hopaq hred hterm =>
    unfold IxCC.Src.evalConst at hev
    rw [hres, hdecl, hopaq] at hev
    dsimp only [↓reduceIte] at hev
    cases k with
    | zero => simp at hev
    | succ k' =>
      obtain ⟨w, hredE, hval⟩ := (ih k' (Nat.lt_succ_self k')).1 .nil hterm hev
      rw [subst_nil] at hredE
      exact ⟨w, Red.trans hred hredE, hval⟩

theorem eval_sim_aux {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k')
    {ls : IxCC.Src.Levels} {d : Nat} {t : IxCC.Src.Term} {kt : Expr md}
    (hterm : RelTerm p env constSpec ls d t kt) :
    ∀ {ρ : List IxCC.Src.Slot} {σ : List (Expr md)} {v : IxCC.Src.Value},
      d = σ.length →
      RelSlots p env constSpec ρ σ →
      IxCC.Src.eval p k ls ρ t = .ok v →
      ∃ w : Expr md, Red env 0 (subst σ 0 kt) w ∧ RelVal p env constSpec v w := by
  induction hterm with
  | @var d i hi =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    cases hget : ρ[i]? with
    | some s =>
      rw [hget] at hev
      obtain ⟨e, hgetE, hs⟩ := hσ.getElem?_some i s hget
      have hsub : subst σ 0 (.bvar i) = e := by simp [subst, hgetE]
      rw [hsub]
      exact force_sim ih hs hev
    | none => simp [hget] at hev
  | @natLit d n =>
    intro ρ σ v _ _ hev
    unfold IxCC.Src.eval at hev
    simp only [IxCC.Sem.Result.ok.injEq] at hev
    subst hev
    exact ⟨.lit (.natVal n), Red.refl, .lit rfl rfl⟩
  | @sort d u kt hkt =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    simp only [IxCC.Sem.Result.ok.injEq] at hev
    subst hev
    have hb0 : (subst σ 0 kt).bvarBound = 0 := by
      have := bvarBound_subst_le hσ.bvarBound_zero kt 0 (by omega)
      omega
    exact ⟨subst σ 0 kt, Red.refl, .irr hb0⟩
  | @pi d b rc dom body kt hkt =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    simp only [IxCC.Sem.Result.ok.injEq] at hev
    subst hev
    have hb0 : (subst σ 0 kt).bvarBound = 0 := by
      have := bvarBound_subst_le hσ.bvarBound_zero kt 0 (by omega)
      omega
    exact ⟨subst σ 0 kt, Red.refl, .irr hb0⟩
  | @lam d b dom body kty kbody mb hty hbeta hbody _ =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    simp only [IxCC.Sem.Result.ok.injEq] at hev
    subst hev
    have hbbody := hbody.bvarBound_le
    have hb0 : (subst σ 0 (.lam kty kbody mb)).bvarBound = 0 := by
      have := bvarBound_subst_le hσ.bvarBound_zero (.lam kty kbody mb) 0 (by simp [Expr.bvarBound]; omega)
      omega
    exact ⟨subst σ 0 (.lam kty kbody mb), Red.refl,
      .clo hb0 (by omega) hbeta hσ (hd ▸ hbody)⟩
  | @app d f a m r kf ka hf ha ihf iha =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    cases hevF : IxCC.Src.eval p k ls ρ f with
    | ok fv =>
      rw [hevF] at hev
      dsimp only at hev
      obtain ⟨wf, hredF, hfv⟩ := ihf hd hσ hevF
      have hba := ha.bvarBound_le
      have hka0 : (subst σ 0 ka).bvarBound = 0 := by
        have := bvarBound_subst_le hσ.bvarBound_zero ka 0 (by omega)
        omega
      by_cases hirr : r.irrAt ls = true
      · simp only [hirr, ↓reduceIte] at hev
        have hslot : RelSlot p env constSpec (.val (.irr (some a) ρ ls)) (subst σ 0 ka) :=
          .val hka0 Red.refl (.irr hka0)
        obtain ⟨w, hredAp, hval⟩ := apply_sim hbasis ih hfv hslot hev
        exact ⟨w, Red.trans (Red.appFn hredF) hredAp, hval⟩
      · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at hev
        cases m with
        | strict =>
          dsimp only at hev
          cases hevA : IxCC.Src.eval p k ls ρ a with
          | ok xv =>
            rw [hevA] at hev
            dsimp only at hev
            obtain ⟨wa, hredA, hxv⟩ := iha hd hσ hevA
            have hslot : RelSlot p env constSpec (.val xv) (subst σ 0 ka) :=
              .val hka0 hredA hxv
            obtain ⟨w, hredAp, hval⟩ := apply_sim hbasis ih hfv hslot hev
            exact ⟨w, Red.trans (Red.appFn hredF) hredAp, hval⟩
          | _ => simp [hevA] at hev
        | byName =>
          dsimp only at hev
          have hslot : RelSlot p env constSpec (.name a ρ ls) (subst σ 0 ka) :=
            .name hka0 hσ (hd ▸ ha)
          obtain ⟨w, hredAp, hval⟩ := apply_sim hbasis ih hfv hslot hev
          exact ⟨w, Red.trans (Red.appFn hredF) hredAp, hval⟩
    | _ => simp [hevF] at hev
  | @letBeta d c r ty vterm body kty kv kbody mb hmb hty hv hbody ihv ihb =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    have hbv := hv.bvarBound_le
    have hkv0 : (subst σ 0 kv).bvarBound = 0 := by
      have := bvarBound_subst_le hσ.bvarBound_zero kv 0 (by omega)
      omega
    have hredBeta : Red env 0 (subst σ 0 (.app (.lam kty kbody mb) kv))
        (subst (subst σ 0 kv :: σ) 0 kbody) :=
      red_betaGate_subst hσ.bvarBound_zero hmb
    by_cases hirr : r.irrAt ls = true
    · simp only [hirr, ↓reduceIte] at hev
      have hslot : RelSlot p env constSpec (.val (.irr (some vterm) ρ ls)) (subst σ 0 kv) :=
        .val hkv0 Red.refl (.irr hkv0)
      obtain ⟨w, hredB, hval⟩ := ihb (by simp [hd]) (.cons hslot hσ) hev
      exact ⟨w, Red.trans hredBeta hredB, hval⟩
    · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at hev
      cases hevV : IxCC.Src.eval p k ls ρ vterm with
      | ok xv =>
        rw [hevV] at hev
        dsimp only at hev
        obtain ⟨wv, hredV, hxv⟩ := ihv hd hσ hevV
        have hslot : RelSlot p env constSpec (.val xv) (subst σ 0 kv) :=
          .val hkv0 hredV hxv
        obtain ⟨w, hredB, hval⟩ := ihb (by simp [hd]) (.cons hslot hσ) hev
        exact ⟨w, Red.trans hredBeta hredB, hval⟩
      | _ => simp [hevV] at hev
  | @letZeta d c r ty vterm body kv kbody hkv0 hv hbody ihv ihb =>
    intro ρ σ v hd hσ hev
    unfold IxCC.Src.eval at hev
    have hsub : subst σ 0 (kbody.instantiate1 kv 0) = subst (kv :: σ) 0 kbody :=
      subst_instantiate1_closed σ kv hkv0 kbody 0
    have hkvSub : subst σ 0 kv = kv := subst_of_bvarBound_le σ kv 0 (by omega)
    rw [hsub]
    by_cases hirr : r.irrAt ls = true
    · simp only [hirr, ↓reduceIte] at hev
      have hslot : RelSlot p env constSpec (.val (.irr (some vterm) ρ ls)) kv :=
        .val hkv0 Red.refl (.irr hkv0)
      exact ihb (by simp [hd]) (.cons hslot hσ) hev
    · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at hev
      cases hevV : IxCC.Src.eval p k ls ρ vterm with
      | ok xv =>
        rw [hevV] at hev
        dsimp only at hev
        obtain ⟨wv, hredV, hxv⟩ := ihv hd hσ hevV
        rw [hkvSub] at hredV
        have hslot : RelSlot p env constSpec (.val xv) kv :=
          .val hkv0 hredV hxv
        exact ihb (by simp [hd]) (.cons hslot hσ) hev
      | _ => simp [hevV] at hev
  | @const d c us kt hkt0 hcs =>
    intro ρ σ v _ _ hev
    unfold IxCC.Src.eval at hev
    rw [subst_of_bvarBound_le σ kt 0 (by omega)]
    exact evalConst_sim hbasis hconst ih hcs hev

theorem eval_sim {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop} {k : Nat}
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    (ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k') :
    EvalSim p env constSpec k := by
  intro ls ρ σ t kt v hσ hterm hev
  exact eval_sim_aux hbasis hconst ih hterm rfl hσ hev

theorem sim_all {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    (k : Nat) :
    EvalSim p env constSpec k ∧ ApplySim p env constSpec k ∧ ForceSim p env constSpec k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    exact ⟨eval_sim hbasis hconst ih, apply_sim hbasis ih, force_sim ih⟩

theorem relSlots_of_natVals : ∀ (xs : List Nat),
    RelSlots p env constSpec
      (xs.map (fun n => IxCC.Src.Slot.val (.lit n)))
      (xs.map (fun n => Expr.lit (.natVal n)))
  | [] => .nil
  | _ :: ns => .cons (.val rfl Red.refl (.lit rfl rfl)) (relSlots_of_natVals ns)

/-- **Layer 1, the simulation lemma.** For a kernel environment `env` storing the `Nat`
basis, and a user-supplied relation `constSpec` closed under `RelConstStep` (`hconst`), if
the root `root` is related to `eRoot` and `Src.run` returns the literal `out` on `Nat`
literal arguments, then `eRoot` applied to those literals reduces under `Red env 0` to a
term whose raw literal is `out`. It says nothing about a program for which no such
`constSpec` exists; see the module docstring for the fragment where one does. -/
theorem srcRun_to_red {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    {k : Nat} {root : IxCC.Src.CId} {eRoot : Expr md}
    {xs : List Nat} {out : Nat}
    (hroot : constSpec [] root eRoot)
    (hrun : IxCC.Src.run p k root (xs.map .lit) = .ok (.lit out)) :
    ∃ w : Expr md,
      Red env 0 (Expr.mkAppN eRoot (xs.map (fun n => Expr.lit (.natVal n)))) w ∧
      rawNatLit? w = some out := by
  simp only [IxCC.Src.run, List.map_map] at hrun
  cases hev : IxCC.Src.evalConst p k [] root with
  | ok fv =>
    rw [hev] at hrun
    have ih : ∀ k' < k, EvalSim p env constSpec k' ∧ ApplySim p env constSpec k' ∧ ForceSim p env constSpec k' :=
      fun k' _ => sim_all hbasis hconst k'
    obtain ⟨wf, hredF, hfv⟩ := evalConst_sim hbasis hconst ih hroot hev
    have hApply : ApplySim p env constSpec k := (sim_all hbasis hconst k).2.1
    obtain ⟨w, hredAp, hval⟩ := applyAll_sim_of_apply hApply (relSlots_of_natVals xs) hfv hrun
    cases hval with
    | lit _ hw =>
      exact ⟨w, Red.trans (red_mkAppN_fn _ hredF) hredAp, hw⟩
  | _ => simp [hev] at hrun
/-! ## Layer 2: Kernel Reduction (`Red`) to Set-Theoretic Denotation (`Denotes`) -/

universe w
variable {V : Type w} [SetTheory V]

theorem wscoped_of_hasFvar_false : ∀ {e : Expr md} (d : Nat),
    e.hasFvar = false → Expr.WScoped d e := by
  intro e
  induction e <;> intro d h <;> simp_all [Expr.hasFvar, Expr.WScoped]

theorem fvarLeaves_of_hasFvar_false : ∀ {e : Expr md},
    e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.hasFvar, Expr.fvarLeaves]

theorem fvarsBelow_zero_of_hasFvar_false : ∀ {e : Expr md},
    e.hasFvar = false → Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.hasFvar, Expr.fvarsBelow]

theorem frame_zero_of_closed {e : Expr md}
    (hnf : e.hasFvar = false) (hlb : e.looseBVarsBounded 0 = true) :
    Frame 0 e := by
  refine ⟨wscoped_of_hasFvar_false 0 hnf, hlb, ?_⟩
  intro l hl
  rw [fvarLeaves_of_hasFvar_false hnf] at hl
  cases hl

theorem ctxOk_nil_of_closed {env : Env md} (m : EnvModel V env) (φ : LevelParam → Nat)
    {e : Expr md} (hnf : e.hasFvar = false) :
    CtxOk m φ 0 [] e := by
  refine ⟨rfl, fun l hl => ?_⟩
  rw [fvarLeaves_of_hasFvar_false hnf] at hl
  cases hl

theorem bvarBound_mkAppN_natVals : ∀ (xs : List Nat) {f : Expr md},
    f.bvarBound = 0 →
    (Expr.mkAppN f (xs.map fun n => Expr.lit (.natVal n))).bvarBound = 0
  | [], f, hf => hf
  | _ :: ns, f, hf => by
    simp only [List.map, Expr.mkAppN]
    apply bvarBound_mkAppN_natVals ns
    simp [Expr.bvarBound, hf]

theorem hasFvar_mkAppN_natVals : ∀ (xs : List Nat) {f : Expr md},
    f.hasFvar = false →
    (Expr.mkAppN f (xs.map fun n => Expr.lit (.natVal n))).hasFvar = false
  | [], f, hf => hf
  | _ :: ns, f, hf => by
    simp only [List.map, Expr.mkAppN]
    apply hasFvar_mkAppN_natVals ns
    simp [Expr.hasFvar, hf]

theorem looseBVarsBounded_zero_of_bvarBound_zero {e : Expr md} (hb : e.bvarBound = 0) :
    e.looseBVarsBounded 0 = true :=
  Expr.looseBVarsBounded_iff.mpr (Nat.le_of_eq hb)

theorem red_natLitToConstructor_of_rawNatLit {env : Env md} {d : Nat} {w : Expr md} {n : Nat}
    (hsup : natLitSupported env = true) (hr : rawNatLit? w = some n) :
    Red env d w (natLitToConstructor n) := by
  cases w with
  | lit l =>
    cases l with
    | natVal k =>
      simp only [rawNatLit?, Option.some.injEq] at hr
      subst hr
      exact Red.natLit hsup
    | strVal _ => simp [rawNatLit?] at hr
  | const c us =>
    cases us with
    | nil =>
      simp only [rawNatLit?] at hr
      split at hr
      · rename_i hc
        simp only [Option.some.injEq] at hr
        subst hr hc
        exact Red.refl
      · cases hr
    | cons _ _ => simp [rawNatLit?] at hr
  | _ => simp [rawNatLit?] at hr

theorem red_to_denotes_nat {μ : CheckMode} {env : Env md}
    (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V)
    {e w : Expr md} {out : Nat} {ea : AnnotTerm}
    (hsup : natLitSupported env = true)
    (hnf : e.hasFvar = false)
    (hlb : e.looseBVarsBounded 0 = true)
    (hea : denoteMeta mp.base2.acval env φ 0 e = some ea)
    (hgrad : Graded V [] ea)
    (hred : Red env 0 e w)
    (hout : rawNatLit? w = some out) :
    ∃ v : V,
      Denotes (Model.ofEnvModelM mp).cval env φ ρ e v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v := by
  have hin : RulesInputs V mp.base2 φ := RulesInputs.ofSem mp φ
  have hred2 : Red env 0 e (natLitToConstructor out) :=
    Red.trans hred (red_natLitToConstructor_of_rawNatLit hsup hout)
  have hsem := red_sound hin hred2 (frame_zero_of_closed hnf hlb)
    (ctxOk_nil_of_closed mp.base2 φ hnf) hea hgrad
  obtain ⟨_, _, ea2, hea2, hgrad2, heq⟩ := hsem
  have hsat : Sat V [] ρ := Sat_nil V ρ
  have hdenE := Denotes_of_denoteMeta (V := V) mp.base2.cval_closedL 0 e hea
    (fvarsBelow_zero_of_hasFvar_false hnf) hlb ρ (hgrad ρ hsat)
  rw [Expr.closeN_of_hasFvar e 0 0 hnf] at hdenE
  have hnfC : (natLitToConstructor out : Expr md).hasFvar = false := by
    cases out <;> rfl
  have hlbC : (natLitToConstructor out : Expr md).looseBVarsBounded 0 = true :=
    Ix.Kernel.natLitToConstructor_looseBVars out
  have hdenC := Denotes_of_denoteMeta (V := V) mp.base2.cval_closedL 0
    (natLitToConstructor out) hea2
    (fvarsBelow_zero_of_hasFvar_false hnfC) hlbC ρ (hgrad2 ρ hsat)
  rw [Expr.closeN_of_hasFvar _ 0 0 hnfC] at hdenC
  refine ⟨interp V ρ ea2, ?_, Denotes.natLit hdenC, hdenC⟩
  rw [← heq ρ hsat]
  exact hdenE

theorem infer_red_to_denotes_nat {μ : CheckMode} {env : Env md}
    (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V)
    {e ty w : Expr md} {out : Nat} {ea : AnnotTerm}
    (hsup : natLitSupported env = true)
    (hnf : e.hasFvar = false)
    (hlb : e.looseBVarsBounded 0 = true)
    (hea : denoteMeta mp.base2.acval env φ 0 e = some ea)
    (hinf : Infer env .full 0 e ty)
    (hred : Red env 0 e w)
    (hout : rawNatLit? w = some out) :
    ∃ v : V,
      Denotes (Model.ofEnvModelM mp).cval env φ ρ e v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v := by
  have hin : RulesInputs V mp.base2 φ := RulesInputs.ofSem mp φ
  have hisem := infer_sound hin hinf (frame_zero_of_closed hnf hlb)
    (ctxOk_nil_of_closed mp.base2 φ hnf) hea
  obtain ⟨_, _, _, _, hgrad, _, _⟩ := hisem
  exact red_to_denotes_nat mp φ ρ hsup hnf hlb hea hgrad hred hout

/-! ## Layer 3: conjunctions with `checkDecls_sound`, `Recheck.sound_nat` and `verifyBytes_immortal_sound`

Every theorem below keeps Layer 1's user-supplied `constSpec`, `hconst` and related root
`eRoot` as premises. `env` and `eRoot` are not derived from the compiled input. -/

/-- Applied kernel expression `eRoot` on `Nat` literal arguments `xs`. -/
abbrev mkNatApp (eRoot : Expr md) (xs : List Nat) : Expr md :=
  Expr.mkAppN eRoot (xs.map fun n => Expr.lit (.natVal n))

/-- Composes Layer 1 (`srcRun_to_red`) with Layer 2 (`red_to_denotes_nat`): for a
user-supplied `constSpec` satisfying `hconst` and a related closed root `eRoot`, a
terminating `Src.run p k root (xs.map .lit) = .ok (.lit out)` gives a `Red env 0`
reduction of `mkNatApp eRoot xs` to `natLitToConstructor out`, and, if that term is
readable (`hea`) and graded (`hgrad`) in `mp`, equal denotations in
`Model.ofEnvModelM mp` for it, `.lit (.natVal out)` and `natLitToConstructor out`. -/
theorem srcRun_to_denotes_nat {μ : CheckMode} {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V)
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    {k : Nat} {root : IxCC.Src.CId} {eRoot : Expr md} {xs : List Nat} {out : Nat}
    {ea : AnnotTerm}
    (hroot : constSpec [] root eRoot)
    (hbRoot : eRoot.bvarBound = 0)
    (hnfRoot : eRoot.hasFvar = false)
    (hrun : IxCC.Src.run p k root (xs.map .lit) = .ok (.lit out))
    (hea : denoteMeta mp.base2.acval env φ 0 (mkNatApp eRoot xs) = some ea)
    (hgrad : Graded V [] ea) :
    Red env 0 (mkNatApp eRoot xs) (natLitToConstructor out) ∧
    ∃ v : V,
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (mkNatApp eRoot xs) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v := by
  obtain ⟨w, hred, hout⟩ := srcRun_to_red hbasis hconst hroot hrun
  have hsup : natLitSupported env = true := natLitSupported_of_natBasisStored hbasis
  have hnf : (mkNatApp eRoot xs).hasFvar = false := hasFvar_mkAppN_natVals xs hnfRoot
  have hlb : (mkNatApp eRoot xs).looseBVarsBounded 0 = true :=
    looseBVarsBounded_zero_of_bvarBound_zero (bvarBound_mkAppN_natVals xs hbRoot)
  exact ⟨Red.trans hred (red_natLitToConstructor_of_rawNatLit hsup hout),
    red_to_denotes_nat mp φ ρ hsup hnf hlb hea hgrad hred hout⟩

/-- Variant of `srcRun_to_denotes_nat` that takes an `Infer env .full 0` derivation for the
applied root in place of `Graded`; the user-supplied `constSpec` premises are unchanged. -/
theorem srcRun_infer_to_denotes_nat {μ : CheckMode} {p : IxCC.Src.Program} {env : Env md}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V)
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    {k : Nat} {root : IxCC.Src.CId} {eRoot ty : Expr md} {xs : List Nat} {out : Nat}
    {ea : AnnotTerm}
    (hroot : constSpec [] root eRoot)
    (hbRoot : eRoot.bvarBound = 0)
    (hnfRoot : eRoot.hasFvar = false)
    (hrun : IxCC.Src.run p k root (xs.map .lit) = .ok (.lit out))
    (hea : denoteMeta mp.base2.acval env φ 0 (mkNatApp eRoot xs) = some ea)
    (hinf : Infer env .full 0 (mkNatApp eRoot xs) ty) :
    Red env 0 (mkNatApp eRoot xs) (natLitToConstructor out) ∧
    ∃ v : V,
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (mkNatApp eRoot xs) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
      Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v := by
  obtain ⟨w, hred, hout⟩ := srcRun_to_red hbasis hconst hroot hrun
  have hsup : natLitSupported env = true := natLitSupported_of_natBasisStored hbasis
  have hnf : (mkNatApp eRoot xs).hasFvar = false := hasFvar_mkAppN_natVals xs hnfRoot
  have hlb : (mkNatApp eRoot xs).looseBVarsBounded 0 = true :=
    looseBVarsBounded_zero_of_bvarBound_zero (bvarBound_mkAppN_natVals xs hbRoot)
  exact ⟨Red.trans hred (red_natLitToConstructor_of_rawNatLit hsup hout),
    infer_red_to_denotes_nat mp φ ρ hsup hnf hlb hea hinf hred hout⟩

/-- Conjoins `Ix.Kernel.Cached.checkDecls_sound` with `srcRun_to_denotes_nat`: an
environment `env` accepted by `checkDecls μ ev ds = .ok env` (with `μ.verifiedChecks = true`)
has a model `Nonempty (EnvModelM V μ env)`; and, for a user-supplied `constSpec` satisfying
`hconst` and a related closed root `eRoot`, a terminating
`Src.run p k root (xs.map .lit) = .ok (.lit out)` gives a reduction of `mkNatApp eRoot xs` to
`natLitToConstructor out`, and equal denotations in every model `mp` in which that term is
readable and graded. `ds` is any declaration stream: it is not required to be the program's
compiled environment, and `p` is not required to come from it. -/
theorem checkDecls_srcRun_denotes_nat {μ : CheckMode} {ev : Evidences md}
    {ds : Array (Declaration md)} {env : Env md}
    {p : IxCC.Src.Program} {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (hμ : μ.verifiedChecks = true)
    (hchk : Ix.Kernel.Cached.checkDecls μ ev ds = .ok env)
    (hbasis : natBasisStored env = true)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e)
    {k : Nat} {root : IxCC.Src.CId} {eRoot : Expr md} {xs : List Nat} {out : Nat}
    (hroot : constSpec [] root eRoot)
    (hbRoot : eRoot.bvarBound = 0)
    (hnfRoot : eRoot.hasFvar = false)
    (hrun : IxCC.Src.run p k root (xs.map .lit) = .ok (.lit out)) :
    Nonempty (EnvModelM V μ env) ∧
    Red env 0 (mkNatApp eRoot xs) (natLitToConstructor out) ∧
    ∀ (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V) (ea : AnnotTerm),
      denoteMeta mp.base2.acval env φ 0 (mkNatApp eRoot xs) = some ea →
      Graded V [] ea →
      ∃ v : V,
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (mkNatApp eRoot xs) v ∧
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v := by
  have hmodel : Nonempty (EnvModelM V μ env) :=
    Ix.Kernel.Cached.checkDecls_sound (V := V) hμ hchk
  obtain ⟨w, hred, hout⟩ := srcRun_to_red hbasis hconst hroot hrun
  have hsup : natLitSupported env = true := natLitSupported_of_natBasisStored hbasis
  refine ⟨hmodel, Red.trans hred (red_natLitToConstructor_of_rawNatLit hsup hout), ?_⟩
  intro mp φ ρ ea hea hgrad
  exact (srcRun_to_denotes_nat mp φ ρ hbasis hconst hroot hbRoot hnfRoot hrun hea hgrad).2

/-- Helper bridging `Src.run s.p k rootId (i.2.map .lit) = .ok (.lit out)` to
`CheckedProgram`'s `Lang.run` and `Lang.obs`. -/
theorem checkedProgram_run_of_srcRun (s : IxCC.Lam.Erase.Proof.CheckedProgram)
    {i : Nat × List Nat} {k : Nat} {rootAddr : IxCC.Ixon.Address} {rootId : IxCC.Src.CId} {out : Nat}
    (hroot : s.p.roots[i.1]? = some (rootAddr, rootId))
    (hrun : IxCC.Src.run s.p k rootId (i.2.map .lit) = .ok (.lit out)) :
    IxCC.Sem.Lang.run s i k = .ok (IxCC.Lam.Erase.Input.ofProgram s.p s.ch, IxCC.Src.Value.lit out) ∧
    IxCC.Sem.Lang.obs (S := IxCC.Lam.Erase.Proof.CheckedProgram)
      (IxCC.Lam.Erase.Input.ofProgram s.p s.ch, IxCC.Src.Value.lit out) = some (IxCC.Sem.Obs.nat out) := by
  refine ⟨?_, rfl⟩
  show IxCC.Lam.Erase.Proof.srcRun s i k = .ok _
  simp [IxCC.Lam.Erase.Proof.srcRun, hroot, hrun, IxCC.Sem.Result.map, IxCC.Sem.Result.bind]

/-- **Conjunction with the recheck pipeline (`checkDecls_recheck_x86_denotes_nat`)**:
`Ix.Kernel.Cached.checkDecls_sound`, `IxCC.Recheck.sound_nat`, `srcRun_to_red` and
`red_to_denotes_nat`, which share only the checked Src program `a.src` and the run `hrun`.
When `checkDecls μ ev ds = .ok env` and `Recheck.run cfg P cert = .ok a` at a `Nat` root
`a.src.roots[i.1]? = some (rootAddr, rootId)` where `Src.run a.src k_src rootId (i.2.map .lit) = .ok (.lit out)`,
on an input `i` the recheck theorems cover (`a.front.Covered cert i`: of exactly the root's declared
parameter count, or any input when the closures step left the certificate's program unchanged),
and for a user-supplied `constSpec` satisfying `hconst` with a related closed root `eRoot`:
1. `env` has a set-theoretic model `Nonempty (EnvModelM V μ env)`;
2. Every valid x86-64 driver `D` (`D.Ok a.backend.encoded.text.size`) never goes wrong on `i`,
   and any terminating x86-64 execution `Lang.run (a.linked D) i k = .ok w` returns `w = some (.nat out)`
   (this is `Recheck.sound_nat`, independent of `env` and `eRoot`);
3. In `env`, `mkNatApp eRoot i.2` reduces via `Ix.Kernel.Rules.Red` to `natLitToConstructor out`;
4. In every `mp : EnvModelM V μ env` in which `mkNatApp eRoot i.2` is readable and graded, it,
   `.lit (.natVal out)` and `natLitToConstructor out` denote the same value `v : V` in
   `Model.ofEnvModelM mp`.

`env` is not derived from `P`, and `eRoot` is not required to be the kernel constant of the
root: the kernel-side conclusions are about whatever term the user related to `rootId`. -/
theorem checkDecls_recheck_x86_denotes_nat {μ : CheckMode} {ev : Evidences md}
    {ds : Array (Declaration md)} {env : Env md}
    {cfg : IxCC.Recheck.Config} {P : IxCC.Src.Program} {cert : IxCC.Recheck.Cert}
    {a : IxCC.Recheck.Artifact}
    {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop}
    (hμ : μ.verifiedChecks = true)
    (hchk : Ix.Kernel.Cached.checkDecls μ ev ds = .ok env)
    (hbasis : natBasisStored env = true)
    (hrec : IxCC.Recheck.run cfg P cert = .ok a)
    (hconst : ∀ ls c e, constSpec ls c e → RelConstStep a.src env constSpec ls c e)
    {i : Nat × List Nat} {k_src : Nat} {rootAddr : IxCC.Ixon.Address} {rootId : IxCC.Src.CId}
    {eRoot : Expr md} {out : Nat}
    (hrootAt : a.src.roots[i.1]? = some (rootAddr, rootId))
    (hcov : a.front.Covered cert i)
    (hty : a.front.tys i.1 = some ({}, .nat))
    (hrootRel : constSpec [] rootId eRoot)
    (hbRoot : eRoot.bvarBound = 0)
    (hnfRoot : eRoot.hasFvar = false)
    (hrun : IxCC.Src.run a.src k_src rootId (i.2.map .lit) = .ok (.lit out)) :
    Nonempty (EnvModelM V μ env) ∧
    Red env 0 (mkNatApp eRoot i.2) (natLitToConstructor out) ∧
    (∀ (D : IxCC.X86.Driver), D.Ok a.backend.encoded.text.size →
      ¬ a.front.GoesWrong i ∧
      (∀ k, ¬ (IxCC.Sem.Lang.run (a.linked D) i k).GoesWrong) ∧
      (∀ k w, IxCC.Sem.Lang.run (a.linked D) i k = .ok w → w = some (.nat out))) ∧
    (∀ (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V) (ea : AnnotTerm),
      denoteMeta mp.base2.acval env φ 0 (mkNatApp eRoot i.2) = some ea →
      Graded V [] ea →
      ∃ v : V,
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (mkNatApp eRoot i.2) v ∧
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
        Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v) := by
  obtain ⟨hmodel, hred, hden⟩ :=
    checkDecls_srcRun_denotes_nat (V := V) hμ hchk hbasis hconst hrootRel hbRoot hnfRoot hrun
  obtain ⟨heval, hobs⟩ :=
    checkedProgram_run_of_srcRun ⟨a.src, a.checked⟩ hrootAt hrun
  refine ⟨hmodel, hred, ?_, hden⟩
  intro D hD
  obtain ⟨_, _, hngw, hsafe, hval⟩ := IxCC.Recheck.sound_nat hrec D hD hcov hty heval hobs
  exact ⟨hngw, hsafe, hval⟩

/-- **Conjunction with the byte-level claim verifier (`checkDecls_verifyBytes_immortal_denotes_nat`)**:
`IxCC.CompileClaim.verifyBytes_immortal_sound` (under `.immortal` policy), `checkDecls_sound`, and,
for every user-supplied `constSpec` satisfying `hconst` and every related closed root `eRoot`,
the conclusions of `checkDecls_recheck_x86_denotes_nat` for the artifact `a` the verifier
rechecked. With the claim's covered conjunct (every argument list of the claim's arity is an
input of root 0 the recheck theorems cover), a consumer discharges the `a.front.Covered cert i`
premise for the claimed inputs `(0, ns)` from this theorem itself. This is not adequacy for the claim: `ds`/`env` occur only in `hchk` and `hbasis`
and `envBytes` only in `hver`, so `env` is not the claim's environment; `eRoot` is not the
kernel constant of `claim.target`; and the root index `i` is not tied to `claim.target`.
Like `verifyBytes_immortal_sound`, it rests on the three standard axioms only (every address
IxCC computes is pure BLAKE3). -/
theorem checkDecls_verifyBytes_immortal_denotes_nat {μ : CheckMode} {ev : Evidences md}
    {ds : Array (Declaration md)} {env : Env md}
    {cfg : IxCC.Recheck.Config} {envBytes : ByteArray} {equations : Lean.Json}
    {claim : IxCC.CompileClaim} {certText : String}
    (hμ : μ.verifiedChecks = true)
    (hchk : Ix.Kernel.Cached.checkDecls μ ev ds = .ok env)
    (hbasis : natBasisStored env = true)
    (hpol : claim.policy = .immortal)
    (hver : IxCC.CompileClaim.verifyBytes cfg envBytes equations claim certText true = true) :
    Nonempty (EnvModelM V μ env) ∧
    ∃ (inp : IxCC.Recheck.Input) (cert : IxCC.Recheck.Cert) (a : IxCC.Recheck.Artifact)
      (rootId : IxCC.Src.CId) (root : IxCC.Recheck.Root) (sig : IxCC.Rt.Sig) (ty : IxCC.Rt.FoTy),
      claim.WellFormed ∧
      IxCC.Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
      IxCC.Ixon.V3.Tc.checkEnv inp.env = .ok () ∧
      inp.env.root = claim.env ∧
      inp.env.bindingAddress = claim.roleTable ∧
      inp.program.roots.head? = some (claim.target, rootId) ∧
      IxCC.Recheck.run cfg inp.program cert = .ok a ∧
      a.roots.head? = some root ∧
      root.ty = some (sig, ty) ∧
      IxCC.Ixon.Address.blake3Pure a.object = claim.elfHash ∧
      (∀ ns : List Nat, ns.length = claim.abiArity → a.front.Covered cert (0, ns)) ∧
      ∀ {constSpec : IxCC.Src.Levels → IxCC.Src.CId → Expr md → Prop},
        (∀ ls c e, constSpec ls c e → RelConstStep a.src env constSpec ls c e) →
        ∀ {i : Nat × List Nat} {k_src : Nat} {rootAddr : IxCC.Ixon.Address} {rootCId : IxCC.Src.CId}
          {eRoot : Expr md} {out : Nat},
          a.src.roots[i.1]? = some (rootAddr, rootCId) →
          a.front.Covered cert i →
          a.front.tys i.1 = some ({}, .nat) →
          constSpec [] rootCId eRoot →
          eRoot.bvarBound = 0 →
          eRoot.hasFvar = false →
          IxCC.Src.run a.src k_src rootCId (i.2.map .lit) = .ok (.lit out) →
          Red env 0 (mkNatApp eRoot i.2) (natLitToConstructor out) ∧
          (∀ (D : IxCC.X86.Driver), D.Ok a.backend.encoded.text.size →
            ¬ a.front.GoesWrong i ∧
            (∀ k, ¬ (IxCC.Sem.Lang.run (a.linked D) i k).GoesWrong) ∧
            (∀ k w, IxCC.Sem.Lang.run (a.linked D) i k = .ok w → w = some (.nat out))) ∧
          (∀ (mp : EnvModelM V μ env) (φ : LevelParam → Nat) (ρ : Nat → V) (ea : AnnotTerm),
            denoteMeta mp.base2.acval env φ 0 (mkNatApp eRoot i.2) = some ea →
            Graded V [] ea →
            ∃ v : V,
              Denotes (Model.ofEnvModelM mp).cval env φ ρ (mkNatApp eRoot i.2) v ∧
              Denotes (Model.ofEnvModelM mp).cval env φ ρ (.lit (.natVal out)) v ∧
              Denotes (Model.ofEnvModelM mp).cval env φ ρ (natLitToConstructor out) v) := by
  have hmodel : Nonempty (EnvModelM V μ env) :=
    Ix.Kernel.Cached.checkDecls_sound (V := V) hμ hchk
  obtain ⟨inp, cert, a, rootId, root, sig, ty, hwf, _, hdec, htc, _, _, henv, hrole, hhead, _,
    hrec, _, _, hahead, _, hty, _, _, hhash, hcovs, _⟩ :=
    IxCC.CompileClaim.verifyBytes_immortal_sound hpol hver
  refine ⟨hmodel, inp, cert, a, rootId, root, sig, ty, hwf, hdec, htc rfl, henv, hrole, hhead, hrec,
    hahead, hty, hhash, hcovs, ?_⟩
  intro constSpec hconst i k_src rootAddr rootCId eRoot out hrootAt hcov htyAt hrootRel hbRoot hnfRoot hrun
  obtain ⟨_, hred, hx86, hden⟩ :=
    checkDecls_recheck_x86_denotes_nat (V := V) hμ hchk hbasis hrec hconst hrootAt hcov htyAt hrootRel hbRoot hnfRoot hrun
  exact ⟨hred, hx86, hden⟩

end IxKernelBridge
