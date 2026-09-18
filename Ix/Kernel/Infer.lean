/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Claims
import Ix.Kernel.Certified.Quotient.Reading
import Ix.Kernel.Level

/-! # Reduction, inference, and conversion

The reference algorithms of the kernel, each returning its result together
with the semantic claim that justifies it (`Ix.Kernel.Claims`); the claims are
erased at run time. Every function is bounded by explicit fuel; exhaustion
declines (`none`) or, for `whnf`, stops reducing.

* `step` performs one head reduction: typed beta (the argument is inferred and
  its type converted to the lambda's domain), delta on definitions with
  bodies, and zeta on lets.
* `whnf` iterates `step`.
* `inferA` infers the type of an annotated term and validates every binder
  annotation against the inferred codomain sort.
* `isDefEq` decides conversion by reducing both sides and comparing
  structurally, with eta for functions and proof irrelevance as fallbacks.

Annotations never steer reduction: `step` and `whnf` read no `PropWhen`. -/

namespace Ix.Kernel

open Model Model.SetTheory Certified

universe u v

variable {β : Type u} [DecidableEq β]

/-- An inferred type with its typing claim. -/
structure Typed (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  type : AExpr β
  claim : TypingClaim.{u,v} entries Γ e type

/-- A reduct with its reduction claim. -/
structure Reduced (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  result : AExpr β
  claim : ReductionClaim.{u,v} entries Γ e result

/-- A conversion verdict. -/
structure Conv (entries : Environment β) (Γ : Context β) (a b : AExpr β) : Type u where
  down : ConvClaim.{u,v} entries Γ a b

/-- A term typed at a sort. -/
structure TypedSort (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  level : VLevel
  claim : TypingClaim.{u,v} entries Γ e (.sort level)

/-- A term typed at a dependent function type. -/
structure TypedPi (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  condition : PropWhen
  domain : AExpr β
  codomain : AExpr β
  claim : TypingClaim.{u,v} entries Γ e (.forallE condition domain codomain)

variable {entries : Environment β} {Γ : Context β}

/-- Read a sort off an already reduced type. -/
def sortOf {e T : AExpr β} (r : Reduced.{u,v} entries Γ T) (he : TypingClaim.{u,v} entries Γ e T) :
    Option (TypedSort.{u,v} entries Γ e) :=
  match r with
  | ⟨T', hr⟩ =>
    match T' with
    | .sort l => some ⟨l, he.convF (FormedClaim.sort l) (ConvClaim.ofReduction hr)⟩
    | _ => none

/-- Read a dependent function type off an already reduced type. -/
def piOf {e T : AExpr β} (r : Reduced.{u,v} entries Γ T) (he : TypingClaim.{u,v} entries Γ e T) :
    Option (TypedPi.{u,v} entries Γ e) :=
  match r with
  | ⟨T', hr⟩ =>
    match T' with
    | .forallE p D B =>
      some ⟨p, D, B, he.convF (hr.formed he.formedType) (ConvClaim.ofReduction hr)⟩
    | _ => none

/-- A typed nested lambda applied to arguments by typed beta steps. -/
structure Applied (entries : Environment β) (Γ : Context β) (f : AExpr β) (args : List (AExpr β)) :
    Type u where
  result : AExpr β
  type : AExpr β
  typed : TypingClaim.{u,v} entries Γ result type
  conv : ConversionClaim.{u,v} entries Γ (AExpr.appN f args) result

/-- The head of an application spine and its arguments, outermost first. -/
def spine : AExpr β → List (AExpr β) → AExpr β × List (AExpr β)
  | .app f a, acc => spine f (a :: acc)
  | e, acc => (e, acc)

/-- The recursor arities published as a fact, if any. -/
def recursorInfo : List (ConstantFact β) → Option (Nat × Nat × Nat × List (ConstRef β × Nat))
  | [] => none
  | .recursor np nm ni rules :: _ => some (np, nm, ni, rules)
  | _ :: rest => recursorInfo rest

/-- The structure arities published as a fact, if any. -/
def structureInfo : List (ConstantFact β) → Option (Nat × Nat)
  | [] => none
  | .«structure» np nf :: _ => some (np, nf)
  | _ :: rest => structureInfo rest

/-- The rule position and field count of a constructor. -/
def ruleIndex (rules : List (ConstRef β × Nat)) (c : ConstRef β) : Option (Nat × Nat) :=
  (rules.zipIdx.find? fun rule => rule.1.1 == c).map fun rule => (rule.2, rule.1.2)

/-- The natural-number fact of an entry, with its membership. -/
def findNatural : (facts : List (ConstantFact β)) →
    Option { p : ConstRef β × ConstRef β // ConstantFact.natural p.1 p.2 ∈ facts }
  | [] => none
  | .natural zero succ :: _ => some ⟨(zero, succ), List.mem_cons_self ..⟩
  | _ :: rest => (findNatural rest).map fun ⟨p, h⟩ => ⟨p, List.mem_cons_of_mem _ h⟩

/-- One unfolding of a literal into constructor form, with its conversion and
the formedness of the result. -/
structure LitUnfold (entries : Environment β) (Γ : Context β) (f : ConstRef β) (n : Nat) :
    Type u where
  result : AExpr β
  conv : ConvClaim.{u,v} entries Γ (.natLit f n) result
  formed : FormedClaim.{u,v} entries Γ result

def unfoldLit (entries : Environment β) (Γ : Context β) (f : ConstRef β) (n : Nat) :
    Option (LitUnfold.{u,v} entries Γ f n) :=
  match h : entries f with
  | some entry =>
    match findNatural entry.facts with
    | some ⟨(zero, succ), hf⟩ =>
      if hn : entry.universes = 0 then
        match n with
        | 0 => some ⟨.const zero [], ConvClaim.natZero h hf hn, FormedClaim.const _ _⟩
        | n + 1 => some ⟨.app (.const succ []) (.natLit f n), ConvClaim.natSucc h hf hn n,
            FormedClaim.natSucc h hf hn n⟩
      else none
    | none => none
  | none => none

/-- The quotient rule an entry's facts yield: the lift, with its equality
family, or the eliminator. -/
def quotientRule (facts : List (ConstantFact β)) : Option (Option (ConstRef β)) :=
  facts.findSome? fun
    | .quotientLift eq => some (some eq)
    | .quotient .ind => some none
    | _ => none

mutual

/-- One head reduction step through the application spine. -/
def step : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    Option (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => none
  | fuel + 1, entries, Γ, e =>
    match e with
    | .app f a =>
      match f with
      | .lam p D b => do
        let ⟨A', ha⟩ ← inferA fuel entries Γ a
        let ⟨hc⟩ ← isDefEq fuel entries Γ A' D
        return ⟨b.inst a, ReductionClaim.beta (p := p) ha hc⟩
      | f =>
        match iota fuel entries Γ (.app f a) with
        | some r => some r
        | none =>
          match quotIota fuel entries Γ (.app f a) with
          | some r => some r
          | none => do
            let ⟨f', hf⟩ ← step fuel entries Γ f
            return ⟨.app f' a, hf.appHead⟩
    | .const r ls =>
      match h : entries r with
      | some entry =>
        match hb : entry.body with
        | some body =>
          if hn : ls.length = entry.universes then
            some ⟨body.instL ls, ReductionClaim.delta h hb hn⟩
          else none
        | none => none
      | none => none
    | .letE _ v b => some ⟨b.inst v, ReductionClaim.zeta⟩
    | .proj r i x => projIota fuel entries Γ r i x
    | _ => none

/-- Apply a typed nested lambda to arguments by typed beta steps, reducing
nothing else. -/
def applyTyped : Nat → (entries : Environment β) → (Γ : Context β) → (f F : AExpr β) →
    TypingClaim.{u,v} entries Γ f F → (args : List (AExpr β)) →
      Option (Applied.{u,v} entries Γ f args)
  | _, _, _, f, F, hf, [] => some ⟨f, F, hf, ConversionClaim.refl _⟩
  | 0, _, _, _, _, _, _ :: _ => none
  | fuel + 1, entries, Γ, f, F, hf, a :: args =>
    match f, F, hf with
    | .lam p D b, .forallE p' D' B, hf =>
      if h : p = p' ∧ D = D' then do
        let ⟨A', ha⟩ ← inferA fuel entries Γ a
        let ⟨hc⟩ ← isDefEq fuel entries Γ A' D
        have hf' : TypingClaim.{u,v} entries Γ (.lam p D b) (.forallE p D B) := by
          obtain ⟨rfl, rfl⟩ := h
          exact hf
        have haD : TypingClaim.{u,v} entries Γ a D := ha.convF hf'.formedType.domain hc
        let rest ← applyTyped fuel entries Γ (b.inst a) (B.inst a) (TypingClaim.betaResult hf' haD) args
        return ⟨rest.result, rest.type, rest.typed,
          (ConversionClaim.appN (ConversionClaim.beta hf' haD) args).trans rest.conv⟩
      else none
    | _, _, _ => none

/-- Iota: a recursor applied to a constructor reduces through the published
rule. The target is converted to the typed instance of the rule's left side
(which checks the constructor's parameters and the indices against the
recursor's), and the rule's equation takes it to the typed instance of the
right side. A literal major is unfolded one step first. K-like reduction: if
the major is not a constructor application but the recursor has a single rule
without fields, the constructor is synthesized from the recursor's parameters;
the conversion of the major to it is then proof irrelevance, which holds
exactly when the major's type converts to the constructor's. -/
def iota : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    Option (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => none
  | fuel + 1, entries, Γ, e =>
    match spine e [] with
    | (.const r ls, args) =>
      match h : entries r with
      | some entry =>
        match recursorInfo entry.facts with
        | some (np, nm, ni, rules) =>
          let majorIdx := np + 1 + nm + ni
          if args.length = majorIdx + 1 then
            match args[majorIdx]? with
            | some major =>
              let major' := (whnf fuel entries Γ major).result
              let major' := match major' with
                | .natLit f n => match unfoldLit.{u,v} entries Γ f n with
                  | some u => u.result
                  | none => major'
                | _ => major'
              let candidate : Option (Nat × Nat × List (AExpr β)) :=
                match spine major' [] with
                | (.const c _, cargs) => (ruleIndex rules c).map fun (j, nf) => (j, nf, cargs)
                | _ =>
                  match rules with
                  | [(_, 0)] => some (0, 0, args.take np)
                  | _ => none
              match candidate with
              | some (j, nf, cargs) =>
                if cargs.length = np + nf then
                  let bargs := args.take (np + 1 + nm) ++ cargs.drop np
                  match hj : entry.equations[j]?, hf1 : entry.facts[1 + 2 * j]?,
                      hf2 : entry.facts[2 + 2 * j]? with
                  | some law, some (.typed lhs T), some (.typed rhs T') =>
                    if hlaw : law.lhs = lhs ∧ law.rhs = rhs then
                      if hn : ls.length = entry.universes then do
                        let appL ← applyTyped fuel entries Γ (lhs.instL ls) (T.instL ls)
                          (TypingClaim.fact h (List.mem_of_getElem? hf1) hn) bargs
                        let appR ← applyTyped fuel entries Γ (rhs.instL ls) (T'.instL ls)
                          (TypingClaim.fact h (List.mem_of_getElem? hf2) hn) bargs
                        let ⟨hc⟩ ← isDefEqCore fuel entries Γ e appL.result
                        have heq : ConversionClaim.{u,v} entries Γ (lhs.instL ls) (rhs.instL ls) := by
                          have := ConversionClaim.equation (Γ := Γ) h (List.mem_of_getElem? hj) hn
                          rwa [hlaw.1, hlaw.2] at this
                        return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
                          (appL.conv.symm.trans ((heq.appN bargs).trans appR.conv)) appR.typed.formed⟩
                      else none
                    else none
                  | _, _, _ => none
                else none
              | none => none
            | none => none
          else none
        | none => none
      | none => none
    | _ => none

/-- Reduce through a rule whose endpoints are typed by inference: the target is
converted to the typed instance of the left side, and the rule's conversion
takes it to the typed instance of the right side. -/
def reduceByRule : Nat → (entries : Environment β) → (Γ : Context β) → (e lhs rhs : AExpr β) →
    ConversionClaim.{u,v} entries Γ lhs rhs → (bargs : List (AExpr β)) →
      Option (Reduced.{u,v} entries Γ e)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, entries, Γ, e, lhs, rhs, heq, bargs => do
    let ⟨TL, hL⟩ ← inferA fuel entries Γ lhs
    let ⟨TR, hR⟩ ← inferA fuel entries Γ rhs
    let appL ← applyTyped fuel entries Γ lhs TL hL bargs
    let appR ← applyTyped fuel entries Γ rhs TR hR bargs
    let ⟨hc⟩ ← isDefEqCore fuel entries Γ e appL.result
    return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
      (appL.conv.symm.trans ((heq.appN bargs).trans appR.conv)) appR.typed.formed⟩

/-- Quotient computation: the lift or the eliminator applied to a constructor
application reduces through its rule, which is derived from the published
facts. The lift's rule needs the former, the constructor, the lift itself, and
the equality family to be the admitted ones; the eliminator's rule holds
outright, since both sides are proofs. The former is read off the entry's
type as the reference other than the known ones. -/
def quotIota : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    Option (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => none
  | fuel + 1, entries, Γ, e =>
    match spine e [] with
    | (.const r ls, args) =>
      match entries r with
      | some entry =>
        match quotientRule entry.facts with
        | some role =>
          let arity := if role.isSome then 6 else 5
          if args.length = arity then
            match args[arity - 1]? with
            | some major =>
              match spine (whnf fuel entries Γ major).result [] with
              | (.const c _, [_, _, a]) =>
                let bargs := args.take (arity - 1) ++ [a]
                match role with
                | some eq =>
                  match entry.type.references.eraseDups.filter (· ≠ eq) with
                  | [q] =>
                    let refs : Certified.Quotient.Refs β := ⟨eq, q, c, r, r⟩
                    if hl : Certified.Quotient.HasLift entries refs then
                      if hq : Certified.Quotient.HasFormer entries refs then
                        if hc : Certified.Quotient.HasCtor entries refs then
                          if hE : Certified.Quotient.EqInterface entries eq then
                            if hn : ls.length = 2 then
                              reduceByRule fuel entries Γ e
                                ((Certified.Quotient.liftRuleLhs refs).instL ls)
                                ((Certified.Quotient.liftRuleRhs refs).instL ls)
                                (Certified.Quotient.liftRule_claim Γ hq hc hl hE hn) bargs
                            else none
                          else none
                        else none
                      else none
                    else none
                  | _ => none
                | none =>
                  match entry.type.references.eraseDups.filter (· ≠ c) with
                  | [q] =>
                    let refs : Certified.Quotient.Refs β := ⟨q, q, c, c, r⟩
                    reduceByRule fuel entries Γ e
                      ((Certified.Quotient.indRuleLhs refs).instL ls)
                      ((Certified.Quotient.indRuleRhs refs).instL ls)
                      (Certified.Quotient.indRule_claim refs Γ ls) bargs
                  | _ => none
              | _ => none
            | none => none
          else none
        | none => none
      | none => none
    | _ => none

/-- Projection iota: a projection of a constructor application reduces
through the structure's published iota rule, whose endpoints are typed by
inference. -/
def projIota : Nat → (entries : Environment β) → (Γ : Context β) → (r : ConstRef β) → (i : Nat) →
    (x : AExpr β) → Option (Reduced.{u,v} entries Γ (.proj r i x))
  | 0, _, _, _, _, _ => none
  | fuel + 1, entries, Γ, r, i, x =>
    match whnf fuel entries Γ x with
    | ⟨x', hx⟩ =>
      match spine x' [] with
      | (.const (.ctor s 0 0) ls, cargs) =>
        match h : entries r with
        | some entry =>
          match structureInfo entry.facts with
          | some (np, nf) =>
            if r = .member s 0 ∧ cargs.length = np + nf ∧ i < nf then
              match hq : entry.equations[1 + i]? with
              | some law =>
                if hn : ls.length = entry.universes then do
                  let ⟨TL, hL⟩ ← inferA fuel entries Γ (law.lhs.instL ls)
                  let ⟨TR, hR⟩ ← inferA fuel entries Γ (law.rhs.instL ls)
                  let appL ← applyTyped fuel entries Γ (law.lhs.instL ls) TL hL cargs
                  let appR ← applyTyped fuel entries Γ (law.rhs.instL ls) TR hR cargs
                  if hl : appL.result = .proj r i x' then
                    have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                      ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                    have hc : ConvClaim.{u,v} entries Γ (.proj r i x) appL.result := by
                      rw [hl]
                      exact ConvClaim.proj (ConvClaim.ofReduction hx)
                    return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
                      (appL.conv.symm.trans ((heq.appN cargs).trans appR.conv)) appR.typed.formed⟩
                  else none
                else none
              | none => none
            else none
          | none => none
        | none => none
      | _ => none

/-- Structure eta: a constructor application of a structure converts to any
term of the structure's type whose projections convert to the fields, through
the published eta rule, whose endpoints are typed by inference. -/
def etaStruct : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    Option (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => none
  | fuel + 1, entries, Γ, a, b =>
    match spine a [] with
    | (.const (.ctor s 0 0) ls, args) =>
      match h : entries (.member s 0) with
      | some entry =>
        match structureInfo entry.facts with
        | some (np, nf) =>
          if args.length = np + nf then
            let bargs := args.take np ++ [b]
            match hq : entry.equations[(0 : Nat)]? with
            | some law =>
              if hn : ls.length = entry.universes then do
                let ⟨TL, hL⟩ ← inferA fuel entries Γ (law.lhs.instL ls)
                let ⟨TR, hR⟩ ← inferA fuel entries Γ (law.rhs.instL ls)
                let appL ← applyTyped fuel entries Γ (law.lhs.instL ls) TL hL bargs
                let appR ← applyTyped fuel entries Γ (law.rhs.instL ls) TR hR bargs
                if hb : appR.result = b then do
                  let ⟨hc⟩ ← isDefEqCore fuel entries Γ a appL.result
                  have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                    ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                  have hr : ConversionClaim.{u,v} entries Γ (AExpr.appN (law.rhs.instL ls) bargs) b := by
                    rw [← hb]
                    exact appR.conv
                  return ⟨hc.trans appL.typed.formed
                    (ConvClaim.ofConversion (appL.conv.symm.trans ((heq.appN bargs).trans hr)))⟩
                else none
              else none
            | none => none
          else none
        | none => none
      | none => none
    | _ => none

/-- Proof irrelevance: both sides inhabit a proposition. -/
def proofIrrelevance : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    Option (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => none
  | fuel + 1, entries, Γ, a, b => do
    let ⟨A, haA⟩ ← inferA fuel entries Γ a
    let ⟨SA, hSA⟩ ← inferA fuel entries Γ A
    let ⟨l, hA⟩ ← sortOf (whnf fuel entries Γ SA) hSA
    if hl : levelIsZero l then do
      let ⟨B, hbB⟩ ← inferA fuel entries Γ b
      let ⟨hBA⟩ ← isDefEq fuel entries Γ B A
      return ⟨ConvClaim.proofIrrel (hA.sortEquiv (levelIsZero_sound hl)) haA (hbB.convF haA.formedType hBA)⟩
    else none

/-- Weak head normalization, as far as the fuel allows. -/
def whnf : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    Reduced.{u,v} entries Γ e
  | 0, _, _, e => ⟨e, ReductionClaim.refl e⟩
  | fuel + 1, entries, Γ, e =>
    match step fuel entries Γ e with
    | some ⟨e', h⟩ =>
      match whnf fuel entries Γ e' with
      | ⟨e'', h'⟩ => ⟨e'', h.trans h'⟩
    | none => ⟨e, ReductionClaim.refl e⟩

/-- Type inference on annotated terms, validating every binder annotation. -/
def inferA : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    Option (Typed.{u,v} entries Γ e)
  | 0, _, _, _ => none
  | fuel + 1, entries, Γ, e =>
    match e with
    | .bvar i =>
      match h : Γ[i]? with
      | some A => some ⟨A, TypingClaim.bvar h⟩
      | none => none
    | .sort l => some ⟨.sort (.succ l), TypingClaim.sort l⟩
    | .const r ls =>
      match h : entries r with
      | some entry =>
        if hn : ls.length = entry.universes then
          some ⟨entry.type.instL ls, TypingClaim.const h hn⟩
        else none
      | none => none
    | .app f a => do
      let ⟨T, hf⟩ ← inferA fuel entries Γ f
      let ⟨p, D, B, hf'⟩ ← piOf (whnf fuel entries Γ T) hf
      let ⟨A', ha⟩ ← inferA fuel entries Γ a
      let ⟨hc⟩ ← isDefEq fuel entries Γ A' D
      return ⟨B.inst a, TypingClaim.app (p := p) hf' (ha.convF hf'.formedType.domain hc)⟩
    | .lam p D b => do
      let ⟨S, hS⟩ ← inferA fuel entries Γ D
      let ⟨_, hD⟩ ← sortOf (whnf fuel entries Γ S) hS
      let ⟨B, hb⟩ ← inferA fuel entries (Γ.push D) b
      let ⟨SB, hSB⟩ ← inferA fuel entries (Γ.push D) B
      let ⟨lB, hB⟩ ← sortOf (whnf fuel entries (Γ.push D) SB) hSB
      if hp : p = zeroCondition lB then
        return ⟨.forallE p D B, TypingClaim.lam hD hB hb hp⟩
      else none
    | .forallE p D B => do
      let ⟨S, hS⟩ ← inferA fuel entries Γ D
      let ⟨lD, hD⟩ ← sortOf (whnf fuel entries Γ S) hS
      let ⟨SB, hSB⟩ ← inferA fuel entries (Γ.push D) B
      let ⟨lB, hB⟩ ← sortOf (whnf fuel entries (Γ.push D) SB) hSB
      if hp : p = zeroCondition lB then
        return ⟨.sort (.imax lD lB), TypingClaim.forallE hD hB hp⟩
      else none
    | .letE t v b => do
      let ⟨S, hS⟩ ← inferA fuel entries Γ t
      let ⟨l, ht⟩ ← sortOf (whnf fuel entries Γ S) hS
      let ⟨A', hv⟩ ← inferA fuel entries Γ v
      let ⟨hc⟩ ← isDefEq fuel entries Γ A' t
      let ⟨B, hb⟩ ← inferA fuel entries (Γ.push t) b
      return ⟨B.inst v, TypingClaim.letE (l := l) ht (hv.convF ht.formed hc) hb⟩
    | .proj r i x => do
      let ⟨T, _⟩ ← inferA fuel entries Γ x
      match spine (whnf fuel entries Γ T).result [] with
      | (.const r' ls, params) =>
        if r' = r then
          match h : entries r with
          | some entry =>
            match structureInfo entry.facts with
            | some (np, nf) =>
              if params.length = np ∧ i < nf then
                match hf : entry.facts[1 + i]? with
                | some (.typed pj pjT) =>
                  if hn : ls.length = entry.universes then do
                    let app ← applyTyped fuel entries Γ (pj.instL ls) (pjT.instL ls)
                      (TypingClaim.fact h (List.mem_of_getElem? hf) hn) (params ++ [x])
                    if hres : app.result = .proj r i x then
                      return ⟨app.type, hres ▸ app.typed⟩
                    else none
                  else none
                | _ => none
              else none
            | none => none
          | none => none
        else none
      | _ => none
    | .natLit f n =>
      match h : entries f with
      | some entry =>
        match findNatural entry.facts with
        | some ⟨(_, _), hf⟩ =>
          if hn : entry.universes = 0 then some ⟨.const f [], TypingClaim.natLit h hf hn n⟩ else none
        | none => none
      | none => none

/-- Structural comparison of two reduced terms, with eta and proof irrelevance. -/
def isDefEqCore : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    Option (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => none
  | fuel + 1, entries, Γ, a, b =>
    if h : a = b then some ⟨h ▸ ConvClaim.refl a⟩ else
    let structural : Option (Conv.{u,v} entries Γ a b) :=
      match a, b with
      | .sort l, .sort l' =>
        if he : levelEquiv l l' then some ⟨ConvClaim.sort (levelEquiv_sound he)⟩ else none
      | .const r ls, .const r' ls' =>
        if hr : r = r' then
          if hl : levelsEquiv ls ls' then
            some ⟨hr ▸ ConvClaim.const (levelsEquiv_sound hl)⟩
          else none
        else none
      | .bvar i, .bvar j => if hij : i = j then some ⟨hij ▸ ConvClaim.refl _⟩ else none
      | .natLit f n, .natLit g m => if hnm : n = m then some ⟨hnm ▸ ConvClaim.natLit f g n⟩ else none
      | .natLit f n, b => do
        let u ← unfoldLit entries Γ f n
        let ⟨hc⟩ ← isDefEqCore fuel entries Γ u.result b
        return ⟨u.conv.trans u.formed hc⟩
      | a, .natLit f n => do
        let u ← unfoldLit entries Γ f n
        let ⟨hc⟩ ← isDefEqCore fuel entries Γ a u.result
        return ⟨hc.trans u.formed u.conv.symm⟩
      | .app f x, .app g y => do
        let ⟨hf⟩ ← isDefEq fuel entries Γ f g
        let ⟨hx⟩ ← isDefEq fuel entries Γ x y
        return ⟨ConvClaim.app hf hx⟩
      | .lam p D e, .lam p' D' e' =>
        if hp : p = p' then do
          let ⟨hD⟩ ← isDefEq fuel entries Γ D D'
          let ⟨he⟩ ← isDefEq fuel entries (Γ.push D) e e'
          return ⟨hp ▸ ConvClaim.lam hD he⟩
        else none
      | .forallE p D B, .forallE p' D' B' =>
        if hp : p = p' then do
          let ⟨hD⟩ ← isDefEq fuel entries Γ D D'
          let ⟨hB⟩ ← isDefEq fuel entries (Γ.push D) B B'
          return ⟨hp ▸ ConvClaim.forallE hD hB⟩
        else none
      | .proj r i x, .proj r' i' y =>
        if hr : r = r' then
          if hi : i = i' then do
            let ⟨hx⟩ ← isDefEq fuel entries Γ x y
            return ⟨hr ▸ hi ▸ ConvClaim.proj hx⟩
          else none
        else none
      | .lam p D e, g => do
        let ⟨T, hg⟩ ← inferA fuel entries Γ g
        let ⟨p'', D'', _, hg'⟩ ← piOf (whnf fuel entries Γ T) hg
        if hp : p'' = p then do
          let ⟨hD⟩ ← isDefEq fuel entries Γ D'' D
          let ⟨he⟩ ← isDefEq fuel entries (Γ.push D) e (.app (g.liftN 1) (.bvar 0))
          return ⟨ConvClaim.eta (hp ▸ hg') hD he⟩
        else none
      | g, .lam p D e => do
        let ⟨T, hg⟩ ← inferA fuel entries Γ g
        let ⟨p'', D'', _, hg'⟩ ← piOf (whnf fuel entries Γ T) hg
        if hp : p'' = p then do
          let ⟨hD⟩ ← isDefEq fuel entries Γ D'' D
          let ⟨he⟩ ← isDefEq fuel entries (Γ.push D) e (.app (g.liftN 1) (.bvar 0))
          return ⟨(ConvClaim.eta (hp ▸ hg') hD he).symm⟩
        else none
      | _, _ => none
    match structural with
    | some c => some c
    | none =>
      match etaStruct fuel entries Γ a b with
      | some c => some c
      | none =>
        match etaStruct fuel entries Γ b a with
        | some ⟨c⟩ => some ⟨c.symm⟩
        | none => proofIrrelevance fuel entries Γ a b

/-- Conversion: reduce both sides, then compare. -/
def isDefEq : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    Option (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => none
  | fuel + 1, entries, Γ, a, b =>
    if h : a = b then some ⟨h ▸ ConvClaim.refl a⟩ else
    match whnf fuel entries Γ a, whnf fuel entries Γ b with
    | ⟨a', ha⟩, ⟨b', hb⟩ => do
      let ⟨hc⟩ ← isDefEqCore fuel entries Γ a' b'
      return ⟨ConvClaim.ofReductions ha hb hc⟩

end

end Ix.Kernel
