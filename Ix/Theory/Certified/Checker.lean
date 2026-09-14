/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Judgment
import Ix.Theory.Certified.LevelEq

/-!
# Executable validation of dependent-function certificates

Witnesses are untrusted trees of rule choices and intermediate syntax. The
validator checks their exact endpoints, scopes, annotations, and dependency
lookups. Every recursive success constructs its semantic proof through the
rule theorems; no semantic proof is an input. Exhausted fuel and unsupported
syntax fail. Proof fields in successful results are erased during execution.
-/

namespace Ix.Theory.Certified

open Model

universe u v

/-- An erased result at the data universe of the checked syntax. This permits
the proof-producing validator to compose with declaration readers. -/
structure CheckedClaim (claim : Prop) : Type u where
  down : claim

mutual
inductive TypingWitness (β : Type u) where
  | sort
  | bvar
  | const
  | app (condition : PropWhen) (domain codomain : AExpr β)
      (fn arg : TypingWitness β)
  | lam (domainLevel codomainLevel : VLevel) (codomain : AExpr β)
      (domainType codomainType body : TypingWitness β)
  | forallE (domainLevel codomainLevel : VLevel)
      (domainType codomainType : TypingWitness β)
  | conv (intermediate : AExpr β) (targetLevel : VLevel)
      (term target : TypingWitness β) (conversion : ConversionWitness β)
  | fact (ref : ConstRef β) (index : Nat) (levels : List VLevel)
  | natLit (ref : ConstRef β) (index : Nat)
  | betaResult (condition : PropWhen) (domain body argument codomain : AExpr β)
      (lambda argumentWitness : TypingWitness β)

inductive ConversionWitness (β : Type u) where
  | refl
  | symm (proof : ConversionWitness β)
  | trans (middle : AExpr β) (left right : ConversionWitness β)
  | app (fn arg : ConversionWitness β)
  | lam (domainLevel : VLevel) (domainType : TypingWitness β)
      (domain body : ConversionWitness β)
  | forallE (domainLevel : VLevel) (domainType : TypingWitness β)
      (domain body : ConversionWitness β)
  | beta (lambdaType : AExpr β) (lambda arg : TypingWitness β)
  | eta (codomain : AExpr β) (fn : TypingWitness β)
  | proofIrrel (type : AExpr β) (typeProof left right : TypingWitness β)
  | delta
  | sort
  | equation (ref : ConstRef β) (index : Nat) (levels : List VLevel)
  | natLiteral (ref : ConstRef β) (index : Nat)
  | proj (major : ConversionWitness β)
end

variable {β : Type u} [DecidableEq β]

mutual
def verifyType (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e A : AExpr β) (witness : TypingWitness β) :
    Option (CheckedClaim.{u} (TypingClaim.{u,v} entries Γ e A)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if e.Scope n Γ.length ∧ A.Scope n Γ.length then
      match e, witness with
      | .sort l, .sort =>
        if h : A = .sort (.succ l) then
          some ⟨by subst A; exact TypingClaim.sort l⟩
        else none
      | .bvar i, .bvar =>
        match h : Γ[i]? with
        | none => none
        | some B =>
          if hA : A = B then some ⟨by subst A; exact TypingClaim.bvar h⟩ else none
      | .const r ls, .const =>
        match h : entries r with
        | none => none
        | some entry =>
          if hn : ls.length = entry.universes then
            if hA : A = entry.type.instL ls then
              some ⟨by subst A; exact TypingClaim.const h hn⟩
            else none
          else none
      | .app f a, .app p D B wf wa =>
        if hA : A = B.inst a then do
          let hf ← verifyType fuel n entries Γ f (.forallE p D B) wf
          let ha ← verifyType fuel n entries Γ a D wa
          return ⟨by subst A; exact TypingClaim.app hf.down ha.down⟩
        else none
      | .lam p D body, .lam lD lB B wD wB wb =>
        if hp : p = zeroCondition lB then
          if hA : A = .forallE p D B then do
            let hD ← verifyType fuel n entries Γ D (.sort lD) wD
            let hB ← verifyType fuel n entries (Γ.push D) B (.sort lB) wB
            let hb ← verifyType fuel n entries (Γ.push D) body B wb
            return ⟨by subst A; exact TypingClaim.lam hD.down hB.down hb.down hp⟩
          else none
        else none
      | .forallE p D B, .forallE lD lB wD wB =>
        if hp : p = zeroCondition lB then
          if hA : A = .sort (.imax lD lB) then do
            let hD ← verifyType fuel n entries Γ D (.sort lD) wD
            let hB ← verifyType fuel n entries (Γ.push D) B (.sort lB) wB
            return ⟨by subst A; exact TypingClaim.forallE hD.down hB.down hp⟩
          else none
        else none
      | e, .conv B lA we wA wc => do
        let he ← verifyType fuel n entries Γ e B we
        let hA ← verifyType fuel n entries Γ A (.sort lA) wA
        let hc ← verifyConversion fuel n entries Γ B A wc
        return ⟨TypingClaim.conv he.down hA.down hc.down⟩
      | e, .fact r index ls =>
        match hr : entries r with
        | none => none
        | some entry =>
          match hf : entry.facts[index]? with
          | some (.typed value type) =>
            if hn : ls.length = entry.universes then
              if ∀ l ∈ ls, l.WF n then
                if he : e = value.instL ls then
                  if hA : A = type.instL ls then
                    some ⟨by subst e A; exact TypingClaim.fact hr (List.mem_of_getElem? hf) hn⟩
                  else none
                else none
              else none
            else none
          | _ => none
      | .natLit value, .natLit r index =>
        match hr : entries r with
        | none => none
        | some entry =>
          match hf : entry.facts[index]? with
          | some (.natural _ _) =>
            if hn : entry.universes = 0 then
              if hA : A = .const r [] then
                some ⟨by subst A; exact TypingClaim.natLit hr (List.mem_of_getElem? hf) hn value⟩
              else none
            else none
          | _ => none
      | e, .betaResult p D body arg B wl wa =>
        if he : e = body.inst arg then
          if hA : A = B.inst arg then do
            let hl ← verifyType fuel n entries Γ (.lam p D body) (.forallE p D B) wl
            let ha ← verifyType fuel n entries Γ arg D wa
            return ⟨by subst e A; exact TypingClaim.betaResult hl.down ha.down⟩
          else none
        else none
      | _, _ => none
    else none

def verifyConversion (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (a b : AExpr β) (witness : ConversionWitness β) :
    Option (CheckedClaim.{u} (ConversionClaim.{u,v} entries Γ a b)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if a.Scope n Γ.length ∧ b.Scope n Γ.length then
      match a, b, witness with
      | a, b, .refl =>
        if h : a = b then some ⟨by subst b; exact ConversionClaim.refl a⟩ else none
      | a, b, .symm w => do
        let h ← verifyConversion fuel n entries Γ b a w
        return ⟨ConversionClaim.symm h.down⟩
      | a, b, .trans c w₁ w₂ => do
        let h₁ ← verifyConversion fuel n entries Γ a c w₁
        let h₂ ← verifyConversion fuel n entries Γ c b w₂
        return ⟨ConversionClaim.trans h₁.down h₂.down⟩
      | .app f a, .app f' a', .app wf wa => do
        let hf ← verifyConversion fuel n entries Γ f f' wf
        let ha ← verifyConversion fuel n entries Γ a a' wa
        return ⟨ConversionClaim.app hf.down ha.down⟩
      | .proj r i a, .proj r' i' b, .proj w =>
        if hr : r = r' then
          if hi : i = i' then do
            let h ← verifyConversion fuel n entries Γ a b w
            return ⟨by subst r' i'; exact ConversionClaim.proj h.down⟩
          else none
        else none
      | .lam p D body, .lam p' D' body', .lam lD wD wd wb =>
        if hp : p = p' then do
          let hD ← verifyType fuel n entries Γ D (.sort lD) wD
          let hd ← verifyConversion fuel n entries Γ D D' wd
          let hb ← verifyConversion fuel n entries (Γ.push D) body body' wb
          return ⟨by subst p'; exact ConversionClaim.lam hD.down hd.down hb.down⟩
        else none
      | .forallE p D B, .forallE p' D' B', .forallE lD wD wd wb =>
        if hp : p = p' then do
          let hD ← verifyType fuel n entries Γ D (.sort lD) wD
          let hd ← verifyConversion fuel n entries Γ D D' wd
          let hb ← verifyConversion fuel n entries (Γ.push D) B B' wb
          return ⟨by subst p'; exact ConversionClaim.forallE hD.down hd.down hb.down⟩
        else none
      | .app (.lam p D body) arg, result, .beta T wl wa =>
        if hr : result = body.inst arg then do
          let hl ← verifyType fuel n entries Γ (.lam p D body) T wl
          let ha ← verifyType fuel n entries Γ arg D wa
          return ⟨by subst result; exact ConversionClaim.beta hl.down ha.down⟩
        else none
      | .lam p D body, f, .eta B wf =>
        if hb : body = .app (f.liftN 1) (.bvar 0) then do
          let hf ← verifyType fuel n entries Γ f (.forallE p D B) wf
          return ⟨by subst body; exact ConversionClaim.eta hf.down⟩
        else none
      | a, b, .proofIrrel A wA wa wb => do
        let hA ← verifyType fuel n entries Γ A (.sort .zero) wA
        let ha ← verifyType fuel n entries Γ a A wa
        let hb ← verifyType fuel n entries Γ b A wb
        return ⟨ConversionClaim.proofIrrel hA.down ha.down hb.down⟩
      | .const r ls, b, .delta =>
        match h : entries r with
        | none => none
        | some entry =>
          match hb : entry.body with
          | none => none
          | some body =>
            if hn : ls.length = entry.universes then
              if hB : b = body.instL ls then
                some ⟨by subst b; exact ConversionClaim.delta h hb hn⟩
              else none
            else none
      | .sort l, .sort l', .sort =>
        if h : LevelEq.check n l l' = true then
          some ⟨ConversionClaim.sort (LevelEq.check_sound h).2.2⟩
        else none
      | a, b, .equation r index ls =>
        match h : entries r with
        | none => none
        | some entry =>
          match he : entry.equations[index]? with
          | none => none
          | some law =>
            if hn : ls.length = entry.universes then
              if hls : ∀ l ∈ ls, l.WF n then
                if ha : a = law.lhs.instL ls then
                  if hb : b = law.rhs.instL ls then
                    some ⟨by
                      subst a b
                      exact ConversionClaim.equation h (List.mem_of_getElem? he) hn⟩
                  else none
                else none
              else none
            else none
      | .natLit value, result, .natLiteral r index =>
        match hr : entries r with
        | none => none
        | some entry =>
          match hf : entry.facts[index]? with
          | some (.natural zero succ) =>
            if hn : entry.universes = 0 then
              match value with
              | 0 =>
                if he : result = .const zero [] then
                  some ⟨by subst result; exact ConversionClaim.natZero hr (List.mem_of_getElem? hf) hn⟩
                else none
              | value + 1 =>
                if he : result = .app (.const succ []) (.natLit value) then
                  some ⟨by subst result; exact ConversionClaim.natSucc hr (List.mem_of_getElem? hf) hn value⟩
                else none
            else none
          | _ => none
      | _, _, _ => none
    else none
end

/-- Soundness is extracted only from an actual successful execution. The
dependency model and context are the documented local preconditions; the
closed acceptance producer must construct them. -/
theorem verifyType_sound {fuel n : Nat} {entries : Environment β} {Γ : Context β}
    {e A : AExpr β} {witness : TypingWitness β} {result}
    (_ : verifyType.{u,v} fuel n entries Γ e A witness = some result) :
    TypingClaim.{u,v} entries Γ e A := result.down

theorem verifyConversion_sound {fuel n : Nat} {entries : Environment β} {Γ : Context β}
    {a b : AExpr β} {witness : ConversionWitness β} {result}
    (_ : verifyConversion.{u,v} fuel n entries Γ a b witness = some result) :
    ConversionClaim.{u,v} entries Γ a b := result.down

def checkTypeCertified (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e A : AExpr β) (witness : TypingWitness β) : Bool :=
  (verifyType.{u,v} fuel n entries Γ e A witness).isSome

def defeqCertified (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (a b : AExpr β) (witness : ConversionWitness β) : Bool :=
  (verifyConversion.{u,v} fuel n entries Γ a b witness).isSome

theorem checkTypeCertified_sound {fuel n : Nat} {entries : Environment β}
    {Γ : Context β} {e A : AExpr β} {witness : TypingWitness β}
    (h : checkTypeCertified.{u,v} fuel n entries Γ e A witness = true) :
    TypingClaim.{u,v} entries Γ e A := by
  unfold checkTypeCertified at h
  cases hr : verifyType.{u,v} fuel n entries Γ e A witness with
  | none => simp [hr] at h
  | some result => exact result.down

theorem defeqCertified_sound {fuel n : Nat} {entries : Environment β}
    {Γ : Context β} {a b : AExpr β} {witness : ConversionWitness β}
    (h : defeqCertified.{u,v} fuel n entries Γ a b witness = true) :
    ConversionClaim.{u,v} entries Γ a b := by
  unfold defeqCertified at h
  cases hr : verifyConversion.{u,v} fuel n entries Γ a b witness with
  | none => simp [hr] at h
  | some result => exact result.down

end Ix.Theory.Certified
