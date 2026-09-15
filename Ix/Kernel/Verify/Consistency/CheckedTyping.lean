/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisMeaning

/-!
# Checked typing: the reduction premise

Reduction soundness cannot be stated over plain semantic typing. In the
proof regime a lambda denotes the canonical proof point, so
`TypingClaim` accepts an application `(fun h : True => h) 5` whose beta
reduct `5` is not convertible to it; the model's `ConversionClaim.beta` needs
the argument typed at the lambda's own domain. `HereditaryTyping` retains
those checks, but its atom rule types a constant at any semantic type, so
delta unfolding cannot transport a derivation to the unfolded body.

`CheckedTyping` is hereditary typing whose atoms carry their canonical types:
a sort at its successor, a constant at its declared instantiated type, a
natural literal at the primitive type, and a projection at a semantic type.
It projects to `HereditaryTyping`, hence to typed lambda spines and semantic
typing, and it is closed under context insertion, dependent substitution,
rewriting the head of an application spine at every type, beta prefixes,
and replacing a constant by any term checked at its declared type. These are
the closure properties the WHNF step cases use; each is proved here once.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Closed annotated terms -/

theorem AExpr.liftN_of_scope {β : Type u} : ∀ {e : AExpr β} {n depth : Nat},
    e.Scope n depth → ∀ (count cutoff : Nat), depth ≤ cutoff → e.liftN count cutoff = e
  | .bvar i, _, depth, scope, count, cutoff, below => by
      simp only [AExpr.Scope] at scope
      simp [AExpr.liftN, liftVar, show i < cutoff by omega]
  | .sort _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _ => rfl
  | .natLit _, _, _, _, _, _, _ => rfl
  | .app f a, n, depth, scope, count, cutoff, below => by
      simp only [AExpr.liftN, AExpr.liftN_of_scope scope.1 count cutoff below,
        AExpr.liftN_of_scope scope.2 count cutoff below]
  | .lam _ a b, n, depth, scope, count, cutoff, below => by
      simp only [AExpr.liftN, AExpr.liftN_of_scope scope.2.1 count cutoff below,
        AExpr.liftN_of_scope scope.2.2 count (cutoff + 1) (by omega)]
  | .forallE _ a b, n, depth, scope, count, cutoff, below => by
      simp only [AExpr.liftN, AExpr.liftN_of_scope scope.2.1 count cutoff below,
        AExpr.liftN_of_scope scope.2.2 count (cutoff + 1) (by omega)]
  | .proj _ _ e, n, depth, scope, count, cutoff, below => by
      simp only [AExpr.liftN, AExpr.liftN_of_scope (e := e) scope count cutoff below]

theorem AExpr.inst_of_scope {β : Type u} : ∀ {e : AExpr β} {n depth : Nat},
    e.Scope n depth → ∀ (argument : AExpr β) (cutoff : Nat), depth ≤ cutoff →
      e.inst argument cutoff = e
  | .bvar i, _, depth, scope, argument, cutoff, below => by
      simp only [AExpr.Scope] at scope
      simp [AExpr.inst, AExpr.instVar, show i < cutoff by omega]
  | .sort _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _ => rfl
  | .natLit _, _, _, _, _, _, _ => rfl
  | .app f a, n, depth, scope, argument, cutoff, below => by
      simp only [AExpr.inst, AExpr.inst_of_scope scope.1 argument cutoff below,
        AExpr.inst_of_scope scope.2 argument cutoff below]
  | .lam _ a b, n, depth, scope, argument, cutoff, below => by
      simp only [AExpr.inst, AExpr.inst_of_scope scope.2.1 argument cutoff below,
        AExpr.inst_of_scope scope.2.2 argument (cutoff + 1) (by omega)]
  | .forallE _ a b, n, depth, scope, argument, cutoff, below => by
      simp only [AExpr.inst, AExpr.inst_of_scope scope.2.1 argument cutoff below,
        AExpr.inst_of_scope scope.2.2 argument (cutoff + 1) (by omega)]
  | .proj _ _ e, n, depth, scope, argument, cutoff, below => by
      simp only [AExpr.inst, AExpr.inst_of_scope (e := e) scope argument cutoff below]

/-- Universe instantiation leaves every bound variable in place, so a closed
type stays closed after instantiation at any universe arguments. -/
theorem AExpr.liftN_instL_of_scope {β : Type u} : ∀ {e : AExpr β} {n depth : Nat},
    e.Scope n depth → ∀ (levels : List VLevel) (count cutoff : Nat), depth ≤ cutoff →
      (e.instL levels).liftN count cutoff = e.instL levels
  | .bvar i, _, depth, scope, levels, count, cutoff, below => by
      simp only [AExpr.Scope] at scope
      simp [AExpr.instL, AExpr.liftN, liftVar, show i < cutoff by omega]
  | .sort _, _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _, _ => rfl
  | .natLit _, _, _, _, _, _, _, _ => rfl
  | .app f a, n, depth, scope, levels, count, cutoff, below => by
      simp only [AExpr.instL, AExpr.liftN, AExpr.liftN_instL_of_scope scope.1 levels count cutoff below,
        AExpr.liftN_instL_of_scope scope.2 levels count cutoff below]
  | .lam _ a b, n, depth, scope, levels, count, cutoff, below => by
      simp only [AExpr.instL, AExpr.liftN, AExpr.liftN_instL_of_scope scope.2.1 levels count cutoff below,
        AExpr.liftN_instL_of_scope scope.2.2 levels count (cutoff + 1) (by omega)]
  | .forallE _ a b, n, depth, scope, levels, count, cutoff, below => by
      simp only [AExpr.instL, AExpr.liftN, AExpr.liftN_instL_of_scope scope.2.1 levels count cutoff below,
        AExpr.liftN_instL_of_scope scope.2.2 levels count (cutoff + 1) (by omega)]
  | .proj _ _ e, n, depth, scope, levels, count, cutoff, below => by
      simp only [AExpr.instL, AExpr.liftN, AExpr.liftN_instL_of_scope (e := e) scope levels count cutoff below]

theorem AExpr.inst_instL_of_scope {β : Type u} : ∀ {e : AExpr β} {n depth : Nat},
    e.Scope n depth → ∀ (levels : List VLevel) (argument : AExpr β) (cutoff : Nat), depth ≤ cutoff →
      (e.instL levels).inst argument cutoff = e.instL levels
  | .bvar i, _, depth, scope, levels, argument, cutoff, below => by
      simp only [AExpr.Scope] at scope
      simp [AExpr.instL, AExpr.inst, AExpr.instVar, show i < cutoff by omega]
  | .sort _, _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _, _ => rfl
  | .natLit _, _, _, _, _, _, _, _ => rfl
  | .app f a, n, depth, scope, levels, argument, cutoff, below => by
      simp only [AExpr.instL, AExpr.inst, AExpr.inst_instL_of_scope scope.1 levels argument cutoff below,
        AExpr.inst_instL_of_scope scope.2 levels argument cutoff below]
  | .lam _ a b, n, depth, scope, levels, argument, cutoff, below => by
      simp only [AExpr.instL, AExpr.inst, AExpr.inst_instL_of_scope scope.2.1 levels argument cutoff below,
        AExpr.inst_instL_of_scope scope.2.2 levels argument (cutoff + 1) (by omega)]
  | .forallE _ a b, n, depth, scope, levels, argument, cutoff, below => by
      simp only [AExpr.instL, AExpr.inst, AExpr.inst_instL_of_scope scope.2.1 levels argument cutoff below,
        AExpr.inst_instL_of_scope scope.2.2 levels argument (cutoff + 1) (by omega)]
  | .proj _ _ e, n, depth, scope, levels, argument, cutoff, below => by
      simp only [AExpr.instL, AExpr.inst, AExpr.inst_instL_of_scope (e := e) scope levels argument cutoff below]

theorem AExpr.appN_append {β : Type u} (head : AExpr β) (first second : List (AExpr β)) :
    head.appN (first ++ second) = (head.appN first).appN second := by
  induction first generalizing head with
  | nil => rfl
  | cons argument first ih => simpa only [List.cons_append, AExpr.appN_cons] using ih (head.app argument)

/-! ### The derivation form -/

/-- Hereditary typing with canonical atom types. Sorts, constants, and
natural literals are typed exactly as the checker infers them; projections
carry a semantic type; binders, applications, and conversions retain their
children as `HereditaryTyping` does. -/
inductive CheckedTyping {β : Type u} (entries : Model.Environment β) :
    Model.Context β → AExpr β → AExpr β → Prop
  | sort {context : Model.Context β} (level : VLevel) :
      CheckedTyping entries context (.sort level) (.sort (.succ level))
  | const {context : Model.Context β} {ref : ConstRef β} {entry : ConstantEntry β}
      {levels : List VLevel} (found : entries ref = some entry)
      (arity : levels.length = entry.universes) :
      CheckedTyping entries context (.const ref levels) (entry.type.instL levels)
  | natLit {context : Model.Context β} {ref zero succ : ConstRef β} {entry : ConstantEntry β}
      (found : entries ref = some entry) (fact : .natural zero succ ∈ entry.facts)
      (arity : entry.universes = 0) (value : Nat) :
      CheckedTyping entries context (.natLit value) (.const ref [])
  | proj {context : Model.Context β} {ref : ConstRef β} {field : Nat} {major type : AExpr β}
      (typed : TypingClaim.{u,v} entries context (.proj ref field major) type) :
      CheckedTyping entries context (.proj ref field major) type
  | bvar {context : Model.Context β} {index : Nat} {type : AExpr β}
      (typed : TypingClaim.{u,v} entries context (.bvar index) type)
      (atIndex : context[index]? = some type) :
      CheckedTyping entries context (.bvar index) type
  | forallE {context : Model.Context β} {condition : Certified.PropWhen}
      {domain body type : AExpr β} {domainLevel bodyLevel : VLevel}
      (typed : TypingClaim.{u,v} entries context (.forallE condition domain body) type)
      (domainCheck : CheckedTyping entries context domain (.sort domainLevel))
      (bodyCheck : CheckedTyping entries (context.push domain) body (.sort bodyLevel))
      (conditionAgrees : condition = Certified.zeroCondition bodyLevel) :
      CheckedTyping entries context (.forallE condition domain body) type
  | lam {context : Model.Context β} {condition : Certified.PropWhen} {domain body codomain : AExpr β}
      (typed : TypingClaim.{u,v} entries context (.lam condition domain body)
        (.forallE condition domain codomain))
      (inner : CheckedTyping entries (context.push domain) body codomain) :
      CheckedTyping entries context (.lam condition domain body) (.forallE condition domain codomain)
  | app {context : Model.Context β} {fn arg : AExpr β} {condition : Certified.PropWhen}
      {domain body : AExpr β}
      (function : CheckedTyping entries context fn (.forallE condition domain body))
      (argument : CheckedTyping entries context arg domain) :
      CheckedTyping entries context (.app fn arg) (body.inst arg)
  | convert {context : Model.Context β} {term sourceType resultType : AExpr β} {level : VLevel}
      (prior : CheckedTyping entries context term sourceType)
      (rigid : AExpr.HeadRigid sourceType resultType)
      (converted : ConversionClaim.{u,v} entries context sourceType resultType)
      (formed : TypingClaim.{u,v} entries context resultType (.sort level)) :
      CheckedTyping entries context term resultType

namespace CheckedTyping

variable {β : Type u} {entries : Model.Environment β}

theorem typing {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type) :
    TypingClaim.{u,v} entries context term type := by
  induction checked with
  | sort level => exact TypingClaim.sort level
  | const found arity => exact TypingClaim.const found arity
  | natLit found fact arity value => exact TypingClaim.natLit found fact arity value
  | proj typed | bvar typed | forallE typed | lam typed => exact typed
  | app _ _ function argument => exact TypingClaim.app function argument
  | convert _ _ converted formed prior => exact prior.conv formed converted

theorem toHereditary {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type) :
    HereditaryTyping.{u,v} entries context term type := by
  induction checked with
  | sort level => exact .atom (TypingClaim.sort level) (.sort level)
  | const found arity => exact .atom (TypingClaim.const found arity) (.const _ _)
  | natLit found fact arity value => exact .atom (TypingClaim.natLit found fact arity value) (.natLit value)
  | proj typed => exact .atom typed (.proj _ _ _)
  | bvar typed atIndex => exact .bvar typed atIndex
  | forallE typed _ _ agrees domain body => exact .forallE typed domain body agrees
  | lam typed _ inner => exact .lam typed inner
  | app _ _ function argument => exact .app function argument
  | convert _ rigid converted formed prior => exact .convert prior rigid converted formed

theorem lambdaSpine {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type) :
    LambdaSpineTyping.{u,v} entries context term type :=
  checked.toHereditary.lambdaSpine

/-! ### Context insertion and dependent substitution -/

theorem weakenAt (wellFormed : entries.WF) {source target : Model.Context β} {cutoff : Nat}
    {term type : AExpr β} (checked : CheckedTyping.{u,v} entries source term type)
    (insertion : ContextInsertion source target cutoff) :
    CheckedTyping.{u,v} entries target (term.liftN 1 cutoff) (type.liftN 1 cutoff) := by
  induction checked generalizing target cutoff with
  | sort level => exact .sort level
  | const found arity =>
      rw [AExpr.liftN_instL_of_scope (wellFormed.typeScope _ _ found) _ 1 cutoff (Nat.zero_le _)]
      exact .const found arity
  | natLit found fact arity value => exact .natLit found fact arity value
  | proj typed => exact .proj (insertion.typing typed)
  | bvar typed found =>
      exact .bvar (insertion.typing typed)
        (by simpa only [liftVar, Nat.add_comm 1] using insertion.lookup found)
  | forallE typed _ _ agrees domain body =>
      exact .forallE (insertion.typing typed) (domain insertion) (body (insertion.push _)) agrees
  | lam typed _ inner => exact .lam (insertion.typing typed) (inner (insertion.push _))
  | app _ _ function argument =>
      simpa only [AExpr.liftN, AExpr.liftN_inst_zero] using
        CheckedTyping.app (function insertion) (argument insertion)
  | convert _ rigid converted formed prior =>
      exact .convert (prior insertion)
        (AExpr.HeadRigid.map rigid (AExpr.liftN 1 · cutoff) (by intros; rfl))
        (insertion.conversion converted) (insertion.typing formed)

theorem liftValue (wellFormed : entries.WF) {base source target : Model.Context β}
    {domain argument term type : AExpr β} {cutoff : Nat}
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (value : CheckedTyping.{u,v} entries base term type) :
    CheckedTyping.{u,v} entries target (term.liftN cutoff) (type.liftN cutoff) := by
  induction substitution with
  | root => simpa only [AExpr.liftN_zero] using value
  | @push source target cutoff prior binder ih =>
      have lifted := ih.weakenAt wellFormed (ContextInsertion.root target (binder.inst argument cutoff))
      simpa only [AExpr.liftN_liftN_merge term cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _),
        AExpr.liftN_liftN_merge type cutoff 1 0 0 (Nat.le_refl _) (Nat.zero_le _)] using lifted

theorem substituteAt (wellFormed : entries.WF) {base source target : Model.Context β}
    {domain argument term type : AExpr β} {cutoff : Nat}
    (checked : CheckedTyping.{u,v} entries source term type)
    (value : CheckedTyping.{u,v} entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    CheckedTyping.{u,v} entries target (term.inst argument cutoff) (type.inst argument cutoff) := by
  induction checked generalizing target cutoff with
  | sort level => exact .sort level
  | const found arity =>
      rw [AExpr.inst_instL_of_scope (wellFormed.typeScope _ _ found) _ argument cutoff (Nat.zero_le _)]
      exact .const found arity
  | natLit found fact arity value => exact .natLit found fact arity value
  | proj typed => exact .proj (typed.instAt value.typing substitution)
  | @bvar context index type typed found =>
      by_cases equal : index = cutoff
      · subst index
        have sameType := substitution.instantiate_removed_type found
        simpa only [AExpr.inst, AExpr.instVar, Nat.lt_irrefl, if_false, if_true, sameType] using
          liftValue wellFormed substitution value
      · have retained := substitution.lookup_other found equal
        have substituted := typed.instAt value.typing substitution
        by_cases below : index < cutoff
        · simp only [AExpr.inst, AExpr.instVar, below, if_true] at substituted retained ⊢
          exact .bvar substituted retained
        · simp only [AExpr.inst, AExpr.instVar, below, equal, if_false] at substituted retained ⊢
          exact .bvar substituted retained
  | forallE typed _ _ agrees domainCheck bodyCheck =>
      exact .forallE (typed.instAt value.typing substitution) (domainCheck substitution)
        (bodyCheck (substitution.push _)) agrees
  | lam typed _ inner => exact .lam (typed.instAt value.typing substitution) (inner (substitution.push _))
  | app _ _ function applied =>
      simpa only [AExpr.inst, AExpr.inst_inst_zero] using
        CheckedTyping.app (function substitution) (applied substitution)
  | convert _ rigid converted formed prior =>
      exact .convert (prior substitution)
        (AExpr.HeadRigid.map rigid (AExpr.inst · argument cutoff) (by intros; rfl))
        (converted.instAt value.typing substitution) (formed.instAt value.typing substitution)

/-! ### Inversions -/

theorem lamType {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type)
    {condition : Certified.PropWhen} {domain body : AExpr β}
    (same : term = .lam condition domain body) :
    ∃ codomain, type = .forallE condition domain codomain ∧
      CheckedTyping.{u,v} entries (context.push domain) body codomain := by
  induction checked with
  | sort | const | natLit | proj | bvar | forallE | app => cases same
  | lam _ inner _ => cases same; exact ⟨_, rfl, inner⟩
  | convert _ rigid _ _ ih =>
      obtain ⟨codomain, typeEq, inner⟩ := ih same
      exact ⟨codomain, (rigid (by simp only [typeEq]; intro fn arg same; cases same)).trans typeEq, inner⟩

theorem appHead {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type)
    {fn arg : AExpr β} (same : term = .app fn arg) :
    ∃ headType, CheckedTyping.{u,v} entries context fn headType := by
  induction checked with
  | sort | const | natLit | proj | bvar | forallE | lam => cases same
  | app function _ _ _ => cases same; exact ⟨_, function⟩
  | convert _ _ _ _ ih => exact ih same

/-- The head of every checked application spine is checked at some type. -/
theorem headTyped {context : Model.Context β} {head type : AExpr β} :
    ∀ {arguments : List (AExpr β)},
      CheckedTyping.{u,v} entries context (head.appN arguments) type →
      ∃ headType, CheckedTyping.{u,v} entries context head headType
  | [], checked => ⟨type, checked⟩
  | argument :: arguments, checked => by
      obtain ⟨applied, spine⟩ := headTyped (arguments := arguments) checked
      exact spine.appHead rfl

/-! ### Rewriting the head of a spine -/

theorem rewriteApp {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type)
    {fn fn' arg : AExpr β} (same : term = .app fn arg)
    (rewrite : ∀ headType, CheckedTyping.{u,v} entries context fn headType →
      CheckedTyping.{u,v} entries context fn' headType) :
    CheckedTyping.{u,v} entries context (.app fn' arg) type := by
  induction checked with
  | sort | const | natLit | proj | bvar | forallE | lam => cases same
  | app function argument _ _ => cases same; exact .app (rewrite _ function) argument
  | convert _ rigid converted formed ih => exact .convert (ih same rewrite) rigid converted formed

/-- Replacing the head of a spine by a term checked at every type of the head
retains the spine's checked typing at its type. -/
theorem rewriteHead {context : Model.Context β} {head head' type : AExpr β}
    (rewrite : ∀ headType, CheckedTyping.{u,v} entries context head headType →
      CheckedTyping.{u,v} entries context head' headType) :
    ∀ {arguments : List (AExpr β)},
      CheckedTyping.{u,v} entries context (head.appN arguments) type →
      CheckedTyping.{u,v} entries context (head'.appN arguments) type
  | [], checked => rewrite _ checked
  | argument :: arguments, checked =>
      rewriteHead (head := head.app argument) (head' := head'.app argument)
        (fun _ applied => applied.rewriteApp rfl rewrite) (arguments := arguments) checked

/-! ### Beta and delta -/

theorem betaStep (wellFormed : entries.WF) {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type)
    {condition : Certified.PropWhen} {domain body argument : AExpr β}
    (same : term = .app (.lam condition domain body) argument) :
    CheckedTyping.{u,v} entries context (body.inst argument) type := by
  induction checked with
  | sort | const | natLit | proj | bvar | forallE | lam => cases same
  | app function argument' _ _ =>
      cases same
      obtain ⟨codomain, typeEq, inner⟩ := function.lamType rfl
      cases typeEq
      exact inner.substituteAt wellFormed argument' .root
  | convert _ rigid converted formed ih => exact .convert (ih same) rigid converted formed

/-- Every beta prefix of a checked spine is checked at the spine's type. -/
theorem betaPrefix (wellFormed : entries.WF) {context : Model.Context β} {type : AExpr β} :
    ∀ (count : Nat) (head : AExpr β) (arguments : List (AExpr β)),
      CheckedTyping.{u,v} entries context (head.appN arguments) type →
      CheckedTyping.{u,v} entries context (AExpr.betaPrefix count head arguments) type
  | 0, _, _, checked => checked
  | count + 1, .lam _ _ body, argument :: arguments, checked =>
      betaPrefix wellFormed count (body.inst argument) arguments
        (rewriteHead (fun _ applied => applied.betaStep wellFormed rfl) checked)
  | _ + 1, .lam _ _ _, [], checked => checked
  | _ + 1, .bvar _, _, checked | _ + 1, .sort _, _, checked
  | _ + 1, .const _ _, _, checked | _ + 1, .app _ _, _, checked
  | _ + 1, .forallE _ _ _, _, checked | _ + 1, .proj _ _ _, _, checked
  | _ + 1, .natLit _, _, checked => checked

/-- A constant may be replaced by any term checked at its declared
instantiated type, at every type the constant is checked at. -/
theorem unfoldConst {context : Model.Context β} {term type : AExpr β}
    (checked : CheckedTyping.{u,v} entries context term type)
    {ref : ConstRef β} {levels : List VLevel} {entry : ConstantEntry β} {output : AExpr β}
    (same : term = .const ref levels) (found : entries ref = some entry)
    (unfolded : CheckedTyping.{u,v} entries context output (entry.type.instL levels)) :
    CheckedTyping.{u,v} entries context output type := by
  induction checked with
  | sort | natLit | proj | bvar | forallE | lam | app => cases same
  | const found' _ =>
      cases same
      cases Option.some.inj (found'.symm.trans found)
      exact unfolded
  | convert _ rigid converted formed ih => exact .convert (ih same unfolded) rigid converted formed

end CheckedTyping

end Ix.Kernel.Consistency

namespace Ix.Kernel.Consistency.CheckedTyping

open Theory Theory.Model

universe u v

/-- A checked constant instance has the arity of its admitted entry. -/
theorem constArity {β : Type u} {entries : Model.Environment β} {context : Model.Context β}
    {term type : AExpr β} (checked : CheckedTyping.{u,v} entries context term type)
    {ref : ConstRef β} {levels : List VLevel} (same : term = .const ref levels) :
    ∃ entry, entries ref = some entry ∧ levels.length = entry.universes := by
  induction checked with
  | sort | natLit | proj | bvar | forallE | lam | app => cases same
  | const found arity => cases same; exact ⟨_, found, arity⟩
  | convert _ _ _ _ ih => exact ih same

end Ix.Kernel.Consistency.CheckedTyping
