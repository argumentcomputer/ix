/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Claims
import Ix.Kernel.Search
import Ix.Kernel.Certified.Quotient.Reading
import Ix.Kernel.Level
import Std.Data.HashMap

/-! # Reduction, inference, and conversion

The reference algorithms of the kernel, each returning its result together
with the semantic claim that justifies it (`Ix.Kernel.Claims`); the claims are
erased at run time. Every function is bounded by explicit fuel. Search
preserves exhaustion and unresolved causes; `whnf` also retains a sound
partial reduct when it cannot finish.

* `step` performs one head reduction: beta (at a binder that may be Prop, the
  argument is inferred and its type converted to the lambda's domain; at a
  uniformly non-Prop binder, `ReductionClaim.betaNever` needs neither), delta
  on definitions with bodies, and zeta on lets.
* `whnf` iterates `step`.
* `inferA` infers the type of an annotated term and validates every binder
  annotation against the inferred codomain sort.
* `isDefEq` searches for conversion by lazy delta: both sides are reduced
  without unfolding their heads and compared; a head is unfolded only when
  needed, with congruence tried first when both heads unfold and proof
  irrelevance before unfolding a proof. Eta for functions and structures and
  proof irrelevance are the structural fallbacks.

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

/-- A sound reduct and the cause that stopped normalization, if any.
`none` means the supported step strategy found no applicable rule; it is
not a completeness claim about Lean's reduction relation. -/
structure Normalized (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  result : AExpr β
  claim : ReductionClaim.{u,v} entries Γ e result
  stopped : Option SearchFailure

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
def sortOf {e T : AExpr β} (r : Normalized.{u,v} entries Γ T) (he : TypingClaim.{u,v} entries Γ e T) :
    Search (TypedSort.{u,v} entries Γ e) :=
  match r with
  | ⟨T', hr, stopped⟩ =>
    match T' with
    | .sort l => .ok ⟨l, he.convF (FormedClaim.sort l) (ConvClaim.ofReduction hr)⟩
    | _ => .error (stopped.getD (.unresolved "the inferred type did not reduce to a sort"))

/-- Read a dependent function type off an already reduced type. -/
def piOf {e T : AExpr β} (r : Normalized.{u,v} entries Γ T) (he : TypingClaim.{u,v} entries Γ e T) :
    Search (TypedPi.{u,v} entries Γ e) :=
  match r with
  | ⟨T', hr, stopped⟩ =>
    match T' with
    | .forallE p D B =>
      .ok ⟨p, D, B, he.convF (hr.formed he.formedType) (ConvClaim.ofReduction hr)⟩
    | .sort _ => .error (.malformed "a sort-valued term was used as a function")
    | _ => .error (stopped.getD (.unresolved "the function's type did not reduce to a Pi"))

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

/-- The numeric operation an entry computes, with its membership. -/
def findNatOp : (facts : List (ConstantFact β)) →
    Option { op : NatOp // ConstantFact.natOp op ∈ facts }
  | [] => none
  | .natOp op :: _ => some ⟨op, List.mem_cons_self ..⟩
  | _ :: rest => (findNatOp rest).map fun ⟨op, h⟩ => ⟨op, List.mem_cons_of_mem _ h⟩

/-- The numeric test an entry computes, with its outcomes and membership. -/
def findNatTest : (facts : List (ConstantFact β)) →
    Option { p : NatTest × ConstRef β × ConstRef β // ConstantFact.natTest p.1 p.2.1 p.2.2 ∈ facts }
  | [] => none
  | .natTest test yes no :: _ => some ⟨(test, yes, no), List.mem_cons_self ..⟩
  | _ :: rest => (findNatTest rest).map fun ⟨p, h⟩ => ⟨p, List.mem_cons_of_mem _ h⟩

/-- The largest exponent `pow` is evaluated at, as in the official kernel. -/
def natPowMaxExponent : Nat := 2 ^ 24

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
family and that family's eliminator, or the eliminator. -/
def quotientRule (facts : List (ConstantFact β)) : Option (Option (ConstRef β × ConstRef β)) :=
  facts.findSome? fun
    | .quotientLift eq eliminator => some (some (eq, eliminator))
    | .quotient .ind => some none
    | _ => none

/-- Delta at the head of an application spine: the head constant's body at its
universe instance, applied to the same arguments. -/
def deltaHead (entries : Environment β) (Γ : Context β) : (e : AExpr β) →
    Option (Reduced.{u,v} entries Γ e)
  | .const r ls =>
    match h : entries r with
    | some entry =>
      match hb : entry.body with
      | some body =>
        if hn : ls.length = entry.universes then some ⟨body.instL ls, ReductionClaim.delta h hb hn⟩
        else none
      | none => none
    | none => none
  | .app f a => (deltaHead entries Γ f).map fun ⟨f', hf⟩ => ⟨.app f' a, hf.appHead⟩
  | _ => none

/-- Whether head delta applies, without instantiating the definition's body
or rebuilding its application spine. No reduct is needed by no-delta WHNF. -/
def hasDeltaHead (entries : Environment β) : AExpr β → Bool
  | .const r ls =>
    match entries r with
    | some entry => entry.body.isSome && ls.length == entry.universes
    | none => false
  | .app f _ => hasDeltaHead entries f
  | _ => false

omit [DecidableEq β] in
theorem hasDeltaHead_eq (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    hasDeltaHead entries e = (deltaHead.{u,v} entries Γ e).isSome := by
  induction e with
  | const r ls =>
    simp only [hasDeltaHead, deltaHead]
    split <;> split <;> simp_all
    subst_vars
    split <;> try simp_all
    split <;> simp_all
  | app f a ih _ => simpa [hasDeltaHead, deltaHead] using ih
  | _ => rfl

/-- Whether the type telescope marks its value after `n` arguments as a proof:
the binder consumed last is annotated `allZero []`, a codomain that is a
proposition at every instance. -/
def telescopeProof : AExpr β → Nat → Bool
  | .forallE p _ B, n + 1 =>
    if n = 0 then (match p with | .allZero [] _ => true | _ => false) else telescopeProof B n
  | _, _ => false

/-- A cheap syntactic test that a term is a proof: its head constant's type
says so for its number of arguments. It only orders the search. -/
def proofHead (entries : Environment β) (e : AExpr β) : Bool :=
  match spine e [] with
  | (.const r _, args) =>
    match entries r with
    | some entry => telescopeProof entry.type args.length
    | none => false
  | _ => false

/-- Whether a type telescope, after `n` arguments, is never a proposition: the
binder consumed last, or the remaining function type, is annotated `.never`, or
what remains is a sort. -/
def telescopeNotProof : AExpr β → Nat → Bool
  | .forallE p _ _, 0 | .forallE p _ _, 1 => match p with | .never => true | _ => false
  | .forallE _ _ B, n + 2 => telescopeNotProof B (n + 1)
  | .sort _, 0 => true
  | _, _ => false

/-- A cheap syntactic test that a term is not a proof, so proof irrelevance
need not be tried: sorts, Pi types and literals, lambdas into non-propositions,
and constants whose type says their value is never a proof. It only orders the
search. -/
def notProof (entries : Environment β) (e : AExpr β) : Bool :=
  match e with
  | .sort _ | .forallE .. | .natLit .. | .lam .never _ _ => true
  | _ =>
    match spine e [] with
    | (.const r _, args) =>
      match entries r with
      | some entry => telescopeNotProof entry.type args.length
      | none => false
    | _ => false

/-- Syntactic conversion up to universe equivalence, without any reduction:
the congruence lazy delta tries before unfolding two equal heads. It never
searches, so a failed attempt costs one traversal. -/
def quickConv (entries : Environment β) (Γ : Context β) : (a b : AExpr β) →
    Option (Conv.{u,v} entries Γ a b)
  | .app f x, .app g y => do
    let ⟨hf⟩ ← quickConv entries Γ f g
    let ⟨hx⟩ ← quickConv entries Γ x y
    return ⟨ConvClaim.app hf hx⟩
  | .const r ls, .const r' ls' =>
    if hr : r = r' then
      if hl : levelsEquiv ls ls' then some ⟨hr ▸ ConvClaim.const (levelsEquiv_sound hl)⟩ else none
    else none
  | .sort l, .sort l' =>
    if he : levelEquiv l l' then some ⟨ConvClaim.sort (levelEquiv_sound he)⟩ else none
  | a, b => if h : a = b then some ⟨h ▸ ConvClaim.refl a⟩ else none

/-- Equal-length spines with the same constant head. Universe arguments are
checked by the conversion attempt; this predicate only schedules it. -/
def sameConstHead : AExpr β → AExpr β → Bool
  | .app f _, .app g _ => sameConstHead f g
  | .const r _, .const s _ => decide (r = s)
  | _, _ => false

/-! ## Per-frame caches

A cache holds results at one context `Γ`, each with its claim, so a hit is
exact evidence at that context and nothing about the table needs proof. It
lives for one frame: a computation under a binder starts with a fresh cache
for the extended context (`KM.inFrame`). A key is found by a depth-bounded
shape hash and confirmed by `DecidableEq`. Only complete results are kept: a
normalization that stopped early, or a conversion search that ran out of fuel,
is not cached. -/

/-- The hash of a reference: its block key's hash and its positions. -/
def refKeyHash (keyHash : β → UInt64) : ConstRef β → UInt64
  | .member b i => mixHash (keyHash b) (hash i)
  | .ctor b i c => mixHash (mixHash (keyHash b) (hash i)) (hash (c + 1))

/-- A hash of the top `depth` levels of a term. -/
def shapeHash (keyHash : β → UInt64) : Nat → AExpr β → UInt64
  | 0, _ => 7
  | depth + 1, e =>
    match e with
    | .bvar i => mixHash 11 (hash i)
    | .sort l => mixHash 13 (hash l)
    | .const r ls => mixHash 17 (mixHash (refKeyHash keyHash r) (hash ls))
    | .app f a => mixHash 19 (mixHash (shapeHash keyHash depth f) (shapeHash keyHash depth a))
    | .lam _ t b => mixHash 23 (mixHash (shapeHash keyHash depth t) (shapeHash keyHash depth b))
    | .forallE _ t b => mixHash 29 (mixHash (shapeHash keyHash depth t) (shapeHash keyHash depth b))
    | .letE t w b =>
      mixHash 31 (mixHash (shapeHash keyHash depth t)
        (mixHash (shapeHash keyHash depth w) (shapeHash keyHash depth b)))
    | .proj _ i x => mixHash 37 (mixHash (hash i) (shapeHash keyHash depth x))
    | .natLit _ n => mixHash 41 (hash n)

/-- The depth the cache keys hash to. -/
def cacheHashDepth : Nat := 8

/-- Results at one context, each with its claim. -/
structure Cache (entries : Environment β) (Γ : Context β) : Type u where
  keyHash : β → UInt64
  /-- Remaining work: every reduction, inference, or conversion call spends one
  unit, across frames, and none is left means exhaustion. It bounds total work,
  where fuel bounds depth. -/
  budget : Nat := 0
  infer : Std.HashMap UInt64 (List (Σ e : AExpr β, Typed.{u,v} entries Γ e)) := {}
  whnf : Std.HashMap UInt64 (List (Σ e : AExpr β, Normalized.{u,v} entries Γ e)) := {}
  conv : Std.HashMap UInt64
    (List ((a : AExpr β) × (b : AExpr β) × Search (Conv.{u,v} entries Γ a b))) := {}

namespace Cache

variable {entries : Environment β} {Γ : Context β}

def empty (keyHash : β → UInt64) (budget : Nat) : Cache.{u,v} entries Γ := { keyHash, budget }

def key (c : Cache.{u,v} entries Γ) (e : AExpr β) : UInt64 := shapeHash c.keyHash cacheHashDepth e

def findInfer (c : Cache.{u,v} entries Γ) (e : AExpr β) : Option (Typed.{u,v} entries Γ e) :=
  (c.infer.getD (c.key e) []).findSome? fun ⟨e', t⟩ => if h : e' = e then some (h ▸ t) else none

def addInfer (c : Cache.{u,v} entries Γ) (e : AExpr β) (t : Typed.{u,v} entries Γ e) :
    Cache.{u,v} entries Γ :=
  let k := c.key e
  { c with infer := c.infer.insert k (⟨e, t⟩ :: c.infer.getD k []) }

def findWhnf (c : Cache.{u,v} entries Γ) (e : AExpr β) : Option (Normalized.{u,v} entries Γ e) :=
  (c.whnf.getD (c.key e) []).findSome? fun ⟨e', n⟩ => if h : e' = e then some (h ▸ n) else none

def addWhnf (c : Cache.{u,v} entries Γ) (e : AExpr β) (n : Normalized.{u,v} entries Γ e) :
    Cache.{u,v} entries Γ :=
  let k := c.key e
  { c with whnf := c.whnf.insert k (⟨e, n⟩ :: c.whnf.getD k []) }

def convKey (c : Cache.{u,v} entries Γ) (a b : AExpr β) : UInt64 := mixHash (c.key a) (c.key b)

def findConv (c : Cache.{u,v} entries Γ) (a b : AExpr β) :
    Option (Search (Conv.{u,v} entries Γ a b)) :=
  (c.conv.getD (c.convKey a b) []).findSome? fun ⟨a', b', r⟩ =>
    if h : a' = a ∧ b' = b then some (h.1 ▸ h.2 ▸ r) else none

def addConv (c : Cache.{u,v} entries Γ) (a b : AExpr β) (r : Search (Conv.{u,v} entries Γ a b)) :
    Cache.{u,v} entries Γ :=
  let k := c.convKey a b
  { c with conv := c.conv.insert k (⟨a, b, r⟩ :: c.conv.getD k []) }

end Cache

/-- Search with a per-frame cache, kept whether the search succeeds or fails. -/
def KM (entries : Environment β) (Γ : Context β) (α : Type u) : Type u :=
  Cache.{u,v} entries Γ → Search α × Cache.{u,v} entries Γ

namespace KM

variable {entries : Environment β} {Γ : Context β} {α γ : Type u}

instance : Monad (KM.{u,v} entries Γ) where
  pure a := fun c => (.ok a, c)
  bind m f := fun c =>
    match m c with
    | (.ok a, c') => f a c'
    | (.error e, c') => (.error e, c')

instance : MonadExceptOf SearchFailure (KM.{u,v} entries Γ) where
  throw e := fun c => (.error e, c)
  tryCatch m h := fun c =>
    match m c with
    | (.ok a, c') => (.ok a, c')
    | (.error e, c') => h e c'

instance : MonadLift Option (KM.{u,v} entries Γ) where
  monadLift value := fun c => (Search.ofOption value, c)

def ofSearch (s : Search α) : KM.{u,v} entries Γ α := fun c => (s, c)

def map (f : α → γ) (m : KM.{u,v} entries Γ α) : KM.{u,v} entries Γ γ := fun c =>
  let (r, c') := m c
  (r.map f, c')

/-- A failed first attempt keeps what it cached; failures merge as in `Search.orElse`. -/
def orElse (first : KM.{u,v} entries Γ α) (next : Unit → KM.{u,v} entries Γ α) :
    KM.{u,v} entries Γ α := fun c =>
  match first c with
  | (.ok a, c') => (.ok a, c')
  | (.error a, c') =>
    match next () c' with
    | (.ok b, c'') => (.ok b, c'')
    | (.error b, c'') => (.error (a.merge b), c'')

def mapError (f : SearchFailure → SearchFailure) (m : KM.{u,v} entries Γ α) :
    KM.{u,v} entries Γ α := fun c =>
  let (r, c') := m c
  (r.mapError f, c')

def remember (cause : Option SearchFailure) (m : KM.{u,v} entries Γ α) : KM.{u,v} entries Γ α :=
  fun c =>
    let (r, c') := m c
    (Search.remember cause r, c')

/-- The outcome of a search, as a value. -/
def attempt (m : KM.{u,v} entries Γ α) : KM.{u,v} entries Γ (Search α) := fun c =>
  let (r, c') := m c
  (.ok r, c')

def cache : KM.{u,v} entries Γ (Cache.{u,v} entries Γ) := fun c => (.ok c, c)

def modifyCache (f : Cache.{u,v} entries Γ → Cache.{u,v} entries Γ) :
    KM.{u,v} entries Γ PUnit :=
  fun c => (.ok ⟨⟩, f c)

/-- Spend one unit of work. -/
def tick : KM.{u,v} entries Γ PUnit := fun c =>
  match c.budget with
  | 0 => (.error .exhausted, c)
  | n + 1 => (.ok ⟨⟩, { c with budget := n })

/-- A computation at another context, with a fresh cache for it; the work it
spends is spent here too. -/
def inFrame {Γ' : Context β} (m : KM.{u,v} entries Γ' α) : KM.{u,v} entries Γ α := fun c =>
  let (r, c') := m (Cache.empty c.keyHash c.budget)
  (r, { c with budget := c'.budget })

/-- Bound optional speculation, reserving at least three quarters of the
remaining work for its fallback. Results and caches are retained, and every
unit actually spent is still charged to the enclosing search. -/
def speculate (limit : Nat) (m : KM.{u,v} entries Γ α) : KM.{u,v} entries Γ α := fun c =>
  let allowance := min limit (c.budget / 4)
  let (r, c') := m { c with budget := allowance }
  (r, { c' with budget := c.budget - allowance + c'.budget })

/-- Run with an empty cache and the given work budget. -/
def run (keyHash : β → UInt64) (budget : Nat) (m : KM.{u,v} entries Γ α) : Search α :=
  (m (Cache.empty keyHash budget)).1

end KM

/-- A binder body's inferred type and that type's sort, at the body's context. -/
structure TypedBody (entries : Environment β) (Γ : Context β) (b : AExpr β) : Type u where
  type : AExpr β
  typed : TypingClaim.{u,v} entries Γ b type
  level : VLevel
  sorted : TypingClaim.{u,v} entries Γ type (.sort level)

mutual

/-- Evaluate a numeric operation whose arguments normalize to literals
(`ConstantFact.natOp`). The first argument is normalized first, and the second
only if the first reached a literal. -/
def natStepC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .app (.const r []) a =>
      match h : entries r with
      | some entry =>
        match findNatOp entry.facts with
        | some ⟨.pred, hf⟩ =>
          if hn : entry.universes = 0 then do
            let ⟨a', ha, _⟩ ← whnfC fuel entries Γ a
            match a', ha with
            | .natLit f x, ha => pure ⟨.natLit f (NatOp.pred.eval x 0), ReductionClaim.natPred h hf hn ha⟩
            | _, _ => throw .noMatch
          else throw .noMatch
        | _ => throw .noMatch
      | none => throw .noMatch
    | .app (.app (.const r []) a) b =>
      match h : entries r with
      | some entry =>
        if hn : entry.universes = 0 then
          match findNatOp entry.facts, findNatTest entry.facts with
          | some ⟨op, hf⟩, _ =>
            if hbin : op = .pred then throw .noMatch else do
            let ⟨a', ha, _⟩ ← whnfC fuel entries Γ a
            match a', ha with
            | .natLit f x, ha => do
              let ⟨b', hb, _⟩ ← whnfC fuel entries Γ b
              match b', hb with
              | .natLit _ y, hb =>
                if op = .pow && y > natPowMaxExponent then throw .noMatch
                else pure ⟨.natLit f (op.eval x y), ReductionClaim.natOp h hf hn hbin ha hb⟩
              | _, _ => throw .noMatch
            | _, _ => throw .noMatch
          | none, some ⟨(test, yes, no), hf⟩ => do
            let ⟨a', ha, _⟩ ← whnfC fuel entries Γ a
            match a', ha with
            | .natLit _ x, ha => do
              let ⟨b', hb, _⟩ ← whnfC fuel entries Γ b
              match b', hb with
              | .natLit _ y, hb =>
                pure ⟨.const (if test.eval x y then yes else no) [], ReductionClaim.natTest h hf hn ha hb⟩
              | _, _ => throw .noMatch
            | _, _ => throw .noMatch
          | none, none => throw .noMatch
        else throw .noMatch
      | none => throw .noMatch
    | _ => throw .noMatch

/-- One head reduction step through the application spine. -/
def stepC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .app f a =>
      match f with
      | .lam .never _ b => pure ⟨b.inst a, ReductionClaim.betaNever⟩
      | .lam p D b => do
        let ⟨A', ha⟩ ← inferAC fuel entries Γ a
        let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
        return ⟨b.inst a, ReductionClaim.beta (p := p) ha hc⟩
      | f =>
        KM.orElse (natStepC fuel entries Γ (.app f a)) fun _ =>
        KM.orElse (KM.mapError SearchFailure.speculative (iotaC fuel entries Γ (.app f a))) fun _ =>
          KM.orElse (KM.mapError SearchFailure.speculative (quotIotaC fuel entries Γ (.app f a))) fun _ => do
            let ⟨f', hf⟩ ← stepC fuel entries Γ f
            return ⟨.app f' a, hf.appHead⟩
    | .const r ls =>
      match h : entries r with
      | some entry =>
        match hb : entry.body with
        | some body =>
          if hn : ls.length = entry.universes then
            pure ⟨body.instL ls, ReductionClaim.delta h hb hn⟩
          else throw .noMatch
        | none => throw .noMatch
      | none => throw .noMatch
    | .letE _ v b => pure ⟨b.inst v, ReductionClaim.zeta⟩
    | .proj r i x => KM.mapError SearchFailure.speculative (projIotaC fuel entries Γ r i x)
    | _ => throw .noMatch

/-- Apply a typed nested lambda to arguments by typed beta steps, reducing
nothing else. -/
def applyTypedC : Nat → (entries : Environment β) → (Γ : Context β) → (f F : AExpr β) →
    TypingClaim.{u,v} entries Γ f F → (args : List (AExpr β)) →
      KM.{u,v} entries Γ (Applied.{u,v} entries Γ f args)
  | _, _, _, f, F, hf, [] => pure ⟨f, F, hf, ConversionClaim.refl _⟩
  | 0, _, _, _, _, _, _ :: _ => throw .exhausted
  | fuel + 1, entries, Γ, f, F, hf, a :: args =>
    match f, F, hf with
    | .lam p D b, .forallE p' D' B, hf =>
      if h : p = p' ∧ D = D' then do
        let ⟨A', ha⟩ ← inferAC fuel entries Γ a
        let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
        have hf' : TypingClaim.{u,v} entries Γ (.lam p D b) (.forallE p D B) := by
          obtain ⟨rfl, rfl⟩ := h
          exact hf
        have haD : TypingClaim.{u,v} entries Γ a D := ha.convF hf'.formedType.domain hc
        let rest ← applyTypedC fuel entries Γ (b.inst a) (B.inst a) (TypingClaim.betaResult hf' haD) args
        return ⟨rest.result, rest.type, rest.typed,
          (ConversionClaim.appN (ConversionClaim.beta hf' haD) args).trans rest.conv⟩
      else throw .noMatch
    | _, _, _ => throw .noMatch

/-- Iota: a recursor applied to a constructor reduces through the published
rule. The target is converted to the typed instance of the rule's left side
(which checks the constructor's parameters and the indices against the
recursor's), and the rule's equation takes it to the typed instance of the
right side. A literal major is unfolded one step first. K-like reduction: if
the major is not a constructor application but the recursor has a single rule
without fields, the constructor is synthesized from the recursor's parameters;
the conversion of the major to it is then proof irrelevance, which holds
exactly when the major's type converts to the constructor's. -/
def iotaC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
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
            | some major => do
              let normalized ← whnfC fuel entries Γ major
              KM.remember normalized.stopped <| do
                let major' := normalized.result
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
                          let appL ← applyTypedC fuel entries Γ (lhs.instL ls) (T.instL ls)
                            (TypingClaim.fact h (List.mem_of_getElem? hf1) hn) bargs
                          let appR ← applyTypedC fuel entries Γ (rhs.instL ls) (T'.instL ls)
                            (TypingClaim.fact h (List.mem_of_getElem? hf2) hn) bargs
                          let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ e appL.result
                          have heq : ConversionClaim.{u,v} entries Γ (lhs.instL ls) (rhs.instL ls) := by
                            have := ConversionClaim.equation (Γ := Γ) h (List.mem_of_getElem? hj) hn
                            rwa [hlaw.1, hlaw.2] at this
                          return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
                            (appL.conv.symm.trans ((heq.appN bargs).trans appR.conv)) appR.typed.formed⟩
                        else throw .noMatch
                      else throw .noMatch
                    | _, _, _ => throw .noMatch
                  else throw .noMatch
                | none => throw .noMatch
            | none => throw .noMatch
          else throw .noMatch
        | none => throw .noMatch
      | none => throw .noMatch
    | _ => throw .noMatch

/-- Reduce through a rule whose endpoints are typed by inference: the target is
converted to the typed instance of the left side, and the rule's conversion
takes it to the typed instance of the right side. -/
def reduceByRuleC : Nat → (entries : Environment β) → (Γ : Context β) → (e lhs rhs : AExpr β) →
    ConversionClaim.{u,v} entries Γ lhs rhs → (bargs : List (AExpr β)) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e, lhs, rhs, heq, bargs => do
    let ⟨TL, hL⟩ ← inferAC fuel entries Γ lhs
    let ⟨TR, hR⟩ ← inferAC fuel entries Γ rhs
    let appL ← applyTypedC fuel entries Γ lhs TL hL bargs
    let appR ← applyTypedC fuel entries Γ rhs TR hR bargs
    let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ e appL.result
    return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
      (appL.conv.symm.trans ((heq.appN bargs).trans appR.conv)) appR.typed.formed⟩

/-- Quotient computation: the lift or the eliminator applied to a constructor
application reduces through its rule, which is derived from the published
facts. The lift's rule needs the former, the constructor, the lift itself, and
the equality family to be the admitted ones; the eliminator's rule holds
outright, since both sides are proofs. The former is read off the entry's
type as the reference other than the known ones. -/
def quotIotaC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
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
            | some major => do
              let normalized ← whnfC fuel entries Γ major
              KM.remember normalized.stopped <| do
                match spine normalized.result [] with
                | (.const c _, [_, _, a]) =>
                  let bargs := args.take (arity - 1) ++ [a]
                  match role with
                  | some (eq, recursor) =>
                    match entry.type.references.eraseDups.filter (· ≠ eq) with
                    | [q] =>
                      let refs : Certified.Quotient.Refs β := ⟨eq, q, c, r, r⟩
                      if hl : Certified.Quotient.HasLift entries refs recursor then
                        if hq : Certified.Quotient.HasFormer entries refs then
                          if hc : Certified.Quotient.HasCtor entries refs then
                            if hE : Certified.Quotient.EqInterface entries eq recursor then
                              if hn : ls.length = 2 then
                                reduceByRuleC fuel entries Γ e
                                  ((Certified.Quotient.liftRuleLhs refs).instL ls)
                                  ((Certified.Quotient.liftRuleRhs refs).instL ls)
                                  (Certified.Quotient.liftRule_claim Γ hq hc hl hE hn) bargs
                              else throw .noMatch
                            else throw .noMatch
                          else throw .noMatch
                        else throw .noMatch
                      else throw .noMatch
                    | _ => throw .noMatch
                  | none =>
                    match entry.type.references.eraseDups.filter (· ≠ c) with
                    | [q] =>
                      let refs : Certified.Quotient.Refs β := ⟨q, q, c, c, r⟩
                      reduceByRuleC fuel entries Γ e
                        ((Certified.Quotient.indRuleLhs refs).instL ls)
                        ((Certified.Quotient.indRuleRhs refs).instL ls)
                        (Certified.Quotient.indRule_claim refs Γ ls) bargs
                    | _ => throw .noMatch
                | _ => throw .noMatch
            | none => throw .noMatch
          else throw .noMatch
        | none => throw .noMatch
      | none => throw .noMatch
    | _ => throw .noMatch

/-- Projection iota: a projection of a constructor application reduces
through the structure's published iota rule, whose endpoints are typed by
inference. -/
def projIotaC : Nat → (entries : Environment β) → (Γ : Context β) → (r : ConstRef β) → (i : Nat) →
    (x : AExpr β) → KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (.proj r i x))
  | 0, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, r, i, x => do
    let ⟨x', hx, stopped⟩ ← whnfC fuel entries Γ x
    KM.remember stopped <| do
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
                  let ⟨TL, hL⟩ ← inferAC fuel entries Γ (law.lhs.instL ls)
                  let ⟨TR, hR⟩ ← inferAC fuel entries Γ (law.rhs.instL ls)
                  let appL ← applyTypedC fuel entries Γ (law.lhs.instL ls) TL hL cargs
                  let appR ← applyTypedC fuel entries Γ (law.rhs.instL ls) TR hR cargs
                  if hl : appL.result = .proj r i x' then
                    have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                      ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                    have hc : ConvClaim.{u,v} entries Γ (.proj r i x) appL.result := by
                      rw [hl]
                      exact ConvClaim.proj (ConvClaim.ofReduction hx)
                    return ⟨appR.result, ReductionClaim.iota hc appL.typed.formed
                      (appL.conv.symm.trans ((heq.appN cargs).trans appR.conv)) appR.typed.formed⟩
                  else throw .noMatch
                else throw .noMatch
              | none => throw .noMatch
            else throw .noMatch
          | none => throw .noMatch
        | none => throw .noMatch
      | _ => throw .noMatch

/-- Structure eta: a constructor application of a structure converts to any
term of the structure's type whose projections convert to the fields, through
the published eta rule, whose endpoints are typed by inference. -/
def etaStructC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
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
                let ⟨TL, hL⟩ ← inferAC fuel entries Γ (law.lhs.instL ls)
                let ⟨TR, hR⟩ ← inferAC fuel entries Γ (law.rhs.instL ls)
                let appL ← applyTypedC fuel entries Γ (law.lhs.instL ls) TL hL bargs
                let appR ← applyTypedC fuel entries Γ (law.rhs.instL ls) TR hR bargs
                if hb : appR.result = b then do
                  let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ a appL.result
                  have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                    ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                  have hr : ConversionClaim.{u,v} entries Γ (AExpr.appN (law.rhs.instL ls) bargs) b := by
                    rw [← hb]
                    exact appR.conv
                  return ⟨hc.trans appL.typed.formed
                    (ConvClaim.ofConversion (appL.conv.symm.trans ((heq.appN bargs).trans hr)))⟩
                else throw .noMatch
              else throw .noMatch
            | none => throw .noMatch
          else throw .noMatch
        | none => throw .noMatch
      | none => throw .noMatch
    | _ => throw .noMatch

/-- Proof irrelevance: both sides inhabit propositions, whose proofs have
the same interpretation even when the propositions differ. -/
def proofIrrelevanceC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b => do
    let ⟨A, haA⟩ ← inferAC fuel entries Γ a
    let ⟨SA, hSA⟩ ← inferAC fuel entries Γ A
    let ⟨l, hA⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ SA) hSA)
    if hl : levelIsZero l then do
      let ⟨B, hbB⟩ ← inferAC fuel entries Γ b
      if hBA : B = A then
        return ⟨ConvClaim.proofIrrel (hA.sortEquiv (levelIsZero_sound hl)) haA (hBA ▸ hbB)⟩
      else
        let ⟨SB, hSB⟩ ← inferAC fuel entries Γ B
        let ⟨lB, hB⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ SB) hSB)
        if hlB : levelIsZero lB then
          return ⟨ConvClaim.proofIrrelHet (hA.sortEquiv (levelIsZero_sound hl))
            (hB.sortEquiv (levelIsZero_sound hlB)) haA hbB⟩
        else throw .noMatch
    else throw .noMatch

/-- Weak head normalization, retaining the reason a partial reduct stopped.
Complete normalizations of reducible-looking terms are cached. -/
def whnfC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Normalized.{u,v} entries Γ e)
  | 0, _, _, e => pure ⟨e, ReductionClaim.refl e, some .exhausted⟩
  | fuel + 1, entries, Γ, e => do
    let n ← KM.attempt KM.tick
    if let .error failure := n then
      return ⟨e, ReductionClaim.refl e, some failure⟩
    let cacheable := match e with | .app .. | .const .. | .proj .. | .letE .. => true | _ => false
    let cache ← KM.cache
    let cached := if cacheable then cache.findWhnf e else none
    match cached with
    | some n => pure n
    | none =>
      let result : Normalized.{u,v} entries Γ e ← do
        match ← KM.attempt (stepC fuel entries Γ e) with
        | .ok ⟨e', h⟩ =>
          let ⟨e'', h', stopped⟩ ← whnfC fuel entries Γ e'
          pure ⟨e'', h.trans h', stopped⟩
        | .error .noMatch => pure ⟨e, ReductionClaim.refl e, none⟩
        | .error failure => pure ⟨e, ReductionClaim.refl e, some failure⟩
      if cacheable && result.stopped.isNone then KM.modifyCache (·.addWhnf e result)
      pure result

/-- Weak head normalization without delta at the head: beta, zeta, iota,
quotient and projection rules only. -/
def whnfCoreC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Normalized.{u,v} entries Γ e)
  | 0, _, _, e => pure ⟨e, ReductionClaim.refl e, some .exhausted⟩
  | fuel + 1, entries, Γ, e => do
    let attemptStep : KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e) :=
      if hasDeltaHead entries e then
        match e with
        | .app f x =>
          KM.orElse (natStepC fuel entries Γ (.app f x)) fun _ =>
          KM.orElse (KM.mapError SearchFailure.speculative (iotaC fuel entries Γ (.app f x))) fun _ =>
            KM.mapError SearchFailure.speculative (quotIotaC fuel entries Γ (.app f x))
        | _ => throw .noMatch
      else stepC fuel entries Γ e
    let next ← KM.attempt attemptStep
    match next with
    | .ok ⟨e', h⟩ =>
      let ⟨e'', h', stopped⟩ ← whnfCoreC fuel entries Γ e'
      pure ⟨e'', h.trans h', stopped⟩
    | .error .noMatch => pure ⟨e, ReductionClaim.refl e, none⟩
    | .error failure => pure ⟨e, ReductionClaim.refl e, some failure⟩

/-- Lazy delta: normalize both sides without head delta and compare; before
constructing unfolded bodies, try congruence for equal constant heads. Full
argument conversion is a bounded optional attempt: if a function ignores
different arguments, unfolding can still establish equality after congruence
fails. Argument failures use the ordinary conversion cache; failure of the
congruence attempt itself is never cached as failure of the whole conversion.
On the first round only, proof irrelevance is tried before unfolding a proof. -/
def lazyDeltaC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) → Bool →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b, first => do
    let ⟨a', ha, stoppedA⟩ ← whnfCoreC fuel entries Γ a
    let ⟨b', hb, stoppedB⟩ ← whnfCoreC fuel entries Γ b
    let compared : KM.{u,v} entries Γ (Conv.{u,v} entries Γ a' b') :=
      if h : a' = b' then pure ⟨h ▸ ConvClaim.refl a'⟩ else
      let proof : KM.{u,v} entries Γ (Conv.{u,v} entries Γ a' b') :=
        if first && (proofHead entries a' || proofHead entries b') then
          proofIrrelevanceC fuel entries Γ a' b'
        else throw .noMatch
      KM.orElse proof fun _ =>
      let congruence : KM.{u,v} entries Γ (Conv.{u,v} entries Γ a' b') :=
        if sameConstHead a' b' && hasDeltaHead entries a' && hasDeltaHead entries b' then
          match quickConv.{u,v} entries Γ a' b' with
          | some c => pure c
          | none =>
            match a', b' with
            | .app f x, .app g y =>
              KM.speculate 256 (appCongrC fuel entries Γ (.app f x) (.app g y))
            | _, _ => throw .noMatch
        else throw .noMatch
      KM.orElse congruence fun _ =>
        match deltaHead.{u,v} entries Γ a', deltaHead.{u,v} entries Γ b' with
        | none, none => isDefEqCoreC fuel entries Γ a' b'
        | some ⟨a'', ha'⟩, none =>
          KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions ha' (ReductionClaim.refl b') hc⟩)
            (lazyDeltaC fuel entries Γ a'' b' false)
        | none, some ⟨b'', hb'⟩ =>
          KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions (ReductionClaim.refl a') hb' hc⟩)
            (lazyDeltaC fuel entries Γ a' b'' false)
        | some ⟨a'', ha'⟩, some ⟨b'', hb'⟩ =>
          KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions ha' hb' hc⟩)
            (lazyDeltaC fuel entries Γ a'' b'' false)
    KM.remember stoppedA <| KM.remember stoppedB <|
      KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions ha hb hc⟩) compared

/-- Type inference on annotated terms, validating every binder annotation.
Compound terms' types are cached; a binder's body is inferred in its own
frame. -/
def inferAC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Typed.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e => do
    KM.tick
    let cacheable := match e with | .bvar .. | .sort .. | .const .. | .natLit .. => false | _ => true
    let cache ← KM.cache
    let cached := if cacheable then cache.findInfer e else none
    match cached with
    | some t => pure t
    | none =>
      let result ← inferCore fuel entries Γ e
      if cacheable then KM.modifyCache (·.addInfer e result)
      pure result

/-- A binder body's type and the sort of that type. A λ body's type is the Π
its own inference builds, and that inference already has the Π's sort, so a
tower of λs is inferred in one pass instead of re-inferring each inner Π. -/
def inferBodyC : Nat → (entries : Environment β) → (Γ : Context β) → (b : AExpr β) →
    KM.{u,v} entries Γ (TypedBody.{u,v} entries Γ b)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, .lam p D c => do
    KM.tick
    let ⟨S, hS⟩ ← inferAC fuel entries Γ D
    let ⟨lD, hD⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ S) hS)
    let ⟨C, hc, lC, hC⟩ ← KM.inFrame (Γ' := Γ.push D) (inferBodyC fuel entries (Γ.push D) c)
    if hp : p = zeroCondition lC then
      return ⟨.forallE p D C, TypingClaim.lam hD hC hc hp, .imax lD lC,
        TypingClaim.forallE hD hC hp⟩
    else throw (.malformed "lambda annotation disagrees with its codomain sort")
  | fuel + 1, entries, Γ, b => do
    let ⟨B, hb⟩ ← inferAC fuel entries Γ b
    let ⟨SB, hSB⟩ ← inferAC fuel entries Γ B
    let ⟨lB, hB⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ SB) hSB)
    return ⟨B, hb, lB, hB⟩

/-- The inference rules, one constructor at a time. -/
def inferCore : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Typed.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .bvar i =>
      match h : Γ[i]? with
      | some A => pure ⟨A, TypingClaim.bvar h⟩
      | none => throw (.malformed "local variable is out of scope")
    | .sort l => pure ⟨.sort (.succ l), TypingClaim.sort l⟩
    | .const r ls =>
      match h : entries r with
      | some entry =>
        if hn : ls.length = entry.universes then
          pure ⟨entry.type.instL ls, TypingClaim.const h hn⟩
        else throw (.malformed "constant has the wrong number of universe arguments")
      | none => throw (.malformed "constant is not installed")
    | .app f a => do
      let ⟨T, hf⟩ ← inferAC fuel entries Γ f
      let ⟨p, D, B, hf'⟩ ← KM.ofSearch (piOf (← whnfC fuel entries Γ T) hf)
      let ⟨A', ha⟩ ← inferAC fuel entries Γ a
      let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
      return ⟨B.inst a, TypingClaim.app (p := p) hf' (ha.convF hf'.formedType.domain hc)⟩
    | .lam p D b => do
      let ⟨S, hS⟩ ← inferAC fuel entries Γ D
      let ⟨_, hD⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ S) hS)
      let ⟨B, hb, lB, hB⟩ ← KM.inFrame (Γ' := Γ.push D) (inferBodyC fuel entries (Γ.push D) b)
      if hp : p = zeroCondition lB then
        return ⟨.forallE p D B, TypingClaim.lam hD hB hb hp⟩
      else throw (.malformed "lambda annotation disagrees with its codomain sort")
    | .forallE p D B => do
      let ⟨S, hS⟩ ← inferAC fuel entries Γ D
      let ⟨lD, hD⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ S) hS)
      let ⟨lB, hB⟩ ← KM.inFrame (Γ' := Γ.push D) (do
        let ⟨SB, hSB⟩ ← inferAC fuel entries (Γ.push D) B
        KM.ofSearch (sortOf (← whnfC fuel entries (Γ.push D) SB) hSB))
      if hp : p = zeroCondition lB then
        return ⟨.sort (.imax lD lB), TypingClaim.forallE hD hB hp⟩
      else throw (.malformed "Pi annotation disagrees with its codomain sort")
    | .letE t v b => do
      let ⟨S, hS⟩ ← inferAC fuel entries Γ t
      let ⟨l, ht⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ S) hS)
      let ⟨A', hv⟩ ← inferAC fuel entries Γ v
      let ⟨hc⟩ ← isDefEqC fuel entries Γ A' t
      have hv' := hv.convF ht.formed hc
      -- The body with the let variable opaque; failing that, the body with the
      -- value substituted, as the official kernel infers it.
      KM.orElse
        (do
          let ⟨B, hb⟩ ← KM.inFrame (Γ' := Γ.push t) (inferAC fuel entries (Γ.push t) b)
          return ⟨B.inst v, TypingClaim.letE (l := l) ht hv' hb⟩)
        fun _ => do
          let ⟨B, hb⟩ ← inferAC fuel entries Γ (b.inst v)
          return ⟨B, TypingClaim.letSubst ht hv' hb⟩
    | .proj r i x => do
      let ⟨T, _⟩ ← inferAC fuel entries Γ x
      let normalized ← whnfC fuel entries Γ T
      KM.remember normalized.stopped <| do
        match spine normalized.result [] with
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
                      let app ← applyTypedC fuel entries Γ (pj.instL ls) (pjT.instL ls)
                        (TypingClaim.fact h (List.mem_of_getElem? hf) hn) (params ++ [x])
                      if hres : app.result = .proj r i x then
                        return ⟨app.type, hres ▸ app.typed⟩
                      else throw .noMatch
                    else throw .noMatch
                  | _ => throw .noMatch
                else if i ≥ nf then throw (.malformed "projection field index is out of range")
                else throw (.unresolved "structure parameter count does not match")
              | none => throw (.unsupported "projection family has no admitted structure interface")
            | none => throw (.malformed "projection family is not installed")
          else throw (.unresolved "projection family does not match the inferred major type")
        | _ => throw (.unresolved "the projection major type did not reduce to a structure")
    | .natLit f n =>
      match h : entries f with
      | some entry =>
        match findNatural entry.facts with
        | some ⟨(_, _), hf⟩ =>
          if hn : entry.universes = 0 then pure ⟨.const f [], TypingClaim.natLit h hf hn n⟩
          else throw (.malformed "literal family has universe parameters")
        | none => throw (.malformed "literal family is not the admitted natural numbers")
      | none => throw (.malformed "literal family is not installed")

/-- Application congruence along the spine. Only the heads and arguments
enter full conversion: every partial application has already had its head
reduced by the surrounding conversion search. Re-entering normalization for
each prefix repeats a linear spine walk and makes long applications quadratic.
Each spine node spends one unit of work and contributes the existing certified
application-congruence rule. -/
def appCongrC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, .app f x, .app g y => do
    KM.tick
    let ⟨hf⟩ ← appCongrC fuel entries Γ f g
    let ⟨hx⟩ ← isDefEqC fuel entries Γ x y
    return ⟨ConvClaim.app hf hx⟩
  | fuel + 1, entries, Γ, a, b => isDefEqC fuel entries Γ a b

/-- Structural comparison of two reduced terms, with eta and proof irrelevance. -/
def isDefEqCoreC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b =>
    if h : a = b then pure ⟨h ▸ ConvClaim.refl a⟩ else
    let structural : KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b) :=
      match a, b with
      | .sort l, .sort l' =>
        if he : levelEquiv l l' then pure ⟨ConvClaim.sort (levelEquiv_sound he)⟩ else throw .noMatch
      | .const r ls, .const r' ls' =>
        if hr : r = r' then
          if hl : levelsEquiv ls ls' then
            pure ⟨hr ▸ ConvClaim.const (levelsEquiv_sound hl)⟩
          else throw .noMatch
        else throw .noMatch
      | .bvar i, .bvar j => if hij : i = j then pure ⟨hij ▸ ConvClaim.refl _⟩ else throw .noMatch
      | .natLit f n, .natLit g m =>
        if hnm : n = m then pure ⟨hnm ▸ ConvClaim.natLit f g n⟩ else throw .noMatch
      | .natLit f n, b => do
        let u ← (unfoldLit entries Γ f n : Option _)
        let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ u.result b
        return ⟨u.conv.trans u.formed hc⟩
      | a, .natLit f n => do
        let u ← (unfoldLit entries Γ f n : Option _)
        let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ a u.result
        return ⟨hc.trans u.formed u.conv.symm⟩
      | .app f x, .app g y =>
        KM.orElse (appCongrC fuel entries Γ (.app f x) (.app g y)) fun _ => do
          -- Rule matching also calls this function before normalization. Keep
          -- its old prefix conversion when a direct spine comparison fails.
          let ⟨hf⟩ ← isDefEqC fuel entries Γ f g
          let ⟨hx⟩ ← isDefEqC fuel entries Γ x y
          return ⟨ConvClaim.app hf hx⟩
      | .lam p D e, .lam p' D' e' =>
        if hp : p = p' then do
          let ⟨hD⟩ ← isDefEqC fuel entries Γ D D'
          let ⟨he⟩ ← KM.inFrame (Γ' := Γ.push D) (isDefEqC fuel entries (Γ.push D) e e')
          return ⟨hp ▸ ConvClaim.lam hD he⟩
        else throw .noMatch
      | .forallE p D B, .forallE p' D' B' =>
        if hp : p = p' then do
          let ⟨hD⟩ ← isDefEqC fuel entries Γ D D'
          let ⟨hB⟩ ← KM.inFrame (Γ' := Γ.push D) (isDefEqC fuel entries (Γ.push D) B B')
          return ⟨hp ▸ ConvClaim.forallE hD hB⟩
        else throw .noMatch
      | .proj r i x, .proj r' i' y =>
        if hr : r = r' then
          if hi : i = i' then do
            let ⟨hx⟩ ← isDefEqC fuel entries Γ x y
            return ⟨hr ▸ hi ▸ ConvClaim.proj hx⟩
          else throw .noMatch
        else throw .noMatch
      | .lam p D e, g => do
        let ⟨T, hg⟩ ← inferAC fuel entries Γ g
        let ⟨p'', D'', _, hg'⟩ ← KM.ofSearch (piOf (← whnfC fuel entries Γ T) hg)
        if hp : p'' = p then do
          let ⟨hD⟩ ← isDefEqC fuel entries Γ D'' D
          let ⟨he⟩ ← KM.inFrame (Γ' := Γ.push D)
            (isDefEqC fuel entries (Γ.push D) e (.app (g.liftN 1) (.bvar 0)))
          return ⟨ConvClaim.eta (hp ▸ hg') hD he⟩
        else throw .noMatch
      | g, .lam p D e => do
        let ⟨T, hg⟩ ← inferAC fuel entries Γ g
        let ⟨p'', D'', _, hg'⟩ ← KM.ofSearch (piOf (← whnfC fuel entries Γ T) hg)
        if hp : p'' = p then do
          let ⟨hD⟩ ← isDefEqC fuel entries Γ D'' D
          let ⟨he⟩ ← KM.inFrame (Γ' := Γ.push D)
            (isDefEqC fuel entries (Γ.push D) e (.app (g.liftN 1) (.bvar 0)))
          return ⟨(ConvClaim.eta (hp ▸ hg') hD he).symm⟩
        else throw .noMatch
      | _, _ => throw .noMatch
    KM.mapError SearchFailure.conversion <|
      KM.orElse structural fun _ =>
        KM.orElse (etaStructC fuel entries Γ a b) fun _ =>
          KM.orElse (KM.map (fun ⟨c⟩ => ⟨c.symm⟩) (etaStructC fuel entries Γ b a)) fun _ =>
            if notProof entries a || notProof entries b then throw .noMatch
            else proofIrrelevanceC fuel entries Γ a b

/-- Conversion by lazy delta (`lazyDeltaC`): reduce both sides without
unfolding their heads, compare, and unfold only as needed. Outcomes that did
not run out of fuel are cached. -/
def isDefEqC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b =>
    if h : a = b then pure ⟨h ▸ ConvClaim.refl a⟩ else do
      KM.tick
      let cache ← KM.cache
      match cache.findConv a b with
      | some r => KM.ofSearch r
      | none =>
        let r ← KM.attempt (KM.mapError SearchFailure.conversion (lazyDeltaC fuel entries Γ a b true))
        match r with
        | .error .exhausted => pure ⟨⟩
        | _ => KM.modifyCache (·.addConv a b r)
        KM.ofSearch r

end

/-- The work budget of a top-level call, per unit of fuel. -/
def workPerFuel : Nat := 10

/-! ## Uncached entry points

The functions above run in `KM`; these start each call with an empty cache
and a work budget of `fuel * workPerFuel`, and keep the kernel's original
interface. -/

def step (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Search (Reduced.{u,v} entries Γ e) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (stepC.{u,v} fuel entries Γ e)

def applyTyped (fuel : Nat) (entries : Environment β) (Γ : Context β) (f F : AExpr β)
    (hf : TypingClaim.{u,v} entries Γ f F) (args : List (AExpr β)) :
    Search (Applied.{u,v} entries Γ f args) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (applyTypedC.{u,v} fuel entries Γ f F hf args)

def iota (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Search (Reduced.{u,v} entries Γ e) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (iotaC.{u,v} fuel entries Γ e)

def proofIrrelevance (fuel : Nat) (entries : Environment β) (Γ : Context β) (a b : AExpr β) :
    Search (Conv.{u,v} entries Γ a b) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (proofIrrelevanceC.{u,v} fuel entries Γ a b)

def whnf (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Normalized.{u,v} entries Γ e :=
  match KM.run (fun _ => 0) (fuel * workPerFuel) (whnfC.{u,v} fuel entries Γ e) with
  | .ok n => n
  | .error failure => ⟨e, ReductionClaim.refl e, some failure⟩

def inferA (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Search (Typed.{u,v} entries Γ e) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (inferAC.{u,v} fuel entries Γ e)

def isDefEq (fuel : Nat) (entries : Environment β) (Γ : Context β) (a b : AExpr β) :
    Search (Conv.{u,v} entries Γ a b) :=
  KM.run (fun _ => 0) (fuel * workPerFuel) (isDefEqC.{u,v} fuel entries Γ a b)

end Ix.Kernel
