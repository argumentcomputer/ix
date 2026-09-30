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

omit [DecidableEq β] in
/-- A decomposed spine reassembles to its term. -/
theorem spine_appN (e : AExpr β) :
    ∀ acc : List (AExpr β), AExpr.appN (spine e acc).1 (spine e acc).2 = AExpr.appN e acc := by
  induction e with
  | app f a ihf _ => intro acc; simp only [spine]; exact ihf (a :: acc)
  | _ => intro acc; rfl

omit [DecidableEq β] in
theorem appN_take_drop (head : AExpr β) (args : List (AExpr β)) (k : Nat) :
    AExpr.appN (AExpr.appN head (args.take k)) (args.drop k) = AExpr.appN head args := by
  rw [← AExpr.appN_append, List.take_append_drop]

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

/-- A definition's unfolding height (`ConstantFact.height`), 0 if it has none. -/
def heightOf (facts : List (ConstantFact β)) : Nat :=
  (facts.findSome? fun | .height n => some n | _ => none).getD 0

/-- The height of an `abbrev`: above every regular height. Such heads unfold
eagerly and are never compared argument-wise, as in the official kernel. -/
def abbrevHeight : Nat := 2 ^ 32

/-- The unfolding height of a term's head constant. -/
def headHeight (entries : Environment β) (e : AExpr β) : Nat :=
  match spine e [] with
  | (.const r _, _) => ((entries r).map (heightOf ·.facts)).getD 0
  | _ => 0

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

/-- Delta at the head of the spine `appN head args`: the head constant's body at
its universe instance, applied to the same arguments. The application is built
once around the body (con-leche's `unfoldDefinition`). -/
def deltaSpine (entries : Environment β) (Γ : Context β) (head : AExpr β) (args : List (AExpr β)) :
    Option (Reduced.{u,v} entries Γ (AExpr.appN head args)) :=
  match head with
  | .const r ls =>
    match h : entries r with
    | some entry =>
      match hb : entry.body with
      | some body =>
        if hn : ls.length = entry.universes then
          some ⟨AExpr.appN (body.instL ls) args, (ReductionClaim.delta h hb hn).appHeadN args⟩
        else none
      | none => none
    | none => none
  | _ => none

/-- Delta at the head of an application spine, decomposed once. -/
def deltaHead (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    Option (Reduced.{u,v} entries Γ e) :=
  let sp := spine e []
  have hsp : AExpr.appN sp.1 sp.2 = e := spine_appN e []
  (deltaSpine entries Γ sp.1 sp.2).map fun r => ⟨r.result, hsp ▸ r.claim⟩

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
theorem deltaSpine_isSome (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    ∀ acc : List (AExpr β),
      (deltaSpine.{u,v} entries Γ (spine e acc).1 (spine e acc).2).isSome = hasDeltaHead entries e := by
  induction e with
  | const r ls =>
    intro acc
    simp only [hasDeltaHead, deltaSpine, spine]
    split <;> split <;> simp_all
    subst_vars
    split <;> simp_all
  | app f a ihf _ => intro acc; simpa only [spine, hasDeltaHead] using ihf (a :: acc)
  | _ => intro acc; rfl

omit [DecidableEq β] in
theorem hasDeltaHead_eq (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    hasDeltaHead entries e = (deltaHead.{u,v} entries Γ e).isSome := by
  simp only [deltaHead, Option.isSome_map, deltaSpine_isSome]

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

/-- A proof-point witness, erased at run time. -/
structure ProofValue (entries : Environment β) (Γ : Context β) (e : AExpr β) : Type u where
  claim : ProofValueClaim.{u,v} entries Γ e

/-- Read a certified proof value without normalization or argument inference.
Only the outermost Pi annotation in a constant's stored type is instantiated
and checked; a deeper telescope annotation would not justify this rule.
Proposition expressions themselves are deliberately not proof values. -/
def proofValue (entries : Environment β) (Γ : Context β) : (e : AExpr β) →
    Option (ProofValue.{u,v} entries Γ e)
  | .const r ls =>
    match hr : entries r with
    | some entry =>
      match ht : entry.type with
      | .forallE p _ _ =>
        if hn : ls.length = entry.universes then
          if hp : instCondition ls p = .always then
            some ⟨ProofValueClaim.const hr hn ht hp⟩
          else none
        else none
      | _ => none
    | none => none
  | .lam (.allZero [] _) _ _ => some ⟨ProofValueClaim.lam⟩
  | .app f _ => (proofValue entries Γ f).map fun ⟨hf⟩ => ⟨hf.app⟩
  | _ => none

/-- Proof irrelevance when both proof points can be read structurally. -/
def quickProofIrrelevance (entries : Environment β) (Γ : Context β) (a b : AExpr β) :
    Option (Conv.{u,v} entries Γ a b) := do
  let ⟨ha⟩ ← proofValue entries Γ a
  let ⟨hb⟩ ← proofValue entries Γ b
  return ⟨ConvClaim.ofProofValues ha hb⟩

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

/-- Decompose a term's application spine once and run a step on it. -/
def onSpine (e : AExpr β) (step : (head : AExpr β) → (args : List (AExpr β)) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN head args))) :
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e) :=
  let sp := spine e []
  have hsp : AExpr.appN sp.1 sp.2 = e := spine_appN e []
  hsp ▸ step sp.1 sp.2

/-- Run a rule on the first `k` arguments of a spine and carry its reduct
through the remaining ones (`ReductionClaim.appHeadN`). A shorter spine does
not match. -/
def atPrefix (k : Nat) (head : AExpr β) (args : List (AExpr β))
    (rule : (pre : List (AExpr β)) → KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN head pre))) :
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN head args)) :=
  if k = args.length then rule args
  else if k < args.length then
    KM.map (fun (r : Reduced.{u,v} entries Γ (AExpr.appN head (args.take k))) =>
        ⟨AExpr.appN r.result (args.drop k), appN_take_drop head args k ▸ r.claim.appHeadN (args.drop k)⟩)
      (rule (args.take k))
  else throw .noMatch

/-- Pairwise conversion of two argument lists. -/
structure ConvArgs (entries : Environment β) (Γ : Context β) (xs ys : List (AExpr β)) : Type u where
  down : ConvClaim.Args.{u,v} entries Γ xs ys

/-- Compare two argument lists pairwise by `conv`, each pair spending one unit
of work. Lists of different lengths do not match. -/
def congrArgs (conv : (x y : AExpr β) → KM.{u,v} entries Γ (Conv.{u,v} entries Γ x y)) :
    (xs ys : List (AExpr β)) → KM.{u,v} entries Γ (ConvArgs.{u,v} entries Γ xs ys)
  | [], [] => pure ⟨trivial⟩
  | x :: xs, y :: ys => do
    KM.tick
    let ⟨hx⟩ ← conv x y
    let ⟨hs⟩ ← congrArgs conv xs ys
    return ⟨⟨hx, hs⟩⟩
  | _, _ => throw .noMatch

omit [DecidableEq β] in
theorem ConvClaim.ofSpines {a b f g : AExpr β} {xs ys : List (AExpr β)}
    (ha : AExpr.appN f xs = a) (hb : AExpr.appN g ys = b)
    (h : ConvClaim.{u,v} entries Γ (AExpr.appN f xs) (AExpr.appN g ys)) :
    ConvClaim.{u,v} entries Γ a b := by
  subst ha hb
  exact h

/-- A binder body's inferred type and that type's sort, at the body's context. -/
structure TypedBody (entries : Environment β) (Γ : Context β) (b : AExpr β) : Type u where
  type : AExpr β
  typed : TypingClaim.{u,v} entries Γ b type
  level : VLevel
  sorted : TypingClaim.{u,v} entries Γ type (.sort level)

/-- Facts that may enable reduction of an application headed by their owner.
Natural and structure formers, constructors, and typed facts do not do so. -/
def headReductionFact : ConstantFact β → Bool
  | .natOp _ | .natTest .. | .recursor .. | .quotientLift .. | .quotient .ind => true
  | _ => false

/-- Whether an application headed by the entry's constant, at the supplied
universe arguments, may reduce: a body at the supplied universe arity, or any
applicable kind of reduction fact. -/
def constHeadActive (entry : ConstantEntry β) (ls : List VLevel) : Bool :=
  (entry.body.isSome && ls.length == entry.universes) || entry.facts.any headReductionFact

/-- The application depth when the head cannot reduce, inspected in one
pass. Lambdas, lets, projections, and constants that are `constHeadActive`
keep the ordinary reduction path. `stepSpineC`'s head dispatch makes the same
classification on the decomposed spine: a neutral head tries no rule. -/
def neutralSpineDepth (entries : Environment β) : AExpr β → Nat → Option Nat
  | .app f _, depth => neutralSpineDepth entries f (depth + 1)
  | .const r ls, depth =>
    match entries r with
    | none => some depth
    | some entry => if constHeadActive entry ls then none else some depth
  | .bvar _, depth | .sort _, depth | .forallE .., depth | .natLit .., depth => some depth
  | _, _ => none

omit [DecidableEq β] in
/-- A term supports its own application spine. -/
theorem SupportClaim.ofSpine {e h : AExpr β} {args : List (AExpr β)}
    (hsp : spine e [] = (h, args)) : SupportClaim.{u,v} entries Γ e (AExpr.appN h args) := by
  have he : AExpr.appN h args = e := by simpa [hsp, AExpr.appN] using spine_appN e []
  rw [he]
  exact SupportClaim.refl e

/-- The endpoints of a rule applied to an argument spine by beta steps. Each
reduction holds wherever the witness `w` (the rule's target) is well denoted. -/
structure RuleApplied (entries : Environment β) (Γ : Context β) (w lhs rhs : AExpr β)
    (args : List (AExpr β)) : Type u where
  lhs' : AExpr β
  rhs' : AExpr β
  hl : IOReductionClaim.{u,v} entries Γ w (AExpr.appN lhs args) lhs'
  hr : IOReductionClaim.{u,v} entries Γ w (AExpr.appN rhs args) rhs'

/-- A typed head whose application to `args` is well denoted wherever `w` is:
the source of domain determination for those arguments. -/
structure Witness (entries : Environment β) (Γ : Context β) (w : AExpr β)
    (args : List (AExpr β)) : Type u where
  head : AExpr β
  type : AExpr β
  typed : IOClaim.{u,v} entries Γ w head type
  support : SupportClaim.{u,v} entries Γ w (AExpr.appN head args)

/-- An argument fitted at a domain under a witness. -/
structure Fit (entries : Environment β) (Γ : Context β) (w a D : AExpr β) : Type u where
  claim : IOClaim.{u,v} entries Γ w a D

/-- An argument's fit, and the witness for the arguments after it while it
still applies. -/
structure ArgFit (entries : Environment β) (Γ : Context β) (w a D : AExpr β)
    (rest : List (AExpr β)) : Type u where
  fit : IOClaim.{u,v} entries Γ w a D
  next : Option (Witness.{u,v} entries Γ w rest)

/-- Advance a witness through its first `n` arguments by substitution alone,
at uniformly non-Prop binders; `none` at the first other binder. -/
def Witness.advance {w : AExpr β} : (n : Nat) → (args : List (AExpr β)) →
    Witness.{u,v} entries Γ w args → Option (Witness.{u,v} entries Γ w (args.drop n))
  | 0, _, wit => some wit
  | n + 1, a :: rest, ⟨g, .forallE .never _ B, hg, hs⟩ =>
    have hs' : SupportClaim.{u,v} entries Γ w (AExpr.appN (.app g a) rest) := hs
    Witness.advance n rest ⟨.app g a, B.inst a, hg.appNever hs'.appNHead, hs'⟩
  | _ + 1, _, _ => none

/-- Fit an argument at a lambda's domain `D`. At a uniformly non-Prop binder of
the witness whose domain is `D` itself, domain determination supplies the fit
without inference and the witness advances by substitution. Otherwise
`checked` infers the argument and converts its type to `D`, the possibly-Prop
residue; the witness still advances if its domain is `D`. -/
def fitArg {w : AExpr β} (D a : AExpr β) (rest : List (AExpr β))
    (checked : Unit → KM.{u,v} entries Γ (Fit.{u,v} entries Γ w a D)) :
    Option (Witness.{u,v} entries Γ w (a :: rest)) →
      KM.{u,v} entries Γ (ArgFit.{u,v} entries Γ w a D rest)
  | some ⟨g, .forallE .never D' B, hg, hs⟩ =>
    have hs' : SupportClaim.{u,v} entries Γ w (AExpr.appN (.app g a) rest) := hs
    if h : D' = D then
      pure ⟨h ▸ hg.argNever hs'.appNHead, some ⟨.app g a, B.inst a, hg.appNever hs'.appNHead, hs'⟩⟩
    else do
      let ⟨fit⟩ ← checked ()
      pure ⟨fit, none⟩
  | some ⟨g, .forallE _ D' B, hg, hs⟩ => do
    have hs' : SupportClaim.{u,v} entries Γ w (AExpr.appN (.app g a) rest) := hs
    let ⟨fit⟩ ← checked ()
    if h : D' = D then
      pure ⟨fit, some ⟨.app g a, B.inst a, hg.app (h ▸ fit), hs'⟩⟩
    else pure ⟨fit, none⟩
  | _ => do
    let ⟨fit⟩ ← checked ()
    pure ⟨fit, none⟩

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

/-- One head reduction step on the spine `appN head args`, whose head is not
an application (con-leche's `whnfCoreStepI`/`whnfAppI` shape). The caller
decomposes the term once per round (`onSpine`); every rule attempt receives
the spine, and the reduct is rebuilt once around the reduced head or prefix
(`ReductionClaim.appHeadN`):

* a lambda head takes its first argument by beta, typed at a binder that may
  be Prop (`ReductionClaim.beta`), untyped at a `.never` one (`betaNever`);
* a let head reduces by zeta, a projection head by projection iota;
* a constant head tries the rules its facts enable, each at its own arity
  (`atPrefix`): literal operations (without `delta`, only on a closed
  prefix), iota, quotient rules; then, when `delta` is set, delta,
  `appN (body.instL ls) args`.

A neutral head (`neutralSpineDepth`) tries no rule. A spine with at least as
many arguments as the fuel is exhausted, as the former recursive step, which
spent one unit of fuel per application, exhausted it. -/
def stepSpineC : Nat → (entries : Environment β) → (Γ : Context β) → (delta : Bool) →
    (head : AExpr β) → (args : List (AExpr β)) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN head args))
  | 0, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, delta, head, args =>
    if fuel < args.length then throw .exhausted else
    match head, args with
    | .lam .never _ b, a :: rest =>
      pure ⟨AExpr.appN (b.inst a) rest, ReductionClaim.betaNever.appHeadN rest⟩
    | .lam p D b, a :: rest => do
      let ⟨A', ha⟩ ← inferAC fuel entries Γ a
      let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
      return ⟨AExpr.appN (b.inst a) rest, (ReductionClaim.beta (p := p) ha hc).appHeadN rest⟩
    | .letE _ v b, args => pure ⟨AExpr.appN (b.inst v) args, ReductionClaim.zeta.appHeadN args⟩
    | .proj r i x, args => do
      let ⟨x', hx⟩ ← KM.mapError SearchFailure.speculative (projIotaC fuel entries Γ r i x)
      return ⟨AExpr.appN x' args, hx.appHeadN args⟩
    | .const r ls, args =>
      match h : entries r with
      | none => throw .noMatch
      | some entry =>
        if !constHeadActive entry ls then throw .noMatch else
        let rules : Unit → KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN (.const r ls) args)) :=
          fun _ =>
            if entry.facts.any headReductionFact then
              let natArity : Nat :=
                match findNatOp entry.facts, findNatTest entry.facts with
                | some ⟨.pred, _⟩, _ => 1
                | some _, _ | none, some _ => 2
                | none, none => 0
              -- Literal evaluation inside conversion (`whnfCoreC`, no delta) only
              -- on closed terms, as in the official kernel and con-leche: an open
              -- argument would be normalized toward unary arithmetic. The `whnf`
              -- loop (with delta) stays unguarded.
              KM.orElse
                (if natArity = 0 then throw .noMatch
                 else atPrefix natArity (.const r ls) args fun pre =>
                  if delta || (AExpr.appN (.const r ls) pre).looseBound == 0 then
                    natStepC fuel entries Γ (AExpr.appN (.const r ls) pre)
                  else throw .noMatch) fun _ =>
              KM.orElse (KM.mapError SearchFailure.speculative (iotaC fuel entries Γ r ls entry h args))
                fun _ => KM.mapError SearchFailure.speculative (quotIotaC fuel entries Γ r ls entry h args)
            else throw .noMatch
        if delta then
          KM.orElse (rules ()) fun _ =>
            match hb : entry.body with
            | some body =>
              if hn : ls.length = entry.universes then
                pure ⟨AExpr.appN (body.instL ls) args, (ReductionClaim.delta h hb hn).appHeadN args⟩
              else throw .noMatch
            | none => throw .noMatch
        else rules ()
    | _, _ => throw .noMatch

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

/-- Apply both endpoints of a rule to an argument spine by beta steps. Each
argument is fitted at the lambdas' domain under the witness `w`, the rule's
target: at a uniformly non-Prop binder of the witness, by domain determination
from the target's own application node, with no inference; at any other binder
by inference and conversion to the domain, the possibly-Prop residue. -/
def applyIOC : Nat → (entries : Environment β) → (Γ : Context β) → (w lhs rhs : AExpr β) →
    SupportClaim.{u,v} entries Γ w lhs → SupportClaim.{u,v} entries Γ w rhs →
    (args : List (AExpr β)) → Option (Witness.{u,v} entries Γ w args) →
      KM.{u,v} entries Γ (RuleApplied.{u,v} entries Γ w lhs rhs args)
  | _, _, _, _, lhs, rhs, hl, hr, [], _ =>
    pure ⟨lhs, rhs, IOReductionClaim.refl hl, IOReductionClaim.refl hr⟩
  | 0, _, _, _, _, _, _, _, _ :: _, _ => throw .exhausted
  | fuel + 1, entries, Γ, w, lhs, rhs, hl, hr, a :: args, wit =>
    match lhs, rhs, hl, hr with
    | .lam _ D b, .lam _ D' b', hl, hr => do
      let checked := fun (E : AExpr β) (hE : SupportClaim.{u,v} entries Γ w E) =>
        show KM.{u,v} entries Γ (Fit.{u,v} entries Γ w a E) from do
          let ⟨A', ha⟩ ← inferAC fuel entries Γ a
          let ⟨hc⟩ ← isDefEqC fuel entries Γ A' E
          pure ⟨IOClaim.checked ha hc hE⟩
      let ⟨ha, wit'⟩ ← fitArg D a args (fun _ => checked D hl.lamDomain) wit
      let ⟨ha'⟩ ← if h : D' = D then pure ⟨h ▸ ha⟩ else checked D' hr.lamDomain
      have hl' := IOReductionClaim.beta hl ha
      have hr' := IOReductionClaim.beta hr ha'
      let rest ← applyIOC fuel entries Γ w (b.inst a) (b'.inst a) hl'.support hr'.support args wit'
      return ⟨rest.lhs', rest.rhs', IOReductionClaim.appN args hl' rest.hl,
        IOReductionClaim.appN args hr' rest.hr⟩
    | _, _, _, _ => throw .noMatch

/-- `applyTypedC` with its arguments fitted under a formed witness: at a
uniformly non-Prop binder of the witness whose domain is the lambda's, domain
determination types the argument without inference. -/
def applyTypedWC : Nat → (entries : Environment β) → (Γ : Context β) → (w f F : AExpr β) →
    FormedClaim.{u,v} entries Γ w → TypingClaim.{u,v} entries Γ f F → (args : List (AExpr β)) →
      Option (Witness.{u,v} entries Γ w args) → KM.{u,v} entries Γ (Applied.{u,v} entries Γ f args)
  | _, _, _, _, f, F, _, hf, [], _ => pure ⟨f, F, hf, ConversionClaim.refl _⟩
  | 0, _, _, _, _, _, _, _, _ :: _, _ => throw .exhausted
  | fuel + 1, entries, Γ, w, f, F, hw, hf, a :: args, wit =>
    match f, F, hf with
    | .lam p D b, .forallE p' D' B, hf =>
      if h : p = p' ∧ D = D' then do
        have hf' : TypingClaim.{u,v} entries Γ (.lam p D b) (.forallE p D B) := by
          obtain ⟨rfl, rfl⟩ := h
          exact hf
        let ⟨ha, wit'⟩ ← fitArg D a args (fun _ => do
          let ⟨A', ha⟩ ← inferAC fuel entries Γ a
          let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
          pure ⟨IOClaim.checked ha hc (SupportClaim.ofFormed hf'.formedType.domain)⟩) wit
        have haD : TypingClaim.{u,v} entries Γ a D := ha.typing hw
        let rest ← applyTypedWC fuel entries Γ w (b.inst a) (B.inst a) hw
          (TypingClaim.betaResult hf' haD) args wit'
        return ⟨rest.result, rest.type, rest.typed,
          (ConversionClaim.appN (ConversionClaim.beta hf' haD) args).trans rest.conv⟩
      else throw .noMatch
    | _, _, _ => throw .noMatch

/-- Iota: a recursor applied to a constructor reduces through the published
rule. The target is converted to the left instance (which checks the
constructor's parameters and the indices against the recursor's), and the
rule's equation takes it to the right instance. Both endpoints are applied by
`applyIOC` under the target: the parameters, motive and minors are fitted by
the recursor's own type along the target's spine, and the fields by the
constructor's type along the major's, so no argument is inferred at a
uniformly non-Prop binder. A literal major is unfolded one step first.
K-like reduction: if the major is not a constructor application but the
recursor has a single rule without fields, the constructor is synthesized
from the recursor's parameters; the conversion of the major to it is then
proof irrelevance, which holds exactly when the major's type converts to the
constructor's. The rule receives the spine of the recursor application and
fires at the recursor's arity; an over-applied spine reduces its prefix
(`atPrefix`), which is then the target and the witnesses' support. -/
def iotaC : Nat → (entries : Environment β) → (Γ : Context β) → (r : ConstRef β) →
    (ls : List VLevel) → (entry : ConstantEntry β) → entries r = some entry →
    (args : List (AExpr β)) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN (.const r ls) args))
  | 0, _, _, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, r, ls, entry, h, args =>
    match recursorInfo entry.facts with
    | some (np, nm, ni, rules) =>
      let majorIdx := np + 1 + nm + ni
      atPrefix (majorIdx + 1) (.const r ls) args fun args =>
        match hmaj : args[majorIdx]? with
        | some major => do
          let normalized ← whnfC fuel entries Γ major
          KM.remember normalized.stopped <| do
            have hsupp : SupportClaim.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                (AExpr.appN (.const r ls) args) := SupportClaim.refl _
            have hmajor : SupportClaim.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                normalized.result :=
              (hsupp.appNArg (List.mem_of_getElem? hmaj)).ofReduction normalized.claim
            let ⟨major', hmajor'⟩ :
                { m : AExpr β // SupportClaim.{u,v} entries Γ (AExpr.appN (.const r ls) args) m } :=
              match normalized.result, hmajor with
              | .natLit f n, hm => match unfoldLit.{u,v} entries Γ f n with
                | some u => ⟨u.result, SupportClaim.ofFormed u.formed⟩
                | none => ⟨.natLit f n, hm⟩
              | m, hm => ⟨m, hm⟩
            let fire := fun (j nf : Nat) (cargs : List (AExpr β))
                (fieldWit : Option (Witness.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                  (cargs.drop np))) =>
              show KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN (.const r ls) args)) from
              if cargs.length = np + nf then
                match hj : entry.equations[j]?, hf1 : entry.facts[1 + 2 * j]?,
                    hf2 : entry.facts[2 + 2 * j]? with
                | some law, some (.typed lhs _), some (.typed rhs _) =>
                  if hlaw : law.lhs = lhs ∧ law.rhs = rhs then
                    if hn : ls.length = entry.universes then do
                      let prefixArgs := args.take (np + 1 + nm)
                      let wit : Witness.{u,v} entries Γ (AExpr.appN (.const r ls) args) prefixArgs :=
                        ⟨.const r ls, entry.type.instL ls,
                          IOClaim.ofTyping (TypingClaim.const h hn), hsupp.appNTake _⟩
                      have hL := TypingClaim.fact h (List.mem_of_getElem? hf1) hn
                      have hR := TypingClaim.fact h (List.mem_of_getElem? hf2) hn
                      let app₁ ← applyIOC fuel entries Γ (AExpr.appN (.const r ls) args)
                        (lhs.instL ls) (rhs.instL ls)
                        (SupportClaim.ofFormed hL.formed) (SupportClaim.ofFormed hR.formed)
                        prefixArgs (some wit)
                      let app₂ ← applyIOC fuel entries Γ (AExpr.appN (.const r ls) args)
                        app₁.lhs' app₁.rhs' app₁.hl.support app₁.hr.support (cargs.drop np) fieldWit
                      let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ (AExpr.appN (.const r ls) args) app₂.lhs'
                      have heq : ConversionClaim.{u,v} entries Γ (lhs.instL ls) (rhs.instL ls) := by
                        have := ConversionClaim.equation (Γ := Γ) h (List.mem_of_getElem? hj) hn
                        rwa [hlaw.1, hlaw.2] at this
                      return ⟨app₂.rhs', ReductionClaim.iotaIO hc (app₁.hl.append app₂.hl)
                        (heq.appN _) (app₁.hr.append app₂.hr)⟩
                    else throw .noMatch
                  else throw .noMatch
                | _, _, _ => throw .noMatch
              else throw .noMatch
            match hms : spine major' [] with
            | (.const c cls, cargs) =>
              match ruleIndex rules c with
              | some (j, nf) =>
                let fieldWit : Option (Witness.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                    (cargs.drop np)) :=
                  match hc : entries c with
                  | some centry =>
                    if hcn : cls.length = centry.universes then
                      Witness.advance np cargs ⟨.const c cls, centry.type.instL cls,
                        IOClaim.ofTyping (TypingClaim.const hc hcn),
                        hmajor'.trans (SupportClaim.ofSpine hms)⟩
                    else none
                  | none => none
                fire j nf cargs fieldWit
              | none => throw .noMatch
            | _ =>
              match rules with
              | [(_, 0)] => fire 0 0 (args.take np) none
              | _ => throw .noMatch
        | none => throw .noMatch
    | none => throw .noMatch

/-- Reduce through a rule whose endpoints are typed by inference: the target is
converted to the left instance, and the rule's conversion takes it to the right
instance. The endpoints are applied by `applyIOC` under the target, first to
the prefix arguments with the prefix witness, then to the field arguments
with the field witness. -/
def reduceByRuleC : Nat → (entries : Environment β) → (Γ : Context β) → (e lhs rhs : AExpr β) →
    ConversionClaim.{u,v} entries Γ lhs rhs → (prefixArgs fieldArgs : List (AExpr β)) →
    Option (Witness.{u,v} entries Γ e prefixArgs) → Option (Witness.{u,v} entries Γ e fieldArgs) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e)
  | 0, _, _, _, _, _, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e, lhs, rhs, heq, prefixArgs, fieldArgs, wit₁, wit₂ => do
    let ⟨_, hL⟩ ← inferAC fuel entries Γ lhs
    let ⟨_, hR⟩ ← inferAC fuel entries Γ rhs
    let app₁ ← applyIOC fuel entries Γ e lhs rhs (SupportClaim.ofFormed hL.formed)
      (SupportClaim.ofFormed hR.formed) prefixArgs wit₁
    let app₂ ← applyIOC fuel entries Γ e app₁.lhs' app₁.rhs' app₁.hl.support app₁.hr.support
      fieldArgs wit₂
    let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ e app₂.lhs'
    return ⟨app₂.rhs', ReductionClaim.iotaIO hc (app₁.hl.append app₂.hl) (heq.appN _)
      (app₁.hr.append app₂.hr)⟩

/-- Quotient computation: the lift or the eliminator applied to a constructor
application reduces through its rule, which is derived from the published
facts. The lift's rule needs the former, the constructor, the lift itself, and
the equality family to be the admitted ones; the eliminator's rule holds
outright, since both sides are proofs. The former is read off the entry's
type as the reference other than the known ones. Like `iotaC`, the rule
receives the spine and fires at its arity. The rule's arguments are fitted
by the entry's type along the target and by the constructor's type along the
major. -/
def quotIotaC : Nat → (entries : Environment β) → (Γ : Context β) → (r : ConstRef β) →
    (ls : List VLevel) → (entry : ConstantEntry β) → entries r = some entry →
    (args : List (AExpr β)) →
      KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (AExpr.appN (.const r ls) args))
  | 0, _, _, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, r, ls, entry, hr, args =>
    match quotientRule entry.facts with
    | some role =>
      let arity := if role.isSome then 6 else 5
      atPrefix arity (.const r ls) args fun args =>
        match hmaj : args[arity - 1]? with
        | some major => do
          let normalized ← whnfC fuel entries Γ major
          KM.remember normalized.stopped <| do
            have hsupp : SupportClaim.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                (AExpr.appN (.const r ls) args) := SupportClaim.refl _
            have hmajor : SupportClaim.{u,v} entries Γ (AExpr.appN (.const r ls) args)
                normalized.result :=
              (hsupp.appNArg (List.mem_of_getElem? hmaj)).ofReduction normalized.claim
            match hms : spine normalized.result [] with
            | (.const c cls, [A, R, a]) =>
              let prefixArgs := args.take (arity - 1)
              let wit₁ : Option (Witness.{u,v} entries Γ (AExpr.appN (.const r ls) args) prefixArgs) :=
                if hn : ls.length = entry.universes then
                  some ⟨.const r ls, entry.type.instL ls, IOClaim.ofTyping (TypingClaim.const hr hn),
                    hsupp.appNTake _⟩
                else none
              let wit₂ : Option (Witness.{u,v} entries Γ (AExpr.appN (.const r ls) args) [a]) :=
                match hc : entries c with
                | some centry =>
                  if hcn : cls.length = centry.universes then
                    Witness.advance 2 [A, R, a] ⟨.const c cls, centry.type.instL cls,
                      IOClaim.ofTyping (TypingClaim.const hc hcn),
                      hmajor.trans (SupportClaim.ofSpine hms)⟩
                  else none
                | none => none
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
                            reduceByRuleC fuel entries Γ (AExpr.appN (.const r ls) args)
                              ((Certified.Quotient.liftRuleLhs refs).instL ls)
                              ((Certified.Quotient.liftRuleRhs refs).instL ls)
                              (Certified.Quotient.liftRule_claim Γ hq hc hl hE hn)
                              prefixArgs [a] wit₁ wit₂
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
                  reduceByRuleC fuel entries Γ (AExpr.appN (.const r ls) args)
                    ((Certified.Quotient.indRuleLhs refs).instL ls)
                    ((Certified.Quotient.indRuleRhs refs).instL ls)
                    (Certified.Quotient.indRule_claim refs Γ ls) prefixArgs [a] wit₁ wit₂
                | _ => throw .noMatch
            | _ => throw .noMatch
        | none => throw .noMatch
    | none => throw .noMatch

/-- Projection iota: a projection of a constructor application reduces
through the structure's published iota rule, whose endpoints are typed by
inference. The rule's arguments are the constructor's, fitted by the
constructor's type along the reduced major. -/
def projIotaC : Nat → (entries : Environment β) → (Γ : Context β) → (r : ConstRef β) → (i : Nat) →
    (x : AExpr β) → KM.{u,v} entries Γ (Reduced.{u,v} entries Γ (.proj r i x))
  | 0, _, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, r, i, x => do
    let ⟨x', hx, stopped⟩ ← whnfC fuel entries Γ x
    KM.remember stopped <| do
      match hsp : spine x' [] with
      | (.const (.ctor s 0 0) ls, cargs) =>
        match h : entries r with
        | some entry =>
          match structureInfo entry.facts with
          | some (np, nf) =>
            if r = .member s 0 ∧ cargs.length = np + nf ∧ i < nf then
              match hq : entry.equations[1 + i]? with
              | some law =>
                if hn : ls.length = entry.universes then do
                  let ⟨_, hL⟩ ← inferAC fuel entries Γ (law.lhs.instL ls)
                  let ⟨_, hR⟩ ← inferAC fuel entries Γ (law.rhs.instL ls)
                  have hsupp : SupportClaim.{u,v} entries Γ (.proj r i x)
                      (AExpr.appN (.const (.ctor s 0 0) ls) cargs) :=
                    ((SupportClaim.refl _).proj.ofReduction hx).trans (SupportClaim.ofSpine hsp)
                  let wit : Option (Witness.{u,v} entries Γ (.proj r i x) cargs) :=
                    match hc : entries (.ctor s 0 0) with
                    | some centry =>
                      if hcn : ls.length = centry.universes then
                        some ⟨.const (.ctor s 0 0) ls, centry.type.instL ls,
                          IOClaim.ofTyping (TypingClaim.const hc hcn), hsupp⟩
                      else none
                    | none => none
                  let app ← applyIOC fuel entries Γ (.proj r i x) (law.lhs.instL ls) (law.rhs.instL ls)
                    (SupportClaim.ofFormed hL.formed) (SupportClaim.ofFormed hR.formed) cargs wit
                  if hl : app.lhs' = .proj r i x' then
                    have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                      ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                    have hc : ConvClaim.{u,v} entries Γ (.proj r i x) app.lhs' := by
                      rw [hl]
                      exact ConvClaim.proj (ConvClaim.ofReduction hx)
                    return ⟨app.rhs', ReductionClaim.iotaIO hc app.hl (heq.appN cargs) app.hr⟩
                  else throw .noMatch
                else throw .noMatch
              | none => throw .noMatch
            else throw .noMatch
          | none => throw .noMatch
        | none => throw .noMatch
      | _ => throw .noMatch

/-- Structure eta: a constructor application of a structure converts to any
term of the structure's type whose projections convert to the fields, through
the published eta rule, whose endpoints are typed by inference. The
parameters are fitted by the constructor's type along the constructor
application; the other side is inferred. -/
def etaStructC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b =>
    match hsp : spine a [] with
    | (.const (.ctor s 0 0) ls, args) =>
      match h : entries (.member s 0) with
      | some entry =>
        match structureInfo entry.facts with
        | some (np, nf) =>
          if args.length = np + nf then
            match hq : entry.equations[(0 : Nat)]? with
            | some law =>
              if hn : ls.length = entry.universes then do
                let ⟨_, hL⟩ ← inferAC fuel entries Γ (law.lhs.instL ls)
                let ⟨_, hR⟩ ← inferAC fuel entries Γ (law.rhs.instL ls)
                let params := args.take np
                let wit : Option (Witness.{u,v} entries Γ a params) :=
                  match hc : entries (.ctor s 0 0) with
                  | some centry =>
                    if hcn : ls.length = centry.universes then
                      some ⟨.const (.ctor s 0 0) ls, centry.type.instL ls,
                        IOClaim.ofTyping (TypingClaim.const hc hcn), (SupportClaim.ofSpine hsp).appNTake np⟩
                    else none
                  | none => none
                let app₁ ← applyIOC fuel entries Γ a (law.lhs.instL ls) (law.rhs.instL ls)
                  (SupportClaim.ofFormed hL.formed) (SupportClaim.ofFormed hR.formed) params wit
                let app₂ ← applyIOC fuel entries Γ a app₁.lhs' app₁.rhs' app₁.hl.support
                  app₁.hr.support [b] none
                if hb : app₂.rhs' = b then do
                  let ⟨hc⟩ ← isDefEqCoreC fuel entries Γ a app₂.lhs'
                  have heq : ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) :=
                    ConversionClaim.equation h (List.mem_of_getElem? hq) hn
                  have hr : IOReductionClaim.{u,v} entries Γ a
                      (AExpr.appN (law.rhs.instL ls) (params ++ [b])) b :=
                    by have h₂ := app₁.hr.append app₂.hr; rw [hb] at h₂; exact h₂
                  return ⟨ConvClaim.ofRuleIO hc (app₁.hl.append app₂.hl) (heq.appN _) hr⟩
                else throw .noMatch
              else throw .noMatch
            | none => throw .noMatch
          else throw .noMatch
        | none => throw .noMatch
      | none => throw .noMatch
    | _ => throw .noMatch

/-- Infer only the side of a proof comparison that lacks a syntactic witness. -/
def inferProofValueC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (ProofValue.{u,v} entries Γ e)
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, e => do
    let ⟨A, he⟩ ← inferAC fuel entries Γ e
    let ⟨SA, hSA⟩ ← inferAC fuel entries Γ A
    let ⟨l, hA⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ SA) hSA)
    if hl : levelIsZero l then
      return ⟨ProofValueClaim.ofTyping (hA.sortEquiv (levelIsZero_sound hl)) he⟩
    else throw .noMatch

/-- Proof irrelevance: both sides inhabit propositions, whose proofs have
the same interpretation even when the propositions differ. -/
def proofIrrelevanceC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b => do
    if let some h := quickProofIrrelevance entries Γ a b then return h
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
        match ← KM.attempt (onSpine e (stepSpineC fuel entries Γ true)) with
        | .ok ⟨e', h⟩ =>
          let ⟨e'', h', stopped⟩ ← whnfC fuel entries Γ e'
          pure ⟨e'', h.trans h', stopped⟩
        | .error .noMatch => pure ⟨e, ReductionClaim.refl e, none⟩
        | .error failure => pure ⟨e, ReductionClaim.refl e, some failure⟩
      if cacheable && result.stopped.isNone then KM.modifyCache (·.addWhnf e result)
      pure result

/-- Weak head normalization without delta at the head: beta, zeta, literal
(closed terms only), iota, quotient and projection rules only. Each round
decomposes the spine once (`stepSpineC` without delta). -/
def whnfCoreC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    KM.{u,v} entries Γ (Normalized.{u,v} entries Γ e)
  | 0, _, _, e => pure ⟨e, ReductionClaim.refl e, some .exhausted⟩
  | fuel + 1, entries, Γ, e => do
    let next ← KM.attempt (onSpine e (stepSpineC fuel entries Γ false))
    match next with
    | .ok ⟨e', h⟩ =>
      let ⟨e'', h', stopped⟩ ← whnfCoreC fuel entries Γ e'
      pure ⟨e'', h.trans h', stopped⟩
    | .error .noMatch => pure ⟨e, ReductionClaim.refl e, none⟩
    | .error failure => pure ⟨e, ReductionClaim.refl e, some failure⟩

/-- Lazy delta: normalize without head delta and compare; the higher head
(`ConstantFact.height`) unfolds first. Equal constant heads try syntactic
congruence before constructing either body, then bounded argument conversion
unless the head is an abbreviation. Failure retains the delta fallback: a
function can ignore unequal arguments. Only argument failures enter the
conversion cache, never failure of the whole congruence attempt. On the first
round, proof irrelevance is tried before unfolding a proof. The side to unfold
is decided from the heads alone, and only that side's body is instantiated. -/
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
              if headHeight entries a' < abbrevHeight then
                KM.speculate 256 (appCongrC fuel entries Γ (.app f x) (.app g y))
              else throw .noMatch
            | _, _ => throw .noMatch
        else throw .noMatch
      KM.orElse congruence fun _ =>
        -- Decision before materialization (con-leche #106, the official
        -- kernel's `lazy_delta_reduction_step`): the heads and their heights
        -- choose the side, and only the side that unfolds is instantiated.
        -- The `none` arms are unreachable (`hasDeltaHead_eq`) and fail soundly.
        let unfoldLeft : Unit → KM.{u,v} entries Γ (Conv.{u,v} entries Γ a' b') := fun _ =>
          match deltaHead.{u,v} entries Γ a' with
          | some ⟨a'', ha'⟩ =>
            KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions ha' (ReductionClaim.refl b') hc⟩)
              (lazyDeltaC fuel entries Γ a'' b' false)
          | none => throw .noMatch
        let unfoldRight : Unit → KM.{u,v} entries Γ (Conv.{u,v} entries Γ a' b') := fun _ =>
          match deltaHead.{u,v} entries Γ b' with
          | some ⟨b'', hb'⟩ =>
            KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions (ReductionClaim.refl a') hb' hc⟩)
              (lazyDeltaC fuel entries Γ a' b'' false)
          | none => throw .noMatch
        match hasDeltaHead entries a', hasDeltaHead entries b' with
        | false, false => isDefEqCoreC fuel entries Γ a' b'
        | true, false => unfoldLeft ()
        | false, true => unfoldRight ()
        | true, true =>
          let heightA := headHeight entries a'
          let heightB := headHeight entries b'
          if heightB < heightA then unfoldLeft ()
          else if heightA < heightB then unfoldRight ()
          else
          match quickConv.{u,v} entries Γ a' b' with
          | some c => pure c
          | none =>
            match deltaHead.{u,v} entries Γ a', deltaHead.{u,v} entries Γ b' with
            | some ⟨a'', ha'⟩, some ⟨b'', hb'⟩ =>
              KM.map (fun ⟨hc⟩ => ⟨ConvClaim.ofReductions ha' hb' hc⟩)
                (lazyDeltaC fuel entries Γ a'' b'' false)
            | _, _ => throw .noMatch
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

/-- Infer an already-formed expression, reusing that evidence only at
non-Prop applications. Its ordinary typing claim can share the full inference
cache. Other application regimes still check the argument and its domain;
other heads use full inference. Front-door inference never calls this helper
without a formedness claim for the exact expression. -/
def inferFormedC : Nat → (entries : Environment β) → (Γ : Context β) → (e : AExpr β) →
    FormedClaim.{u,v} entries Γ e → KM.{u,v} entries Γ (Typed.{u,v} entries Γ e)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, .app f a, hfa => do
    KM.tick
    let cache ← KM.cache
    match cache.findInfer (.app f a) with
    | some t => pure t
    | none =>
      let ⟨T, hf⟩ ← inferFormedC fuel entries Γ f hfa.appFn
      let ⟨p, D, B, hf'⟩ ← KM.ofSearch (piOf (← whnfC fuel entries Γ T) hf)
      let result ← match p, hf' with
        | .never, hf' => pure ⟨B.inst a, TypingClaim.appFormedNever hf' hfa⟩
        | p, hf' => do
          let ⟨A', ha⟩ ← inferAC fuel entries Γ a
          let ⟨hc⟩ ← isDefEqC fuel entries Γ A' D
          pure ⟨B.inst a, TypingClaim.app (p := p) hf' (ha.convF hf'.formedType.domain hc)⟩
      KM.modifyCache (·.addInfer (.app f a) result)
      pure result
  | fuel + 1, entries, Γ, e, _ => inferAC fuel entries Γ e

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
    let ⟨SB, hSB⟩ ← match B with
      | .app .. => inferFormedC fuel entries Γ B hb.formedType
      | _ => inferAC fuel entries Γ B
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
      let ⟨_, ht⟩ ← KM.ofSearch (sortOf (← whnfC fuel entries Γ S) hS)
      let ⟨A', hv⟩ ← inferAC fuel entries Γ v
      let ⟨hc⟩ ← isDefEqC fuel entries Γ A' t
      have hv' := hv.convF ht.formed hc
      -- The body with the value substituted, as the official kernel's
      -- `infer_let` does: no opaque attempt to back out of, which nested lets
      -- would make exponential. The substituted value is shared.
      let ⟨B, hb⟩ ← inferAC fuel entries Γ (b.inst v)
      return ⟨B, TypingClaim.letSubst ht hv' hb⟩
    | .proj r i x => do
      let ⟨T, hx⟩ ← inferAC fuel entries Γ x
      let normalized ← whnfC fuel entries Γ T
      KM.remember normalized.stopped <| do
        match hsp : spine normalized.result [] with
        | (.const r' ls, params) =>
          if hr' : r' = r then
            match h : entries r with
            | some entry =>
              match structureInfo entry.facts with
              | some (np, nf) =>
                if params.length = np ∧ i < nf then
                  match hf : entry.facts[1 + i]? with
                  | some (.typed pj pjT) =>
                    if hn : ls.length = entry.universes then do
                      -- The parameters are fitted by the family's type along the
                      -- major's reduced type, which is formed; the major by inference.
                      have hT : FormedClaim.{u,v} entries Γ normalized.result :=
                        normalized.claim.formed hx.formedType
                      have hsp' : spine normalized.result [] = (.const r ls, params) := hr' ▸ hsp
                      let wit : Witness.{u,v} entries Γ normalized.result params :=
                        ⟨.const r ls, entry.type.instL ls, IOClaim.ofTyping (TypingClaim.const h hn),
                          SupportClaim.ofSpine hsp'⟩
                      let app₁ ← applyTypedWC fuel entries Γ normalized.result (pj.instL ls)
                        (pjT.instL ls) hT (TypingClaim.fact h (List.mem_of_getElem? hf) hn) params (some wit)
                      let app₂ ← applyTypedC fuel entries Γ app₁.result app₁.type app₁.typed [x]
                      if hres : app₂.result = .proj r i x then
                        return ⟨app₂.type, hres ▸ app₂.typed⟩
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

/-- Spine-wise application congruence (the official kernel's
`is_def_eq_app`, con-leche #106): both spines are collected once and must have
the same length; the heads are compared once, then the arguments pairwise,
each by full conversion (`ConvClaim.appN`). No partial application enters
conversion: re-entering normalization, proof irrelevance and lazy delta for
each prefix made long applications quadratic. Each argument pair spends one
unit of work. -/
def appCongrC : Nat → (entries : Environment β) → (Γ : Context β) → (a b : AExpr β) →
    KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b)
  | 0, _, _, _, _ => throw .exhausted
  | fuel + 1, entries, Γ, a, b =>
    let sa := spine a []
    let sb := spine b []
    if sa.2.length = sb.2.length then do
      let ⟨hh⟩ ← isDefEqC fuel entries Γ sa.1 sb.1
      let ⟨hs⟩ ← congrArgs (isDefEqC fuel entries Γ) sa.2 sb.2
      return ⟨ConvClaim.ofSpines (spine_appN a []) (spine_appN b []) (ConvClaim.appN hh hs)⟩
    else throw .noMatch

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
        -- Spine-wise congruence only; a failure falls through to the eta and
        -- proof-irrelevance fallbacks below. No prefix conversion is kept.
        -- Conversion reaches this case with both sides normalized by
        -- `whnfCoreC` and lazy delta already decided on the head the prefixes
        -- share. Rule matching (`iotaC`, `reduceByRuleC`, `etaStructC`) calls
        -- it on an unnormalized redex, but against an instance of the rule's
        -- left side with the same head and spine length by construction: the
        -- recursor's arity, the quotient rule's five or six arguments, the
        -- structure's parameters and fields; unnormalized arguments are
        -- compared by full conversion here.
        appCongrC fuel entries Γ (.app f x) (.app g y)
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
        let fast : KM.{u,v} entries Γ (Conv.{u,v} entries Γ a b) := do
          match proofValue entries Γ a, proofValue entries Γ b with
          | some ⟨ha⟩, some ⟨hb⟩ => return ⟨ConvClaim.ofProofValues ha hb⟩
          | some ⟨ha⟩, none =>
            let ⟨hb⟩ ← KM.speculate 256 (inferProofValueC fuel entries Γ b)
            return ⟨ConvClaim.ofProofValues ha hb⟩
          | none, some ⟨hb⟩ =>
            let ⟨ha⟩ ← KM.speculate 256 (inferProofValueC fuel entries Γ a)
            return ⟨ConvClaim.ofProofValues ha hb⟩
          | none, none => throw .noMatch
        -- A failed optional proof search always tries ordinary conversion.
        -- Keep exhaustion visible if both fail so it is not cached negatively.
        let r ← KM.attempt (KM.mapError SearchFailure.conversion <|
          KM.orElse fast fun _ => lazyDeltaC fuel entries Γ a b true)
        match r with
        | .error .exhausted => pure ⟨⟩
        | _ => KM.modifyCache (·.addConv a b r)
        KM.ofSearch r

end

/-- One head reduction step: `stepSpineC`, with delta, on the term's spine. -/
def stepC (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : AExpr β) :
    KM.{u,v} entries Γ (Reduced.{u,v} entries Γ e) :=
  onSpine e (stepSpineC fuel entries Γ true)

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
  KM.run (fun _ => 0) (fuel * workPerFuel) <| onSpine e fun head args =>
    match head with
    | .const r ls =>
      match h : entries r with
      | some entry => iotaC.{u,v} fuel entries Γ r ls entry h args
      | none => throw .noMatch
    | _ => throw .noMatch

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
