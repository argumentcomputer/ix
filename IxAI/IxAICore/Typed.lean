import IxAICore.Decision
import IxAICore.Dpll

/-!
# Kernel-decided typed questions

Two families of questions whose labels are computed by pure, total decision procedures, so every
label is a closed `Bool`/enum computation the kernel can evaluate (`decide`, or an Ix `Eval`
claim):

* **Simply typed λ-calculus.** A context `Γ` of five free variables and a de Bruijn term `t` over
  the base types `N` and `B`. Questions: does `t` have a type in `Γ` (`wellTyped`), and which of
  four candidate types is its type (`pick`, with `none` when it has no type or its type is not
  listed). `infer_iff` proves the checker agrees with the typing relation `HasType`.
* **Propositional status.** A random 3-CNF near the satisfiability threshold (12 atoms, or 40 in
  the hard setting), or its De Morgan dual. Question: is it a tautology, a contradiction, or
  contingent? `status_tautology_iff` and its siblings prove the enumeration agrees with the
  semantics over all assignments; `fastStatus_eq` proves the DPLL labeller (`IxAICore.Dpll`)
  computes the same status.

Instances are drawn so labels are roughly balanced: half the λ-terms receive a type error by a
local mutation, and the propositional sampler draws a target class first and then a formula of
that class (`sampleLogic`). Labels are always recomputed by
the decision procedure; the sampler's intent never becomes a label.

`fresh` removes test instances equal to a training instance (`fresh_disjoint`), so evaluation
sets drawn from a separate seed share no exact duplicates with training.
-/

namespace IxAICore
namespace Typed

/-! ## Simply typed λ-calculus -/

inductive Ty where
  | nat
  | bool
  | arr (a b : Ty)
  deriving DecidableEq, Repr, Inhabited

/-- De Bruijn terms: `var i` is bound by the `i`-th enclosing `lam`, counting from the innermost;
indices past the binders refer to the context. -/
inductive Term where
  | var (i : Nat)
  | lam (a : Ty) (body : Term)
  | app (f x : Term)
  | zero
  | succ (t : Term)
  | tt
  | ff
  | isZero (t : Term)
  | ite (c t e : Term)
  deriving DecidableEq, Repr, Inhabited

def lookup : List Ty → Nat → Option Ty
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, i + 1 => lookup as i

/-- The type checker: the unique type of `t` in `Γ`, if any. -/
def infer : List Ty → Term → Option Ty
  | Γ, .var i => lookup Γ i
  | Γ, .lam a t => (infer (a :: Γ) t).map (.arr a)
  | Γ, .app f x =>
    match infer Γ f, infer Γ x with
    | some (.arr a b), some a' => if a = a' then some b else none
    | _, _ => none
  | _, .zero => some .nat
  | Γ, .succ t => if infer Γ t = some .nat then some .nat else none
  | _, .tt => some .bool
  | _, .ff => some .bool
  | Γ, .isZero t => if infer Γ t = some .nat then some .bool else none
  | Γ, .ite c t e =>
    match infer Γ c, infer Γ t, infer Γ e with
    | some .bool, some a, some b => if a = b then some a else none
    | _, _, _ => none

/-- The typing judgment. -/
inductive HasType : List Ty → Term → Ty → Prop
  | var {Γ i a} : lookup Γ i = some a → HasType Γ (.var i) a
  | lam {Γ a t b} : HasType (a :: Γ) t b → HasType Γ (.lam a t) (.arr a b)
  | app {Γ f x a b} : HasType Γ f (.arr a b) → HasType Γ x a → HasType Γ (.app f x) b
  | zero {Γ} : HasType Γ .zero .nat
  | succ {Γ t} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  | tt {Γ} : HasType Γ .tt .bool
  | ff {Γ} : HasType Γ .ff .bool
  | isZero {Γ t} : HasType Γ t .nat → HasType Γ (.isZero t) .bool
  | ite {Γ c t e a} : HasType Γ c .bool → HasType Γ t a → HasType Γ e a → HasType Γ (.ite c t e) a

theorem infer_sound : ∀ {Γ : List Ty} {t : Term} {a : Ty}, infer Γ t = some a → HasType Γ t a := by
  intro Γ t
  induction t generalizing Γ with
  | var i => intro a h; exact .var h
  | lam b t ih =>
    intro a h
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact .lam (ih hc)
  | app f x ihf ihx =>
    intro a h
    simp only [infer] at h
    split at h
    · rename_i a1 b1 a2 hf hx
      split at h
      · rename_i heq
        subst heq
        cases h
        exact .app (ihf hf) (ihx hx)
      · cases h
    · cases h
  | zero => intro a h; cases h; exact .zero
  | succ t ih =>
    intro a h
    simp only [infer] at h
    split at h
    · rename_i ht; cases h; exact .succ (ih ht)
    · cases h
  | tt => intro a h; cases h; exact .tt
  | ff => intro a h; cases h; exact .ff
  | isZero t ih =>
    intro a h
    simp only [infer] at h
    split at h
    · rename_i ht; cases h; exact .isZero (ih ht)
    · cases h
  | ite c t e ihc iht ihe =>
    intro a h
    simp only [infer] at h
    split at h
    · rename_i a1 b1 hc ht he
      split at h
      · rename_i heq
        subst heq
        cases h
        exact .ite (ihc hc) (iht ht) (ihe he)
      · cases h
    · cases h

theorem infer_complete {Γ : List Ty} {t : Term} {a : Ty} (h : HasType Γ t a) : infer Γ t = some a := by
  induction h with
  | var h => exact h
  | lam _ ih => simp [infer, ih]
  | app _ _ ihf ihx => simp [infer, ihf, ihx]
  | zero => rfl
  | succ _ ih => simp [infer, ih]
  | tt => rfl
  | ff => rfl
  | isZero _ ih => simp [infer, ih]
  | ite _ _ _ ihc iht ihe => simp [infer, ihc, iht, ihe]

/-- The checker decides the typing judgment. -/
theorem infer_iff {Γ : List Ty} {t : Term} {a : Ty} : infer Γ t = some a ↔ HasType Γ t a :=
  ⟨infer_sound, infer_complete⟩

/-- Types are unique. -/
theorem HasType.unique {Γ : List Ty} {t : Term} {a b : Ty} (ha : HasType Γ t a) (hb : HasType Γ t b) :
    a = b := by
  have := (infer_complete ha).symm.trans (infer_complete hb)
  exact Option.some.inj this

/-! ### Items and their questions -/

/-- One question instance: a context, a term, and four candidate types. -/
structure TypeItem where
  ctx : List Ty
  term : Term
  cands : List Ty
  deriving DecidableEq, Repr, Inhabited

def TypeItem.wellTyped (it : TypeItem) : Bool := (infer it.ctx it.term).isSome

theorem TypeItem.wellTyped_iff (it : TypeItem) :
    it.wellTyped = true ↔ ∃ a, HasType it.ctx it.term a := by
  simp only [TypeItem.wellTyped, Option.isSome_iff_exists, infer_iff]

/-- The answer to "which candidate is the term's type?". -/
inductive Pick where
  | a | b | c | d | none
  deriving DecidableEq, Repr, Inhabited

instance : Finite Pick := ⟨[.a, .b, .c, .d, .none], fun
  | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .none => 4⟩

def TypeItem.cand (it : TypeItem) (k : Nat) : Ty := getD it.cands k .nat

def TypeItem.pick (it : TypeItem) : Pick :=
  match infer it.ctx it.term with
  | none => .none
  | some T =>
    if it.cand 0 = T then .a else if it.cand 1 = T then .b
    else if it.cand 2 = T then .c else if it.cand 3 = T then .d else .none

/-- A non-`none` pick names a candidate that is the term's type. -/
theorem TypeItem.pick_sound (it : TypeItem) (p : Pick) (hp : it.pick = p) (hn : p ≠ .none) :
    HasType it.ctx it.term (it.cand (Finite.index p)) := by
  unfold TypeItem.pick at hp
  split at hp
  · exact absurd hp.symm hn
  · rename_i T hT
    have ht := infer_sound hT
    by_cases h0 : it.cand 0 = T
    · rw [if_pos h0] at hp; subst hp
      show HasType _ _ (it.cand 0); rw [h0]; exact ht
    rw [if_neg h0] at hp
    by_cases h1 : it.cand 1 = T
    · rw [if_pos h1] at hp; subst hp
      show HasType _ _ (it.cand 1); rw [h1]; exact ht
    rw [if_neg h1] at hp
    by_cases h2 : it.cand 2 = T
    · rw [if_pos h2] at hp; subst hp
      show HasType _ _ (it.cand 2); rw [h2]; exact ht
    rw [if_neg h2] at hp
    by_cases h3 : it.cand 3 = T
    · rw [if_pos h3] at hp; subst hp
      show HasType _ _ (it.cand 3); rw [h3]; exact ht
    rw [if_neg h3] at hp
    exact absurd hp.symm hn

/-- `none` exactly when no listed candidate is a type of the term. -/
theorem TypeItem.pick_none_iff (it : TypeItem) :
    it.pick = .none ↔ ∀ k, k < 4 → ¬ HasType it.ctx it.term (it.cand k) := by
  constructor
  · intro hp k hk ht
    have hi := infer_complete ht
    unfold TypeItem.pick at hp
    rw [hi] at hp
    simp only at hp
    by_cases h0 : it.cand 0 = it.cand k
    · rw [if_pos h0] at hp; cases hp
    rw [if_neg h0] at hp
    by_cases h1 : it.cand 1 = it.cand k
    · rw [if_pos h1] at hp; cases hp
    rw [if_neg h1] at hp
    by_cases h2 : it.cand 2 = it.cand k
    · rw [if_pos h2] at hp; cases hp
    rw [if_neg h2] at hp
    by_cases h3 : it.cand 3 = it.cand k
    · rw [if_pos h3] at hp; cases hp
    match k, hk with
    | 0, _ => exact h0 rfl
    | 1, _ => exact h1 rfl
    | 2, _ => exact h2 rfl
    | 3, _ => exact h3 rfl
  · intro h
    unfold TypeItem.pick
    split
    · rfl
    · rename_i T hT
      have ht := infer_sound hT
      have hne : ∀ k, k < 4 → it.cand k ≠ T := fun k hk he => h k hk (he ▸ ht)
      rw [if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
        if_neg (hne 3 (by decide))]

/-! ### Generation -/

def Ty.gen : Nat → Rng → Ty × Rng
  | 0, r => let (k, r) := r.below 2; (if k == 0 then .nat else .bool, r)
  | d + 1, r =>
    let (k, r) := r.below 3
    if k == 0 then (.nat, r) else if k == 1 then (.bool, r) else
    let (a, r) := Ty.gen d r
    let (b, r) := Ty.gen d r
    (.arr a b, r)

def Ty.size : Ty → Nat
  | .arr a b => a.size + b.size + 1
  | _ => 1

/-- The argument types `[A₁, …, Aₖ]` with `A = A₁ → … → Aₖ → T`, if `T` is a suffix of `A`'s
arrow spine (the shortest such). -/
def peelTo (T : Ty) : Ty → Option (List Ty)
  | .arr a b => if Ty.arr a b = T then some [] else (peelTo T b).map (a :: ·)
  | A => if A = T then some [] else none

/-- Context variables that produce a `T` after zero or more arguments, with those arguments. -/
def heads (Γ : List Ty) (T : Ty) : List (Nat × List Ty) :=
  (withIndex Γ 0).filterMap fun (A, i) => (peelTo T A).map (i, ·)

def pickVar (Γ : List Ty) (T : Ty) (r : Rng) : Option Nat × Rng :=
  let vs := (withIndex Γ 0).filter (·.1 == T)
  let (k, r) := r.below (vs.length + 1)
  (if k < vs.length then some (getD vs k (T, 0)).2 else none, r)

/-- A minimal term of type `T`: a variable of that type, else an introduction form. -/
def leaf : List Ty → Ty → Rng → Term × Rng
  | Γ, .nat, r => match pickVar Γ .nat r with
    | (some i, r) => (.var i, r)
    | (none, r) => (.zero, r)
  | Γ, .bool, r => match pickVar Γ .bool r with
    | (some i, r) => (.var i, r)
    | (none, r) => let (b, r) := r.below 2; (if b == 0 then .tt else .ff, r)
  | Γ, .arr a b, r => match pickVar Γ (.arr a b) r with
    | (some i, r) => (.var i, r)
    | (none, r) => let (t, r) := leaf (a :: Γ) b r; (.lam a t, r)

/-- A random term of type `T` in `Γ`, of generation depth at most `d`. -/
def genTm : Nat → List Ty → Ty → Rng → Term × Rng
  | 0, Γ, T, r => leaf Γ T r
  | d + 1, Γ, T, r =>
    let (k, r) := r.below 8
    let hs := heads Γ T
    if k < 2 && !hs.isEmpty then
      let (j, r) := r.below hs.length
      let (i, tys) := getD hs j (0, [])
      let (args, r) := tys.foldl (fun (acc : List Term × Rng) A =>
        let (x, r) := genTm d Γ A acc.2
        (acc.1 ++ [x], r)) ([], r)
      (args.foldl .app (.var i), r)
    else if k == 2 then
      let (c, r) := genTm d Γ .bool r
      let (t, r) := genTm d Γ T r
      let (e, r) := genTm d Γ T r
      (.ite c t e, r)
    else if k == 3 then
      let (A, r) := Ty.gen 1 r
      let (body, r) := genTm d (A :: Γ) T r
      let (x, r) := genTm d Γ A r
      (.app (.lam A body) x, r)
    else if k == 4 then
      let (A, r) := Ty.gen 1 r
      let (f, r) := genTm d Γ (.arr A T) r
      let (x, r) := genTm d Γ A r
      (.app f x, r)
    else match T with
      | .nat =>
        if k == 7 then (.zero, r) else
        let (t, r) := genTm d Γ .nat r
        (.succ t, r)
      | .bool =>
        if k == 7 then let (b, r) := r.below 2; (if b == 0 then .tt else .ff, r) else
        let (t, r) := genTm d Γ .nat r
        (.isZero t, r)
      | .arr a b =>
        let (t, r) := genTm d (a :: Γ) b r
        (.lam a t, r)

def Term.size : Term → Nat
  | .lam _ t | .succ t | .isZero t => t.size + 1
  | .app f x => f.size + x.size + 1
  | .ite c t e => c.size + t.size + e.size + 1
  | _ => 1

def Term.depth : Term → Nat
  | .lam _ t | .succ t | .isZero t => t.depth + 1
  | .app f x => max f.depth x.depth + 1
  | .ite c t e => max c.depth (max t.depth e.depth) + 1
  | _ => 0

/-- Replace the `k`-th subterm in preorder by `g Γ s`, where `Γ` is its context. -/
def mapAt (g : List Ty → Term → Term) : Nat → List Ty → Term → Term
  | 0, Γ, t => g Γ t
  | k + 1, Γ, .lam a t => .lam a (mapAt g k (a :: Γ) t)
  | k + 1, Γ, .succ t => .succ (mapAt g k Γ t)
  | k + 1, Γ, .isZero t => .isZero (mapAt g k Γ t)
  | k + 1, Γ, .app f x =>
    if k < f.size then .app (mapAt g k Γ f) x else .app f (mapAt g (k - f.size) Γ x)
  | k + 1, Γ, .ite c t e =>
    if k < c.size then .ite (mapAt g k Γ c) t e
    else if k < c.size + t.size then .ite c (mapAt g (k - c.size) Γ t) e
    else .ite c t (mapAt g (k - c.size - t.size) Γ e)
  | _ + 1, _, t => t

/-- Swap one base type somewhere in `T`. -/
def Ty.flip : Ty → Rng → Ty × Rng
  | .nat, r => (.bool, r)
  | .bool, r => (.nat, r)
  | .arr a b, r =>
    let (s, r) := r.below 2
    if s == 0 then let (a, r) := a.flip r; (.arr a b, r) else let (b, r) := b.flip r; (.arr a b, r)

/-- A nearby type: one base flipped, the first argument dropped or swapped with the second, or
an argument added. -/
def Ty.mutate (T : Ty) (r : Rng) : Ty × Rng :=
  let (k, r) := r.below 4
  if k == 0 then T.flip r
  else if k == 1 then match T with
    | .arr _ b => (b, r)
    | t => let (u, r) := t.flip r; (.arr u t, r)
  else if k == 2 then
    let (A, r) := Ty.gen 1 r
    (.arr A T, r)
  else match T with
    | .arr a (.arr b c) => if a = b then T.flip r else (.arr b (.arr a c), r)
    | .arr a b => if a = b then T.flip r else (.arr b a, r)
    | _ => T.flip r

/-- Three types near `T`, distinct from each other and from `T`, and `T` inserted at a random
position. -/
def candidatesFor (T : Ty) (r : Rng) : List Ty × Rng :=
  let rec collect : Nat → List Ty → Rng → List Ty × Rng
    | 0, acc, r => (acc, r)
    | fuel + 1, acc, r =>
      if acc.length ≥ 3 then (acc, r) else
      let (base, r) := if acc.isEmpty then (T, r) else
        let (j, r) := r.below (acc.length + 1)
        (if j == 0 then T else getD acc (j - 1) T, r)
      let (u, r) := base.mutate r
      collect fuel (if u == T || acc.contains u then acc else acc ++ [u]) r
  let (acc, r) := collect 24 [] r
  let fallback := [Ty.arr .nat T, .arr .bool T, .arr .nat (.arr .bool T), .arr .bool (.arr .nat T)]
  let acc := acc ++ (fallback.filter (!acc.contains ·)).take (3 - acc.length)
  let (p, r) := r.below 4
  (acc.take p ++ [T] ++ acc.drop p, r)

/-- Introduce a local error at one subterm: a variable re-pointed at another binder, a λ
annotation changed, or the subterm replaced by a term of another type. -/
def breakAt (r : Rng) (Γ : List Ty) : Term → Term
  | .var i =>
    let (j, _) := r.below (max Γ.length 1)
    .var (if j == i then (i + 1) % (max Γ.length 1) else j)
  | .lam a t => .lam (a.mutate r).1 t
  | t =>
    let T := (infer Γ t).getD .nat
    let (U, r) := T.mutate r
    (genTm 1 Γ U r).1

/-- Mutate random subterms until the term has no type, at most `fuel` attempts, each on the
original term. -/
def breakTerm (Γ : List Ty) (t : Term) : Nat → Rng → Term × Rng
  | 0, r => (t, r)
  | fuel + 1, r =>
    let (k, r) := r.below t.size
    let (s, r) := r.next
    let t' := mapAt (breakAt (Rng.seeded s)) k Γ t
    if (infer Γ t').isNone || fuel == 0 then (t', r) else breakTerm Γ t fuel r

/-- Generation parameters for the λ family. -/
structure TypeGen where
  /-- Generation depth of `genTm`. -/
  depth : Nat
  /-- Terms smaller than this are redrawn. -/
  minSize : Nat
  /-- Terms larger than this are redrawn. -/
  maxSize : Nat
  /-- Context variables. -/
  ctxSize : Nat
  deriving Repr

def TypeGen.default : TypeGen := { depth := 7, minSize := 80, maxSize := 160, ctxSize := 5 }

def genCtx : Nat → Rng → List Ty × Rng
  | 0, r => ([], r)
  | n + 1, r =>
    let (a, r) := Ty.gen 2 r
    let (as, r) := genCtx n r
    (a :: as, r)

/-- A well-typed term within the size bounds (or the last draw after 64 tries). -/
def drawTerm (g : TypeGen) (Γ : List Ty) : Nat → Rng → Ty × Term × Rng
  | 0, r => let (T, r) := Ty.gen 2 r; let (t, r) := genTm g.depth Γ T r; (T, t, r)
  | fuel + 1, r =>
    let (T, r) := Ty.gen 2 r
    let (t, r) := genTm g.depth Γ T r
    if g.minSize ≤ t.size && t.size ≤ g.maxSize then (T, t, r) else drawTerm g Γ fuel r

def sampleTypeItem (g : TypeGen) (r : Rng) : TypeItem × Rng :=
  let (ctx, r) := genCtx g.ctxSize r
  let (T, t, r) := drawTerm g ctx 64 r
  let (bad, r) := r.below 2
  let (t, r) := if bad == 1 then breakTerm ctx t 6 r else (t, r)
  let (cs, r) := candidatesFor ((infer ctx t).getD T) r
  (⟨ctx, t, cs⟩, r)

/-! ### Features -/

def Ty.arrows : Ty → Nat
  | .arr _ b => b.arrows + 1
  | _ => 0

def Ty.codomain : Ty → Ty
  | .arr _ b => b.codomain
  | t => t

def Term.leadingLams : Term → List Ty
  | .lam a t => a :: t.leadingLams
  | _ => []

/-- Whether `T`'s first arguments are exactly `as`. -/
def prefixMatch : List Ty → Ty → Bool
  | [], _ => true
  | a :: as, .arr b c => a == b && prefixMatch as c
  | _ :: _, _ => false

/-- Node counts: var, lam, app, zero/succ, true/false, isZero, ite. -/
def Term.kinds : Term → List Nat
  | .var _ => [1, 0, 0, 0, 0, 0, 0]
  | .lam _ t => List.zipWith (· + ·) [0, 1, 0, 0, 0, 0, 0] t.kinds
  | .app f x => List.zipWith (· + ·) [0, 0, 1, 0, 0, 0, 0] (List.zipWith (· + ·) f.kinds x.kinds)
  | .zero => [0, 0, 0, 1, 0, 0, 0]
  | .succ t => List.zipWith (· + ·) [0, 0, 0, 1, 0, 0, 0] t.kinds
  | .tt | .ff => [0, 0, 0, 0, 1, 0, 0]
  | .isZero t => List.zipWith (· + ·) [0, 0, 0, 0, 0, 1, 0] t.kinds
  | .ite c t e =>
    List.zipWith (· + ·) [0, 0, 0, 0, 0, 0, 1] (List.zipWith (· + ·) c.kinds (List.zipWith (· + ·) t.kinds e.kinds))

/-- The largest de Bruijn index minus the number of enclosing binders, plus one (0 if none). -/
def Term.freeReach : Nat → Term → Nat
  | b, .var i => i + 1 - b
  | b, .lam _ t => t.freeReach (b + 1)
  | b, .app f x => max (f.freeReach b) (x.freeReach b)
  | b, .succ t | b, .isZero t => t.freeReach b
  | b, .ite c t e => max (c.freeReach b) (max (t.freeReach b) (e.freeReach b))
  | _, _ => 0

/-- The syntactic shape of a subterm: 1 numeral-like, 2 boolean-like, 3 λ, 0 otherwise. -/
def Term.shape : Term → Nat
  | .zero | .succ _ => 1
  | .tt | .ff | .isZero _ => 2
  | .lam _ _ => 3
  | _ => 0

def shapeClash (a : Ty) (s : Nat) : Bool :=
  match a with
  | .nat => s == 2 || s == 3
  | .bool => s == 1 || s == 3
  | .arr _ _ => s == 1 || s == 2

/-- Type errors visible from one node and its children's shapes alone, without inference. -/
def Term.localErrors : Term → Nat
  | .lam _ t => t.localErrors
  | .app f x =>
    let here := match f with
      | .lam a _ => if shapeClash a x.shape then 1 else 0
      | _ => if f.shape == 1 || f.shape == 2 then 1 else 0
    here + f.localErrors + x.localErrors
  | .succ t | .isZero t => (if t.shape == 2 || t.shape == 3 then 1 else 0) + t.localErrors
  | .ite c t e =>
    (if c.shape == 1 || c.shape == 3 then 1 else 0) + c.localErrors + t.localErrors + e.localErrors
  | _ => 0

/-- The type of a variable, a constant, or a variable applied to arguments, read off the context
without inference; `none` for anything else. -/
def quickTy (Γ : List Ty) : Term → Option Ty
  | .var i => lookup Γ i
  | .zero | .succ _ => some .nat
  | .tt | .ff | .isZero _ => some .bool
  | .app f _ => match quickTy Γ f with
    | some (.arr _ b) => some b
    | _ => none
  | _ => none

def clash (a : Option Ty) (b : Ty) : Bool :=
  match a with
  | some a => a != b
  | none => false

/-- Errors visible one level deep once variables carry their context or binder types: an
argument, condition or operand whose `quickTy` is wrong, a non-function applied, or an unbound
index. -/
def Term.shallowErrors : List Ty → Term → Nat
  | Γ, .var i => if (lookup Γ i).isNone then 1 else 0
  | Γ, .lam a t => t.shallowErrors (a :: Γ)
  | Γ, .app f x =>
    let here := match f, quickTy Γ f with
      | _, some (.arr a _) => if clash (quickTy Γ x) a then 1 else 0
      | _, some _ => 1
      | .lam a _, none => if clash (quickTy Γ x) a then 1 else 0
      | _, none => 0
    here + f.shallowErrors Γ + x.shallowErrors Γ
  | Γ, .succ t | Γ, .isZero t => (if clash (quickTy Γ t) .nat then 1 else 0) + t.shallowErrors Γ
  | Γ, .ite c t e =>
    let branches := match quickTy Γ t, quickTy Γ e with
      | some a, some b => if a != b then 1 else 0
      | _, _ => 0
    (if clash (quickTy Γ c) .bool then 1 else 0) + branches +
      c.shallowErrors Γ + t.shallowErrors Γ + e.shallowErrors Γ
  | _, _ => 0

/-- The body under the leading λs, with the context extended by their annotations. -/
def Term.underLams : List Ty → Term → List Ty × Term
  | Γ, .lam a t => t.underLams (a :: Γ)
  | Γ, t => (Γ, t)

/-- The type suggested by the leading λ annotations and the body's `quickTy`, if any. -/
def TypeItem.quickType (it : TypeItem) : Option Ty :=
  let (Γ, body) := it.term.underLams it.ctx
  (quickTy Γ body).map fun b => it.term.leadingLams.foldr Ty.arr b

/-- Features stay in `0 … 3`: `Fx` inputs are not normalized, and larger inputs make the summed
batch gradient large enough to switch off every hidden unit. -/
def cap (n : Nat) : Int := Int.ofNat (min n 3)

def TypeItem.features (it : TypeItem) : List Int :=
  let t := it.term
  let lams := t.leadingLams
  [cap (t.size / 10), cap (t.depth / 3)] ++ t.kinds.map (fun k => cap (k / 2)) ++
  let shallow := t.shallowErrors it.ctx
  let quick := it.quickType
  [cap (t.freeReach 0), cap (it.ctx.filter (·.arrows > 0)).length, cap lams.length, cap t.localErrors,
   cap shallow, if shallow == 0 then 1 else 0, if quick.isSome then 1 else 0] ++
  (List.range 4).flatMap fun k =>
    let c := it.cand k
    [cap c.arrows, if prefixMatch lams c then 1 else 0, if c.codomain == .nat then 1 else 0,
     cap (c.size / 2), if quick == some c then 1 else 0]

def wellTypedQ : Question TypeItem Bool := ⟨"typechecks", TypeItem.wellTyped⟩
def pickQ : Question TypeItem Pick := ⟨"type", TypeItem.pick⟩

def typeSpec (g : TypeGen) : Spec TypeItem :=
  { name := "stlc-typing"
    features := TypeItem.features
    numFeatures := 36
    slots := [wellTypedQ.slot, pickQ.slot]
    sample := sampleTypeItem g }

example : infer [] (.lam .nat (.succ (.var 0))) = some (.arr .nat .nat) := by decide
example : infer [.bool] (.succ (.var 0)) = none := by decide

/-! ## Propositional status -/

inductive PForm where
  | atom (i : Nat)
  | neg (a : PForm)
  | and (a b : PForm)
  | or (a b : PForm)
  | imp (a b : PForm)
  | iff (a b : PForm)
  deriving DecidableEq, Repr, Inhabited

namespace PForm

/-- Truth value under an assignment; atom `i` reads position `i`, false if absent. -/
def eval (v : List Bool) : PForm → Bool
  | atom i => getD v i false
  | neg a => !a.eval v
  | and a b => a.eval v && b.eval v
  | or a b => a.eval v || b.eval v
  | imp a b => !a.eval v || b.eval v
  | iff a b => a.eval v == b.eval v

end PForm

/-- Every assignment of `n` atoms. -/
def assignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (assignments n).flatMap fun l => [false :: l, true :: l]

theorem mem_assignments : ∀ {n : Nat} {l : List Bool}, l ∈ assignments n ↔ l.length = n := by
  intro n
  induction n with
  | zero => intro l; simp [assignments, List.length_eq_zero_iff]
  | succ n ih =>
    intro l
    simp only [assignments, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨a, ha, h | h⟩ <;> subst h <;> simp [ih.mp ha]
    · intro h
      match l, h with
      | b :: l', h =>
        refine ⟨l', ih.mpr (by simpa using h), ?_⟩
        cases b <;> simp

def valid (n : Nat) (f : PForm) : Bool := (assignments n).all (f.eval ·)
def sat (n : Nat) (f : PForm) : Bool := (assignments n).any (f.eval ·)

theorem valid_iff (n : Nat) (f : PForm) :
    valid n f = true ↔ ∀ l : List Bool, l.length = n → f.eval l = true := by
  simp [valid, List.all_eq_true, mem_assignments]

theorem sat_iff (n : Nat) (f : PForm) :
    sat n f = true ↔ ∃ l : List Bool, l.length = n ∧ f.eval l = true := by
  simp [sat, List.any_eq_true, mem_assignments]

inductive Status where
  | contradiction
  | contingent
  | tautology
  deriving DecidableEq, Repr, Inhabited

instance : Finite Status := ⟨[.contradiction, .contingent, .tautology], fun
  | .contradiction => 0 | .contingent => 1 | .tautology => 2⟩

def status (n : Nat) (f : PForm) : Status :=
  if valid n f then .tautology else if sat n f then .contingent else .contradiction

theorem status_tautology_iff (n : Nat) (f : PForm) :
    status n f = .tautology ↔ ∀ l : List Bool, l.length = n → f.eval l = true := by
  rw [← valid_iff]
  unfold status
  cases valid n f <;> cases sat n f <;> simp

theorem status_contradiction_iff (n : Nat) (f : PForm) :
    status n f = .contradiction ↔ ∀ l : List Bool, l.length = n → f.eval l = false := by
  have hs := sat_iff n f
  have hv := valid_iff n f
  unfold status
  constructor
  · intro h l hl
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hsat
        cases he : f.eval l
        · rfl
        · exact absurd (hs.mpr ⟨l, hl, he⟩) hsat
  · intro h
    have hsat : sat n f = false := by
      cases hq : sat n f
      · rfl
      · obtain ⟨l, hl, he⟩ := hs.mp hq
        rw [h l hl] at he
        cases he
    have hval : valid n f = false := by
      cases hq : valid n f
      · rfl
      · have := hv.mp hq (List.replicate n false) (by simp)
        rw [h _ (by simp)] at this
        cases this
    simp [hsat, hval]

theorem status_contingent_iff (n : Nat) (f : PForm) :
    status n f = .contingent ↔
      (∃ l : List Bool, l.length = n ∧ f.eval l = true) ∧
      (∃ l : List Bool, l.length = n ∧ f.eval l = false) := by
  have ht := status_tautology_iff n f
  have hc := status_contradiction_iff n f
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      have : status n f = .contradiction := hc.mpr fun l hl => by
        cases he : f.eval l
        · rfl
        · exact absurd ⟨l, hl, he⟩ hn
      rw [h] at this; cases this
    · apply Classical.byContradiction
      intro hn
      have : status n f = .tautology := ht.mpr fun l hl => by
        cases he : f.eval l
        · exact absurd ⟨l, hl, he⟩ hn
        · rfl
      rw [h] at this; cases this
  · rintro ⟨⟨l₁, hl₁, he₁⟩, ⟨l₂, hl₂, he₂⟩⟩
    cases hs : status n f
    · rw [hc.mp hs l₁ hl₁] at he₁; cases he₁
    · rfl
    · rw [ht.mp hs l₂ hl₂] at he₂; cases he₂

namespace PForm

def size : PForm → Nat
  | atom _ => 1
  | neg a => a.size + 1
  | and a b | or a b | imp a b | iff a b => a.size + b.size + 1

def depth : PForm → Nat
  | atom _ => 0
  | neg a => a.depth + 1
  | and a b | or a b | imp a b | iff a b => max a.depth b.depth + 1

def occurs (i : Nat) : PForm → Bool
  | atom j => i == j
  | neg a => a.occurs i
  | and a b | or a b | imp a b | iff a b => a.occurs i || b.occurs i

def distinctAtoms (n : Nat) (f : PForm) : Nat := ((List.range n).filter f.occurs).length

/-- Occurrences of atom `i` under an even (`pos`) or odd (`neg`) number of negations, counting
the left of `→` as negated and both sides of `↔` as both. -/
def polarity (i : Nat) : Bool → PForm → Nat × Nat
  | s, atom j => if i == j then (if s then (1, 0) else (0, 1)) else (0, 0)
  | s, neg a => a.polarity i (!s)
  | s, and a b | s, or a b =>
    let (p, q) := a.polarity i s; let (p', q') := b.polarity i s; (p + p', q + q')
  | s, imp a b =>
    let (p, q) := a.polarity i (!s); let (p', q') := b.polarity i s; (p + p', q + q')
  | s, iff a b =>
    let (p, q) := a.polarity i s; let (p', q') := b.polarity i s
    (p + p' + q + q', p + p' + q + q')

/-- Node counts: ¬, ∧, ∨, →, ↔. -/
def kinds : PForm → List Nat
  | atom _ => [0, 0, 0, 0, 0]
  | neg a => List.zipWith (· + ·) [1, 0, 0, 0, 0] a.kinds
  | and a b => List.zipWith (· + ·) [0, 1, 0, 0, 0] (List.zipWith (· + ·) a.kinds b.kinds)
  | or a b => List.zipWith (· + ·) [0, 0, 1, 0, 0] (List.zipWith (· + ·) a.kinds b.kinds)
  | imp a b => List.zipWith (· + ·) [0, 0, 0, 1, 0] (List.zipWith (· + ·) a.kinds b.kinds)
  | iff a b => List.zipWith (· + ·) [0, 0, 0, 0, 1] (List.zipWith (· + ·) a.kinds b.kinds)

def topKind : PForm → Nat
  | atom _ => 0
  | neg _ => 1
  | and _ _ => 2
  | or _ _ => 3
  | imp _ _ => 4
  | iff _ _ => 5

end PForm

/-- Fixed probe assignments: bit `i` of each mask is atom `i`. -/
def probeMasks : List Nat := [0, 4095, 1365, 2730, 819, 3276, 3855, 240]

def bitsOf (n mask : Nat) : List Bool := (List.range n).map fun i => (mask >>> i) % 2 == 1

def PForm.features (n : Nat) (f : PForm) : List Int :=
  let pols := (List.range n).map fun i => f.polarity i true
  let used := pols.filter fun (p, q) => p + q > 0
  let both := (used.filter fun (p, q) => p > 0 && q > 0).length
  let onlyPos := (used.filter fun (_, q) => q == 0).length
  let onlyNeg := (used.filter fun (p, _) => p == 0).length
  let maxOcc := pols.foldl (fun m (p, q) => max m (p + q)) 0
  let probes := probeMasks.map fun m => f.eval (bitsOf n m)
  let top := f.topKind
  let hits := (probes.filter id).length
  [cap (f.size / 20), cap (f.depth / 2)] ++ f.kinds.map (fun k => cap (k / 3)) ++
  [cap (f.distinctAtoms n / 3), cap (both / 2), cap onlyPos, cap onlyNeg, cap (maxOcc / 3),
   if hits == 0 then 1 else 0, if hits == probes.length then 1 else 0,
   if probes.headD false then 1 else 0, if (probes.drop 1).headD false then 1 else 0] ++
  (List.range 5).map fun k => if top == k + 1 then 1 else 0

/-- Generation parameters for the propositional family. -/
structure LogicGen where
  atoms : Nat
  /-- Clauses of three literals per formula. -/
  clauses : Nat
  /-- Draws per instance before the last draw is kept. -/
  fuel : Nat
  deriving Repr

/-- 12 atoms and 52 clauses (ratio 4.33) sit near the satisfiability threshold, where random 3-CNF
is about evenly satisfiable and unsatisfiable. -/
def LogicGen.default : LogicGen := { atoms := 12, clauses := 52, fuel := 200 }

def literal (n : Nat) (r : Rng) : PForm × Rng :=
  let (i, r) := r.below n
  let (s, r) := r.below 2
  (if s == 0 then .atom i else .neg (.atom i), r)

def clause (n : Nat) (r : Rng) : PForm × Rng :=
  let (a, r) := literal n r
  let (b, r) := literal n r
  let (c, r) := literal n r
  (.or (.or a b) c, r)

/-- A conjunction of `k + 1` random 3-clauses. -/
def cnf (n : Nat) : Nat → Rng → PForm × Rng
  | 0, r => clause n r
  | k + 1, r =>
    let (c, r) := clause n r
    let (rest, r) := cnf n k r
    (.and c rest, r)

/-- The De Morgan dual: `∧` and `∨` swapped and every literal negated. -/
def PForm.dual : PForm → PForm
  | .atom i => .neg (.atom i)
  | .neg a => a
  | .and a b => .or a.dual b.dual
  | .or a b => .and a.dual b.dual
  | .imp a b => .and a b.dual
  | .iff a b => .iff a b.dual

theorem PForm.eval_dual (v : List Bool) (f : PForm) : f.dual.eval v = !f.eval v := by
  induction f with
  | atom i => rfl
  | neg a _ => simp [PForm.dual, PForm.eval]
  | and a b iha ihb => simp [PForm.dual, PForm.eval, iha, ihb]
  | or a b iha ihb => simp [PForm.dual, PForm.eval, iha, ihb]
  | imp a b _ ihb => simp [PForm.dual, PForm.eval, ihb]
  | iff a b _ ihb => simp only [PForm.dual, PForm.eval, ihb]; cases PForm.eval v a <;> cases PForm.eval v b <;> rfl

/-! ## Labels by DPLL

`fastStatus` reads a CNF or DNF formula into clauses (`cnf?`, `dnf?`) and decides it with
`Dpll.satN`; any other formula falls back to enumeration. `fastStatus_eq` proves it equals
`status`, so the `status_*_iff` theorems describe it, at a cost that does not grow as `2^n`. -/

theorem getD_eq_ofList (v : List Bool) (i : Nat) : getD v i false = Dpll.ofList v i := by
  induction v generalizing i with
  | nil => rfl
  | cons b v ih => cases i <;> simp [getD, Dpll.ofList, ih]

namespace PForm

def lit? : PForm → Option Dpll.Lit
  | atom i => some (i, true)
  | neg (atom i) => some (i, false)
  | _ => none

/-- A disjunction of literals. -/
def clause? : PForm → Option Dpll.Clause
  | or a b =>
    match a.clause?, b.clause? with
    | some x, some y => some (x ++ y)
    | _, _ => none
  | f => f.lit?.map ([·])

/-- A conjunction of literals. -/
def term? : PForm → Option Dpll.Clause
  | and a b =>
    match a.term?, b.term? with
    | some x, some y => some (x ++ y)
    | _, _ => none
  | f => f.lit?.map ([·])

/-- A conjunction of clauses. -/
def cnf? : PForm → Option Dpll.CNF
  | and a b =>
    match a.cnf?, b.cnf? with
    | some x, some y => some (x ++ y)
    | _, _ => none
  | f => f.clause?.map ([·])

/-- A disjunction of terms. -/
def dnf? : PForm → Option (List Dpll.Clause)
  | or a b =>
    match a.dnf?, b.dnf? with
    | some x, some y => some (x ++ y)
    | _, _ => none
  | f => f.term?.map ([·])

theorem lit?_eval {v : List Bool} : ∀ {f : PForm} {m : Dpll.Lit}, f.lit? = some m →
    f.eval v = Dpll.litEval (Dpll.ofList v) m
  | atom i, m, h => by cases h; simp [eval, Dpll.litEval, getD_eq_ofList]
  | neg (atom i), m, h => by cases h; simp [eval, Dpll.litEval, getD_eq_ofList]
  | neg (neg _), _, h | neg (and _ _), _, h | neg (or _ _), _, h | neg (imp _ _), _, h
  | neg (iff _ _), _, h | and _ _, _, h | or _ _, _, h | imp _ _, _, h | iff _ _, _, h => by
    simp [lit?] at h

theorem clause?_eval {v : List Bool} : ∀ {f : PForm} {c : Dpll.Clause}, f.clause? = some c →
    f.eval v = Dpll.clauseEval (Dpll.ofList v) c := by
  intro f
  induction f with
  | or a b iha ihb =>
    intro c h
    simp only [clause?] at h
    split at h
    · rename_i x y hx hy
      cases h
      simp [eval, iha hx, ihb hy, Dpll.clauseEval, List.any_append]
    · cases h
  | _ =>
    intro c h
    simp only [clause?, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [lit?_eval hm, Dpll.clauseEval]

theorem term?_eval {v : List Bool} : ∀ {f : PForm} {t : Dpll.Clause}, f.term? = some t →
    f.eval v = t.all (Dpll.litEval (Dpll.ofList v)) := by
  intro f
  induction f with
  | and a b iha ihb =>
    intro c h
    simp only [term?] at h
    split at h
    · rename_i x y hx hy
      cases h
      simp [eval, iha hx, ihb hy, List.all_append]
    · cases h
  | _ =>
    intro c h
    simp only [term?, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [lit?_eval hm]

theorem cnf?_eval {v : List Bool} : ∀ {f : PForm} {F : Dpll.CNF}, f.cnf? = some F →
    f.eval v = Dpll.cnfEval (Dpll.ofList v) F := by
  intro f
  induction f with
  | and a b iha ihb =>
    intro c h
    simp only [cnf?] at h
    split at h
    · rename_i x y hx hy
      cases h
      simp [eval, iha hx, ihb hy, Dpll.cnfEval, List.all_append]
    · cases h
  | _ =>
    intro c h
    simp only [cnf?, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [clause?_eval hm, Dpll.cnfEval]

theorem dnf?_eval {v : List Bool} : ∀ {f : PForm} {D : List Dpll.Clause}, f.dnf? = some D →
    f.eval v = D.any fun t => t.all (Dpll.litEval (Dpll.ofList v)) := by
  intro f
  induction f with
  | or a b iha ihb =>
    intro c h
    simp only [dnf?] at h
    split at h
    · rename_i x y hx hy
      cases h
      simp [eval, iha hx, ihb hy, List.any_append]
    · cases h
  | _ =>
    intro c h
    simp only [dnf?, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [term?_eval hm]

end PForm

/-- A term as a CNF of unit clauses. -/
def units (t : Dpll.Clause) : Dpll.CNF := t.map ([·])

theorem cnfEval_units (σ : Nat → Bool) (t : Dpll.Clause) :
    Dpll.cnfEval σ (units t) = t.all (Dpll.litEval σ) := by
  induction t with
  | nil => rfl
  | cons m t ih => simp_all [units, Dpll.cnfEval, Dpll.clauseEval]

/-- `sat`, by DPLL on CNF and term by term on DNF. -/
def fastSat (n : Nat) (f : PForm) : Bool :=
  match f.cnf? with
  | some F => Dpll.satN n F
  | none =>
    match f.dnf? with
    | some D => D.any fun t => Dpll.satN n (units t)
    | none => sat n f

theorem fastSat_eq (n : Nat) (f : PForm) : fastSat n f = sat n f := by
  apply Bool.eq_iff_iff.mpr
  rw [sat_iff]
  unfold fastSat
  split
  · rename_i F hF
    rw [Dpll.satN_iff]
    simp only [PForm.cnf?_eval hF]
  · split
    · rename_i D hD
      simp only [PForm.dnf?_eval hD, List.any_eq_true, Dpll.satN_iff, cnfEval_units]
      exact ⟨fun ⟨t, ht, l, hl, he⟩ => ⟨l, hl, t, ht, he⟩, fun ⟨l, hl, t, ht, he⟩ => ⟨t, ht, l, hl, he⟩⟩
    · rw [sat_iff]

theorem valid_eq_not_sat_dual (n : Nat) (f : PForm) : valid n f = !sat n f.dual := by
  simp only [valid, sat, PForm.eval_dual]
  induction assignments n with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- `status` decided by `fastSat`: a tautology when the dual is unsatisfiable. -/
def fastStatus (n : Nat) (f : PForm) : Status :=
  if !fastSat n f.dual then .tautology else if fastSat n f then .contingent else .contradiction

theorem fastStatus_eq (n : Nat) (f : PForm) : fastStatus n f = status n f := by
  simp only [fastStatus, status, fastSat_eq, valid_eq_not_sat_dual]


/-- Draw a target status uniformly, then random 3-CNFs until one is unsatisfiable (for
contradictions and tautologies) or satisfiable (for contingent formulas). Tautologies are duals of
unsatisfiable CNFs (`eval_dual`), and half the contingent formulas are duals too, so the outer
connective does not reveal the label. The label is always recomputed by `status`. -/
def sampleLogic (g : LogicGen) (r : Rng) : PForm × Rng :=
  let (c, r) := r.below 3
  let (form, r) := r.below 2
  let n := g.atoms
  let want := c == 1
  let rec go : Nat → Rng → PForm → PForm × Rng
    | 0, r, last => (last, r)
    | fuel + 1, r, _ =>
      let (f, r) := cnf n (g.clauses - 1) r
      if fastSat n f == want then (f, r) else go fuel r f
  let (f, r) := go g.fuel r (.atom 0)
  (if c == 2 || (c == 1 && form == 1) then f.dual else f, r)

def statusQ (n : Nat) : Question PForm Status := ⟨"status", fastStatus n⟩

def logicSpec (g : LogicGen) : Spec PForm :=
  { name := "prop-status"
    features := PForm.features g.atoms
    numFeatures := 21
    slots := [(statusQ g.atoms).slot]
    sample := sampleLogic g }

example : status 2 (.imp (.atom 0) (.or (.atom 0) (.atom 1))) = .tautology := by decide
example : status 2 (.and (.atom 1) (.neg (.atom 1))) = .contradiction := by decide

/-! ## Harder propositional instances

Threshold 3-CNF over many atoms, labelled by `fastStatus`. Extra features probe the formula's
CNF core (the formula, or the dual of a DNF) with cheap, incomplete parts of DPLL: unit
propagation after each single literal (a failed literal, one whose propagation reaches an empty
clause, is false in every model) and DPLL cut off after a few nodes (a model found within the
budget proves the core satisfiable; an unsatisfiable core is never refuted within it). -/

/-- The CNF that decides a CNF or DNF formula: the formula itself, or the dual of a DNF, which is
unsatisfiable exactly when the DNF is a tautology. -/
def PForm.core (f : PForm) : Dpll.CNF :=
  match f.cnf? with
  | some F => F
  | none => f.dual.cnf?.getD []

/-- Unit propagation to a fixpoint: `none` on reaching an empty clause, otherwise the number of
literals it assigned. -/
def unitProp : Nat → Dpll.CNF → Nat → Option Nat
  | 0, _, k => some k
  | fuel + 1, F, k =>
    match Dpll.shortest F with
    | some [] => none
    | some [l] => unitProp fuel (Dpll.assign l F) (k + 1)
    | _ => some k

/-- `Dpll.dpll` with a budget of nodes: the answer if the search ends within it, and the budget
left. -/
def boundedDpll : Nat → Dpll.CNF → Nat → Option Bool × Nat
  | 0, _, b => (none, b)
  | _ + 1, _, 0 => (none, 0)
  | fuel + 1, F, b + 1 =>
    match Dpll.shortest F with
    | none => (some true, b)
    | some [] => (some false, b)
    | some (l :: rest) =>
      if rest.isEmpty then boundedDpll fuel (Dpll.assign l F) b
      else
        match boundedDpll fuel (Dpll.assign l F) b with
        | (some false, b) => boundedDpll fuel (Dpll.assign (l.1, !l.2) F) b
        | r => r

theorem boundedDpll_sat : ∀ (fuel : Nat) (F : Dpll.CNF) (b : Nat),
    (boundedDpll fuel F b).1 = some true → Dpll.Sat F
  | 0, _, _, h => by simp [boundedDpll] at h
  | _ + 1, _, 0, h => by simp [boundedDpll] at h
  | fuel + 1, F, b + 1, h => by
    simp only [boundedDpll] at h
    split at h
    · rename_i hs
      rw [Dpll.shortest_eq_none hs]
      exact ⟨fun _ => false, rfl⟩
    · simp at h
    · rename_i l rest hs
      split at h
      · exact Dpll.sat_of_sat_assign (boundedDpll_sat fuel _ b h)
      · split at h
        · exact Dpll.sat_of_sat_assign (boundedDpll_sat fuel _ _ h)
        · exact Dpll.sat_of_sat_assign (boundedDpll_sat fuel _ b h)

/-- Features of a CNF over `n` atoms, each in 0…3: failed literals, whether some atom fails both
ways (a refutation), total propagation after one literal, how early DPLL with a budget of `4n`
nodes finds a model (3 within `3n/2` nodes, 2 within `5n/2`, 1 within `4n`, 0 not; a model needs
about `n` nodes), and the polarity imbalance
`Σ |pos − neg|` over atoms, bucketed. -/
def coreFeatures (n : Nat) (F : Dpll.CNF) : List Int :=
  let fuel := n + 1
  let probes := (List.range n).flatMap fun i => [(i, true), (i, false)]
  let runs := probes.map fun l => unitProp fuel (Dpll.assign l F) 0
  let failed := (runs.filter Option.isNone).length
  let both := ((List.range n).filter fun i =>
    (runs.getD (2 * i) none).isNone && (runs.getD (2 * i + 1) none).isNone).length
  let props := runs.foldl (fun s r => s + r.getD 0) 0
  let early := match boundedDpll fuel F (4 * n) with
    | (some true, left) =>
      let used := 4 * n - left
      if 2 * used ≤ 3 * n then 3 else if 2 * used ≤ 5 * n then 2 else 1
    | _ => 0
  let imb := (List.range n).foldl (fun s i =>
    let p := (F.filter (·.contains (i, true))).length
    let q := (F.filter (·.contains (i, false))).length
    s + (if p > q then p - q else q - p)) 0
  [cap failed, if both > 0 then 1 else 0, cap (props / 8), early, cap ((imb - min imb (2 * n)) / 15)]

def PForm.hardFeatures (n : Nat) (f : PForm) : List Int := f.features n ++ coreFeatures n f.core

/-- 40 atoms and 170 clauses (ratio 4.25): DPLL takes several hundred nodes to refute an
unsatisfiable draw. -/
def LogicGen.hard : LogicGen := { atoms := 40, clauses := 170, fuel := 200 }

def logicHardSpec (g : LogicGen) : Spec PForm :=
  { name := "prop-hard"
    features := PForm.hardFeatures g.atoms
    numFeatures := 26
    slots := [(statusQ g.atoms).slot]
    sample := sampleLogic g }

/-! ## Certificates

Two cheap one-sided procedures on the CNF core: the capped DPLL of `coreFeatures`, which can only
find a model, and `Dpll.lookahead`, which can only refute. When either succeeds, `certify` names
the status, and `certify_sound` proves it is the label. -/

/-- Literals over the atoms below `n` that occur in `F`. -/
def probeLits (n : Nat) (F : Dpll.CNF) : List Dpll.Lit :=
  (List.range n).flatMap fun i => if F.any (·.any (·.1 == i)) then [(i, true), (i, false)] else []

/-- The literal of greatest weight product: a literal weighs 4 per binary clause it is in and 1 per
longer clause, an atom scores `(w⁺ + 1)(w⁻ + 1)`, and the heavier side is tried first. -/
def weightPick (n : Nat) (F : Dpll.CNF) : Option Dpll.Lit :=
  let w : Dpll.Lit → Nat := fun l =>
    F.foldl (fun s c => if c.contains l then s + (if c.length ≤ 2 then 4 else 1) else s) 0
  let best := (List.range n).foldl (fun (acc : Option (Nat × Dpll.Lit)) i =>
    let p := w (i, true)
    let q := w (i, false)
    if p + q == 0 then acc else
    let sc := (p + 1) * (q + 1)
    match acc with
    | some (t, _) => if sc > t then some (sc, (i, Nat.ble q p)) else acc
    | none => some (sc, (i, Nat.ble q p))) none
  best.map (·.2)

/-- The literal whose atom shrinks the formula most on both sides under unit propagation, scored
`(d⁺ + 1)(d⁻ + 1)` with `d` the drop in `Dpll.size`; the side with the larger drop first. -/
def lookPick (fuel n : Nat) (F : Dpll.CNF) : Option Dpll.Lit :=
  let sz := Dpll.size F
  let d : Dpll.Lit → Nat := fun l => match Dpll.propagate fuel (Dpll.assign l F) with
    | none => sz
    | some G => sz - Dpll.size G
  let best := (probeLits n F).foldl (fun (acc : Option (Nat × Dpll.Lit)) (l : Dpll.Lit) =>
    if !l.2 then acc else
    let p : Nat := d (l.1, true)
    let q : Nat := d (l.1, false)
    let sc := (p + 1) * (q + 1)
    match acc with
    | some (t, _) => if sc > t then some (sc, (l.1, Nat.ble q p)) else acc
    | none => some (sc, (l.1, Nat.ble q p))) none
  best.map (·.2)

/-- Limits of the refutation search: closure passes per node, split depth, total nodes, and the
branching rule (`lookPick` when `look`, else `weightPick`). -/
structure RefuteCfg where
  rounds : Nat
  depth : Nat
  budget : Nat
  look : Bool
  deriving Repr

/-- `Dpll.lookahead` on a CNF over `n` atoms: whether it was refuted, and the nodes left. -/
def refuteCore (n : Nat) (c : RefuteCfg) (F : Dpll.CNF) : Bool × Nat :=
  Dpll.lookahead (n + 1) c.rounds (probeLits n) (if c.look then lookPick (n + 1) n else weightPick n)
    c.depth F c.budget

theorem refuteCore_sound (n : Nat) (c : RefuteCfg) (F : Dpll.CNF) (h : (refuteCore n c F).1 = true) :
    ¬ Dpll.Sat F :=
  Dpll.lookahead_sound _ _ _ _ _ _ _ h

def negLit (m : Dpll.Lit) : Dpll.Lit := (m.1, !m.2)

/-- Some clause can be made false by an assignment of `n` atoms. -/
def falsifiable (n : Nat) (F : Dpll.CNF) : Bool := F.any fun c => Dpll.satN n (units (c.map negLit))

theorem falsifiable_sound {n : Nat} {F : Dpll.CNF} (h : falsifiable n F = true) :
    ∃ l : List Bool, l.length = n ∧ Dpll.cnfEval (Dpll.ofList l) F = false := by
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp h
  obtain ⟨l, hl, he⟩ := (Dpll.satN_iff n _).mp hs
  refine ⟨l, hl, ?_⟩
  rw [cnfEval_units, List.all_eq_true] at he
  have hcf : Dpll.clauseEval (Dpll.ofList l) c = false := by
    simp only [Dpll.clauseEval, List.any_eq_false]
    intro m hm hm'
    have := he _ (List.mem_map_of_mem hm)
    simp only [negLit, Dpll.litEval, beq_iff_eq] at this hm'
    cases e : m.2 <;> simp_all
  simp only [Dpll.cnfEval, List.all_eq_false]
  exact ⟨c, hc, by simp [hcf]⟩

/-- A model of `F` within `4n` DPLL nodes over atoms below `n` (the capped search of
`coreFeatures`, on `Dpll.restrict n F`). -/
def modelFound (n : Nat) (F : Dpll.CNF) : Bool :=
  (boundedDpll (n + 1) (Dpll.restrict n F) (4 * n)).1 == some true

theorem modelFound_sound {n : Nat} {F : Dpll.CNF} (h : modelFound n F = true) :
    ∃ l : List Bool, l.length = n ∧ Dpll.cnfEval (Dpll.ofList l) F = true :=
  (Dpll.sat_restrict_iff n F).mp (boundedDpll_sat _ _ _ (by simpa [modelFound] using h))

/-- What the certificates say about a CNF: `some false` refuted, `some true` a model found and a
clause falsifiable, `none` neither. -/
def coreCert (n : Nat) (c : RefuteCfg) (F : Dpll.CNF) : Option Bool :=
  if (refuteCore n c F).1 then some false
  else if modelFound n F && falsifiable n F then some true else none

theorem coreCert_false {n : Nat} {c : RefuteCfg} {F : Dpll.CNF} (h : coreCert n c F = some false) :
    ∀ σ, Dpll.cnfEval σ F = false := by
  intro σ
  unfold coreCert at h
  split at h
  · rename_i hr
    cases e : Dpll.cnfEval σ F
    · rfl
    · exact absurd ⟨σ, e⟩ (refuteCore_sound n c F hr)
  · split at h <;> cases h

theorem coreCert_true {n : Nat} {c : RefuteCfg} {F : Dpll.CNF} (h : coreCert n c F = some true) :
    (∃ l : List Bool, l.length = n ∧ Dpll.cnfEval (Dpll.ofList l) F = true) ∧
    (∃ l : List Bool, l.length = n ∧ Dpll.cnfEval (Dpll.ofList l) F = false) := by
  unfold coreCert at h
  split at h
  · cases h
  · split at h
    · rename_i hm
      rw [Bool.and_eq_true] at hm
      exact ⟨modelFound_sound hm.1, falsifiable_sound hm.2⟩
    · cases h

/-- The status certified for a CNF formula, or for a DNF through the CNF of its dual. -/
def certify (n : Nat) (c : RefuteCfg) (f : PForm) : Option Status :=
  match f.cnf? with
  | some F => (coreCert n c F).map fun b => if b then .contingent else .contradiction
  | none =>
    match f.dual.cnf? with
    | some F => (coreCert n c F).map fun b => if b then .contingent else .tautology
    | none => none

/-- A certified status is the label. -/
theorem certify_sound (n : Nat) (c : RefuteCfg) (f : PForm) (s : Status) (h : certify n c f = some s) :
    status n f = s := by
  unfold certify at h
  split at h
  · rename_i F hF
    have hev := fun v => PForm.cnf?_eval (v := v) hF
    cases hc : coreCert n c F with
    | none => simp [hc] at h
    | some b =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst h
      cases b
      · exact (status_contradiction_iff n f).mpr fun l _ => (hev l).trans (coreCert_false hc _)
      · obtain ⟨⟨l₁, hl₁, he₁⟩, ⟨l₂, hl₂, he₂⟩⟩ := coreCert_true hc
        exact (status_contingent_iff n f).mpr
          ⟨⟨l₁, hl₁, (hev l₁).trans he₁⟩, ⟨l₂, hl₂, (hev l₂).trans he₂⟩⟩
  · split at h
    · rename_i F hF
      have hev : ∀ v, f.eval v = !Dpll.cnfEval (Dpll.ofList v) F := fun v => by
        rw [← PForm.cnf?_eval hF, PForm.eval_dual, Bool.not_not]
      cases hc : coreCert n c F with
      | none => simp [hc] at h
      | some b =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        cases b
        · exact (status_tautology_iff n f).mpr fun l _ => by rw [hev, coreCert_false hc]; rfl
        · obtain ⟨⟨l₁, hl₁, he₁⟩, ⟨l₂, hl₂, he₂⟩⟩ := coreCert_true hc
          exact (status_contingent_iff n f).mpr
            ⟨⟨l₂, hl₂, by rw [hev, he₂]; rfl⟩, ⟨l₁, hl₁, by rw [hev, he₁]; rfl⟩⟩
    · cases h

/-- The refutation search used for `prop-hard`'s certificates and feature. -/
def LogicGen.refute : RefuteCfg := { rounds := 1, depth := 6, budget := 16, look := false }

/-- The refutation result as a feature in 0…3: 3 refuted by closure alone (one node), 2 within a
quarter of the budget, 1 within the budget, 0 not refuted. -/
def refuteFeature (n : Nat) (c : RefuteCfg) (F : Dpll.CNF) : Int :=
  let (ok, left) := refuteCore n c F
  if !ok then 0 else
  let used := c.budget - left
  if used ≤ 1 then 3 else if 4 * used ≤ c.budget then 2 else 1

def PForm.certFeatures (n : Nat) (c : RefuteCfg) (f : PForm) : List Int :=
  f.hardFeatures n ++ [refuteFeature n c f.core]

/-- `prop-hard` with the refutation feature: the same instances and labels. -/
def logicCertSpec (g : LogicGen) (c : RefuteCfg) : Spec PForm :=
  { name := "prop-hard-cert"
    features := PForm.certFeatures g.atoms c
    numFeatures := 27
    slots := [(statusQ g.atoms).slot]
    sample := sampleLogic g }

/-! ## Fresh evaluation sets -/

/-- `n` instances drawn from `seed`, without those equal to a training instance. -/
def fresh {σ : Type} [DecidableEq σ] (s : Spec σ) (train : List σ) (seed n : Nat) : List σ :=
  ((s.sampleN n (Rng.seeded seed)).1).filter fun x => !train.contains x

theorem fresh_disjoint {σ : Type} [DecidableEq σ] (s : Spec σ) (train : List σ) (seed n : Nat)
    (x : σ) (h : x ∈ fresh s train seed n) : x ∉ train := by
  intro hx
  simp [fresh, List.mem_filter, hx] at h

/-! ## Training configurations -/

/-- Chosen by validation accuracy (`ixai bench typed-sweep`). Updates are rounded toward negative
infinity, so every step drifts small weights down; large batches keep the step count low. -/
def typeConfig : Config :=
  { seed := 2611, hidden := 16, lrRaw := 1, epochs := 10, batch := 50, trainSize := 2000, testSize := 200 }

def logicConfig : Config :=
  { seed := 2612, hidden := 16, lrRaw := 1, epochs := 10, batch := 50, trainSize := 2000, testSize := 200 }

def logicHardConfig : Config :=
  { seed := 2613, hidden := 16, lrRaw := 1, epochs := 10, batch := 50, trainSize := 2000, testSize := 200 }

end Typed
end IxAICore
