import Ix.CompileCert.Opt.Basic

/-!
# M7 L3-def: the shape of an image, and the laws the definitional passes read

Every definitional pass reads the **shape** of the image of the related Lean recursor
(`Ix.Compile.Pass.Opt.RecShape`, read off `img(r)` by `readShape`): the image is
`λ ps ms mins is t. ρ.{ℓs} ps ms′ mins′ is t` with the parameters, indices and major passed as
its own variables, every Ix motive one of its motive variables (`motiveSrc`), every Ix minor a
minor variable (`minorSrc = some j`) or another term. `ShapeAt s ls v` says this of an erased
term `v` at the universe arguments `ls` of `ρ`.

The **laws** are the rules of the conversion environment `Γ` the passes' docstrings use, stated
at the occurrence's own universe arguments (design D-1 (a), `plans/review2/M7-L3-def.md` §1.1):

* `RecLaw`: a Lean recursor of a changed block δ-reduces to its image, whose shape is the one
  the block records (decision 3; Pass 3a);
* `RecOnLaw`: Lean's `x.recOn` δ-reduces to `mkRecOn` over `x.rec` (Def 3.5: Lean's auxiliary
  over the image), and `x.rec` to its image;
* `IxRecOnLaw` (AuxLaws, OD5): Pass 2's `ρ.recOn` δ-reduces to the same construction over `ρ`.

Each is a hypothesis of the theorems that use it; who discharges it is in the report's laws
ledger (§2).

`Option` do-blocks: `obind` (a bind that succeeded), `onone_bind`, `opure_bind`.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## `Option` do-blocks -/

theorem obind {α β : Type} {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none =>
    constructor
    · intro h; cases h
    · intro h; obtain ⟨_, h, _⟩ := h; cases h
  | some a =>
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · intro h; obtain ⟨a', h1, h2⟩ := h; cases h1; exact h2

theorem onone_bind {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl

theorem opure_bind {α β : Type} (a : α) (f : α → Option β) : ((pure a : Option α) >>= f) = f a := rfl

/-- **An `Option` guard** `if c then none` followed by the rest of a do-block, as the
do-elaborator leaves it after `dsimp` (the join point inlined): a run that succeeded passed it. -/
theorem oguard {c : Prop} [Decidable c] {α β : Type} {f : α → Option β} {r : Option β} {e : β}
    (h : (if c then (none >>= f) else r) = some e) : ¬ c ∧ r = some e := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h
    cases h
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, h⟩

/-- A run through a `none`: impossible. -/
macro "oabsurd" h:ident : tactic =>
  `(tactic| first
    | (dsimp only at $h:ident; rw [onone_bind] at $h:ident; cases $h:ident)
    | (rw [onone_bind] at $h:ident; cases $h:ident)
    | (cases $h:ident; done)
    | (simp at $h:ident; done))

/-- The `then` branch of an `if` that holds. -/
theorem oite_true {c : Prop} [Decidable c] {α : Type} {a b x : α} (hc : c)
    (h : (if c then a else b) = x) : a = x := by
  simp only [hc, ↓reduceIte] at h
  exact h

/-- The `else` branch of an `if` that fails. -/
theorem oite_false {c : Prop} [Decidable c] {α : Type} {a b x : α} (hc : ¬ c)
    (h : (if c then a else b) = x) : b = x := by
  simp only [hc, ↓reduceIte] at h
  exact h


/-! ## Shapes -/

/-- Telescope position `p` of a shape's image, as a variable of its body. -/
def shapeTv (s : RecShape) (p : Nat) : Tm := .bvar (s.arity - 1 - p)

/-- The body's arguments, with the given minor terms. -/
def shapeArgs (s : RecShape) (mins : List Tm) : List Tm :=
  (List.range s.np).map (shapeTv s) ++ s.motiveSrc.toList.map (fun p => shapeTv s (s.np + p)) ++ mins ++
    (List.range (s.ni + 1)).map (fun i => shapeTv s (s.np + s.nm + s.nmin + i))

/-- `v` is the (erased) image of shape `s`, at the universe arguments `ls` of `ρ`. -/
def ShapeAt (s : RecShape) (ls : Array Level) (v : Tm) : Prop :=
  ∃ ts mins, ts.length = s.arity ∧ mins.length = s.minorSrc.size ∧
    (∀ (k j : Nat), s.minorSrc[k]? = some (some j) → mins[k]? = some (shapeTv s (s.np + s.nm + j))) ∧
    v = lamN ts (Tm.appN (.const s.ixRec ls) (shapeArgs s mins))

/-- The Lean minors a selection shape passes, in Ix order. -/
def selMinors (s : RecShape) : List Nat := s.minorSrc.toList.filterMap id

/-- The telescope positions a selection shape passes to `ρ`, in Ix order. -/
def shapeIdx (s : RecShape) : List Nat :=
  List.range s.np ++ s.motiveSrc.toList.map (s.np + ·) ++ (selMinors s).map (s.np + s.nm + ·) ++
    (List.range (s.ni + 1)).map (s.np + s.nm + s.nmin + ·)

theorem mins_eq (f : Nat → Tm) : ∀ (l : List (Option Nat)) (mins : List Tm),
    (∀ x ∈ l, x.isSome = true) → mins.length = l.length →
    (∀ (k j : Nat), l[k]? = some (some j) → mins[k]? = some (f j)) → mins = (l.filterMap id).map f
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: l, m :: mins, hs, hlen, hpt => by
    obtain ⟨j, rfl⟩ : ∃ j, x = some j := Option.isSome_iff_exists.1 (hs x (List.mem_cons_self ..))
    have hm : m = f j := by
      have := hpt 0 j (by simp)
      simpa using this
    have ih := mins_eq f l mins (fun y hy => hs y (List.mem_cons_of_mem _ hy)) (by simpa using hlen)
      (fun k j' h => by
        have := hpt (k + 1) j' (by simpa using h)
        simpa using this)
    rw [hm, ih]
    rfl

/-- **A selection shape** (every Ix minor a minor variable): the body is `ρ` applied to telescope
positions. -/
theorem ShapeAt.sel {s : RecShape} {ls : Array Level} {v : Tm}
    (hsel : s.minorSrc.all Option.isSome = true) (h : ShapeAt s ls v) :
    ∃ ts, ts.length = s.arity ∧
      v = lamN ts (Tm.appN (.const s.ixRec ls) ((shapeIdx s).map fun p => .bvar (s.arity - 1 - p))) := by
  obtain ⟨ts, mins, hts, hlen, hpt, rfl⟩ := h
  refine ⟨ts, hts, ?_⟩
  have hall : ∀ x ∈ s.minorSrc.toList, x.isSome = true := fun x hx =>
    Array.all_eq_true_iff_forall_mem.mp hsel x (Array.mem_toList_iff.mp hx)
  have hm : mins = (s.minorSrc.toList.filterMap id).map (fun j => shapeTv s (s.np + s.nm + j)) :=
    mins_eq _ s.minorSrc.toList mins hall (by rw [hlen, Array.length_toList])
      (fun k j hk => hpt k j (by rw [← Array.getElem?_toList]; exact hk))
  rw [hm]
  simp only [shapeArgs, shapeIdx, selMinors, List.map_append, List.map_map]
  rfl

/-- `v` is the (erased) image of shape `s` at `ls`, with its minor terms `mins` named (closed
over the image's telescope: no loose variable past it). -/
def ImageAt (s : RecShape) (ls : Array Level) (mins : List Tm) (v : Tm) : Prop :=
  ∃ ts, ts.length = s.arity ∧ mins.length = s.minorSrc.size ∧
    (∀ (k j : Nat), s.minorSrc[k]? = some (some j) → mins[k]? = some (shapeTv s (s.np + s.nm + j))) ∧
    (∀ t ∈ mins, t.range ≤ s.arity) ∧
    v = lamN ts (Tm.appN (.const s.ixRec ls) (shapeArgs s mins))

/-- A shape's bounds (what `readShape` checks: motive and minor sources in Lean's ranges). -/
structure ShapeWF (s : RecShape) : Prop where
  motives : ∀ m ∈ s.motiveSrc.toList, m < s.nm
  minors : ∀ j ∈ selMinors s, j < s.nmin

/-! ## The laws -/

/-- The shapes the passes can read: those of some block of some head. -/
def ShapeIn (env : OptEnv) (s : RecShape) : Prop :=
  ∃ h b r, env.blockOf h = some b ∧ b.shapes.get? r = some s

/-- **`RecLaw`** (decision 3, Pass 3a): a Lean recursor `h` of a changed block δ-reduces, at every
universe argument `us`, to its image, whose shape is the one the block records. -/
def RecLaw (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (h r : Name) (b : OptBlock) (s : RecShape) (us : Array Level),
    classify h = some (.kRec, r) → env.blockOf h = some b → b.shapes.get? r = some s →
    ∃ v, Γ.ax (.const h us) v ∧ ShapeAt s (s.levelsAt us) v

/-- The positions of `rec`'s arguments `ps ms mins is t` in `recOn`'s telescope `ps ms is t
mins` (Lean's `mkRecOn`). -/
def recOnIdx (np nm nmin ni : Nat) : List Nat :=
  List.range np ++ (List.range nm).map (np + ·) ++ (List.range nmin).map (np + nm + ni + 1 + ·) ++
    (List.range (ni + 1)).map (np + nm + ·)

/-- `v` is `mkRecOn` over `c.{us}`: `λ ps ms is t mins. c.{us} ps ms mins is t`. -/
def RecOnBody (c : Name) (us : Array Level) (np nm nmin ni : Nat) (v : Tm) : Prop :=
  ∃ ts, ts.length = np + nm + nmin + ni + 1 ∧
    v = lamN ts (Tm.appN (.const c us)
      ((recOnIdx np nm nmin ni).map fun p => .bvar (np + nm + nmin + ni + 1 - 1 - p)))

/-- **`RecOnLaw`** (Def 3.5, Lean's `mkRecOn`): Lean's `x.recOn` δ-reduces to `mkRecOn` over
`x.rec` at the same universe arguments, and `x.rec` to its image. -/
def RecOnLaw (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (h r : Name) (b : OptBlock) (s : RecShape) (us : Array Level),
    classify h = some (.kRecOn, r) → env.blockOf h = some b → b.shapes.get? r = some s →
    (∃ v, Γ.ax (.const h us) v ∧ RecOnBody r us s.np s.nm s.nmin s.ni v) ∧
    (∃ v, Γ.ax (.const r us) v ∧ ShapeAt s (s.levelsAt us) v)

/-- **`IxRecOnLaw`** (AuxLaws, OD5): Pass 2's `ρ.recOn` (the display name next to `ρ`, when it
resolves) δ-reduces to `mkRecOn` over `ρ` at the same universe arguments, with `ρ`'s counts. -/
def IxRecOnLaw (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (s : RecShape) (ixRecOn : Name) (ls : Array Level), ShapeIn env s →
    ixAuxOf s.ixRec .kRecOn = some ixRecOn → env.resolves ixRecOn = true →
    ∃ v, Γ.ax (.const ixRecOn ls) v ∧
      RecOnBody s.ixRec ls s.np s.motiveSrc.size s.minorSrc.size s.ni v

/-! ## Facts about the compiler's helpers -/

theorem O5_levels_eq {s : RecShape} {us ls : Array Level} (h : O5.levels s us = some ls) :
    ls = s.levelsAt us := by
  unfold O5.levels at h
  split at h
  · exact (Option.some.inj h).symm
  · split at h
    · split at h
      · exact (Option.some.inj h).symm
      · cases h
    · cases h

/-- The telescope length `standardTelescope` checks, by kind. -/
def stdArity (s : RecShape) (k : AuxKind) (nctors : Nat) : Nat :=
  match k with
  | .kRec | .kRecOn => s.np + s.nm + s.nmin + s.ni + 1
  | .kCasesOn => s.np + 1 + s.ni + 1 + nctors
  | .kBelow => s.np + s.nm + s.ni + 1
  | .kBRecOn | .kGo | .kEq => s.np + s.nm + s.ni + 1 + s.nm

theorem standardTelescope_eq {env : OptEnv} {s : RecShape} {k : AuxKind} {a : Name} {nctors n : Nat}
    (h : standardTelescope env s k a nctors = some n) : n = stdArity s k nctors := by
  unfold standardTelescope at h
  obtain ⟨ci, _, h⟩ := obind.1 h
  dsimp only at h
  obtain ⟨_, h⟩ := oguard h
  obtain ⟨_, h⟩ := oguard h
  simp only [pure, Option.some.injEq] at h
  rw [← h]
  cases k <;> rfl

theorem isPerm_sel {s : RecShape} (h : s.isPerm = true) :
    s.minorSrc.all Option.isSome = true ∧ s.motiveSrc.size = s.nm ∧ s.minorSrc.size = s.nmin := by
  simp only [RecShape.isPerm, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.2, h.1.1.1.1, h.1.1.1.2⟩

theorem filterMap_id_length : ∀ (l : List (Option Nat)), (∀ x ∈ l, x.isSome = true) →
    (l.filterMap id).length = l.length
  | [], _ => rfl
  | x :: l, hall => by
    obtain ⟨j, rfl⟩ : ∃ j, x = some j := Option.isSome_iff_exists.1 (hall x (List.mem_cons_self ..))
    simp only [List.filterMap_cons, id_eq, List.length_cons]
    rw [filterMap_id_length l (fun y hy => hall y (List.mem_cons_of_mem _ hy))]

theorem selMinors_length {s : RecShape} (hsel : s.minorSrc.all Option.isSome = true) :
    (selMinors s).length = s.minorSrc.size := by
  have hall : ∀ x ∈ s.minorSrc.toList, x.isSome = true := fun x hx =>
    Array.all_eq_true_iff_forall_mem.mp hsel x (Array.mem_toList_iff.mp hx)
  unfold selMinors
  rw [filterMap_id_length _ hall, Array.length_toList]

end Ix.CompileCert.Opt
