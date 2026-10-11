import Ix.CompileCert.Image.Post

/-!
# M7 L2a-syn: the domain of the image construction, decidably

`Dom` is stated by running the construction with a **checking development**
`domDev`: each development call is checked to be in one of the fuel classes of `Fuel.lean` (the
substituted values first-order and closed at motive sites, or the variables passive; the call-site
arguments inert) with its height bound within `defaultFuel`, and is then computed with an ample
fuel `bigFuel`. So `Dom r` holds when the construction's own analyses succeed (the Lean recursor's
shape, the eliminator of every Lean motive, non-empty slot classes, the elimination level, the
canonical and Lean minors' shapes, relocation within its bound) and every development it makes is
in the classes. All of it is decidable (`Dom` is a computation).

* `checkSubst`, `checkInst`: the classes, as `Bool`s (`hdB_iff`, `siteB_iff`, `noOccB_iff`,
  `inertB_iff`);
* `devRel_dom`: **on a call `domDev` accepts, X1's core at `defaultFuel` returns the same
  result** (the fuel bounds of `Fuel.lean` and X1's `fuel_mono`), and from shifted counters a
  related one.
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor ImageSpec
  GenOptions Image)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)

/-! ## The fuel classes, decidably -/

def noOccB (K k : Nat) (e : Expr) : Bool := (List.range K).all fun j => !Tm.occ (er e) (k + j)

theorem noOccB_iff {K k : Nat} {e : Expr} : noOccB K k e = true ↔ NoOcc K k e := by
  unfold noOccB NoOcc
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true]

def siteB (K H k : Nat) (e : Expr) : Bool :=
  match (getAppFnArgs e).1 with
  | .bvar i _ => decide (k ≤ i) && decide (i < k + K) &&
      (getAppFnArgs e).2.toList.all (noOccB K k) && decide (hsum (getAppFnArgs e).2.toList ≤ H)
  | _ => false

theorem siteB_iff {K H k : Nat} {e : Expr} : siteB K H k e = true ↔ Site K H k e := by
  unfold siteB Site
  generalize getAppFnArgs e = p
  obtain ⟨hd, args⟩ := p
  simp only
  constructor
  · intro h
    split at h
    · rename_i i hh
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      exact ⟨i, hh, rfl, h.1.1.1, h.1.1.2, fun a ha => noOccB_iff.1 (h.1.2 a ha), h.2⟩
    · cases h
  · rintro ⟨i, hh, rfl, h1, h2, h3, h4⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨⟨h1, h2⟩, fun a ha => noOccB_iff.2 (h3 a ha)⟩, h4⟩

/-- `Hd`, decidably. -/
def hdB (K H : Nat) : Nat → Expr → Bool
  | k, .forallE _ t b _ _ => hdB K H k t && hdB K H (k + 1) b
  | k, .mdata _ x _ => hdB K H k x
  | k, e => siteB K H k e || noOccB K k e

theorem hdB_iff {K H : Nat} : ∀ {k : Nat} {e : Expr}, hdB K H k e = true ↔ Hd K H k e
  | k, .forallE _ t b _ _ => by
    simp only [hdB, Hd, Bool.and_eq_true, hdB_iff (e := t), hdB_iff (e := b)]
  | k, .mdata _ x _ => by simp only [hdB, Hd, hdB_iff (e := x)]
  | k, .bvar .. | k, .fvar .. | k, .mvar .. | k, .sort .. | k, .const .. | k, .app ..
  | k, .lam .. | k, .letE .. | k, .lit .. | k, .proj .. => by
    simp only [hdB, Hd, Bool.or_eq_true, siteB_iff, noOccB_iff]

/-- The `H` a motive-site structure needs: the largest sum of argument heights at a leaf. -/
def hdH : Expr → Nat
  | .forallE _ t b _ _ => max (hdH t) (hdH b)
  | .mdata _ x _ => hdH x
  | e => hsum (getAppFnArgs e).2.toList

/-- `TmInert`, decidably. -/
def inertB (t : Tm) : Bool :=
  match thd t with
  | .lam .. => false
  | .const c _ => (ctorKind c).isNone
  | _ => true

theorem inertB_iff {t : Tm} : inertB t = true ↔ TmInert t := by
  unfold inertB TmInert
  split <;> simp_all [Option.isNone_iff_eq_none]

/-- The largest height in a list. -/
def maxHgt (L : List Expr) : Nat := L.foldr (fun v m => max (hgt v) m) 0

theorem le_maxHgt : ∀ {L : List Expr} {v : Expr}, v ∈ L → hgt v ≤ maxHgt L
  | _ :: _, _, .head _ => by simp only [maxHgt, List.foldr_cons]; omega
  | a :: l, v, .tail _ h => by
    have := le_maxHgt h
    simp only [maxHgt, List.foldr_cons] at this ⊢; omega

/-- A substitution `substFVars xs vs e` in the fuel classes: the values closed, and either
first-order at motive sites (`substChain_sites`) or substituted for passive variables
(`substChain_passive`), with the height bound within `defaultFuel`. -/
def checkSubst (xs : Array Name) (vs : Array Expr) (e : Expr) : Bool :=
  let acc := Ix.Compile.Image.abstractFVars xs e
  let L := vs.toList.reverse
  let K := L.length
  let V := maxHgt L
  let H := hdH acc
  xs.size == vs.size && L.all (fun v => looseRangeP v == 0) &&
    ((L.all (fun v => FOv (er v) 0) && hdB K H 0 acc &&
        decide (hgt acc + K * (V + H) + 1 ≤ Ix.Compile.Image.defaultFuel)) ||
      ((List.range K).all (fun j => Passive j (er acc)) &&
        decide (hgt acc + hsum L ≤ Ix.Compile.Image.defaultFuel)))

/-- A call-site development `instantiate f args` in the fuel class: the arguments inert. -/
def checkInst (f : Expr) (args : Array Expr) : Bool :=
  args.toList.all (fun a => inertB (er a)) &&
    decide (hgt f + hsum args.toList + 1 ≤ Ix.Compile.Image.defaultFuel)

/-- An ample fuel: the domain's computation is not limited by the development's bound. -/
def bigFuel : Nat := 1 <<< 64

theorem defaultFuel_le_big : Ix.Compile.Image.defaultFuel ≤ bigFuel := by
  unfold Ix.Compile.Image.defaultFuel bigFuel; decide

/-- **The checking development** of `Dom`. -/
def domDev : DevOps where
  subst xs vs e :=
    if checkSubst xs vs e then substChain bigFuel vs.toList.reverse (Ix.Compile.Image.abstractFVars xs e)
    else throw "Dom: a substitution outside the fuel classes"
  inst f args :=
    if checkInst f args then happP bigFuel f args.toList
    else throw "Dom: a call-site development outside the fuel class"

/-- `Dom` for one Lean recursor `r`: the construction succeeds with the checking development. -/
def Dom (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec) (r : Name) :
    Prop :=
  (imageOfW domDev opts const? spec r).isOk = true

instance (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec) (r : Name) :
    Decidable (Dom opts const? spec r) := by unfold Dom; infer_instance

/-! ## On the domain, the core at `defaultFuel` returns -/

theorem substChain_mono {n m : Nat} (hnm : n ≤ m) : ∀ {L : List Expr} {acc r : Expr},
    substChain n L acc = .ok r → substChain m L acc = .ok r
  | [], acc, r, h => h
  | v :: L, acc, r, h => by
    unfold substChain at h ⊢
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨acc', h1, h2⟩ := bind_ok h
    obtain ⟨⟨a, c⟩, ha, rfl⟩ := map_ok h1
    have := (fuel_mono n m hnm).1 v 0 acc _ ha
    rw [this]
    exact substChain_mono hnm (L := L) h2

/-- On a substitution `domDev` accepts, X1's core returns the same result. -/
theorem core_subst_of_dom {xs : Array Name} {vs : Array Expr} {e r : Expr}
    (h : domDev.subst xs vs e = .ok r) : substFVarsP xs vs e = .ok r := by
  simp only [domDev] at h
  split at h
  · rename_i hc
    unfold checkSubst at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      at hc
    obtain ⟨⟨hsz, hcl⟩, hcls⟩ := hc
    rw [substFVarsP_eq _ _ _ hsz]
    have hcl' : ∀ v ∈ vs.toList.reverse, looseRangeP v = 0 := fun v hv => by
      have := hcl v hv; simpa using this
    rcases hcls with ⟨⟨hfo, hd⟩, hb⟩ | ⟨hp, hb⟩
    · obtain ⟨r0, h0, -⟩ := substChain_sites _ _ vs.toList.reverse _ Ix.Compile.Image.defaultFuel
        (fun v hv => ⟨hcl' v hv, hfo v hv, le_maxHgt hv⟩) (hdB_iff.1 hd) hb
      have := substChain_mono defaultFuel_le_big h0
      rw [this] at h; cases h; exact h0
    · obtain ⟨r0, h0, -⟩ := substChain_passive vs.toList.reverse _ Ix.Compile.Image.defaultFuel
        hcl' (fun j hj => hp j (List.mem_range.2 hj)) hb
      have := substChain_mono defaultFuel_le_big h0
      rw [this] at h; cases h; exact h0
  · cases h

/-- On a call-site development `domDev` accepts, X1's core returns the same result. -/
theorem core_inst_of_dom {f : Expr} {args : Array Expr} {r : Expr}
    (h : domDev.inst f args = .ok r) : instantiateP f args = .ok r := by
  simp only [domDev] at h
  split at h
  · rename_i hc
    unfold checkInst at hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨r0, h0, -⟩ := instantiateP_inert (fun a ha => inertB_iff.1 (hc.1 a ha)) hc.2
    have := (fuel_mono _ _ defaultFuel_le_big).2 f args.toList r0 h0
    rw [this] at h; cases h; exact h0
  · cases h

section
variable {s0 d B : Nat}

/-- **On the domain, X1's core at `defaultFuel` follows the checking development**, from shifted
counters too. -/
theorem devRel_dom (hok : InjOn (shift s0 d) (FreshBelow B)) : DevRel s0 d B domDev coreDev := by
  refine ⟨fun hxs hv he r hr => ?_, fun hf ha r hr => ?_⟩
  · exact (devRel_core hok).subst hxs hv he r (core_subst_of_dom hr)
  · exact (devRel_core hok).inst hf ha r (core_inst_of_dom hr)

end

end Ix.CompileCert.Img
