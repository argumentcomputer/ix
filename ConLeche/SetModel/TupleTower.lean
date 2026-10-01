module

public import ConLeche.SetTheory.Derive.Sigma

@[expose] public section

/-!
# The uniform tuple model: unit-terminated pair towers (agent/tuple-model)

The semantic carrier construction for directly-installed structures
(DESIGN.md, "AMENDMENT — the uniform tuple model"): every qualifying
structure's carrier is the **right-nested pair tower with unit
terminator**

    towerSet w ⟨F₀, …, F_{n−1}⟩ = F₀ ⋉ (F₁ ⋉ (… ⋉ (F_{n−1} ⋉ unitSet)))

(each `⋉` a `sigmaSet w`, dependency right-nested along the field
telescope), the constructor is the uniform tupler `mkTower`, and the
semantic projection family is ONE definition depending only on the
index:

    projS i = sfst ∘ ssnd^i        (structure-independent)

The unit terminator is what buys index-only uniformity: with a bare
tail the last field would be read by `ssnd^{n−1}` (no `sfst`), making
the family depend on the arity — i.e. on the structure.  It also
gives the 0/1-field degeneracies for free (`n = 0`: the carrier is
`unitSet`, members exactly `pt = mkTower []`; `n = 1`: members are
`spair a pt` and `projS 0 = sfst` is lawful).

**ProjCoherence by uniform tupling**: the constructor is one
instantiation-independent function with global left inverses
(`kpair_inj` iterated), so the parked study's boundary predicate is
discharged by representation — tier form `mkTower_inj`, proved through
the iota law alone.

**No `pw` datum — `pt` is separate from pairs** (user refinement,
2026-09-04): the interface keeps the proof point apart from every
Kuratowski pair (`pt_ne_kpair`, the `Derive/Pt.lean` selection
principle, surfaced as `sfst_pt`/`ssnd_pt`; the task-#109 pt-freshness
battery is the systematic form), so the destructors fix `pt` and
`projS i pt = pt` holds outright.  A `Prop` structure's element
denotes `pt` and its proof fields denote `pt`, so projection-of-`pt`
is the *correct* answer by proof irrelevance — iota and membership
hold with one uniform `projS`, no per-structure variant.  The squash
membership law carries the proof-field premise `PropS` (every field
set a truth value — the levelwise `structSort = 0 → fieldSort = 0`
bound); that is not a datum on the projection but the per-use
legality the checker's own `infer_proj` Prop restriction discharges.
The two regimes are disjoint by the same separation: graph-regime
members of a nonempty tower are never `pt` (`tower_mem_ne_pt`, from
`ptFresh_sigmaSet_pos`), squash members are exactly `pt`.

Everything here is over the bare `SetTheory` interface; no syntax, no
environment.  Kernel wiring is out of scope (post-B4; see the DESIGN
handoff record).
-/

namespace ConLeche.SetTheory.Tower

universe u

/-- A dependent field-set telescope over `V`, indexed by its length:
field `i`'s set may depend on the values of fields `0..i−1`. -/
inductive TeleS (V : Type u) : Nat → Type u where
  | nil : TeleS V 0
  | cons {n : Nat} (A : V) (B : V → TeleS V n) : TeleS V (n + 1)

variable {V : Type u} [SetTheory V]

/-- `FitsS T as`: the value list `as` fits the telescope `T` — right
length, each value in its field's set at the earlier values. -/
def FitsS : {n : Nat} → TeleS V n → List V → Prop
  | _, .nil, [] => True
  | _, .nil, _ :: _ => False
  | _, .cons _ _, [] => False
  | _, .cons A B, a :: as => a ∈ˢ A ∧ FitsS (B a) as

/-- The carrier: the right-nested `sigmaSet w` tower over the
telescope, terminated by `unitSet`. -/
noncomputable def towerSet (w : Nat) : {n : Nat} → TeleS V n → V
  | _, .nil => unitSet
  | _, .cons A B => sigmaSet w A (fun a => towerSet w (B a))

/-- The uniform tupler: the right-nested Kuratowski pair tower with
`pt` (the sole member of `unitSet`) as terminator. -/
noncomputable def mkTower : List V → V
  | [] => pt
  | a :: as => spair a (mkTower as)

/-- **The uniform semantic projection family**: `projS i = sfst ∘
ssnd^i`.  One definition for every structure and every index. -/
noncomputable def projS : Nat → V → V
  | 0, x => sfst x
  | i + 1, x => projS i (ssnd x)

/-- The first-`n` projection tuple of a value. -/
noncomputable def projList : Nat → V → List V
  | 0, _ => []
  | n + 1, x => sfst x :: projList n (ssnd x)

/-- The `k`-fold second projection (task #210 Part A): the tuple tower
below `k` leading pair components — `projS (i + k) x = projS i (dropS k
x)`, so a projection table with offset `k` reads its fields off
`dropS k` of the subject (`k = 1` at the fixpoint route's tagged
tower, whose first component is the constructor tag). -/
noncomputable def dropS : Nat → V → V
  | 0, x => x
  | k + 1, x => dropS k (ssnd x)

theorem projS_add_dropS : ∀ (i k : Nat) (x : V), projS (i + k) x = projS i (dropS k x)
  | _, 0, _ => rfl
  | i, k + 1, x => by
    show projS (i + k) (ssnd x) = projS i (dropS k (ssnd x))
    exact projS_add_dropS i k (ssnd x)

theorem dropS_pt : ∀ k : Nat, dropS k (pt : V) = pt
  | 0 => rfl
  | k + 1 => by show dropS k (ssnd pt) = pt; rw [ssnd_pt, dropS_pt k]

/-- The `i`-th field set of a telescope at a prefix valuation
(`empty` out of range — never consumed in range). -/
noncomputable def teleNth : {n : Nat} → TeleS V n → Nat → List V → V
  | _, .nil, _, _ => empty
  | _, .cons A _, 0, _ => A
  | _, .cons _ B, i + 1, a :: as => teleNth (B a) i as
  | _, .cons _ _, _ + 1, [] => empty

/-- `PropS T`: every field set is a truth value, hereditarily — the
levelwise `structSort = 0 → fieldSort = 0` bound, telescope-side. -/
def PropS : {n : Nat} → TeleS V n → Prop
  | _, .nil => True
  | _, .cons A B => A ∈ˢ (univZero : V) ∧ ∀ a, a ∈ˢ A → PropS (B a)

/-- `BoundS w T`: every field set lives in `univ w`, hereditarily —
the formation premise (per-field sorts `≤ w` via cumulativity). -/
def BoundS (w : Nat) : {n : Nat} → TeleS V n → Prop
  | _, .nil => True
  | _, .cons A B => A ∈ˢ (univ w : V) ∧ ∀ a, a ∈ˢ A → BoundS w (B a)

/-! ## Auxiliary lemmas -/

theorem FitsS.length_eq : ∀ {n} {T : TeleS V n} {as : List V},
    FitsS T as → as.length = n
  | _, .nil, [], _ => rfl
  | _, .cons _ _, _ :: _, h =>
    congrArg Nat.succ (FitsS.length_eq h.2)

theorem projList_length : ∀ (n : Nat) (x : V), (projList n x).length = n
  | 0, _ => rfl
  | n + 1, x => congrArg Nat.succ (projList_length n (ssnd x))

theorem projList_get : ∀ (n i : Nat) (x : V) (h : i < n),
    (projList n x)[i]'((projList_length n x).symm ▸ h) = projS i x
  | _ + 1, 0, _, _ => rfl
  | n + 1, i + 1, x, h =>
    projList_get n i (ssnd x) (Nat.lt_of_succ_lt_succ h)

theorem projList_take : ∀ (n i : Nat) (x : V), i ≤ n →
    (projList n x).take i = projList i x
  | _, 0, _, _ => rfl
  | n + 1, i + 1, x, h => by
    show sfst x :: (projList n (ssnd x)).take i = sfst x :: projList i (ssnd x)
    rw [projList_take n i (ssnd x) (Nat.le_of_succ_le_succ h)]

theorem projList_mkTower : ∀ (n : Nat) (as : List V), as.length = n →
    projList n (mkTower as) = as
  | 0, [], _ => rfl
  | n + 1, a :: as, h => by
    show sfst (spair a (mkTower as)) :: projList n (ssnd (spair a (mkTower as)))
      = a :: as
    rw [sfst_spair, ssnd_spair, projList_mkTower n as (Nat.succ.inj h)]

theorem projList_mkTower_append : ∀ (as bs : List V), projList as.length (mkTower (as ++ bs)) = as
  | [], _ => rfl
  | a :: as, bs => by
    show sfst (spair a (mkTower (as ++ bs))) :: projList as.length (ssnd (spair a (mkTower (as ++ bs))))
      = a :: as
    rw [sfst_spair, ssnd_spair, projList_mkTower_append as bs]

theorem projList_pt : ∀ n : Nat, projList n (pt : V) = List.replicate n pt
  | 0 => rfl
  | n + 1 => by
    show sfst (pt : V) :: projList n (ssnd (pt : V)) = pt :: List.replicate n pt
    rw [sfst_pt, ssnd_pt, projList_pt n]

/-- `projS` fixes `pt`: the interface's pt-vs-pair separation
(`sfst_pt`/`ssnd_pt`, from `pt_ne_kpair`) makes projection-of-`pt`
return `pt` — the correct proof-field answer, with no separate
`Prop`-structure variant. -/
theorem projS_pt : ∀ i : Nat, projS i (pt : V) = pt
  | 0 => sfst_pt
  | i + 1 => by rw [projS, ssnd_pt, projS_pt i]

/-- `FitsS` reads off `teleNth` membership: each fitting value is in
its field's set at the earlier values. -/
theorem fitsS_mem_teleNth : ∀ {n} {T : TeleS V n} {as : List V},
    (hf : FitsS T as) → ∀ (i : Nat) (h : i < n),
    as[i]'(FitsS.length_eq hf ▸ h) ∈ˢ teleNth T i (as.take i)
  | _, .cons _ _, _ :: _, hf, 0, _ => hf.1
  | _, .cons _ B, a :: as, hf, i + 1, h =>
    fitsS_mem_teleNth (T := B a) (as := as) hf.2 i (Nat.lt_of_succ_lt_succ h)

/-- `PropS` forces every fitting value to `pt`, so the all-`pt` list
fits whenever anything does. -/
theorem fitsS_replicate_of_prop : ∀ {n} {T : TeleS V n} {as : List V},
    PropS T → FitsS T as → FitsS T (List.replicate n pt)
  | _, .nil, [], _, _ => trivial
  | _, .cons _ B, a :: as, hP, hf => by
    have ha : a = pt := eq_pt_of_mem_univZero hP.1 hf.1
    show (pt : V) ∈ˢ _ ∧ FitsS (B pt) (List.replicate _ pt)
    exact ⟨ha ▸ hf.1, ha ▸ fitsS_replicate_of_prop (hP.2 a hf.1) hf.2⟩

/-! ## The law families (frozen in the DESIGN amendment) -/

/-- **Intro** (graph regime): a fitting tuple's tower is in the
carrier. -/
theorem mkTower_mem {w : Nat} (hw : w ≠ 0) :
    ∀ {n} {T : TeleS V n} {as : List V},
    FitsS T as → mkTower as ∈ˢ towerSet w T
  | _, .nil, [], _ => pt_mem_unitSet
  | _, .cons _ B, a :: _, hf =>
    spair_mem hw hf.1 (mkTower_mem hw (T := B a) hf.2)

/-- **Intro** (squash regime): the carrier at `w = 0` is the truth
value of fittability. -/
theorem pt_mem_tower : ∀ {n} {T : TeleS V n} {as : List V},
    FitsS T as → (pt : V) ∈ˢ towerSet 0 T
  | _, .nil, [], _ => pt_mem_unitSet
  | _, .cons _ B, a :: _, hf =>
    pt_mem_sigma hf.1 (pt_mem_tower (T := B a) hf.2)

/-- **Iota — UNCONDITIONAL**: no membership premise, no level.  The
checker's `.proj`/`mk` reduction is denotation-sound with no typing of
the fields at all. -/
theorem projS_mkTower : ∀ (i : Nat) (as : List V) (h : i < as.length),
    projS i (mkTower as) = as[i]
  | 0, a :: as, _ => by
    show sfst (spair a (mkTower as)) = a
    exact sfst_spair a (mkTower as)
  | i + 1, a :: as, h => by
    show projS i (ssnd (spair a (mkTower as))) = as[i]'(Nat.lt_of_succ_lt_succ h)
    rw [ssnd_spair]
    exact projS_mkTower i as (Nat.lt_of_succ_lt_succ h)

/-- The projection list of a point-terminated tower is the fields'
prefix (task #210: the fixpoint route's constructor payload). -/
theorem projList_mkTower_take {fs : List V} {i : Nat} (hi : i ≤ fs.length) :
    projList i (mkTower (fs ++ [pt])) = fs.take i := by
  have h1 : projList (fs.length + 1) (mkTower (fs ++ [pt])) = fs ++ [pt] := projList_mkTower _ _ (by simp)
  have h2 := projList_take (fs.length + 1) i (mkTower (fs ++ [pt])) (by omega)
  rw [h1, List.take_append_of_le_length hi] at h2
  exact h2.symm

/-- A field projection of a point-terminated tower, `getD`-form. -/
theorem projS_mkTower_getD {fs : List V} {i : Nat} (hi : i < fs.length) :
    projS i (mkTower (fs ++ [pt])) = fs.getD i pt := by
  rw [projS_mkTower i (fs ++ [pt]) (by simp; omega), List.getElem_append_left hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **Eta + elim** (graph regime): every carrier member IS the tower
of its own projections, and those projections fit the telescope. -/
theorem towerSet_elim {w : Nat} (hw : w ≠ 0) :
    ∀ {n} (T : TeleS V n) {x : V}, x ∈ˢ towerSet w T →
    FitsS T (projList n x) ∧ x = mkTower (projList n x)
  | _, .nil, x, hx => ⟨trivial, mem_unitSet_iff.mp hx⟩
  | _, .cons A B, x, hx => by
    obtain ⟨a, b, ha, hb, -, hpos⟩ :=
      mem_sigma_elim (A := A) (B := fun a => towerSet w (B a)) hx
    have hx' : x = spair a b := hpos hw
    subst hx'
    obtain ⟨hfit, heta⟩ := towerSet_elim hw (B a) hb
    constructor
    · show sfst (spair a b) ∈ˢ A ∧ FitsS (B (sfst (spair a b)))
        (projList _ (ssnd (spair a b)))
      rw [sfst_spair, ssnd_spair]
      exact ⟨ha, hfit⟩
    · show spair a b
        = spair (sfst (spair a b)) (mkTower (projList _ (ssnd (spair a b))))
      rw [sfst_spair, ssnd_spair, ← heta]

/-- **Elim** (squash regime): a `w = 0` carrier member is `pt`, and
some tuple fits. -/
theorem towerSet_zero_elim : ∀ {n} (T : TeleS V n) {x : V},
    x ∈ˢ towerSet 0 T → x = pt ∧ ∃ as, FitsS T as
  | _, .nil, x, hx => ⟨mem_unitSet_iff.mp hx, [], trivial⟩
  | _, .cons A B, x, hx => by
    obtain ⟨a, b, ha, hb, hz, -⟩ :=
      mem_sigma_elim (A := A) (B := fun a => towerSet 0 (B a)) hx
    obtain ⟨-, as, hfit⟩ := towerSet_zero_elim (B a) hb
    exact ⟨hz rfl, a :: as, ha, hfit⟩

/-- **Membership** (graph regime): the `i`-th projection lands in the
`i`-th field set at the earlier projections. -/
theorem projS_mem {w : Nat} (hw : w ≠ 0) {n} {T : TeleS V n} {x : V}
    (hx : x ∈ˢ towerSet w T) (i : Nat) (h : i < n) :
    projS i x ∈ˢ teleNth T i (projList i x) := by
  obtain ⟨hfit, -⟩ := towerSet_elim hw T hx
  have hm := fitsS_mem_teleNth hfit i h
  rw [projList_take n i x (Nat.le_of_lt h)] at hm
  rw [← projList_get n i x h]
  exact hm

/-- **Membership** (squash regime): the SAME statement, with the
proof-field premise `PropS` in place of `w ≠ 0` — every member is
`pt`, `projS` fixes it, and every truth-value field set at the
all-`pt` prefix contains it (proof irrelevance, semantically). -/
theorem projS_mem_zero {n} {T : TeleS V n} {x : V} (hP : PropS T)
    (hx : x ∈ˢ towerSet 0 T) (i : Nat) (h : i < n) :
    projS i x ∈ˢ teleNth T i (projList i x) := by
  obtain ⟨rfl, as, hfit⟩ := towerSet_zero_elim T hx
  have hrep := fitsS_replicate_of_prop hP hfit
  have hm := fitsS_mem_teleNth hrep i h
  rw [List.take_replicate, Nat.min_eq_left (Nat.le_of_lt h),
    List.getElem_replicate] at hm
  rw [projS_pt, projList_pt]
  exact hm

/-- **Coherence by uniform tupling**: `ProjCoh` holds by
representation — equal towers of equal arity have equal components.
Proved through the iota law alone (`kpair_inj` iterated). -/
theorem mkTower_inj {as bs : List V} (hlen : as.length = bs.length)
    (h : mkTower as = mkTower bs) : as = bs := by
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← projS_mkTower i as h1, ← projS_mkTower i bs h2, h]

/-- **The recursor, DERIVED** (graph regime): large-elimination typing
and iota for `r := m ∘ projList n`, with eta (`towerSet_elim`) as the
load-bearing step of the typing — the probe's `builtModel_recElimU2`,
promoted to every arity and dependency shape. -/
theorem towerRec {w : Nat} (hw : w ≠ 0) {n} (T : TeleS V n)
    (M : V → V) (m : List V → V)
    (hm : ∀ as, FitsS T as → m as ∈ˢ M (mkTower as)) :
    ∃ r : V → V, (∀ x, x ∈ˢ towerSet w T → r x ∈ˢ M x) ∧
      (∀ as, FitsS T as → r (mkTower as) = m as) := by
  refine ⟨fun x => m (projList n x), fun x hx => ?_, fun as hf => ?_⟩
  · obtain ⟨hfit, heta⟩ := towerSet_elim hw T hx
    have := hm _ hfit
    rwa [← heta] at this
  · show m (projList n (mkTower as)) = m as
    rw [projList_mkTower n as hf.length_eq]

/-- **The recursor at squash**: constant elimination is lawful — the
semantic form of subsingleton elimination (the minor's value must be
instantiation-independent, which all-proof-field instantiations
satisfy with `m = pt`). -/
theorem towerRec_zero {n} (T : TeleS V n) (M : V → V) (m : V)
    (hm : (∃ as, FitsS T as) → m ∈ˢ M pt) :
    ∀ x, x ∈ˢ towerSet 0 T → m ∈ˢ M x := by
  intro x hx
  obtain ⟨rfl, hex⟩ := towerSet_zero_elim T hx
  exact hm hex

/-- **Formation**: the carrier lives at the structure's own level,
given the per-field bound (cumulativity is applied by the consumer
when a field's sort is `< w`). -/
theorem towerSet_mem_univ {w : Nat} : ∀ {n} (T : TeleS V n),
    BoundS w T → towerSet w T ∈ˢ (univ w : V)
  | _, .nil, _ => unitSet_mem_univ w
  | _, .cons A B, hb => by
    simp only [towerSet]
    have h := sigma_mem_univ (u := w) (v := w) hb.1
      (fun a ha => towerSet_mem_univ (B a) (hb.2 a ha))
    rwa [show Nat.max w w = w from Nat.max_self w] at h

/-- **Formation, squash regime — UNCONDITIONAL**: at `w = 0` the
carrier is a truth value with no field bounds at all (`sigmaSet 0`
truncates whatever its arguments are), so definitely-`Prop`
structures with arbitrary-sorted data fields (`Exists`) still get a
lawful carrier; only their *projections* wait on `PropS`. -/
theorem towerSet_zero_mem_univZero : ∀ {n} (T : TeleS V n),
    towerSet 0 T ∈ˢ (univZero : V)
  | _, .nil => univ_zero (V := V) ▸ unitSet_mem_univ 0
  | _, .cons _ B => by
    show sigmaSet 0 _ (fun a => towerSet 0 (B a)) ∈ˢ (univZero : V)
    rw [sigmaSet_zero]
    exact truthVal_mem_univZero _

/-- **Storage hygiene**: a tower carrier is never the proof point
(the task-#100 collapse-era non-`pt`-ness of stored values). -/
theorem towerSet_ne_pt {w : Nat} : ∀ {n} (T : TeleS V n),
    towerSet w T ≠ (pt : V)
  | _, .nil => fun h =>
    truthVal_ne_pt True ((truthVal_eq_unitSet trivial).trans h)
  | _, .cons _ _ => sigmaSet_ne_pt

/-- **The 0-field degeneracy**: the empty tower is `unitSet` at every
level — hence unit-likeness (next lemma) and, at `w = 0`, the correct
truth value `⟦True⟧`. -/
theorem towerSet_nil {w : Nat} : towerSet w (.nil : TeleS V 0) = unitSet := by
  rfl

/-- Unit-likeness at `n = 0`: any two members are equal. -/
theorem tower_nil_unitlike {w : Nat} {x y : V}
    (hx : x ∈ˢ towerSet w (.nil : TeleS V 0))
    (hy : y ∈ˢ towerSet w (.nil : TeleS V 0)) : x = y :=
  (mem_unitSet_iff.mp hx).trans (mem_unitSet_iff.mp hy).symm

/-! ## Degeneracy checks (build-time regressions) -/

/-- `n = 1`: the terminator makes `projS 0 = sfst` lawful — the sole
field of a one-field tower reads back. -/
example (a : V) : projS 0 (mkTower [a]) = a :=
  projS_mkTower 0 [a] (by simp)

/-- `n = 2`: both indices read back through the one uniform family. -/
example (a b : V) : projS 0 (mkTower [a, b]) = a ∧ projS 1 (mkTower [a, b]) = b :=
  ⟨projS_mkTower 0 [a, b] (by simp), projS_mkTower 1 [a, b] (by simp)⟩

/-- `n = 0`: the empty tower's sole member is `mkTower []`. -/
example {w : Nat} {x : V} (hx : x ∈ˢ towerSet w (.nil : TeleS V 0)) :
    x = mkTower [] :=
  mem_unitSet_iff.mp hx

end ConLeche.SetTheory.Tower
