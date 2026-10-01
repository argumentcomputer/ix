module

public import ConLeche.SetModel.RecGraph
public import ConLeche.SetModel.Iter
public import ConLeche.SetTheory.Derive.Choice

@[expose] public section

/-!
# The closure witness of a member container (task #202, Stage B)

A recursive family with function-space slots (`WType`, `PSet`, …) is the
least fixed point of a functor whose fibres contain *functions* from
member domains into the family's own fibres.  Its least pre-fixed point
(`lfpFamSet`) needs a CLOSED MEMBER family to be intersected from; for
finitary blocks that is the ω-iterate, for `Prop`-valued ones the top
family — with a function-space slot at `Sort w`, `w ≠ 0`, neither works
(the family's ranks are unbounded below the universe).

This module exhibits the witness abstractly, for a functor `Φ` on
families over an index set `I` PRESENTED AS A CONTAINER: every element
of `Φ X` at `i` is `mk a g` for a shape `a ∈ A i` and a function `g`
from the shape's positions `B a` into the fibres of `X` at the targets
`tgt a p` (`helim`); shapes and position sets are members of `univ w`.
The witness is the family of DECODED TREE CODES: a code is a set of
labelled paths (a subset of a member `codeSpace t` built from the shapes
and positions reachable from `t`), decoding is the recursion theorem
(`RecGraph`) along the immediate-subcode relation on the accessible
codes, and the decoded family is closed because a constructor step on
decoded subcodes is the decoding of the assembled code (`mkCode`).
Membership comes from replacement (`image_mem`) alone — the fibres are
images of members — so no injection and no size argument beyond the
universe's own closure is needed.  Everything here is over the bare
`SetTheory` interface; no syntax.

The index set `I` need not be a member of any universe (an index type
may live above the family's sort): the reachable shapes are collected
by depth (`shapesN`) through the shapes and positions only, which ARE
members; no index is ever put inside a set.
-/

namespace ConLeche.SetTheory

open ConLeche.SetTheory.Tower (natUnion mem_natUnion natUnion_mem_univ_pos)

universe u

variable {V : Type u} [SetTheory V]

/-! ## Pair projections on `kpair` -/


/-! ## The spaces reachable from an index -/

section Spaces

variable (A B : V → V) (tgt : V → V → V)

/-- The shapes reachable from `t` in exactly `n` steps. -/
noncomputable def shapesN (t : V) : Nat → V
  | 0 => A t
  | n + 1 => sUnion (image (fun a => sUnion (image (fun p => A (tgt a p)) (B a))) (shapesN t n))

/-- The shapes reachable from `t`. -/
noncomputable def shapes (t : V) : V := natUnion (shapesN A B tgt t)

/-- The positions of the reachable shapes. -/
noncomputable def positions (t : V) : V := sUnion (image B (shapes A B tgt t))

/-- Paths of length `n`: nested pairs of positions, the first step
outermost, `pt` the empty path. -/
noncomputable def pathsN (t : V) : Nat → V
  | 0 => unitSet
  | n + 1 => sigmaPairs (positions A B tgt t) (fun _ => pathsN t n)

/-- The paths from `t`. -/
noncomputable def paths (t : V) : V := natUnion (pathsN A B tgt t)

/-- The code space at `t`: the sets of labelled paths. -/
noncomputable def codeSpace (t : V) : V :=
  power (sigmaPairs (paths A B tgt t) (fun _ => shapes A B tgt t))

variable {A B tgt}

theorem mem_shapesN_succ {t x : V} {n : Nat} :
    x ∈ˢ shapesN A B tgt t (n + 1) ↔
      ∃ a, a ∈ˢ shapesN A B tgt t n ∧ ∃ p, p ∈ˢ B a ∧ x ∈ˢ A (tgt a p) := by
  show x ∈ˢ sUnion (image _ _) ↔ _
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    obtain ⟨z, hz, hxz⟩ := mem_sUnion.mp hxy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
    exact ⟨a, ha, p, hp, hxz⟩
  · rintro ⟨a, ha, p, hp, hx⟩
    exact ⟨_, mem_image.mpr ⟨a, ha, rfl⟩, mem_sUnion.mpr ⟨_, mem_image.mpr ⟨p, hp, rfl⟩, hx⟩⟩

theorem mem_shapes {t x : V} : x ∈ˢ shapes A B tgt t ↔ ∃ n, x ∈ˢ shapesN A B tgt t n :=
  mem_natUnion

theorem mem_positions {t p : V} :
    p ∈ˢ positions A B tgt t ↔ ∃ a, a ∈ˢ shapes A B tgt t ∧ p ∈ˢ B a := by
  show p ∈ˢ sUnion (image B _) ↔ _
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hpy⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ⟨a, ha, hpy⟩
  · rintro ⟨a, ha, hp⟩
    exact ⟨B a, mem_image.mpr ⟨a, ha, rfl⟩, hp⟩

theorem mem_paths {t x : V} : x ∈ˢ paths A B tgt t ↔ ∃ n, x ∈ˢ pathsN A B tgt t n :=
  mem_natUnion

theorem pt_mem_paths (t : V) : (pt : V) ∈ˢ paths A B tgt t :=
  mem_paths.mpr ⟨0, pt_mem_unitSet⟩

theorem mem_pathsN_succ {t x : V} {n : Nat} :
    x ∈ˢ pathsN A B tgt t (n + 1) ↔
      ∃ p, p ∈ˢ positions A B tgt t ∧ ∃ q, q ∈ˢ pathsN A B tgt t n ∧ x = kpair p q :=
  mem_sigmaPairs

/-- Paths are closed under consing a position. -/
theorem kpair_mem_paths {t p q : V} (hp : p ∈ˢ positions A B tgt t) (hq : q ∈ˢ paths A B tgt t) :
    kpair p q ∈ˢ paths A B tgt t := by
  obtain ⟨n, hn⟩ := mem_paths.mp hq
  exact mem_paths.mpr ⟨n + 1, mem_pathsN_succ.mpr ⟨p, hp, q, hn, rfl⟩⟩

/-- A path's tail is a path (and its head a position). -/
theorem paths_uncons {t p q : V} (h : kpair p q ∈ˢ paths A B tgt t) :
    p ∈ˢ positions A B tgt t ∧ q ∈ˢ paths A B tgt t := by
  obtain ⟨n, hn⟩ := mem_paths.mp h
  cases n with
  | zero =>
    exact absurd (mem_unitSet_iff.mp hn).symm (pt_ne_kpair p q)
  | succ n =>
    obtain ⟨p', hp', q', hq', heq⟩ := mem_pathsN_succ.mp hn
    obtain ⟨rfl, rfl⟩ := kpair_inj heq
    exact ⟨hp', mem_paths.mpr ⟨n, hq'⟩⟩

theorem mem_codeSpace {t S : V} :
    S ∈ˢ codeSpace A B tgt t ↔
      ∀ x, x ∈ˢ S → ∃ q, q ∈ˢ paths A B tgt t ∧ ∃ a, a ∈ˢ shapes A B tgt t ∧ x = kpair q a := by
  show S ∈ˢ power _ ↔ _
  rw [mem_power]
  constructor
  · intro h x hx
    exact mem_sigmaPairs.mp (h x hx)
  · intro h x hx
    obtain ⟨q, hq, a, ha, rfl⟩ := h x hx
    exact mem_sigmaPairs.mpr ⟨q, hq, a, ha, rfl⟩

/-! ### Membership in the universe -/

section Univ

variable {w : Nat} (hw : w ≠ 0) {I : V}
  (hA : ∀ i, i ∈ˢ I → A i ∈ˢ (univ w : V))
  (hB : ∀ i a, i ∈ˢ I → a ∈ˢ A i → B a ∈ˢ (univ w : V))
  (htgt : ∀ i a p, i ∈ˢ I → a ∈ˢ A i → p ∈ˢ B a → tgt a p ∈ˢ I)
include hw hA hB htgt

omit hw hA hB in
/-- Every reachable shape is a shape at some index. -/
theorem shapesN_sub {t : V} (ht : t ∈ˢ I) :
    ∀ n a, a ∈ˢ shapesN A B tgt t n → ∃ i, i ∈ˢ I ∧ a ∈ˢ A i
  | 0, a, ha => ⟨t, ht, ha⟩
  | n + 1, a, ha => by
    obtain ⟨a', ha', p, hp, hx⟩ := mem_shapesN_succ.mp ha
    obtain ⟨i, hi, hai⟩ := shapesN_sub ht n a' ha'
    exact ⟨tgt a' p, htgt i a' p hi hai hp, hx⟩

theorem shapesN_mem {t : V} (ht : t ∈ˢ I) : ∀ n, shapesN A B tgt t n ∈ˢ (univ w : V)
  | 0 => hA t ht
  | n + 1 => by
    have hU := univ_isTGUniverse (V := V) hw
    show sUnion (image _ _) ∈ˢ _
    refine hU.famUnion_mem (shapesN_mem ht n) fun a ha => ?_
    obtain ⟨i, hi, hai⟩ := shapesN_sub htgt ht n a ha
    refine hU.famUnion_mem (hB i a hi hai) fun p hp => ?_
    exact hA _ (htgt i a p hi hai hp)

theorem shapes_mem {t : V} (ht : t ∈ˢ I) : shapes A B tgt t ∈ˢ (univ w : V) :=
  natUnion_mem_univ_pos hw (shapesN_mem hw hA hB htgt ht)

omit hw hA hB in
theorem shapes_sub {t a : V} (ht : t ∈ˢ I) (ha : a ∈ˢ shapes A B tgt t) :
    ∃ i, i ∈ˢ I ∧ a ∈ˢ A i := by
  obtain ⟨n, hn⟩ := mem_shapes.mp ha
  exact shapesN_sub htgt ht n a hn

theorem positions_mem {t : V} (ht : t ∈ˢ I) : positions A B tgt t ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine hU.famUnion_mem (shapes_mem hw hA hB htgt ht) fun a ha => ?_
  obtain ⟨i, hi, hai⟩ := shapes_sub htgt ht ha
  exact hB i a hi hai

theorem pathsN_mem {t : V} (ht : t ∈ˢ I) : ∀ n, pathsN A B tgt t n ∈ˢ (univ w : V)
  | 0 => unitSet_mem_univ w
  | n + 1 => (univ_isTGUniverse hw).sigmaPairs_mem (positions_mem hw hA hB htgt ht)
      fun _ _ => pathsN_mem ht n

theorem paths_mem {t : V} (ht : t ∈ˢ I) : paths A B tgt t ∈ˢ (univ w : V) :=
  natUnion_mem_univ_pos hw (pathsN_mem hw hA hB htgt ht)

theorem codeSpace_mem {t : V} (ht : t ∈ˢ I) : codeSpace A B tgt t ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  exact hU.power_mem (hU.sigmaPairs_mem (paths_mem hw hA hB htgt ht)
    fun _ _ => shapes_mem hw hA hB htgt ht)

end Univ

/-! ### The spaces grow along a step -/

section Step

variable {t a p : V} (ha : a ∈ˢ A t) (hp : p ∈ˢ B a)
include ha hp

theorem shapesN_step_sub : ∀ n, shapesN A B tgt (tgt a p) n ⊆ˢ shapesN A B tgt t (n + 1)
  | 0 => fun x hx => mem_shapesN_succ.mpr ⟨a, ha, p, hp, hx⟩
  | n + 1 => fun x hx => by
    obtain ⟨a', ha', p', hp', hx'⟩ := mem_shapesN_succ.mp hx
    exact mem_shapesN_succ.mpr ⟨a', shapesN_step_sub n a' ha', p', hp', hx'⟩

theorem shapes_step_sub : shapes A B tgt (tgt a p) ⊆ˢ shapes A B tgt t := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_shapes.mp hx
  exact mem_shapes.mpr ⟨n + 1, shapesN_step_sub ha hp n x hn⟩

theorem positions_step_sub : positions A B tgt (tgt a p) ⊆ˢ positions A B tgt t := by
  intro x hx
  obtain ⟨a', ha', hx'⟩ := mem_positions.mp hx
  exact mem_positions.mpr ⟨a', shapes_step_sub ha hp a' ha', hx'⟩

theorem pathsN_step_sub : ∀ n, pathsN A B tgt (tgt a p) n ⊆ˢ pathsN A B tgt t n
  | 0 => Subset.refl _
  | n + 1 => fun x hx => by
    obtain ⟨p', hp', q, hq, rfl⟩ := mem_pathsN_succ.mp hx
    exact mem_pathsN_succ.mpr ⟨p', positions_step_sub ha hp p' hp', q, pathsN_step_sub n q hq, rfl⟩

theorem paths_step_sub : paths A B tgt (tgt a p) ⊆ˢ paths A B tgt t := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_paths.mp hx
  exact mem_paths.mpr ⟨n, pathsN_step_sub ha hp n x hn⟩

/-- A position of a root shape is a position of the root's space. -/
theorem mem_positions_of_root : p ∈ˢ positions A B tgt t :=
  mem_positions.mpr ⟨a, mem_shapes.mpr ⟨0, ha⟩, hp⟩

end Step

end Spaces

/-! ## Codes: the root label, the subcodes, the assembly -/

section Codes

variable (B : V → V)

/-- The labels at the empty path. -/
noncomputable def rootLabels (S : V) : V := image ssnd (sep S fun pr => sfst pr = pt)

/-- A code has a root: some label sits at the empty path. -/
def HasRoot (S : V) : Prop := ∃ a, kpair pt a ∈ˢ S

/-- The root label (a choice among the labels at the empty path). -/
noncomputable def lab (S : V) : V := schoice (rootLabels S)

/-- The subcode at position `p`: the labelled paths under `p`, the
first step stripped. -/
noncomputable def subCode (S p : V) : V :=
  image (fun pr => kpair (ssnd (sfst pr)) (ssnd pr)) (sep S fun pr => ∃ q, sfst pr = kpair p q)

/-- The code of a tree with root shape `a` and subcodes `app g p` at
the positions `p ∈ B a`: the root pair and every subcode's pairs with
the position prepended. -/
noncomputable def mkCode (a g : V) : V :=
  binUnion (sing (kpair pt a))
    (sUnion (image (fun p => image (fun pr => kpair (kpair p (sfst pr)) (ssnd pr)) (app g p)) (B a)))

variable {B}

theorem mem_mkCode {a g x : V} :
    x ∈ˢ mkCode B a g ↔
      x = kpair pt a ∨ ∃ p, p ∈ˢ B a ∧ ∃ pr, pr ∈ˢ app g p ∧ x = kpair (kpair p (sfst pr)) (ssnd pr) := by
  unfold mkCode
  rw [mem_binUnion, mem_sing, mem_sUnion]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    obtain ⟨pr, hpr, rfl⟩ := mem_image.mp hxy
    exact ⟨p, hp, pr, hpr, rfl⟩
  · rintro ⟨p, hp, pr, hpr, rfl⟩
    exact ⟨_, mem_image.mpr ⟨p, hp, rfl⟩, mem_image.mpr ⟨pr, hpr, rfl⟩⟩

theorem mem_rootLabels {S x : V} :
    x ∈ˢ rootLabels S ↔ ∃ pr, pr ∈ˢ S ∧ sfst pr = pt ∧ ssnd pr = x := by
  unfold rootLabels
  rw [mem_image]
  constructor
  · rintro ⟨pr, hpr, rfl⟩
    exact ⟨pr, (mem_sep.mp hpr).1, (mem_sep.mp hpr).2, rfl⟩
  · rintro ⟨pr, hpr, h1, rfl⟩
    exact ⟨pr, mem_sep.mpr ⟨hpr, h1⟩, rfl⟩

theorem hasRoot_mkCode (a g : V) : HasRoot (mkCode B a g) :=
  ⟨a, mem_mkCode.mpr (Or.inl rfl)⟩

theorem rootLabels_mkCode (a g : V) : rootLabels (mkCode B a g) = sing a := by
  apply ext
  intro x
  rw [mem_rootLabels, mem_sing]
  constructor
  · rintro ⟨pr, hpr, h1, rfl⟩
    rcases mem_mkCode.mp hpr with rfl | ⟨p, -, pr', -, rfl⟩
    · exact ssnd_kpair _ _
    · rw [sfst_kpair] at h1
      exact absurd h1.symm (pt_ne_kpair _ _)
  · rintro rfl
    exact ⟨kpair pt x, mem_mkCode.mpr (Or.inl rfl), sfst_kpair _ _, ssnd_kpair _ _⟩

theorem lab_mkCode (a g : V) : lab (mkCode B a g) = a := by
  unfold lab
  rw [rootLabels_mkCode]
  exact mem_sing.mp (schoice_mem (mem_sing.mpr rfl))

/-- The subcode of an assembled code at a position is the subcode put
there (the codes' elements being labelled paths). -/
theorem subCode_mkCode {a g p : V} (hp : p ∈ˢ B a)
    (hpairs : ∀ x, x ∈ˢ app g p → ∃ q b, x = kpair q b) :
    subCode (mkCode B a g) p = app g p := by
  apply ext
  intro x
  unfold subCode
  rw [mem_image]
  constructor
  · rintro ⟨pr, hpr, rfl⟩
    obtain ⟨hmem, q, hq⟩ := mem_sep.mp hpr
    rcases mem_mkCode.mp hmem with rfl | ⟨p', hp', pr', hpr', rfl⟩
    · rw [sfst_kpair] at hq
      exact absurd hq (pt_ne_kpair _ _)
    · rw [sfst_kpair] at hq
      obtain ⟨rfl, rfl⟩ := kpair_inj hq
      obtain ⟨q', b, rfl⟩ := hpairs pr' hpr'
      simp only [sfst_kpair, ssnd_kpair]
      exact hpr'
  · intro hx
    obtain ⟨q, b, rfl⟩ := hpairs x hx
    refine ⟨kpair (kpair p q) b, mem_sep.mpr ⟨mem_mkCode.mpr (Or.inr ⟨p, hp, kpair q b, hx, ?_⟩), q, sfst_kpair _ _⟩, ?_⟩
    · rw [sfst_kpair, ssnd_kpair]
    · rw [sfst_kpair, ssnd_kpair, ssnd_kpair]

section InSpace

variable {A : V → V} {tgt : V → V → V}

theorem codeSpace_pairs {t S : V} (hS : S ∈ˢ codeSpace A B tgt t) :
    ∀ x, x ∈ˢ S → ∃ q a, x = kpair q a := by
  intro x hx
  obtain ⟨q, -, a, -, rfl⟩ := mem_codeSpace.mp hS x hx
  exact ⟨q, a, rfl⟩

/-- Subcodes stay in the code space. -/
theorem subCode_mem_codeSpace {t S p : V} (hS : S ∈ˢ codeSpace A B tgt t) :
    subCode S p ∈ˢ codeSpace A B tgt t := by
  rw [mem_codeSpace]
  intro x hx
  unfold subCode at hx
  obtain ⟨pr, hpr, rfl⟩ := mem_image.mp hx
  obtain ⟨hmem, q, hq⟩ := mem_sep.mp hpr
  obtain ⟨q', hq', a, ha, rfl⟩ := mem_codeSpace.mp hS pr hmem
  rw [sfst_kpair] at hq
  subst hq
  rw [sfst_kpair, ssnd_kpair, ssnd_kpair]
  exact ⟨q, (paths_uncons hq').2, a, ha, rfl⟩

/-- The assembled code of a root shape at `t` and subcodes at the
targets is in the code space at `t`. -/
theorem mkCode_mem_codeSpace {t a g : V} (ha : a ∈ˢ A t)
    (hg : ∀ p, p ∈ˢ B a → app g p ∈ˢ codeSpace A B tgt (tgt a p)) :
    mkCode B a g ∈ˢ codeSpace A B tgt t := by
  rw [mem_codeSpace]
  intro x hx
  rcases mem_mkCode.mp hx with rfl | ⟨p, hp, pr, hpr, rfl⟩
  · exact ⟨pt, pt_mem_paths t, a, mem_shapes.mpr ⟨0, ha⟩, rfl⟩
  · obtain ⟨q, hq, b, hb, rfl⟩ := mem_codeSpace.mp (hg p hp) pr hpr
    rw [sfst_kpair, ssnd_kpair]
    refine ⟨kpair p q, kpair_mem_paths (mem_positions_of_root ha hp) (paths_step_sub ha hp q hq),
      b, shapes_step_sub ha hp b hb, rfl⟩

end InSpace

end Codes

/-! ## Decoding: the recursion theorem along the subcodes -/

section Decode

variable (A B : V → V) (tgt : V → V → V) (I : V) (w : Nat) (mk : V → V → V)

/-- All codes at all indices (a set; membership in a universe is not
needed for a recursion index set). -/
noncomputable def allCodes : V := sUnion (image (codeSpace A B tgt) I)

open Classical in
/-- The immediate subcodes of a code with a root. -/
noncomputable def codePred (S : V) : V :=
  if HasRoot S then image (subCode S) (B (lab S)) else empty

open Classical in
/-- The decoding step: the container's builder at the root label (a
shape at some index) and the decoded subcodes (the point off the
guard). -/
noncomputable def codeStep (S g : V) : V :=
  if HasRoot S ∧ ∃ i, i ∈ˢ I ∧ lab S ∈ˢ A i then
    mk (lab S) (graph (fun p => app g (subCode S p)) (B (lab S)))
  else pt

/-- The decoding graph: the recursion theorem's least fixed point at
level `w + 1`, bounded by `univ w`. -/
noncomputable def decodeGraph : V :=
  recGraph (w + 1) (allCodes A B tgt I) (codePred B) (fun _ => univ w) (codeStep A B I mk)

/-- The accessible codes. -/
noncomputable def accCodes : V := accFam (allCodes A B tgt I) (codePred B) (fun _ => True)

/-- The decoding: the selector of the decoding graph. -/
noncomputable def decode (S : V) : V := recSel (decodeGraph A B tgt I w mk) S

variable {A B tgt I w mk}

theorem mem_allCodes {S : V} : S ∈ˢ allCodes A B tgt I ↔ ∃ t, t ∈ˢ I ∧ S ∈ˢ codeSpace A B tgt t := by
  unfold allCodes
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hS⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hy
    exact ⟨t, ht, hS⟩
  · rintro ⟨t, ht, hS⟩
    exact ⟨_, mem_image.mpr ⟨t, ht, rfl⟩, hS⟩

theorem codePred_of_root {S : V} (h : HasRoot S) : codePred B S = image (subCode S) (B (lab S)) := by
  unfold codePred; exact if_pos h

theorem codePred_of_not {S : V} (h : ¬ HasRoot S) : codePred B S = empty := by
  unfold codePred; exact if_neg h

theorem codePred_sub {S : V} (hS : S ∈ˢ allCodes A B tgt I) : codePred B S ⊆ˢ allCodes A B tgt I := by
  intro x hx
  by_cases h : HasRoot S
  · rw [codePred_of_root h] at hx
    obtain ⟨p, -, rfl⟩ := mem_image.mp hx
    obtain ⟨t, ht, hSt⟩ := mem_allCodes.mp hS
    exact mem_allCodes.mpr ⟨t, ht, subCode_mem_codeSpace hSt⟩
  · rw [codePred_of_not h] at hx
    exact absurd hx (not_mem_empty x)

/-- **Accessibility, unfolded**: a code is accessible iff its immediate
subcodes are. -/
theorem accFam_iff {J : V} {pred : V → V} {Cond : V → Prop} (hpred : ∀ i, i ∈ˢ J → pred i ⊆ˢ J)
    {i : V} (hi : i ∈ˢ J) :
    (∃ y, y ∈ˢ app (accFam J pred Cond) i) ↔
      Cond i ∧ ∀ j, j ∈ˢ pred i → ∃ y, y ∈ˢ app (accFam J pred Cond) j := by
  have h := app_lfpFamSet_eq (F := accStep J pred Cond) ⟨_, accStep_closed (pred := pred) (Cond := Cond)⟩
    (accStep_mono hpred) accStep_maps hi
  unfold accFam
  rw [← h, app_app_accStep (lfpFamSet_mem _ _ _) hi]
  unfold accFibre
  constructor
  · rintro ⟨y, hy⟩
    exact (mem_truthVal.mp hy).1
  · intro hc
    exact ⟨pt, mem_truthVal.mpr ⟨hc, rfl⟩⟩

theorem accCodes_iff {S : V} (hS : S ∈ˢ allCodes A B tgt I) :
    (∃ y, y ∈ˢ app (accCodes A B tgt I) S) ↔
      ∀ S', S' ∈ˢ codePred B S → ∃ y, y ∈ˢ app (accCodes A B tgt I) S' := by
  unfold accCodes
  rw [accFam_iff (fun _ hS' => codePred_sub hS') hS]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

section Facts

variable {w : Nat} (hw : w ≠ 0)
  (hB : ∀ i a, i ∈ˢ I → a ∈ˢ A i → B a ∈ˢ (univ w : V))
  (hmkU : ∀ i a g, i ∈ˢ I → a ∈ˢ A i → g ∈ˢ (univ w : V) → mk a g ∈ˢ (univ w : V))
include hw hB hmkU

omit hw hB hmkU in
theorem decodeGraph_hB : ∀ S, S ∈ˢ allCodes A B tgt I → (univ w : V) ∈ˢ (univ (w + 1) : V) :=
  fun _ _ => univ_mem_univ w

/-- The step lands in the bound: the builder at members. -/
theorem codeStep_mem {S g : V} (hS : S ∈ˢ allCodes A B tgt I)
    (hg : g ∈ˢ piSet (codePred B S) fun j => app (decodeGraph A B tgt I w mk) j) :
    codeStep A B I mk S g ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold codeStep
  split
  · next h =>
    obtain ⟨hroot, i, hi, hlab⟩ := h
    have hBl : B (lab S) ∈ˢ (univ w : V) := hB i _ hi hlab
    refine hmkU i _ _ hi hlab ?_
    -- the graph of the decoded subcodes over the member position set
    unfold graph
    refine hU.image_mem hBl fun p hp => ?_
    refine hU.kpair_mem hBl (hU.transitive hBl hp) ?_
    -- the value: in the decoding graph's fibre, bounded by the universe
    have hpred : subCode S p ∈ˢ codePred B S := by
      rw [codePred_of_root hroot]
      exact mem_image.mpr ⟨p, hp, rfl⟩
    have hv := app_mem_of_mem_piSet hg hpred
    unfold decodeGraph at hv
    rw [app_recGraph_eq decodeGraph_hB (fun _ hS' => codePred_sub hS')
      (codePred_sub hS _ hpred)] at hv
    exact (mem_recGraphFibre.mp hv).1
  · exact hU.pt_mem (empty_mem_univ w)

theorem decodeGraph_hst : ∀ S, S ∈ˢ allCodes A B tgt I →
    ∀ g, g ∈ˢ piSet (codePred B S) (fun j => app (decodeGraph A B tgt I w mk) j) →
      codeStep A B I mk S g ∈ˢ (univ w : V) :=
  fun _ hS _ hg => codeStep_mem hw hB hmkU hS hg

/-- **Accessible codes decode uniquely**: the decoding graph's fibre is
a singleton. -/
theorem decode_unique {S : V} (hS : S ∈ˢ allCodes A B tgt I)
    (hacc : ∃ y, y ∈ˢ app (accCodes A B tgt I) S) :
    (∃ v, v ∈ˢ app (decodeGraph A B tgt I w mk) S) ∧
      ∀ v v', v ∈ˢ app (decodeGraph A B tgt I w mk) S → v' ∈ˢ app (decodeGraph A B tgt I w mk) S →
        v = v' :=
  recGraph_exists_unique decodeGraph_hB (fun _ hS' => codePred_sub hS')
    (decodeGraph_hst hw hB hmkU) S hS _ hacc.choose_spec

/-- The decoding of an accessible code is a member. -/
theorem decode_mem_univ {S : V} (hS : S ∈ˢ allCodes A B tgt I)
    (hacc : ∃ y, y ∈ˢ app (accCodes A B tgt I) S) :
    decode A B tgt I w mk S ∈ˢ (univ w : V) := by
  have hv := recSel_mem (decode_unique hw hB hmkU hS hacc).1
  unfold decodeGraph at hv
  rw [app_recGraph_eq decodeGraph_hB (fun _ hS' => codePred_sub hS') hS] at hv
  exact (mem_recGraphFibre.mp hv).1

/-- **The decoding equation** at an accessible code with a root: the
builder at the root label and the decoded subcodes. -/
theorem decode_eq {S : V} (hS : S ∈ˢ allCodes A B tgt I)
    (hacc : ∃ y, y ∈ˢ app (accCodes A B tgt I) S) (hroot : HasRoot S)
    (hlab : ∃ i, i ∈ˢ I ∧ lab S ∈ˢ A i) :
    decode A B tgt I w mk S
      = mk (lab S) (graph (fun p => decode A B tgt I w mk (subCode S p)) (B (lab S))) := by
  have hP : ∀ j, j ∈ˢ codePred B S →
      (∃ v, v ∈ˢ app (decodeGraph A B tgt I w mk) j) ∧
      ∀ v v', v ∈ˢ app (decodeGraph A B tgt I w mk) j → v' ∈ˢ app (decodeGraph A B tgt I w mk) j →
        v = v' :=
    fun j hj => decode_unique hw hB hmkU (codePred_sub hS j hj) ((accCodes_iff hS).mp hacc j hj)
  have heq := recSel_eq decodeGraph_hB (fun _ hS' => codePred_sub hS') hS
    (decode_unique hw hB hmkU hS hacc).1 hP
  unfold decode
  unfold decodeGraph at heq ⊢
  rw [heq]
  unfold codeStep
  rw [if_pos ⟨hroot, hlab⟩]
  congr 1
  refine graph_congr fun p hp => ?_
  rw [app_graph (show subCode S p ∈ˢ codePred B S from by
    rw [codePred_of_root hroot]; exact mem_image.mpr ⟨p, hp, rfl⟩)]

omit hw hB hmkU in
/-- An assembled code of accessible subcodes is accessible. -/
theorem acc_mkCode {t a g : V} (ht : t ∈ˢ I) (ha : a ∈ˢ A t)
    (hg : ∀ p, p ∈ˢ B a → app g p ∈ˢ codeSpace A B tgt (tgt a p))
    (hacc : ∀ p, p ∈ˢ B a → ∃ y, y ∈ˢ app (accCodes A B tgt I) (app g p)) :
    ∃ y, y ∈ˢ app (accCodes A B tgt I) (mkCode B a g) := by
  have hS : mkCode B a g ∈ˢ allCodes A B tgt I :=
    mem_allCodes.mpr ⟨t, ht, mkCode_mem_codeSpace ha hg⟩
  rw [accCodes_iff hS]
  intro S' hS'
  rw [codePred_of_root (hasRoot_mkCode a g), lab_mkCode] at hS'
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hS'
  rw [subCode_mkCode hp (codeSpace_pairs (hg p hp))]
  exact hacc p hp

end Facts

end Decode

/-! ## The closure witness -/

/-- **A member container has a closed member family**: the family of
the decoded accessible codes.  The functor `Φ` on families over `I` is
presented as a container by `helim` — every element of `Φ X` at `i` is
`mk a g` for a shape `a ∈ A i` and a function `g` from the positions
`B a` into the fibres of `X` at the targets `tgt a p`; shapes and
position sets are members of `univ w`, the builder keeps members.  The
decoded family's fibres are images of members (replacement), and a
constructor step on decoded subcodes decodes the assembled code. -/
theorem container_closed_exists {w : Nat} (hw : w ≠ 0) {I : V} (Φ : V → V)
    (A B : V → V) (tgt : V → V → V) (mk : V → V → V)
    (hA : ∀ i, i ∈ˢ I → A i ∈ˢ (univ w : V))
    (hB : ∀ i a, i ∈ˢ I → a ∈ˢ A i → B a ∈ˢ (univ w : V))
    (htgt : ∀ i a p, i ∈ˢ I → a ∈ˢ A i → p ∈ˢ B a → tgt a p ∈ˢ I)
    (hmkU : ∀ i a g, i ∈ˢ I → a ∈ˢ A i → g ∈ˢ (univ w : V) → mk a g ∈ˢ (univ w : V))
    (helim : ∀ X, X ∈ˢ famSpace w I → ∀ i, i ∈ˢ I → ∀ x, x ∈ˢ app (Φ X) i →
      ∃ a, a ∈ˢ A i ∧ ∃ g, g ∈ˢ piSet (B a) (fun p => app X (tgt a p)) ∧ x = mk a g) :
    ∃ L, L ∈ˢ famSpace w I ∧ FamLe I (Φ L) L := by
  have hU := univ_isTGUniverse (V := V) hw
  let Lf : V → V := fun i => image (decode A B tgt I w mk)
    (sep (codeSpace A B tgt i) fun S =>
      (∃ y, y ∈ˢ app (accCodes A B tgt I) S) ∧ HasRoot S ∧ lab S ∈ˢ A i)
  have hLmem : graph Lf I ∈ˢ famSpace w I := by
    refine graph_mem_famSpace fun i hi => ?_
    refine hU.image_mem (hU.sep_mem (codeSpace_mem hw hA hB htgt hi)) fun S hS => ?_
    obtain ⟨hSi, hacc, -, -⟩ := mem_sep.mp hS
    exact decode_mem_univ hw hB hmkU (mem_allCodes.mpr ⟨i, hi, hSi⟩) hacc
  refine ⟨graph Lf I, hLmem, ?_⟩
  intro i hi x hx
  obtain ⟨a, ha, g, hg, rfl⟩ := helim _ hLmem i hi x hx
  -- every subtree is the decoding of an accessible code at its target
  have hsub : ∀ p, p ∈ˢ B a → ∃ S, S ∈ˢ codeSpace A B tgt (tgt a p) ∧
      (∃ y, y ∈ˢ app (accCodes A B tgt I) S) ∧ HasRoot S ∧ lab S ∈ˢ A (tgt a p) ∧
      decode A B tgt I w mk S = app g p := by
    intro p hp
    have hgp := app_mem_of_mem_piSet hg hp
    rw [app_graph (htgt i a p hi ha hp)] at hgp
    obtain ⟨S, hS, hdec⟩ := mem_image.mp hgp
    obtain ⟨hSi, hacc, hroot, hlab⟩ := mem_sep.mp hS
    exact ⟨S, hSi, hacc, hroot, hlab, hdec.symm⟩
  classical
  let cs : V → V := fun p => if h : p ∈ˢ B a then Classical.choose (hsub p h) else empty
  have hcs : ∀ p, p ∈ˢ B a → cs p ∈ˢ codeSpace A B tgt (tgt a p) ∧
      (∃ y, y ∈ˢ app (accCodes A B tgt I) (cs p)) ∧ HasRoot (cs p) ∧ lab (cs p) ∈ˢ A (tgt a p) ∧
      decode A B tgt I w mk (cs p) = app g p := by
    intro p hp
    have hcp : cs p = Classical.choose (hsub p hp) := by
      show (if h : p ∈ˢ B a then Classical.choose (hsub p h) else empty) = _
      rw [dif_pos hp]
    rw [hcp]
    exact Classical.choose_spec (hsub p hp)
  have hgS : ∀ p, p ∈ˢ B a → app (graph cs (B a)) p = cs p := fun p hp => app_graph hp
  have hSmem : mkCode B a (graph cs (B a)) ∈ˢ codeSpace A B tgt i :=
    mkCode_mem_codeSpace ha fun p hp => by rw [hgS p hp]; exact (hcs p hp).1
  have hSacc : ∃ y, y ∈ˢ app (accCodes A B tgt I) (mkCode B a (graph cs (B a))) :=
    acc_mkCode hi ha (fun p hp => by rw [hgS p hp]; exact (hcs p hp).1)
      (fun p hp => by rw [hgS p hp]; exact (hcs p hp).2.1)
  rw [app_graph hi]
  refine mem_image.mpr ⟨mkCode B a (graph cs (B a)),
    mem_sep.mpr ⟨hSmem, hSacc, hasRoot_mkCode a _, by rw [lab_mkCode]; exact ha⟩, ?_⟩
  rw [decode_eq hw hB hmkU (mem_allCodes.mpr ⟨i, hi, hSmem⟩) hSacc (hasRoot_mkCode a _)
    ⟨i, hi, by rw [lab_mkCode]; exact ha⟩, lab_mkCode]
  congr 1
  refine (eq_graph_app_of_mem_piSet hg).symm.trans (graph_congr fun p hp => ?_)
  rw [subCode_mkCode hp (fun x hx => codeSpace_pairs (hcs p hp).1 x (by rwa [hgS p hp] at hx)),
    hgS p hp]
  exact ((hcs p hp).2.2.2.2).symm

end ConLeche.SetTheory
