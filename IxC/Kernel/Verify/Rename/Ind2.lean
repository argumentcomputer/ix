module

public import IxC.Kernel.Verify.Rename.Ind1
public import IxC.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# Renaming and the native recogniser

The shape records of the inductive routes renamed (`InductiveShape.mapKeys`,
`NativeParts.mapKeys`), and the native recogniser (`nativeParts?`) at a
renamed block: it finds the renamed shape.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-! ## The shape records -/

/-- Rename a shape record. -/
def InductiveShape.mapKeys (f : md.Id → md'.Id) (p : InductiveShape md) : InductiveShape md' :=
  { cvT := p.cvT.mapKeys f, ctors := p.ctors.map fun c => (c.1.mapKeys f, c.2), nP := p.nP,
    nIdx := p.nIdx, cvR := p.cvR.mapKeys f, elim := p.elim, resSort := p.resSort,
    rhss := p.rhss.map (Expr.mapKeys f), large := p.large, isProp := p.isProp }

/-- A good shape record. -/
structure InductiveShape.Good (P : md.Id → Prop) (p : InductiveShape md) : Prop where
  cvT : p.cvT.Good P
  ctors : ∀ c ∈ p.ctors, c.1.Good P
  cvR : p.cvR.Good P
  rhss : Expr.GoodList P p.rhss

/-- Rename a native record (the kinds and the pin verdict name no key). -/
def NativeParts.mapKeys (f : md.Id → md'.Id) (p : NativeParts md) : NativeParts md' :=
  ⟨p.toInductiveShape.mapKeys f, p.kinds, p.recPinned⟩

abbrev NativeParts.Good (P : md.Id → Prop) (p : NativeParts md) : Prop :=
  p.toInductiveShape.Good P

@[simp] theorem NativeParts.mapKeys_toInductiveShape (p : NativeParts md) :
    (p.mapKeys f).toInductiveShape = p.toInductiveShape.mapKeys f := rfl
@[simp] theorem NativeParts.mapKeys_kinds (p : NativeParts md) : (p.mapKeys f).kinds = p.kinds :=
  rfl
@[simp] theorem NativeParts.mapKeys_recPinned (p : NativeParts md) :
    (p.mapKeys f).recPinned = p.recPinned := rfl

/-! ## Splitting a block -/

/-- Rename the split of a block. -/
def sumSplitMap (f : md.Id → md'.Id) :
    List (ConstantVal md × Nat × Nat) × ConstantVal md × Nat × Nat × List (RecRule md) →
      List (ConstantVal md' × Nat × Nat) × ConstantVal md' × Nat × Nat × List (RecRule md')
  | (cs, cvR, mI, rP, rules) =>
    (cs.map fun c => (c.1.mapKeys f, c.2), cvR.mapKeys f, mI, rP, rules.map (RecRule.mapKeys f))

theorem sumSplit_map : ∀ (block : List (ConstantInfo md)),
    sumSplit (block.map (ConstantInfo.mapKeys f)) = (sumSplit block).map (sumSplitMap f)
  | [] => rfl
  | [.recInfo cvR mI rP rules] => rfl
  | .ctorInfo cvC nP nF :: rest => by
    simp only [List.map_cons, ConstantInfo.mapKeys.eq_5]
    rw [sumSplit, sumSplit, sumSplit_map rest, Option.map_map, Option.map_map]
    cases sumSplit rest <;> rfl
  | .axiomInfo _ :: _ => rfl
  | .defnInfo _ _ _ :: _ => rfl
  | .thmInfo _ _ :: _ => rfl
  | .indInfo _ _ :: _ => rfl
  | .projInfo _ :: _ => rfl
  | .recInfo _ _ _ _ :: _ :: _ => rfl

theorem sumSplit_good : ∀ {block : List (ConstantInfo md)}, (∀ c ∈ block, c.Good P) →
    ∀ {q}, sumSplit block = some q →
      (∀ c ∈ q.1, c.1.Good P) ∧ q.2.1.Good P ∧ ∀ r ∈ q.2.2.2.2, r.Good P
  | [], _, _, h => nomatch h
  | [.recInfo cvR mI rP rules], hb, q, h => by
    simp only [sumSplit, Option.some.injEq] at h
    subst h
    have := hb _ (List.mem_singleton_self _)
    exact ⟨fun _ h => (nomatch h), this.1, this.2⟩
  | .ctorInfo cvC nP nF :: rest, hb, q, h => by
    simp only [sumSplit, Option.map_eq_some_iff] at h
    obtain ⟨q₀, h₀, rfl⟩ := h
    simp only [List.mem_cons, forall_eq_or_imp] at hb
    obtain ⟨hcs, hR, hrules⟩ := sumSplit_good hb.2 h₀
    refine ⟨?_, hR, hrules⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hb.1
    · exact hcs c hc
  | .axiomInfo _ :: _, _, _, h | .defnInfo _ _ _ :: _, _, _, h | .thmInfo _ _ :: _, _, _, h
  | .indInfo _ _ :: _, _, _, h | .projInfo _ :: _, _, _, h
  | .recInfo _ _ _ _ :: _ :: _, _, _, h => nomatch h

/-! ## Telescopes by binders -/

theorem Expr.piBinders_mapKeys : ∀ e : Expr md,
    (e.mapKeys f).piBinders = Expr.mapTele f e.piBinders
  | .forallE ty b m => by
    simp only [Expr.mapKeys, Expr.piBinders, Expr.piBinders_mapKeys b, Expr.mapTele]
    rfl
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ _
  | .lit _ | .proj _ _ _ => rfl

theorem Expr.piBinders_good : ∀ {e : Expr md}, e.Good P →
    Expr.BindersGood P e.piBinders.1 ∧ e.piBinders.2.Good P
  | .forallE ty b m, he => by
    simp only [Expr.Good] at he
    obtain ⟨h1, h2⟩ := Expr.piBinders_good he.2
    refine ⟨?_, h2⟩
    intro x hx
    simp only [Expr.piBinders, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he.1
    · exact h1 x hx
  | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he
  | .lam _ _ _, he | .letE _ _ _ _, he | .lit _, he | .proj _ _ _, he =>
    ⟨fun _ h => (nomatch h), he⟩

/-! ## The native recogniser -/

theorem nativeCounts?_map (nPd : Nat) (cvT : ConstantVal md)
    (cs : List (ConstantVal md × Nat × Nat)) (mI rP : Nat) :
    nativeCounts? nPd (cvT.mapKeys f) (cs.map fun c => (c.1.mapKeys f, c.2)) mI rP =
      nativeCounts? nPd cvT cs mI rP := by
  unfold nativeCounts?
  rw [ConstantVal.mapKeys_type, Expr.piBinders_mapKeys, List.length_map]
  obtain ⟨bs, b⟩ := cvT.type.piBinders
  simp only [Expr.mapTele, Expr.mapBinders, List.length_map]
  cases b <;> simp [Expr.mapKeys, List.length_map]

theorem nativeRecPinOk_map (hf : InjOn f P) (p : InductiveShape md)
    {block : List (ConstantInfo md)} (hb : ∀ c ∈ block, c.Good P) :
    nativeRecPinOk (p.mapKeys f) (block.map (ConstantInfo.mapKeys f)) = nativeRecPinOk p block := by
  unfold nativeRecPinOk
  rcases block with _ | ⟨c, rest⟩
  · rfl
  cases c with
  | indInfo cvT caps =>
    simp only [List.map_cons, ConstantInfo.mapKeys.eq_4]
    rw [sumSplit_map rest]
    simp only [List.mem_cons, forall_eq_or_imp] at hb
    cases hs : sumSplit rest with
    | none => rfl
    | some q =>
      obtain ⟨cs, cvR, mI, rP, rules⟩ := q
      obtain ⟨hcs, _, hrules⟩ := sumSplit_good hb.2 hs
      simp only [Option.map_some, sumSplitMap, InductiveShape.mapKeys, List.length_map]
      congr 1
      apply List.all_congr_mem
      intro j _
      simp only [List.getElem?_map]
      cases hr : rules[j]? with
      | none => rfl
      | some r =>
        cases hc : cs[j]? with
        | none => rfl
        | some c =>
          obtain ⟨cvC, nP', nF⟩ := c
          have hrg := hrules r (List.mem_of_getElem? hr)
          have hcg := hcs _ (List.mem_of_getElem? hc)
          simp only [Option.map_some, RecRule.mapKeys, ConstantVal.mapKeys_name,
            Key.map_beq hf hrg.1 hcg.1]
  | _ => rfl

theorem nativeRecLpsOk_map (p : InductiveShape md) :
    nativeRecLpsOk (p.mapKeys f) = nativeRecLpsOk p := rfl

theorem nativeShape?_map (nPd : Nat) (block : List (ConstantInfo md)) :
    nativeShape? nPd (block.map (ConstantInfo.mapKeys f)) =
      (nativeShape? nPd block).map (InductiveShape.mapKeys f) := by
  unfold nativeShape?
  rcases block with _ | ⟨c, rest⟩
  · rfl
  cases c with
  | indInfo cvT caps =>
    simp only [List.map_cons, ConstantInfo.mapKeys.eq_4]
    rw [sumSplit_map rest]
    cases hs : sumSplit rest with
    | none => rfl
    | some q =>
      obtain ⟨cs, cvR, mI, rP, rules⟩ := q
      simp only [Option.map_some, sumSplitMap]
      rw [nativeCounts?_map]
      cases nativeCounts? nPd cvT cs mI rP with
      | none => rfl
      | some c =>
        obtain ⟨nP, nIdx⟩ := c
        simp only [ConstantVal.mapKeys_name, reservedBasisNames_contains_map, List.all_map,
          Function.comp_def, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
          Expr.stripPis_mapKeys]
        cases hst : Expr.stripPis (nP + nIdx) cvT.type with
        | none =>
          simp only [Option.map_none]
          split <;> (try split) <;> simp_all [InductiveShape.mapKeys, List.map_map, Function.comp_def]
        | some r =>
          obtain ⟨bs, b⟩ := r
          cases b <;> simp only [Option.map_some, Expr.mapTele, Expr.mapKeys] <;>
            split <;> (try split) <;> simp_all [InductiveShape.mapKeys, List.map_map, Function.comp_def]
  | _ => rfl

end Ix.Kernel
