import Ix.Cert.Compile
import IxC.Ixon.Verify.BoundedConstant

/-! # A cheap definition-projection reader, equal on every input

The header filter reads only the production decoder's first TagN. It does
not inspect the rest of a non-projection record. A possible projection still
uses the complete decoder, including its failures; cached values still take
precedence over bytes, and the uncached path keeps the same buffer/offset
semantics, without assuming the lazy window or its cache is well formed.
`fast_eq` is the unconditional equality used by the collision check's proof.
-/

namespace Ix.Cert.ProjectionRead

open Ixon

theorem bind_ok {α β : Type} {action : GetM α} {next : α → GetM β}
    {start finish : GetState} {out : β} (h : (action >>= next) start = .ok out finish) :
    ∃ middle state, action start = .ok middle state ∧ next middle state = .ok out finish := by
  change EStateM.bind action next start = _ at h
  cases ran : action start with
  | error e state => simp [EStateM.bind, ran] at h
  | ok middle state => exact ⟨middle, state, rfl, by simpa [EStateM.bind, ran] using h⟩

theorem constant_info {start finish : GetState} {c : Constant}
    (h : getConstant start = .ok c finish) :
    ∃ state, getConstantInfo start = .ok c.info state := by
  unfold getConstant getConstantWithUnivs at h
  obtain ⟨info, state, hi, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨state, hi⟩

theorem info_header {start finish : GetState} {p : DefinitionProj}
    (h : getConstantInfo start = .ok (.dPrj p) finish) :
    ∃ tag state, getTagN 4 start = .ok tag state ∧
      tag.flag = Constant.FLAG ∧ tag.value = ConstantInfo.CONST_DPRJ := by
  unfold getConstantInfo at h
  obtain ⟨tag, state, ht, h⟩ := bind_ok h
  refine ⟨tag, state, ht, ?_⟩
  split at h
  · obtain ⟨_, _, _, h⟩ := bind_ok h
    cases h
  · split at h
    · rename_i flag
      refine ⟨beq_iff_eq.mp flag, ?_⟩
      by_cases v0 : tag.value = 0
      · simp only [v0, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v1 : tag.value = 1
      · simp only [v1, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v2 : tag.value = 2
      · simp only [v2, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v3 : tag.value = 3
      · simp only [v3, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v4 : tag.value = 4
      · simp only [v4, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v5 : tag.value = 5
      · simp only [v5, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v6 : tag.value = 6
      · simp only [v6, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v7 : tag.value = 7
      · simpa [ConstantInfo.CONST_DPRJ] using v7
      · simp only at h
        cases h
    · cases h

theorem header_of_projection {buf : ByteArray} {off len : Nat} {c : Constant} {p : DefinitionProj}
    (h : deConstantAt buf off len = .ok c) (hp : c.info = .dPrj p) :
    definitionProjectionHeader buf off = true := by
  unfold deConstantAt at h
  split at h
  · cases hc : (Bounded.getConstant loadMaxUnivNodes).run { idx := off, bytes := buf } with
    | error e state => simp [hc] at h
    | ok value state =>
      simp only [hc] at h
      split at h
      · simp only [Except.ok.injEq] at h
        subst value
        obtain ⟨mid, hi⟩ := constant_info
          (Ixon.Verify.BoundedConstant.getConstant_spec _ _ _ _ hc).1
        rw [hp] at hi
        obtain ⟨tag, _, ht, hf, hv⟩ := info_header hi
        simp [definitionProjectionHeader, EStateM.run, ht, hf, hv]
      · cases h
  · cases h

theorem fast_eq (e : Address × LazyConstant) : definitionProjectionFast e = definitionProjection e := by
  unfold definitionProjectionFast
  cases cache : e.2.cache with
  | some c => rfl
  | none =>
    cases hp : definitionProjection e with
    | none => simp
    | some value =>
      have hheader : definitionProjectionHeader e.2.buf e.2.off = true := by
        unfold definitionProjection LazyConstant.get? at hp
        rw [cache] at hp
        cases hget : deConstantAt e.2.buf e.2.off e.2.len with
        | error err => simp [hget, Except.toOption] at hp
        | ok c =>
          simp only [hget, Except.toOption] at hp
          cases hi : c.info <;> simp only [hi] at hp <;> try cases hp
          exact header_of_projection hget hi
      simp [hheader]


theorem findSome_filterMap {α β γ : Type} (f : α → Option β) (g : β → Option γ) (l : List α) :
    (l.filterMap f).findSome? g = l.findSome? fun x => (f x).bind g := by
  rw [← List.head?_filterMap, List.filterMap_filterMap, List.head?_filterMap]

/-- The optimized collision check returns exactly the original check's first
collision, including on malformed or cached lazy constants. -/
theorem collision_eq (ixe : Ixon.Env) :
    projectionCollision ixe =
      let entries := ixe.consts.toList
      let first : Std.HashMap (Address × Nat) Address := entries.foldl (init := {}) fun m e =>
        match definitionProjection e with
        | some (r, a) => if m.contains r then m else m.insert r a
        | none => m
      entries.findSome? fun e =>
        match definitionProjection e with
        | some (r, a) => if decide (first[r]? = some a) then none else some r
        | none => none := by
  have reader : definitionProjectionFast = definitionProjection := funext fast_eq
  unfold projectionCollision
  dsimp only
  rw [reader, List.foldl_filterMap, findSome_filterMap]
  congr 1
  funext e
  cases definitionProjection e with
  | none => rfl
  | some p =>
    rcases p with ⟨r, a⟩
    simp only [Option.bind]
    congr 4
    congr 2
    funext m x
    cases definitionProjection x with
    | none => rfl
    | some p => cases p; rfl

end Ix.Cert.ProjectionRead
