import IxVMRefinement.Binding.FamilyFlatLocal
import IxVMRefinement.Callees.RouteDispatch

/-! # The dispatch on a block over two stores

The reconstruction's head normalization asks, at a projection of a constructor, whether the
structure's block is on the modeled route (`block_is_modeled`, modelled by `Route.blockRoute`).
That answer passes to a store that holds more, and to a used-closed sub-store that holds the
block:

* `reconLeaf`, `exprTree_reconLeaves`: the scan's tree has as constant leaves only references the
  expression or the sharing table uses, or the block's members (as in `Binding.ClosureRoute`,
  stated here below the family model);
* `nestedN_mono_on`, `ctorAnswer_mono_on`, `blockRoute_mono_on`: the dispatch answers the same
  under head tests that answer the same where the first answers, at the leaves;
* **`blockRoute_grow`**, **`blockRoute_of_sub`**: over a store holding the first's records, and
  over a used-closed sub-store of the run's store that holds the block. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Route
open IxVM.Refinement.Binding.FamilyFlat

set_option linter.unusedVariables false

/-- **`a` is a constant leaf of the tree.** -/
def reconLeaf (a : _root_.Address) : ScanTree → Prop
  | .atom => False
  | .const b => b = a
  | .app f x => reconLeaf a f ∨ reconLeaf a x
  | .lam t b => reconLeaf a t ∨ reconLeaf a b
  | .all t b => reconLeaf a t ∨ reconLeaf a b
  | .letE t v b => reconLeaf a t ∨ reconLeaf a v ∨ reconLeaf a b
  | .proj x => reconLeaf a x

theorem reconLeaf_head {a : _root_.Address} : ∀ {T : ScanTree}, reconLeaf a T.head → reconLeaf a T
  | .app f x, h => Or.inl (reconLeaf_head (T := f) h)
  | .atom, h => h
  | .const _, h => h
  | .lam _ _, h => h
  | .all _ _, h => h
  | .letE _ _ _, h => h
  | .proj _, h => h

theorem reconLeaf_args {a : _root_.Address} :
    ∀ {T A : ScanTree}, A ∈ T.args → reconLeaf a A → reconLeaf a T
  | .app f x, A, hA, h => by
    have hA' : A ∈ f.args ++ [x] := hA
    rcases List.mem_append.mp hA' with hf | hx
    · exact Or.inl (reconLeaf_args hf h)
    · rw [List.mem_singleton] at hx
      rw [hx] at h
      exact Or.inr h
  | .atom, _, hA, _ => nomatch hA
  | .const _, _, hA, _ => nomatch hA
  | .lam _ _, _, hA, _ => nomatch hA
  | .all _ _, _, hA, _ => nomatch hA
  | .letE _ _ _, _, hA, _ => nomatch hA
  | .proj _, _, hA, _ => nomatch hA

theorem reconLeaf_constAddr {a : _root_.Address} :
    ∀ {H : ScanTree}, H.constAddr? = some a → reconLeaf a H
  | .const b, h => Option.some.inj h
  | .atom, h => nomatch h
  | .app _ _, h => nomatch h
  | .lam _ _, h => nomatch h
  | .all _ _, h => nomatch h
  | .letE _ _ _, h => nomatch h
  | .proj _, h => nomatch h

theorem reconLeaf_peel {a : _root_.Address} :
    ∀ {n : Nat} {T T' : ScanTree}, T.peel n = some T' → reconLeaf a T' → reconLeaf a T
  | 0, T, T', hp, h => by
    have e : some T = some T' := hp
    rw [Option.some.inj e]
    exact h
  | n + 1, .all _ b, T', hp, h => Or.inr (reconLeaf_peel (n := n) hp h)
  | _ + 1, .atom, _, hp, _ => nomatch hp
  | _ + 1, .const _, _, hp, _ => nomatch hp
  | _ + 1, .app _ _, _, hp, _ => nomatch hp
  | _ + 1, .lam _ _, _, hp, _ => nomatch hp
  | _ + 1, .letE _ _ _, _, hp, _ => nomatch hp
  | _ + 1, .proj _, _, hp, _ => nomatch hp

/-- **The constant leaves of an expression's tree**: references at indices the expression or
the sharing table uses, or recursion addresses. -/
theorem exprTree_reconLeaves {refs recur : List _root_.Address} {sharing : List Ixon.Expr} :
    ∀ {b : Nat} {e : Ixon.Expr} {T : ScanTree}, ExprTree refs recur sharing b e T →
      ∀ a, reconLeaf a T →
        (∃ i, refs[i]? = some a ∧ (i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s)) ∨
          a ∈ recur := by
  intro b e T h
  induction h with
  | var => intro a ha; exact ha.elim
  | sort => intro a ha; exact ha.elim
  | str => intro a ha; exact ha.elim
  | nat => intro a ha; exact ha.elim
  | ref hr =>
    intro a ha
    have e : _ = a := ha
    subst e
    exact Or.inl ⟨_, hr, Or.inl (List.mem_singleton.mpr rfl)⟩
  | recur hr =>
    intro a ha
    have e : _ = a := ha
    subst e
    exact Or.inr (List.mem_of_getElem? hr)
  | prj _ ih =>
    intro a ha
    rcases ih a ha with ⟨i, hi, hin | hs⟩ | hrec
    · exact Or.inl ⟨i, hi, Or.inl (List.mem_cons_of_mem _ hin)⟩
    · exact Or.inl ⟨i, hi, Or.inr hs⟩
    · exact Or.inr hrec
  | app _ _ ihf iha =>
    intro a ha
    rcases ha with ha | ha
    · rcases ihf a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_left _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
    · rcases iha a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_right _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
  | lam _ _ iht ihb =>
    intro a ha
    rcases ha with ha | ha
    · rcases iht a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_left _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
    · rcases ihb a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_right _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
  | all _ _ iht ihb =>
    intro a ha
    rcases ha with ha | ha
    · rcases iht a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_left _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
    · rcases ihb a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_right _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
  | letE _ _ _ iht ihv ihb =>
    intro a ha
    rcases ha with ha | ha | ha
    · rcases iht a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_left _ (List.mem_append_left _ hin))⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
    · rcases ihv a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_left _ (List.mem_append_right _ hin))⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
    · rcases ihb a ha with ⟨i, hi, hin | hs⟩ | hrec
      · exact Or.inl ⟨i, hi, Or.inl (List.mem_append_right _ hin)⟩
      · exact Or.inl ⟨i, hi, Or.inr hs⟩
      · exact Or.inr hrec
  | share _ hsh _ ih =>
    intro a ha
    rcases ih a ha with ⟨i, hi, hin | hs⟩ | hrec
    · exact Or.inl ⟨i, hi, Or.inr ⟨_, List.mem_of_getElem? hsh, hin⟩⟩
    · exact Or.inl ⟨i, hi, Or.inr hs⟩
    · exact Or.inr hrec


/-! ## The scan under head tests that answer more -/

theorem orElse_mono {o₁ o₂ o₁' o₂' : Option Bool} (h₁ : ∀ x, o₁ = some x → o₁' = some x)
    (h₂ : ∀ x, o₂ = some x → o₂' = some x) :
    ∀ x, orElse o₁ o₂ = some x → orElse o₁' o₂' = some x := by
  intro x h
  cases o₁ with
  | none => simp [orElse] at h
  | some b =>
    rw [h₁ b rfl]
    cases b with
    | true => exact h
    | false => exact h₂ x h

theorem foldr_orElse_mono {α : Type} {f g : α → Option Bool} :
    ∀ (l : List α), (∀ A ∈ l, ∀ x, f A = some x → g A = some x) →
      ∀ x, (l.map f).foldr orElse (some false) = some x →
        (l.map g).foldr orElse (some false) = some x
  | [], _, x, h => h
  | A :: rest, hl, x, h =>
    orElse_mono (hl A List.mem_cons_self)
      (foldr_orElse_mono rest (fun B hB => hl B (List.mem_cons_of_mem _ hB))) x h

theorem hereOf_mono_on {isInd isInd' : _root_.Address → Option Bool} {M : List _root_.Address}
    {H : ScanTree} {m : Bool} {w w' : Option Bool}
    (h : ∀ a, H.constAddr? = some a → ∀ b, isInd a = some b → isInd' a = some b)
    (hw : ∀ x, w = some x → w' = some x) :
    ∀ x, hereOf isInd M H m w = some x → hereOf isInd' M H m w' = some x := by
  intro x hx
  unfold hereOf at hx ⊢
  cases hc : H.constAddr? with
  | none =>
    rw [hc] at hx
    exact hw x hx
  | some a =>
    rw [hc] at hx
    show hereConst isInd' a (memB M a) m = some x
    have hx' : hereConst isInd a (memB M a) m = some x := hx
    cases hm : memB M a <;> cases m <;> rw [hm] at hx' <;> simp only [hereConst] at hx' ⊢
    · exact hx'
    · exact h a hc x hx'
    · exact hx'
    · exact hx'

/-- **The scan answers the same under a head test that answers the same where the first answers,
at the tree's constant leaves.** -/
theorem nestedN_mono_on {isInd isInd' : _root_.Address → Option Bool} {M : List _root_.Address} :
    ∀ (n : Nat) (T : ScanTree),
      (∀ a, reconLeaf a T → ∀ b, isInd a = some b → isInd' a = some b) →
      ∀ x, nestedN isInd M n T = some x → nestedN isInd' M n T = some x
  | 0, _, _, _, h => h
  | _ + 1, .atom, _, _, h => h
  | _ + 1, .const _, _, _, h => h
  | n + 1, .lam t b, hT, x, h =>
    orElse_mono (nestedN_mono_on n t fun a ha => hT a (Or.inl ha))
      (nestedN_mono_on n b fun a ha => hT a (Or.inr ha)) x h
  | n + 1, .all t b, hT, x, h =>
    orElse_mono (nestedN_mono_on n t fun a ha => hT a (Or.inl ha))
      (nestedN_mono_on n b fun a ha => hT a (Or.inr ha)) x h
  | n + 1, .letE t v b, hT, x, h =>
    orElse_mono (nestedN_mono_on n t fun a ha => hT a (Or.inl ha))
      (orElse_mono (nestedN_mono_on n v fun a ha => hT a (Or.inr (Or.inl ha)))
        (nestedN_mono_on n b fun a ha => hT a (Or.inr (Or.inr ha)))) x h
  | n + 1, .proj y, hT, x, h => nestedN_mono_on n y hT x h
  | n + 1, .app f y, hT, x, h => by
    have hH : ∀ a, reconLeaf a (ScanTree.app f y).head → ∀ b, isInd a = some b →
        isInd' a = some b := fun a ha => hT a (reconLeaf_head ha)
    exact orElse_mono
      (hereOf_mono_on (fun a hc => hH a (reconLeaf_constAddr hc))
        (nestedN_mono_on n _ hH))
      (foldr_orElse_mono _ fun A hA =>
        nestedN_mono_on n A fun a ha => hT a (reconLeaf_args hA ha)) x h

/-- **The answer on a constructor under a head test that answers the same where the first
answers, at its type tree's constant leaves.** -/
theorem ctorAnswer_mono_on {isInd isInd' : _root_.Address → Option Bool}
    {M refs : List _root_.Address} {sharing : List Ixon.Expr} {ct : Ixon.Constructor}
    (h : ∀ a, ((∃ i, refs[i]? = some a ∧
        (i ∈ exprRefIdxs ct.typ ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s)) ∨ a ∈ M) →
      ∀ b, isInd a = some b → isInd' a = some b) :
    ∀ x, ctorAnswer isInd M refs sharing ct = some x →
      ctorAnswer isInd' M refs sharing ct = some x := by
  intro x hx
  unfold ctorAnswer at hx ⊢
  cases hT : exprTree? refs M sharing ct.typ with
  | none => rw [hT] at hx; simp at hx
  | some T =>
    rw [hT] at hx
    have hE : ExprTree refs M sharing 4294967295 ct.typ T := by
      unfold exprTree? at hT
      split at hT
      · next hex =>
        rw [← Option.some.inj hT]
        exact Classical.choose_spec hex
      · cases hT
    simp only at hx ⊢
    cases hp : T.peel ct.params.toNat with
    | none => rw [hp] at hx; simp at hx
    | some B =>
      rw [hp] at hx
      simp only at hx ⊢
      unfold Route.ctorBody at hx ⊢
      cases hm : B.mentions M with
      | false => rw [hm] at hx; exact hx
      | true =>
        rw [hm] at hx
        exact nestedN_mono_on B.size B
          (fun a ha => h a (exprTree_reconLeaves hE a (reconLeaf_peel hp ha))) x hx

/-- **The dispatch answers the same under stores whose head tests answer the same where the first
answers, at the block's used references and members.** -/
theorem blockRoute_mono_on {E E' : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    (hB : recordOf E B = some cb) (hB' : recordOf E' B = some cb)
    (hiso : ∀ a, ((∃ i ∈ usedRefIdxs cb, cb.refs[i]? = some a) ∨
        (∃ ms i m, cb.info = .muts ms ∧ ms[i]? = some m ∧ a = memberAddr B i m)) →
      ∀ b, isIndAt E a = some b → isIndAt E' a = some b) :
    ∀ x, blockRoute E B = some x → blockRoute E' B = some x := by
  intro x hx
  unfold blockRoute at hx ⊢
  rw [hB] at hx
  rw [hB']
  show recordRoute E' B cb = some x
  have hx' : recordRoute E B cb = some x := hx
  by_cases hmu : ∃ ms, cb.info = .muts ms
  · obtain ⟨ms, hms⟩ := hmu
    have hone : ∀ y, oneRoute E B cb ms = some y → oneRoute E' B cb ms = some y := by
      intro y hy
      unfold oneRoute at hy ⊢
      cases hf : firstIndc ms.toList 0 with
      | none => rw [hf] at hy; simp at hy
      | some p =>
        obtain ⟨j, ind⟩ := p
        rw [hf] at hy
        obtain ⟨k, -, hmk⟩ := firstIndc_spec hf
        have hmem : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hmk
        exact foldr_orElse_mono _ (fun ct hct => ctorAnswer_mono_on (fun a ha => hiso a (by
          rcases ha with ⟨i, hi, hin | ⟨s, hs, hin⟩⟩ | hrec
          · refine Or.inl ⟨i, ?_, by rw [← Array.getElem?_toList]; exact hi⟩
            unfold usedRefIdxs
            rw [hms]
            refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind, hmem, ?_⟩)
            simp only [mutRefIdxs]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ct, hct, hin⟩)
          · refine Or.inl ⟨i, ?_, by rw [← Array.getElem?_toList]; exact hi⟩
            unfold usedRefIdxs
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, hin⟩)
          · obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hrec
            obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hn
            exact Or.inr ⟨ms, n, m, hms, hm, hxm⟩))) y hy
    simp only [recordRoute, hms, mutsRoute] at hx' ⊢
    split at hx'
    · exact hx'
    · exact hone x hx'
    · exact hx'
  · rw [recordRoute_of_not_muts (fun ms h => hmu ⟨ms, h⟩)] at hx'
    rw [recordRoute_of_not_muts (fun ms h => hmu ⟨ms, h⟩)]
    exact hx'

/-- **The dispatch over a store holding the first's records answers the same where the first
answers.** -/
theorem blockRoute_grow {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c) {B : _root_.Address} :
    ∀ x, blockRoute E B = some x → blockRoute E' B = some x := by
  intro x hx
  cases hB : recordOf E B with
  | none => unfold blockRoute at hx; rw [hB] at hx; simp at hx
  | some cb =>
    refine blockRoute_mono_on hB (hle B cb hB) (fun a _ b hb => ?_) x hx
    unfold isIndAt at hb ⊢
    cases ha : recordOf E a with
    | none => rw [ha] at hb; simp at hb
    | some c => rw [ha] at hb; rw [hle a c ha]; exact hb

/-- **The dispatch over a used-closed sub-store of `E₀` that holds the block answers as over
`E₀`**: the scan reads the block's used references and members, which the sub-store holds. -/
theorem blockRoute_of_sub {E₀ R : Ixon.Env}
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    {B : _root_.Address} (hB : Held R B) :
    ∀ x, blockRoute E₀ B = some x → blockRoute R B = some x := by
  intro x hx
  obtain ⟨cb, hcbR⟩ := Option.isSome_iff_exists.mp hB
  have hcb₀ : recordOf E₀ B = some cb := hsub B cb hcbR
  refine blockRoute_mono_on hcb₀ hcbR (fun a ha b hb => ?_) x hx
  have hRa : Held R a := by
    rcases ha with ⟨i, hi, hx'⟩ | ⟨ms', i, m, hms', hm, hx'⟩
    · exact (hcl.1 B cb hcbR).2 i hi a hx'
    · rw [hx']
      exact Option.isSome_iff_exists.mpr ⟨_, (hcl.2 B cb ms' hcbR hms' i m hm).1⟩
  unfold isIndAt at hb ⊢
  rw [recordOf_eq_of_held hsub hRa]
  exact hb

end IxVM.Refinement.Binding.FamilyRecon
