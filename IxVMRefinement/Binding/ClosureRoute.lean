import IxVMRefinement.Binding.ClosureFoldStore
import IxVMRefinement.Callees.RouteDispatch
import IxVMRefinement.StatementRel.LoadedReads

/-! # The route of a block reads the store at its used references and its members only

`Route.blockRoute E B` is the dispatch's answer at the block `B` as a function of the store `E`.
Beside the block's own record it reads the store through `isIndAt E` only, at the constant
leaves of its constructors' type trees: references at indices the record uses (its sharing
table included) and the block's own members (`exprTree_leaves`). So two stores that hold the
block's record and agree on `isIndAt` there give one answer (`blockRoute_congr`), and adding
records to a store closed under used references and block members keeps the answer at a block
it holds (`blockRoute_closureStore`). -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Route

set_option linter.unusedVariables false

/-- **`a` is a constant leaf of the tree.** -/
def leafIn (a : _root_.Address) : ScanTree → Prop
  | .atom => False
  | .const b => b = a
  | .app f x => leafIn a f ∨ leafIn a x
  | .lam t b => leafIn a t ∨ leafIn a b
  | .all t b => leafIn a t ∨ leafIn a b
  | .letE t v b => leafIn a t ∨ leafIn a v ∨ leafIn a b
  | .proj x => leafIn a x

theorem leafIn_head {a : _root_.Address} : ∀ {T : ScanTree}, leafIn a T.head → leafIn a T
  | .app f x, h => Or.inl (leafIn_head (T := f) h)
  | .atom, h => h
  | .const _, h => h
  | .lam _ _, h => h
  | .all _ _, h => h
  | .letE _ _ _, h => h
  | .proj _, h => h

theorem leafIn_args {a : _root_.Address} :
    ∀ {T A : ScanTree}, A ∈ T.args → leafIn a A → leafIn a T
  | .app f x, A, hA, h => by
    have hA' : A ∈ f.args ++ [x] := hA
    rcases List.mem_append.mp hA' with hf | hx
    · exact Or.inl (leafIn_args hf h)
    · rw [List.mem_singleton] at hx
      rw [hx] at h
      exact Or.inr h
  | .atom, _, hA, _ => nomatch hA
  | .const _, _, hA, _ => nomatch hA
  | .lam _ _, _, hA, _ => nomatch hA
  | .all _ _, _, hA, _ => nomatch hA
  | .letE _ _ _, _, hA, _ => nomatch hA
  | .proj _, _, hA, _ => nomatch hA

theorem leafIn_constAddr {a : _root_.Address} :
    ∀ {H : ScanTree}, H.constAddr? = some a → leafIn a H
  | .const b, h => Option.some.inj h
  | .atom, h => nomatch h
  | .app _ _, h => nomatch h
  | .lam _ _, h => nomatch h
  | .all _ _, h => nomatch h
  | .letE _ _ _, h => nomatch h
  | .proj _, h => nomatch h

theorem leafIn_peel {a : _root_.Address} :
    ∀ {n : Nat} {T T' : ScanTree}, T.peel n = some T' → leafIn a T' → leafIn a T
  | 0, T, T', hp, h => by
    have e : some T = some T' := hp
    rw [Option.some.inj e]
    exact h
  | n + 1, .all _ b, T', hp, h => Or.inr (leafIn_peel (n := n) hp h)
  | _ + 1, .atom, _, hp, _ => nomatch hp
  | _ + 1, .const _, _, hp, _ => nomatch hp
  | _ + 1, .app _ _, _, hp, _ => nomatch hp
  | _ + 1, .lam _ _, _, hp, _ => nomatch hp
  | _ + 1, .letE _ _ _, _, hp, _ => nomatch hp
  | _ + 1, .proj _, _, hp, _ => nomatch hp

theorem hereOf_congr {isInd isInd' : _root_.Address → Option Bool} {M : List _root_.Address}
    {H : ScanTree} {m : Bool} {w : Option Bool}
    (h : ∀ a, H.constAddr? = some a → isInd a = isInd' a) :
    hereOf isInd M H m w = hereOf isInd' M H m w := by
  unfold hereOf
  cases hc : H.constAddr? with
  | none => rfl
  | some a =>
    show hereConst isInd a (memB M a) m = hereConst isInd' a (memB M a) m
    cases memB M a <;> cases m <;> simp [hereConst, h a hc]

/-- **The scan reads `isInd` at the tree's constant leaves only.** -/
theorem nestedN_congr {isInd isInd' : _root_.Address → Option Bool} {M : List _root_.Address} :
    ∀ (n : Nat) (T : ScanTree), (∀ a, leafIn a T → isInd a = isInd' a) →
      nestedN isInd M n T = nestedN isInd' M n T
  | 0, _, _ => rfl
  | _ + 1, .atom, _ => rfl
  | _ + 1, .const _, _ => rfl
  | n + 1, .lam t b, h => by
    simp only [nestedN]
    rw [nestedN_congr n t (fun a ha => h a (Or.inl ha)),
      nestedN_congr n b (fun a ha => h a (Or.inr ha))]
  | n + 1, .all t b, h => by
    simp only [nestedN]
    rw [nestedN_congr n t (fun a ha => h a (Or.inl ha)),
      nestedN_congr n b (fun a ha => h a (Or.inr ha))]
  | n + 1, .letE t v b, h => by
    simp only [nestedN]
    rw [nestedN_congr n t (fun a ha => h a (Or.inl ha)),
      nestedN_congr n v (fun a ha => h a (Or.inr (Or.inl ha))),
      nestedN_congr n b (fun a ha => h a (Or.inr (Or.inr ha)))]
  | n + 1, .proj x, h => by
    simp only [nestedN]
    exact nestedN_congr n x h
  | n + 1, .app f x, h => by
    simp only [nestedN]
    have hH : ∀ a, leafIn a (ScanTree.app f x).head → isInd a = isInd' a :=
      fun a ha => h a (leafIn_head ha)
    have e1 := nestedN_congr n _ hH
    have e2 : (ScanTree.app f x).args.map (nestedN isInd M n) =
        (ScanTree.app f x).args.map (nestedN isInd' M n) :=
      List.map_congr_left (fun A hA => nestedN_congr n A (fun a ha => h a (leafIn_args hA ha)))
    rw [e1, e2, hereOf_congr (fun a hc => hH a (leafIn_constAddr hc))]

/-- **The constant leaves of an expression's tree**: references at indices the expression or
the sharing table uses, or recursion addresses. -/
theorem exprTree_leaves {refs recur : List _root_.Address} {sharing : List Ixon.Expr} :
    ∀ {b : Nat} {e : Ixon.Expr} {T : ScanTree}, ExprTree refs recur sharing b e T →
      ∀ a, leafIn a T →
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

/-- **The answer on a constructor reads `isInd` at its type tree's constant leaves only.** -/
theorem ctorAnswer_congr {isInd isInd' : _root_.Address → Option Bool}
    {M refs : List _root_.Address} {sharing : List Ixon.Expr} {ct : Ixon.Constructor}
    (h : ∀ a, ((∃ i, refs[i]? = some a ∧
        (i ∈ exprRefIdxs ct.typ ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s)) ∨ a ∈ M) →
      isInd a = isInd' a) :
    ctorAnswer isInd M refs sharing ct = ctorAnswer isInd' M refs sharing ct := by
  unfold ctorAnswer
  cases hT : exprTree? refs M sharing ct.typ with
  | none => rfl
  | some T =>
    have hE : ExprTree refs M sharing 4294967295 ct.typ T := by
      unfold exprTree? at hT
      split at hT
      · next hex =>
        rw [← Option.some.inj hT]
        exact Classical.choose_spec hex
      · cases hT
    show (match T.peel ct.params.toNat with
        | none => none
        | some B => ctorBody isInd M B) =
      (match T.peel ct.params.toNat with
        | none => none
        | some B => ctorBody isInd' M B)
    cases hp : T.peel ct.params.toNat with
    | none => rfl
    | some B =>
      show ctorBody isInd M B = ctorBody isInd' M B
      unfold ctorBody
      cases hm : B.mentions M with
      | false => rfl
      | true =>
        show nestedN isInd M B.size B = nestedN isInd' M B.size B
        exact nestedN_congr B.size B
          (fun a ha => h a (exprTree_leaves hE a (leafIn_peel hp ha)))

/-- **The route of a block reads the store at its used references and its members only.** -/
theorem blockRoute_congr {E E' : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    (hB : recordOf E B = some cb) (hB' : recordOf E' B = some cb)
    (hiso : ∀ a, ((∃ i ∈ usedRefIdxs cb, cb.refs[i]? = some a) ∨
        (∃ ms i m, cb.info = .muts ms ∧ ms[i]? = some m ∧ a = memberAddr B i m)) →
      isIndAt E' a = isIndAt E a) :
    blockRoute E' B = blockRoute E B := by
  unfold blockRoute
  rw [hB, hB']
  show recordRoute E' B cb = recordRoute E B cb
  by_cases hmu : ∃ ms, cb.info = .muts ms
  · obtain ⟨ms, hms⟩ := hmu
    have hone : oneRoute E' B cb ms = oneRoute E B cb ms := by
      unfold oneRoute
      cases hf : firstIndc ms.toList 0 with
      | none => rfl
      | some p =>
        obtain ⟨j, ind⟩ := p
        obtain ⟨k, -, hmk⟩ := firstIndc_spec hf
        show (ind.ctors.toList.map (ctorAnswer (isIndAt E') (L1.blockRecurAddrs B ms.toList)
            cb.refs.toList cb.sharing.toList)).foldr orElse (some false) =
          (ind.ctors.toList.map (ctorAnswer (isIndAt E) (L1.blockRecurAddrs B ms.toList)
            cb.refs.toList cb.sharing.toList)).foldr orElse (some false)
        have hmem : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hmk
        have e : ind.ctors.toList.map (ctorAnswer (isIndAt E') (L1.blockRecurAddrs B ms.toList)
              cb.refs.toList cb.sharing.toList) =
            ind.ctors.toList.map (ctorAnswer (isIndAt E) (L1.blockRecurAddrs B ms.toList)
              cb.refs.toList cb.sharing.toList) := by
          refine List.map_congr_left (fun ct hct => ctorAnswer_congr (fun a ha => hiso a ?_))
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
            obtain ⟨m, hm, hx⟩ := LoadedReads.blockRecurAddrs_get hn
            exact Or.inr ⟨ms, n, m, hms, hm, hx⟩
        rw [e]
    simp only [recordRoute, hms, mutsRoute, hone]
  · rw [recordRoute_of_not_muts (fun ms h => hmu ⟨ms, h⟩),
      recordRoute_of_not_muts (fun ms h => hmu ⟨ms, h⟩)]

/-- **Adding the group's records keeps the route of a block held before the group**, `R` being
closed under used references and block members. -/
theorem blockRoute_closureStore {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat}
    {R R' : Ixon.Env} (hadm : Admits ρ t g R R') (hR : UsedClosed R) {B : _root_.Address}
    {cb : Ixon.Constant} (hB : recordOf R B = some cb) :
    blockRoute (closureStore t g R R') B = blockRoute R B := by
  refine blockRoute_congr hB (recordOf_closureStore_of_R hadm hB) (fun a ha => ?_)
  have hRa : (recordOf R a).isSome = true := by
    rcases ha with ⟨i, hi, hx⟩ | ⟨ms, i, m, hms, hm, hx⟩
    · exact (hR.1 B cb hB).2 i hi a hx
    · rw [hx]
      exact Option.isSome_iff_exists.mpr ⟨_, (hR.2 B cb ms hB hms i m hm).1⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hRa
  unfold isIndAt
  rw [recordOf_closureStore_of_R hadm hc, hc]

end IxVM.Refinement.Binding
