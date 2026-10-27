import Ix.Cert.CtxAgreeOwners
import IxC.Kernel.Verify.Rename.Decl5
import Ix.Cert.StreamUnits

/-! # Lowering a renamed block

`lowerInductive` checks a block's recursors (`Checks`: skipped for a nested block) and then
lowers it (`Body`: the modeller's records, then the block's declaration). `lowerInductive_iff`
states it. The checks read counts, the block's sort and the types' telescope lengths, which a
renaming keeps (`checks_mapKeys`), and lowering never reads a recursor's motive
(`body_motives`). So a block quotient Source lowers, renamed, lowers at a related state
(`lowerInductive_transfer`), also with its recursors' motives replaced in a nested block,
whose motives are not checked. -/

namespace Ix.Cert.LowerTransfer

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend Ix.Kernel.Frontend.InModel
open Ix.Cert.CtxAgree

variable {md md' : Mode}

/-- What the stream's checks of a block expect of its recursors' `k`. -/
def kExpectedOf (rb : BlockRead md) : Option Bool :=
  match rb.types.toList, rb.ctorNames.toList, rb.ctors.toList with
  | [(ty, _, _)], [[_]], [(_, _, nF)] =>
    match ty.type.piResult with
    | .sort s => some (nF == 0 && Ix.Kernel.Level.isEquiv s .zero == some true)
    | _ => none
  | _, _, _ => some false

/-- A recursor passes the block's checks. -/
def RecChecks (rb : BlockRead md) (r : RecCounts) : Prop :=
  r.params = rb.numParams ∧ r.motives = rb.types.size ∧ r.minors = rb.ctors.size ∧
    (∀ kE, kExpectedOf rb = some kE → r.k = kE) ∧
    ∀ m (ty : CVal md) p i n, r.motive = some m → rb.types[m]? = some (ty, p, i) →
      ty.type.piSortTeleLen? = some n → rb.numParams + r.indices = n

/-- **The block passes the stream's checks**: a nested block is not checked; every recursor of
another passes them. -/
def Checks (rb : BlockRead md) : Prop :=
  numNestedOf rb ≠ 0 ∨ ∀ x ∈ rb.recs.toList, RecChecks rb x.2.1

/-- **What the block lowers to**, past its checks. -/
def Body (st : State md) (rb : BlockRead md) (r : Read md) : Prop :=
  (wants (blockRecOf rb) = true ∧ ∃ gens, generate (genCtx st rb) (blockRecOf rb) = .ok gens ∧
      r = { decls := gens.toArray.push (indDeclOf rb), generated := gens.length, owners := ownersOf rb,
            blocks := CtxAgree.blocksOf rb }) ∨
    (wants (blockRecOf rb) = false ∧
      r = { decls := #[indDeclOf rb], owners := ownersOf rb, blocks := CtxAgree.blocksOf rb })

theorem forIn_unit_ok_iff {α ε : Type} (body : α → PUnit → Except ε (ForInStep PUnit)) (Q : α → Prop)
    (step : ∀ x, body x () = .ok (.yield ()) ↔ Q x) (yields : ∀ x r, body x () = .ok r → r = .yield ()) :
    ∀ l : List α, forIn l () body = .ok () ↔ ∀ x ∈ l, Q x
  | [] => by simp; rfl
  | x :: l => by
    rw [List.forIn_cons]
    constructor
    · intro h
      obtain ⟨r, hr, rest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      cases yields x r hr
      have := (forIn_unit_ok_iff body Q step yields l).mp rest
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (step y).mp hr
      · exact this y hy
    · intro h
      rw [(step x).mpr (h x List.mem_cons_self)]
      exact (forIn_unit_ok_iff body Q step yields l).mpr fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- One recursor's checks, as `lowerInductive` runs them. -/
def checkStep (rb : BlockRead md) (x : CVal md × RecCounts × List (RecRule md)) (_ : PUnit) :
    ReadM (ForInStep PUnit) := do
  let (cv, r, _) := x
  unless r.params == rb.numParams do
    malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {rb.numParams}"
  unless r.motives == rb.types.size do
    malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {rb.types.size} types"
  unless r.minors == rb.ctors.size do
    malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {rb.ctors.size} constructors"
  if let some kE := kExpectedOf rb then
    unless r.k == kE do
      malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
  if let some m := r.motive then
    if let some (ty, _, _) := rb.types[m]? then
      if let some n := ty.type.piSortTeleLen? then
        unless rb.numParams + r.indices == n do
          malformed s!"recursor {cv.name} declares {r.indices} indices; {ty.name} has {n - rb.numParams}"
  pure (.yield ())

/-- The lowering past the checks, as `lowerInductive` runs it. -/
def lowerBody (st : State md) (rb : BlockRead md) : ReadM (Read md) :=
  if wants (blockRecOf rb) then
    match generate (genCtx st rb) (blockRecOf rb) with
    | .error why =>
      declined s!"in-process model of {(rb.types[0]?.map (toString ·.1.name)).getD "[anonymous]"}: {why}"
    | .ok gen =>
      pure { decls := gen.toArray.push (indDeclOf rb), generated := gen.length, owners := ownersOf rb,
             blocks := CtxAgree.blocksOf rb }
  else pure { decls := #[indDeclOf rb], owners := ownersOf rb, blocks := CtxAgree.blocksOf rb }

theorem lowerInductive_eq (st : State md) (rb : BlockRead md) :
    lowerInductive st rb = if (numNestedOf rb != 0) = true then lowerBody st rb
      else (forIn rb.recs PUnit.unit (checkStep rb) >>= fun _ => lowerBody st rb) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  rfl

theorem checkStep_iff (rb : BlockRead md) (x : CVal md × RecCounts × List (RecRule md)) :
    checkStep rb x () = .ok (.yield ()) ↔ RecChecks rb x.2.1 := by
  obtain ⟨cv, rc, rules⟩ := x
  simp only [checkStep, RecChecks]
  by_cases hp : rc.params = rb.numParams <;> by_cases hm : rc.motives = rb.types.size <;>
    by_cases hn : rc.minors = rb.ctors.size <;>
    simp [hp, hm, hn, malformed, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals simp_all
  all_goals
    intro m ty p i n e ht hs
    subst e
    simp_all

theorem checkStep_yields (rb : BlockRead md) (x : CVal md × RecCounts × List (RecRule md))
    (r : ForInStep PUnit) (h : checkStep rb x () = .ok r) : r = .yield () := by
  obtain ⟨cv, rc, rules⟩ := x
  simp only [checkStep] at h
  by_cases hp : rc.params = rb.numParams <;> by_cases hm : rc.motives = rb.types.size <;>
    by_cases hn : rc.minors = rb.ctors.size <;>
    simp [hp, hm, hn, malformed, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
      Except.pure] at h
  repeat' split at h
  all_goals simp_all

theorem lowerBody_iff {st : State md} {rb : BlockRead md} {r : Read md} :
    lowerBody st rb = .ok r ↔ Body st rb r := by
  unfold lowerBody Body
  by_cases hw : wants (blockRecOf rb) = true
  · simp only [hw, ↓reduceIte, true_and, Bool.true_eq_false, false_and, or_false]
    split
    · rename_i why hgen
      simp [declined, throw, throwThe, MonadExceptOf.throw, hgen]
    · rename_i gens hgen
      simp [pure, Except.pure, hgen, eq_comm]
  · simp only [Bool.not_eq_true] at hw
    simp [hw, pure, Except.pure, eq_comm]

/-- **What `lowerInductive` accepts and returns**: a block passing its checks, lowered. -/
theorem lowerInductive_iff {st : State md} {rb : BlockRead md} {r : Read md} :
    lowerInductive st rb = .ok r ↔ Checks rb ∧ Body st rb r := by
  have loop : forIn rb.recs PUnit.unit (checkStep rb) = .ok () ↔ ∀ x ∈ rb.recs.toList, RecChecks rb x.2.1 := by
    rw [← Array.forIn_toList]
    exact forIn_unit_ok_iff _ _ (checkStep_iff rb) (checkStep_yields rb) _
  rw [lowerInductive_eq]
  unfold Checks
  by_cases hn : numNestedOf rb = 0
  · have hb : (numNestedOf rb != 0) = false := by simp [hn]
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte, hn, ne_eq, not_true_eq_false, false_or]
    constructor
    · intro h
      obtain ⟨u, hfor, hbody⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      exact ⟨loop.mp hfor, lowerBody_iff.mp hbody⟩
    · rintro ⟨hc, hbody⟩
      rw [loop.mpr hc]
      exact lowerBody_iff.mpr hbody
  · have hb : (numNestedOf rb != 0) = true := by simp [hn]
    rw [hb]
    simp only [↓reduceIte]
    rw [lowerBody_iff]
    exact ⟨fun h => ⟨.inl hn, h⟩, fun h => h.2⟩

/-! ## Renaming -/

section Rename

variable {f : md.Id → md'.Id} {P : KeyScope md}

theorem kExpectedOf_mapKeys (rb : BlockRead md) : kExpectedOf (rb.mapKeys f) = kExpectedOf rb := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  simp only [kExpectedOf, BlockRead.mapKeys, Array.toList_map]
  generalize types.toList = T
  generalize ctors.toList = C
  generalize ctorNames.toList = N
  rcases T with _ | ⟨⟨ty, p, i⟩, _ | _⟩ <;> rcases N with _ | ⟨_ | ⟨n, _ | _⟩, _ | _⟩ <;>
    rcases C with _ | ⟨⟨c, q, nF⟩, _ | _⟩ <;> try rfl
  simp only [List.map_cons, List.map_nil, ConstantVal.mapKeys_type, ← Expr.mapKeys_piResult]
  generalize ty.type.piResult = e
  cases e <;> rfl

theorem recChecks_mapKeys (rb : BlockRead md) (rc : RecCounts) :
    RecChecks (rb.mapKeys f) rc ↔ RecChecks rb rc := by
  unfold RecChecks
  rw [kExpectedOf_mapKeys]
  have hT : (rb.mapKeys f).types.size = rb.types.size := Array.size_map ..
  have hC : (rb.mapKeys f).ctors.size = rb.ctors.size := Array.size_map ..
  have hN : (rb.mapKeys f).numParams = rb.numParams := rfl
  rw [hT, hC, hN]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨fun h m ty p i n hm ht hs => ?_, fun h m ty p i n hm ht hs => ?_⟩
  · have ht' : (rb.mapKeys f).types[m]? = some (ty.mapKeys f, p, i) := by
      simp [BlockRead.mapKeys, ht]
    exact h m _ p i n hm ht' (by rw [ConstantVal.mapKeys_type, Expr.piSortTeleLen?_mapKeys]; exact hs)
  · simp only [BlockRead.mapKeys, Array.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨⟨ty₀, p₀, i₀⟩, ht₀, he⟩ := ht
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h m ty₀ p₀ i₀ n hm ht₀ (by rw [ConstantVal.mapKeys_type, Expr.piSortTeleLen?_mapKeys] at hs; exact hs)

/-- **A renaming keeps a block's checks.** -/
theorem checks_mapKeys (rb : BlockRead md) : Checks (rb.mapKeys f) ↔ Checks rb := by
  unfold Checks
  rw [numNestedOf_mapKeys]
  refine or_congr_right ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := h (x.1.mapKeys f, x.2.1, x.2.2.map (RecRule.mapKeys f))
      (by simp only [BlockRead.mapKeys, Array.toList_map, List.mem_map]; exact ⟨x, hx, rfl⟩)
    exact (recChecks_mapKeys rb _).mp this
  · simp only [BlockRead.mapKeys, Array.toList_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (recChecks_mapKeys rb _).mpr (h y hy)

/-- **A block quotient Source lowers lowers renamed** at a state related to Source's, to a
renamed read. -/
theorem lowerInductive_transfer (hP : P.Pre) (hf : InjOn f P) {stS : State md} {stA : State md'}
    (hst : StateAgree f P stS stA) {rb : BlockRead md} (hg : rb.Good P) {rS : Read md}
    (hS : lowerInductive stS rb = .ok rS) :
    ∃ rA, lowerInductive stA (rb.mapKeys f) = .ok rA ∧ StreamUnits.ReadRen f rS rA := by
  obtain ⟨checks, body⟩ := lowerInductive_iff.mp hS
  have hw : wants (blockRecOf (rb.mapKeys f)) = wants (blockRecOf rb) := by
    rw [blockRecOf_mapKeys hf hg, wants_mapKeys]
  have exists_ok : ∃ rA, lowerInductive stA (rb.mapKeys f) = .ok rA := by
    have checksA := (checks_mapKeys (f := f) rb).mpr checks
    rcases body with ⟨hwS, gens, hgen, -⟩ | ⟨hwS, -⟩
    · have hgen' := generate_toOption_mapKeys hP hf (ctxAgree_genCtx hf hst hg) (blockRecOf_good hg)
      rw [hgen] at hgen'
      rw [← blockRecOf_mapKeys hf hg] at hgen'
      cases hA : generate (genCtx stA (rb.mapKeys f)) (blockRecOf (rb.mapKeys f)) with
      | error e => rw [hA] at hgen'; cases hgen'
      | ok gensA => exact ⟨_, lowerInductive_iff.mpr ⟨checksA, .inl ⟨hw.trans hwS, gensA, hA, rfl⟩⟩⟩
    · exact ⟨_, lowerInductive_iff.mpr ⟨checksA, .inr ⟨hw.trans hwS, rfl⟩⟩⟩
  obtain ⟨rA, hA⟩ := exists_ok
  exact ⟨rA, hA, lowerInductive_mapKeys hP hf hst hg hS hA, lowerInductive_owners_mapKeys hf hg hS hA⟩

end Rename

/-! ## Motives -/

/-- A block with its recursors' motives forgotten. -/
def eraseMotives (rb : BlockRead md) : BlockRead md :=
  { rb with recs := rb.recs.map fun (cv, rc, rules) => (cv, { rc with motive := none }, rules) }

theorem numNestedOf_eraseMotives (rb : BlockRead md) : numNestedOf (eraseMotives rb) = numNestedOf rb := by
  simp only [numNestedOf, eraseMotives, Array.getElem?_map]
  cases rb.recs[0]? <;> rfl

theorem blockRecOf_eraseMotives (rb : BlockRead md) : blockRecOf (eraseMotives rb) = blockRecOf rb := by
  simp only [blockRecOf, numNestedOf_eraseMotives]
  simp [eraseMotives, isRecOf, isReflexiveOf, fieldDomsOf, memberNamesOf, Function.comp_def]

theorem body_eraseMotives {st : State md} {rb : BlockRead md} {r : Read md} :
    Body st (eraseMotives rb) r ↔ Body st rb r := by
  have hg : genCtx st (eraseMotives rb) = genCtx st rb := by
    simp only [genCtx, blockRecOf_eraseMotives]
    rfl
  have hd : indDeclOf (eraseMotives rb) = indDeclOf rb := by
    simp [indDeclOf, eraseMotives, Function.comp_def]
  have ho : ownersOf (eraseMotives rb) = ownersOf rb := by
    simp [ownersOf, eraseMotives, Function.comp_def, isRecOf, fieldDomsOf, memberNamesOf]
  have hb : CtxAgree.blocksOf (eraseMotives rb) = CtxAgree.blocksOf rb := by
    simp only [CtxAgree.blocksOf, blockRecOf_eraseMotives]
  simp only [Body, blockRecOf_eraseMotives, hg, hd, ho, hb]

/-- **Lowering a nested block reads no motive**: two nested blocks equal but for their
recursors' motives lower alike. -/
theorem lowerInductive_motives {st : State md} {rb rb' : BlockRead md} (hn : numNestedOf rb ≠ 0)
    (he : eraseMotives rb' = eraseMotives rb) {r : Read md} :
    lowerInductive st rb' = .ok r ↔ lowerInductive st rb = .ok r := by
  have hn' : numNestedOf rb' ≠ 0 := by
    rw [← numNestedOf_eraseMotives, he, numNestedOf_eraseMotives]
    exact hn
  rw [lowerInductive_iff, lowerInductive_iff, ← body_eraseMotives, he, body_eraseMotives]
  exact ⟨fun h => ⟨.inl hn, h.2⟩, fun h => ⟨.inl hn', h.2⟩⟩

/-- **A block quotient Source lowers lowers renamed, motives aside**: at a state related to
Source's, the renamed block, or a nested one with other motives, lowers to a renamed read. -/
theorem lowerInductive_transfer_motives {f : md.Id → md'.Id} {P : KeyScope md} (hP : P.Pre)
    (hf : InjOn f P) {stS : State md} {stA : State md'} (hst : StateAgree f P stS stA) {rb : BlockRead md}
    (hg : rb.Good P) {rS : Read md} (hS : lowerInductive stS rb = .ok rS) {rb' : BlockRead md'}
    (he : eraseMotives rb' = eraseMotives (rb.mapKeys f)) (hm : numNestedOf rb ≠ 0 ∨ rb' = rb.mapKeys f) :
    ∃ rA, lowerInductive stA rb' = .ok rA ∧ StreamUnits.ReadRen f rS rA := by
  obtain ⟨rA, hA, ren⟩ := lowerInductive_transfer hP hf hst hg hS
  rcases hm with hn | rfl
  · exact ⟨rA, (lowerInductive_motives (by rw [numNestedOf_mapKeys]; exact hn) he).mpr hA, ren⟩
  · exact ⟨rA, hA, ren⟩

/--
info: 'Ix.Cert.LowerTransfer.lowerInductive_transfer_motives' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lowerInductive_transfer_motives

end Ix.Cert.LowerTransfer
