import Ix.CompileCert.Opt.Total
import Ix.CompileCert.Canon.Cache
import Ix.Compile.Pass.Driver

/-!
# M7 L3-def: invariants for the shape reader

The successful reader's guards bound every selected motive and minor by the Lean source
telescope. The block-building loops preserve those bounds, so `shapesWF_optLookup` discharges
`ShapesWF` for the driver's actual optimization environment. This is the range hypothesis used
by the totality of O1, O4 and O6 (`Total.lean`), with no name/hash agreement premise. It does not
by itself prove the image's recorded minor terms closed or establish `RecLaw`.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Pass.Opt

/-- **An invariant of a loop** (in `Option`): kept by every successful step, it holds of the result. -/
theorem forIn_option_inv {α σ : Type} (f : α → σ → Option (ForInStep σ)) (P : σ → Prop)
    (hstep : ∀ x a r, P a → f x a = some r → P r.value) :
    ∀ (l : List α) (a res : σ), P a → forIn l a f = some res → P res
  | [], a, res, ha, h => by
    rw [List.forIn_nil] at h
    simp only [pure, Option.some.injEq] at h
    exact h ▸ ha
  | x :: l, a, res, ha, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := obind.1 h
    have hp := hstep x a r ha hr
    cases r with
    | done b =>
      simp only [pure, Option.some.injEq] at h
      exact h ▸ hp
    | yield b => exact forIn_option_inv f P hstep l b res hp h


/-- Every successful shape read keeps its motive and minor sources in the Lean telescope's
ranges. This is a property of the reader's guards, without a name/hash agreement premise. -/
theorem readShape_wf {leanRec : Name} {levelParams : Array Name} {np nm nmin ni : Nat}
    {value : Expr} {ixRecInfo : Name → Option RecursorVal} {s : RecShape}
    (h : readShape leanRec levelParams np nm nmin ni value ixRecInfo = some s) : ShapeWF s := by
  unfold readShape at h
  obtain ⟨body, _, h⟩ := obind.1 h
  try dsimp only at h
  generalize Ix.Compile.Canon.getAppFnArgs body = pair at h
  obtain ⟨head, args⟩ := pair
  cases head <;> try (oabsurd h)
  rename_i rho ls _hash
  try dsimp only at h
  obtain ⟨iv, _, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨_, h⟩ := oguard h
  obtain ⟨_, h⟩ := oguard h
  obtain ⟨_, _, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨_, _, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨motives, hm, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨minorState, hmin, h⟩ := obind.1 h
  try dsimp only at h
  have hmotives : ∀ m ∈ motives.toList, m < nm := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hm
    refine forIn_option_inv _ (fun ms => ∀ m ∈ ms.toList, m < nm) ?_ _ _ _ (by simp) hm
    intro k acc res ha hb
    try dsimp only at hb
    obtain ⟨p, _, hb⟩ := obind.1 hb
    try dsimp only at hb
    obtain ⟨hrange, hb⟩ := oguard hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrange
    simp only [pure, Option.some.injEq] at hb
    subst res
    intro m hm
    simp only [ForInStep.value, Array.toList_push, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ha m hm
    · omega
  have hminors : ∀ j ∈ minorState.1.toList.filterMap id, j < nmin := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hmin
    refine forIn_option_inv _
      (fun (st : Array (Option Nat) × Array Expr) => ∀ j ∈ st.1.toList.filterMap id, j < nmin)
      ?_ _ _ _ (by simp) hmin
    rintro k ⟨src, terms⟩ res ha hb
    try dsimp only at hb
    split at hb
    · rename_i p _hp
      obtain ⟨hrange, hb⟩ := oguard hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hrange
      simp only [pure, Option.some.injEq] at hb
      subst res
      intro j hj
      simp only [ForInStep.value, Array.toList_push, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, id_eq, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact ha j hj
      · omega
    · simp only [pure, Option.some.injEq] at hb
      subst res
      simpa only [ForInStep.value, Array.toList_push, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, id_eq, List.append_nil] using ha
  simp only [pure, Option.some.injEq] at h
  cases h
  exact ⟨hmotives, hminors⟩

/-- A state predicate preserved by every step also holds after an `Id` loop. -/
theorem forIn_id_inv {α σ : Type} (f : α → σ → Id (ForInStep σ)) (P : σ → Prop)
    (hstep : ∀ x a, P a → P (f x a).value) :
    ∀ (l : List α) (a : σ), P a → P (forIn (m := Id) l a f)
  | [], a, ha => by simpa only [List.forIn_nil, pure] using ha
  | x :: l, a, ha => by
    rw [List.forIn_cons]
    have hp := hstep x a ha
    generalize f x a = step at hp ⊢
    cases step with
    | done b => exact hp
    | yield b => exact forIn_id_inv f P hstep l b hp

theorem forIn_id_array_inv {α σ : Type} (f : α → σ → Id (ForInStep σ)) (P : σ → Prop)
    (hstep : ∀ x a, P a → P (f x a).value) (xs : Array α) (a : σ) (ha : P a) :
    P (forIn (m := Id) xs a f) := by
  rw [← Array.forIn_toList]
  exact forIn_id_inv f P hstep xs.toList a ha

/-- Inserting a value that satisfies `P` preserves `P` for every value returned by a name map.
This does not identify hash-equal names with structurally equal names. -/
theorem nameMap_forall_insert {β : Type} (P : β → Prop) {m : Std.HashMap Name β}
    (hm : ∀ k v, m.get? k = some v → P v) {k : Name} {v : β} (hv : P v) :
    ∀ n w, (m.insert k v).get? n = some w → P w := by
  intro n w h
  simp only [Std.HashMap.get?_eq_getElem?] at hm h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · cases h; exact hv
  · exact hm n w h

/-- Every shape inserted by `optBlockOf` came from a successful shape read. -/
theorem optBlockOf_wf (inp : Ix.Compile.Pass.ViewInput) (v : Ix.Compile.Pass.BlockView) :
    ∀ r s, (optBlockOf inp v).shapes.get? r = some s → ShapeWF s := by
  unfold optBlockOf
  dsimp only [Id.run, Bind.bind, Pure.pure]
  refine forIn_id_array_inv _
    (fun (st : Std.HashMap Name RecShape × Std.HashMap Name (Array Name × Expr)) =>
      ∀ r s, st.1.get? r = some s → ShapeWF s) ?_ _ _ ?_
  · rintro r ⟨shapes, images⟩ ha
    dsimp only
    split
    · rename_i rv _hrv
      split
      · rename_i img _himg
        split
        · rename_i s hs
          exact nameMap_forall_insert ShapeWF ha (readShape_wf hs)
        · exact ha
      · exact ha
    · exact ha
  · intro r s h
    simp at h

/-- The driver's block table contains only shapes in the Lean source ranges. -/
theorem optBlocks_wf (cenv : Ix.CompileM.CompileEnv)
    (views : Std.HashMap Name Ix.Compile.Pass.BlockView) :
    ∀ n b, (Ix.Compile.Pass.optBlocks cenv views).get? n = some b →
      ∀ r s, b.shapes.get? r = some s → ShapeWF s := by
  unfold Ix.Compile.Pass.optBlocks
  rw [Std.HashMap.fold_eq_foldl_toList]
  refine List.foldlRecOn (motive := fun bs : Std.HashMap Name OptBlock =>
    ∀ n b, bs.get? n = some b → ∀ r s, b.shapes.get? r = some s → ShapeWF s) _ _ ?_ ?_
  · intro n b h
    simp at h
  · intro bs hbs nv _hmem
    exact nameMap_forall_insert (fun (b : OptBlock) => ∀ r s, b.shapes.get? r = some s → ShapeWF s)
      hbs (optBlockOf_wf (Ix.Compile.Pass.viewInput cenv) nv.2)

/-- The actual environment passed to `optLookup` satisfies the shape-bound hypothesis. -/
theorem shapesWF_optLookup (cenv : Ix.CompileM.CompileEnv)
    (views : Std.HashMap Name Ix.Compile.Pass.BlockView) :
    ShapesWF
      { ienv := cenv.env, resolves := fun n => (Ix.Compile.Pass.resolveAddr cenv n).isSome
        blockOf := fun h => (cenv.p3Heads.get? h).bind (Ix.Compile.Pass.optBlocks cenv views).get?
        addrOf := Ix.Compile.Pass.resolveAddr cenv
        ixForm? := Ix.Compile.Pass.ixFormOf cenv } := by
  intro h b r s hb hs
  obtain ⟨key, _, hb⟩ := obind.1 hb
  exact optBlocks_wf cenv views key b hb r s hs

end Ix.CompileCert.Opt
