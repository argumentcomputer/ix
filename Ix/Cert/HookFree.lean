import Ix.Cert.Resolution
import Ix.Cert.Claims
import Ix.Cert.Condense
import Ix.Cert.Closure
import Ix.Cert.Unchanged

/-! # `HookFree` discharged (Route A, B9b, `HookFree`'s discharge, step 4)

`Ix.Cert.Resolution.compileReport_claim` gives each resolved name outside the
aux map as a primary claim of a block compile, the block compile's under
`HookFree`. This file discharges `HookFree` for every such name of a closure
`sub` that avoids the changed set and has no failure
(`compileReport_hookFree`):

* a claim of a promoted block's cross-SCC subset is refuted: its name, or its
  constructor's inductive, is one of the subset's unresolved names
  (`auxBlockOutcome_cross_names`, `Claims.runBlock_owned`), each of which the
  application leaves an extra name or a failure
  (`applyAuxBlockOutcome_cross_extras`), which the tenth check and `NoFailure`
  refute (`cross_refuted`);
* a compiled block's claim is its key or a projection name, owned by a member
  (`Claims.runBlock_owned`, the driver's view of the input carrying its names,
  `namedEnv_view`), so the block is in the closure (`owned_sub`,
  `Condense.condense_scc`, `Condense.closure_path`);
* at a block of the closure the hooks are identities (`hookFree_of_sub`): no
  reference of the block holding its key, and no member, is a head of the
  snapshot (`not_head`: a head the final environment keeps is a regenerated
  input name in the changed set, the eleventh check; one it withdrew is a
  recorded failure, an input name by the fourteenth; either is refuted for a
  name the closure reaches). -/

namespace Ix.Cert.HookFree

open Ix Ix.CompileM Ix.Cert.Resolution Ix.Cert.Condense
open Ix.Compile.ExactKey (ExactName)

/-! ## A promoted block's cross-SCC claims -/

/-- A name an inserting fold over `L` holds is `==` one of `L`'s. -/
theorem foldl_insert_mem {L : Array Ix.Name} {x : Ix.Name}
    (h : (L.foldl (fun s n => s.insert n) ({} : Ix.Set Ix.Name)).contains x = true) :
    ∃ y ∈ L, (y == x) = true := by
  rw [← Array.foldl_toList] at h
  suffices key : ∀ (l : List Ix.Name) (s : Ix.Set Ix.Name),
      (l.foldl (fun s n => s.insert n) s).contains x = true → s.contains x = true ∨ ∃ y ∈ l, (y == x) = true by
    rcases key _ _ h with h | ⟨y, hy, e⟩
    · simp at h
    · exact ⟨y, Array.mem_toList_iff.mp hy, e⟩
  intro l
  induction l with
  | nil => intro s h; exact .inl h
  | cons y l ih =>
    intro s h
    rcases ih _ h with h | ⟨z, hz, e⟩
    · rw [Std.HashSet.contains_insert] at h
      rcases Bool.or_eq_true_iff.mp h with e | h
      · exact .inr ⟨y, List.mem_cons_self, e⟩
      · exact .inl h
    · exact .inr ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- **A promoted block's cross-SCC subset is its unresolved names** `cn`, under
one of them. -/
theorem auxBlockOutcome_cross_names {cenv : CompileEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {clo : Ix.Name} {r : BlockResult} {c : BlockState} {p : Ix.Compile.Pass.Published}
    {cn : Array Ix.Name} {cf : Option (Array Ix.Name × String)} {im : Option String}
    {na : Option (BlockResult × BlockState)} {nf : Option String}
    (h : auxBlockOutcome cenv lo all = .promoted (some (clo, r, c, p)) cn cf im na nf) :
    ∃ layout : Option Ixon.AuxLayout, clo ∈ cn ∧
      runBlock cenv (cn.foldl (fun s n => s.insert n) {}) clo = .ok (r, c, layout, p) := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · revert h
    refine loop_bind_mem _ _ _ _ (fun _ : Array Ix.Name => True)
      (fun o : AuxBlockOutcome => o = .promoted (some (clo, r, c, p)) cn cf im na nf →
        ∃ layout : Option Ixon.AuxLayout, clo ∈ cn ∧
          runBlock cenv (cn.foldl (fun s n => s.insert n) {}) clo = .ok (r, c, layout, p))
      trivial (fun _ _ _ _ => trivial) ?_
    intro L _ h'
    repeat' (first | (focus (cases h'; done)) | split at h')
    all_goals
      cases h'
      have hne : (!cn.isEmpty) = true := ‹_›
      exact ⟨_, canonicalKey_mem (fun e => by subst e; cases hne), ‹_›⟩
  · split at h <;> cases h


/-- `y` is an extra name or a recorded failure in `c`. -/
def ExtraOrFail (c : CompileEnv) (y : Ix.Name) : Prop :=
  c.auxGenExtraNames.contains y = true ∨ c.ungrounded.contains y = true

theorem ExtraOrFail.mono {c c' : CompileEnv} (m : Mono c c') {y : Ix.Name} (h : ExtraOrFail c y) :
    ExtraOrFail c' y := by
  rcases h with h | h
  · exact m.2.2 y h
  · exact .inr (m.1 y h)

/-- A loop over names whose every step yields, keeps a property of each name
and gives it to the name it steps on, gives it to every name. -/
theorem forIn_marks (xs : Array Ix.Name) (init : DriverAcc)
    (f : Ix.Name → DriverAcc → Id (ForInStep DriverAcc)) (P : Ix.Name → DriverAcc → Prop)
    (yields : ∀ x s, ∃ s', f x s = .yield s') (keep : ∀ x s y, P y s → P y (f x s).value)
    (hit : ∀ x s, P x (f x s).value) : ∀ y ∈ xs, P y (forIn (m := Id) xs init f) := by
  rw [← Array.forIn_toList]
  suffices key : ∀ (l : List Ix.Name) (s : DriverAcc) (y : Ix.Name), (P y s ∨ y ∈ l) →
      P y (forIn (m := Id) l s f) from fun y hy => key _ _ y (.inr (Array.mem_toList_iff.mpr hy))
  intro l
  induction l with
  | nil => intro s y h; rcases h with h | h; exacts [h, nomatch h]
  | cons x l ih =>
    intro s y h
    rw [List.forIn_cons]
    obtain ⟨s', hs'⟩ := yields x s
    have hv : (f x s).value = s' := by rw [hs']; rfl
    simp only [hs', bind]
    refine ih s' y ?_
    rcases h with h | h
    · exact .inl (hv ▸ keep x s y h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (hv ▸ hit y s)
      · exact .inr h

theorem set_insert_keep {s : Ix.Set Ix.Name} {a y : Ix.Name} (h : s.contains y = true) :
    (s.insert a).contains y = true := by
  rw [Std.HashSet.contains_insert, h, Bool.or_true]

theorem set_insert_hit {s : Ix.Set Ix.Name} {a : Ix.Name} : (s.insert a).contains a = true := by
  rw [Std.HashSet.contains_insert, BEq.rfl, Bool.true_or]

theorem map_insert_keep {s : Std.HashMap Ix.Name String} {a y : Ix.Name} {v : String}
    (h : s.contains y = true) : (s.insert a v).contains y = true := by
  rw [Std.HashMap.contains_insert, h, Bool.or_true]

theorem map_insert_hit {s : Std.HashMap Ix.Name String} {a : Ix.Name} {v : String} :
    (s.insert a v).contains a = true := by
  rw [Std.HashMap.contains_insert, BEq.rfl, Bool.true_or]

theorem ef_pure {d : DriverAcc} {x : Array Ix.Name} {b : Bool} {y : Ix.Name} (h : ExtraOrFail d.cenv y) :
    ExtraOrFail (pure (d, x, b) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv y := h

/-- A loop that marks each name an extra name or a failure, then its continuation. -/
theorem loop_marks {β : Type} (xs : Array Ix.Name) (init : DriverAcc)
    (f : Ix.Name → DriverAcc → Id (ForInStep DriverAcc)) (k : DriverAcc → Id β) (Q : β → Prop)
    (yields : ∀ x s, ∃ s', f x s = .yield s')
    (keep : ∀ x s y, ExtraOrFail s.cenv y → ExtraOrFail (f x s).value.cenv y)
    (hit : ∀ x s, ExtraOrFail (f x s).value.cenv x) {y : Ix.Name} (hy : y ∈ xs)
    (cont : ∀ L, ExtraOrFail L.cenv y → Q (k L)) : Q (forIn (m := Id) xs init f >>= k) :=
  cont _ (forIn_marks xs init f (fun y s => ExtraOrFail s.cenv y) yields keep hit y hy)

set_option hygiene false in
/-- The promotion's tail keeps a name an extra name or a failure; `x` proves
it of the state the tail starts from. -/
local macro "ef_tail" x:tacticSeq : tactic => `(tactic| (
  split
  · exact ef_pure (ExtraOrFail.mono (failAuxPromotion_step _ _ _ (fun _ _ _ => True)).1.2.2 (by $x))
  · split
    · exact ef_pure (ExtraOrFail.mono (failAuxPromotion_step _ _ _ (fun _ _ _ => True)).1.2.2 (by $x))
    · split
      · exact ef_pure (ExtraOrFail.mono (finishAuxPromotion_step _ _ _ _ (fun _ _ _ => True)).1.2.2 (by $x))
      · exact ef_pure (ExtraOrFail.mono (finishAuxPromotion_step _ _ _ _ (fun _ _ _ => True)).1.2.2 (by $x))))

set_option hygiene false in
/-- A marking loop's steps (`recordFailure`'s, or the extra names'). -/
local macro "marks_steps" : tactic => `(tactic| (
  · intro _ _ _ h
    rcases h with h | h
    · first | exact .inl h | exact .inl (set_insert_keep h)
    · first | exact .inr h | exact .inr (map_insert_keep h)
  · intro _ _
    first | exact .inl set_insert_hit | exact .inr map_insert_hit))

set_option hygiene false in
/-- A loop over registered names, then the rest. -/
local macro "names_loop" : tactic => `(tactic|
  refine loop_bind _ _ _ _ (fun _ => True) (fun r : DriverAcc × Array Ix.Name × Bool => ExtraOrFail r.1.cenv y) trivial
    (fun _ _ _ _ => trivial) fun _ _ => ?_)

set_option hygiene false in
/-- The extra names' loop, then the promotion's tail. -/
local macro "extras_tail" : tactic => `(tactic| (
  refine loop_marks _ _ _ _ (fun r : DriverAcc × Array Ix.Name × Bool => ExtraOrFail r.1.cenv y) (fun _ _ => ⟨_, rfl⟩) ?_ ?_ hy fun L hL => ?_
  marks_steps
  ef_tail exact hL))

/-- **A promoted block's application leaves each unresolved name of its
cross-SCC subset an extra name or a failure**: a conflicting subset records
them as failures, a merged one adds them to the extra names, and the
promotion's tail moves them as `Mono` says. -/
theorem applyAuxBlockOutcome_cross_extras (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (clo : Ix.Name) (result : BlockResult) (cache : BlockState) (published : Ix.Compile.Pass.Published)
    (cn : Array Ix.Name) (cf : Option (Array Ix.Name × String)) (im : Option String)
    (na : Option (BlockResult × BlockState)) (nf : Option String) {y : Ix.Name} (hy : y ∈ cn) :
    ExtraOrFail (applyAuxBlockOutcome acc lo all
      (.promoted (some (clo, result, cache, published)) cn cf im na nf)).1.cenv y := by
  unfold applyAuxBlockOutcome
  simp only [Id.run]
  rcases cf with _ | ⟨names, msg⟩ <;> dsimp only <;> split
  all_goals first
    | (ef_tail
        refine loop_marks _ _ _ pure (fun L => ExtraOrFail L.cenv y) (fun _ _ => ⟨_, rfl⟩) ?_ ?_ hy
          fun L hL => hL
        marks_steps)
    | (split
       · names_loop
         extras_tail
       · names_loop
         names_loop
         extras_tail)


/-! ## The closure's names -/

/-- `x` is a name of the closure `sub`. -/
def InSub (sub : Ix.Environment) (x : Ix.Name) : Prop := (sub.consts.get? x).isSome = true

theorem InSub.congr {sub : Ix.Environment} {x y : Ix.Name} (h : InSub sub x) (e : (x == y) = true) :
    InSub sub y := by
  unfold InSub at *
  rw [Std.HashMap.get?_eq_getElem?] at *
  rwa [← Std.HashMap.getElem?_congr e]

theorem reaches_of_sub {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x : Ix.Name} (hx : InSub sub x) : Reaches env roots x := by
  refine Classical.byContradiction fun hr => ?_
  unfold InSub at hx
  rw [(hcl x).2 hr] at hx
  cases hx

theorem sub_of_reaches {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x : Ix.Name} (hr : Reaches env roots x)
    (he : (env.consts.get? x).isSome = true) : InSub sub x := by
  unfold InSub
  rw [(hcl x).1 hr]
  exact he

/-- A constructor references its inductive (`Ix.graphConst`). -/
theorem refsOf_ctor (cv : Ix.ConstructorVal) : (refsOf (.ctorInfo cv)).contains cv.induct = true := by
  unfold refsOf Ix.GraphM.run
  simp only [Ix.graphConst]
  exact Std.HashSet.contains_insert_self

/-- **An owned name of the closure has its member in the closure**: a
member's name is one, and a constructor's inductive is reached from it. -/
theorem owned_sub {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {roots : List Ix.Name} {sub : Ix.Environment} (h : compileReport env = .ok (ixe, failures))
    (hcl : IsClosure env roots sub) {E : Ix.Environment} (hE : ∀ x, E.get? x = env.consts.get? x)
    {A : Ix.Set Ix.Name} {n : Ix.Name} (hn : InSub sub n) (ho : Ix.Cert.Claims.Owned E A n) :
    ∃ m, A.contains m = true ∧ InSub sub m ∧
      ((n == m) = true ∨ ∃ iv c, env.consts.get? m = some (.inductInfo iv) ∧ c ∈ iv.ctors ∧ (c == n) = true) := by
  rcases ho with ⟨m, hm, e⟩ | ⟨I, iv, c, hI, hiv, hc, e⟩
  · exact ⟨m, hm, hn.congr e, .inl e⟩
  · rw [hE] at hiv
    obtain ⟨cv, hcv, hind⟩ := ctorsBelong h I iv hiv c hc
    have rc : Reaches env roots c := Closure.reaches_congr (reaches_of_sub hcl hn) e
    have ri : Reaches env roots cv.induct := .step rc ⟨_, hcv, .inl (refsOf_ctor cv)⟩
    exact ⟨I, hI, sub_of_reaches hcl (Closure.reaches_congr ri hind) (by rw [hiv]; rfl),
      .inr ⟨iv, c, hiv, hc, BEq.symm e⟩⟩


/-- A claim of a block compile is its key or one of its projections' names. -/
theorem claim_name {k n : Ix.Name} {r : BlockResult} {a : Address} {b : ByteArray}
    (h : (n, a, b) ∈ claimWrites k r) : n = k ∨ ∃ row ∈ r.projections, row.1 = n := by
  unfold claimWrites at h
  split at h
  · left
    simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at h
    exact h.1
  · right
    obtain ⟨row, hrow, he⟩ := Array.mem_map.1 h
    exact ⟨row, hrow, (Prod.mk.inj he).1⟩

/-- An `Id` loop that stops with `some false` at the first name failing `q`
returns `none`, every name passing, or `some false`. -/
theorem forIn_all_pass (q : Ix.Name → Bool) :
    ∀ (l : List Ix.Name),
      ((forIn (m := Id) l ((none : Option Bool), ()) (fun n _ =>
        if q n = true then pure (ForInStep.done (some false, ())) else pure (ForInStep.yield (none, ())))).1 = none ∧
          ∀ a ∈ l, q a = false) ∨
      (forIn (m := Id) l ((none : Option Bool), ()) (fun n _ =>
        if q n = true then pure (ForInStep.done (some false, ())) else pure (ForInStep.yield (none, ())))).1 = some false
  | [] => .inl ⟨rfl, fun _ h => nomatch h⟩
  | a :: l => by
    rw [List.forIn_cons]
    cases hq : q a
    · simp only [Bool.false_eq_true, ↓reduceIte, pure, bind]
      rcases forIn_all_pass q l with ⟨h, hl⟩ | h
      · refine .inl ⟨h, fun b hb => ?_⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hq
        · exact hl b hb
      · exact .inr h
    · simp only [↓reduceIte, pure, bind]
      exact .inr trivial

/-- An image block's members are all heads. -/
theorem isImageBlock_heads {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    (h : Ix.Compile.Pass.isImageBlock cenv all = true) : ∀ a ∈ all.toList, cenv.p3Heads.contains a = true := by
  unfold Ix.Compile.Pass.isImageBlock at h
  simp only [Id.run] at h
  split at h
  · cases h
  · rw [Std.HashSet.forIn_eq_forIn_toList] at h
    rcases forIn_all_pass (fun n => !cenv.p3Heads.contains n) all.toList with ⟨-, hall⟩ | h0
    · intro a ha
      simpa using hall a ha
    · generalize forIn (m := Id) all.toList _ _ = r at h h0
      obtain ⟨r1, r2⟩ := r
      simp only at h0
      subst h0
      cases h


/-! ## The driver's environment -/

theorem view_get (E : Ix.Environment) (x : Ix.Name) :
    ({ consts := {}, fallback? := some E.get? } : Ix.Environment).get? x = E.get? x := by
  simp [Ix.Environment.get?]

theorem input_get (consts : Std.HashMap Ix.Name Ix.ConstantInfo) (x : Ix.Name) :
    ({ consts } : Ix.Environment).get? x = consts.get? x := by
  unfold Ix.Environment.get?
  split <;> simp_all

/-- **The driver's view of the input carries its names** (the twelfth check). -/
theorem namedEnv_view {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    Ix.Cert.Claims.NamedEnv { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } := by
  intro x ci hx
  rw [view_get, input_get, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hx
  obtain ⟨k, hxk, hk⟩ := hx
  exact PartialEquivBEq.trans (inputsNamed h k ci hk) (BEq.symm hxk)

/-! ## What the final environment says -/

/-- What `compileReport`'s checks say of the driver's final environment
`cenv`: each head is an input name in the changed set (the eleventh check),
and each recorded failure is an input name (the fourteenth) and reported. -/
structure Final (env : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (cenv : CompileEnv) : Prop where
  changed : ∀ (n : ExactName) (k : Ix.Name), cenv.p3Heads.get? n = some k →
    (Ix.Compile.ChangedSet.ofCompile env ixe).contains n = true
  headInput : ∀ (n : ExactName) (k : Ix.Name), cenv.p3Heads.get? n = some k → (env.consts.get? n).isSome = true
  failInput : ∀ x : Ix.Name, cenv.ungrounded.contains x = true → (env.consts.get? x).isSome = true
  failed : ∀ x : Ix.Name, cenv.ungrounded.contains x = true → failures.failed x = true

/-- A key an `ExactName` map holds has a value (typed: `Ix.Name` arguments
elaborate as `ExactName`). -/
theorem exact_get_of_contains {α : Type} {m : Std.HashMap ExactName α} {x : ExactName}
    (h : m.contains x = true) : ∃ k, m.get? x = some k := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  rw [Std.HashMap.get?_eq_getElem?]
  exact Option.isSome_iff_exists.mp h

/-- **No name the closure reaches is a head** of a state the final
environment follows. -/
theorem not_head {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {roots : List Ix.Name}
    {sub : Ix.Environment} {cenv : CompileEnv} (hf : Final env ixe failures cenv)
    (hcl : IsClosure env roots sub) (nofail : NoFailure failures sub)
    (avoids : (Ix.Compile.ChangedSet.ofCompile env ixe).Avoids sub) {c : CompileEnv} (hm : Mono c cenv)
    {x : Ix.Name} (hx : Reaches env roots x) : c.p3Heads.contains x = false := by
  cases hc : c.p3Heads.contains x with
  | false => rfl
  | true =>
    exfalso
    rcases hm.2.1 x hc with hh | hu
    · obtain ⟨k, hk⟩ := exact_get_of_contains hh
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (sub_of_reaches hcl hx (hf.headInput x k hk))
      have := avoids x ci hci
      rw [hf.changed x k hk] at this
      cases this
    · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (sub_of_reaches hcl hx (hf.failInput x hu))
      have := nofail x ci hci
      rw [hf.failed x hu] at this
      cases this


/-- An entry of the ground graph read with a default: an edge of the input. -/
theorem ground_getD_dependsOn {env : Ix.Environment} {a r : Ix.Name}
    (h : ((groundSplit { consts := env.consts }).1.getD a {}).contains r = true) : DependsOn env a r := by
  rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?] at h
  cases hg : (groundSplit { consts := env.consts }).1.get? a with
  | none => rw [hg] at h; simp at h
  | some rs => rw [hg] at h; exact groundSplit_dependsOn (env := { consts := env.consts }) hg h

/-- **`HookFree` at a block of the closure**: no reference of the block
holding its key is a head (each is reached from the closure), and no member
is (so it is not an image block). -/
theorem hookFree_of_sub {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {roots : List Ix.Name}
    {sub : Ix.Environment} {cenv : CompileEnv} (hf : Final env ixe failures cenv)
    (hcl : IsClosure env roots sub) (nofail : NoFailure failures sub)
    (avoids : (Ix.Compile.ChangedSet.ofCompile env ixe).Avoids sub) {cenv₀ : CompileEnv} {sched : FoldSchedule}
    {snap : DriverAcc} {rep : Ix.Name} {all : Ix.Set Ix.Name}
    (hsnap : Reach (Ix.CondenseM.run (groundSplit { consts := env.consts }).1)
      (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched).acc snap)
    (hm : Mono snap.cenv cenv)
    (hall : (Ix.CondenseM.run (groundSplit { consts := env.consts }).1).blocks.get? rep = some all)
    (hsub : ∀ x, all.contains x = true → InSub sub x) : HookFree snap.cenv all (blockKey rep all) := by
  have hkey := blockKey_mem (lo := rep) (condense_nonempty hall)
  obtain ⟨rs, hrs, -⟩ := condense_blockRefs hall
  obtain ⟨refs, rep', all', hinit, hall', hrefs', hkey'⟩ :=
    init_p3BlockRefs (cenv := cenv₀) (sched := sched) hall hrs fun _ _ hb => condense_nonempty hb
  have hsub' : ∀ x, all'.contains x = true → InSub sub x := fun x hx =>
    closure_path hcl (condense_scc hall' hkey' hx) (hsub _ hkey)
  refine ⟨Ix.Cert.PassHooks.prepareBlock_unreferenced _ _ _ refs (by rw [reach_p3BlockRefs hsnap]; exact hinit)
    fun r hr => ?_, ?_⟩
  · obtain ⟨rs', hrs'', hsplit⟩ := condense_blockRefs hall'
    rw [hrefs'] at hrs''
    cases hrs''
    obtain ⟨a, ha, har⟩ := hsplit r (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList hr))
    exact not_head hf hcl nofail avoids hm (.step (reaches_of_sub hcl (hsub' a ha)) (ground_getD_dependsOn har))
  · cases hi : Ix.Compile.Pass.isImageBlock snap.cenv all with
    | false => rfl
    | true =>
      exfalso
      have hl : all.toList.contains (blockKey rep all) = true := by
        rw [Std.HashSet.contains_toList]; exact hkey
      obtain ⟨a, ha, -⟩ := List.contains_iff_exists_mem_beq.mp hl
      have hin := hsub a (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_of_mem_toList ha))
      have := not_head hf hcl nofail avoids hm (reaches_of_sub hcl hin)
      rw [isImageBlock_heads hi a ha] at this
      cases this

/-- **A cross-SCC claim of the closure is refuted** by the tenth check: its
name, or its constructor's inductive, is an extra name or a failure. -/
theorem cross_refuted {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {roots : List Ix.Name}
    {sub : Ix.Environment} {cenv : CompileEnv} (h : compileReport env = .ok (ixe, failures))
    (hu : compileUnchecked env = .ok (ixe, failures, cenv)) (hcl : IsClosure env roots sub)
    (nofail : NoFailure failures sub) {E : Ix.Environment} (hE : ∀ x, E.get? x = env.consts.get? x)
    {cn : Array Ix.Name} (marks : ∀ y ∈ cn, ExtraOrFail cenv y) {n : ExactName} {a : Address}
    (hn : cenv.nameToAddr.get? n = some a) (hnaux : cenv.auxNameToAddr.contains n = false)
    (hs : InSub sub n) (hc : n ∈ cn ∨ Ix.Cert.Claims.Owned E (cn.foldl (fun s n => s.insert n) {}) n) :
    False := by
  obtain ⟨cenv', hu', hx⟩ := noCrossClaims h
  rw [hu] at hu'
  cases hu'
  obtain ⟨hext, hctor⟩ := hx n a hn hnaux
  have nf : ∀ x, InSub sub x → cenv.ungrounded.contains x = true → False := fun x hx hf => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hx
    have := nofail x ci hci
    rw [compileUnchecked_ungrounded hu hf] at this
    cases this
  rcases hc with hc | ho
  · rcases marks n hc with he | hf
    · rw [he] at hext; cases hext
    · exact nf n hs hf
  · obtain ⟨m, hm, hms, hrel⟩ := owned_sub h hcl hE hs ho
    obtain ⟨y, hy, ey⟩ := foldl_insert_mem hm
    rcases marks y hy with he | hf
    · rcases hrel with e | ⟨iv, c, hiv, hcm, hcn⟩
      · rw [Std.HashSet.contains_congr (PartialEquivBEq.trans ey (BEq.symm e))] at he
        rw [he] at hext; cases hext
      · rw [Std.HashSet.contains_congr ey] at he
        rw [extraCtors_contains he hiv hcm hcn] at hctor
        cases hctor
    · exact nf m hms (by rwa [Std.HashMap.contains_congr ey] at hf)



/-! ## `HookFree` discharged -/

/-- **What the checks say of the final environment** (`Final`): the eleventh
check (`headsChanged`, `foreignHead_regenerated`, `regeneratedNames_spec`),
the fourteenth (`failuresInput`) and `compileUnchecked_ungrounded`. -/
theorem final_of_report {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) {cenv : CompileEnv}
    (hu : compileUnchecked env = .ok (ixe, failures, cenv)) : Final env ixe failures cenv := by
  obtain ⟨c₁, hu₁, hch⟩ := headsChanged h
  obtain ⟨c₂, hu₂, hin⟩ := failuresInput h
  obtain ⟨c₃, hu₃, hc⟩ := compileReport_ok h
  rw [hu] at hu₁ hu₂ hu₃
  cases hu₁
  cases hu₂
  cases hu₃
  refine ⟨hch, fun n k hk => ?_, hin, fun x hx => compileUnchecked_ungrounded hu hx⟩
  obtain ⟨_, _, _, -, -, hd⟩ :=
    regeneratedNames_spec (foreignHead_regenerated (checkReport_ok hc).2.2.2.2.2.2.2.2.2.2.1 n k hk)
  rw [Bool.and_eq_true] at hd
  exact hd.2

/-- **B9b with `HookFree` discharged**: when `compileReport` returns, every
resolved name `n ↦ a` outside the final aux map that a closure `sub` holds,
where `sub` avoids the changed set and has no failure, is published at `a`
and is a primary claim of `runBlock` on a whole condensation block of `sub`
under its key, against a state the fold reached that the final environment
follows; its bytes `b` are stored at `a`; Pass 3's hooks are identities at
that compile (`HookFree`), and the claim is the block compile's
(`BlockCompiled`). -/
theorem compileReport_hookFree {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {roots : List Ix.Name} {sub : Ix.Environment} (h : compileReport env = .ok (ixe, failures))
    (hcl : IsClosure env roots sub) (nofail : NoFailure failures sub)
    (avoids : (Ix.Compile.ChangedSet.ofCompile env ixe).Avoids sub) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult) (c : BlockState)
          (layout : Option Ixon.AuxLayout) (p : Ix.Compile.Pass.Published) (b : ByteArray),
          Reach blocks (FoldState.init cenv₀ blocks sched).acc snap ∧ blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧ (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
          runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout, p) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          HookFree snap.cenv all (blockKey rep all) ∧ BlockCompiled snap.cenv all (blockKey rep all) n a b := by
  obtain ⟨cenv, hu, pub⟩ := Ix.Cert.resolvedPublished h
  have hf := final_of_report h hu
  obtain ⟨bytes, cenv₀, sched, -, henv, prov⟩ := compileUnchecked_provenance hu
  refine ⟨cenv, _, cenv₀, sched, hu, rfl, fun n a hn hnaux hs => ⟨pub n a hn, ?_⟩⟩
  rcases prov n a hn with hx | ⟨b, hc, hb⟩
  · rw [hnaux] at hx; cases hx
  obtain ⟨snap, pre, rep, all, hsnap, -, hm, hall, hpost, hclaim⟩ := hc
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env hsnap, henv, view_get, input_get]
  have hnamed : Ix.Cert.Claims.NamedEnv snap.cenv.env := by
    rw [reach_env hsnap, henv]
    exact namedEnv_view h
  have hfinal : Mono snap.cenv cenv := hm.trans ((applyAuxBlockOutcome_mono _ _ _ _).trans hpost)
  generalize ho : auxBlockOutcome snap.cenv (blockKey rep all) all = o at hclaim hpost
  cases o with
  | compiled r c p =>
    obtain ⟨layout, hr⟩ := auxBlockOutcome_compiled ho
    obtain ⟨m, hmA, hms⟩ : ∃ m, all.contains m = true ∧ InSub sub m := by
      rcases claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact ⟨_, blockKey_mem (condense_nonempty hall), e ▸ hs⟩
      · obtain ⟨m, hm, hms, -⟩ :=
          owned_sub h hcl hE (e ▸ hs) (Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
        exact ⟨m, hm, hms⟩
    have hsub : ∀ x, all.contains x = true → InSub sub x := fun x hx =>
      closure_path hcl (condense_scc hall hmA hx) hms
    have hfree := hookFree_of_sub hf hcl nofail avoids hsnap hfinal hall hsub
    exact ⟨snap, rep, all, r, c, layout, p, b, hsnap, hall, hfinal, hsub, hr, hclaim, hb, hfree,
      hookFree_compiled hfree hr hclaim⟩
  | promoted cs cn cf im na nf =>
    rcases cs with _ | ⟨clo, r, c, p⟩
    · exact False.elim hclaim
    · exfalso
      obtain ⟨layout, hclo, hr⟩ := auxBlockOutcome_cross_names ho
      have marks : ∀ y ∈ cn, ExtraOrFail cenv y := fun y hy =>
        (applyAuxBlockOutcome_cross_extras pre _ all clo r c p cn cf im na nf hy).mono hpost
      refine cross_refuted h hu hcl nofail hE marks hn hnaux hs ?_
      rcases claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact .inl (e ▸ hclo)
      · exact .inr (e ▸ Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
  | failed msg => exact False.elim hclaim

end Ix.Cert.HookFree
