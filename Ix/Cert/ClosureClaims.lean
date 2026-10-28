import Ix.Cert.Resolution
import Ix.Cert.Claims
import Ix.Cert.Condense
import Ix.Cert.Closure

/-! # The claims of a closure

`Ix.Cert.Resolution.compileReport_claim` gives each resolved name outside the
aux map as a primary claim of a block compile (`BlockCompiled`). This file
places the block in the closure, for every such name of a closure `sub` that
has no failure (`compileReport_owned`):

* a claim of a promoted block's cross-SCC subset is refuted: its name, or its
  constructor's inductive, is one of the subset's unresolved names
  (`auxBlockOutcome_cross_names`, `Claims.runBlock_owned`), each of which the
  application leaves an extra name or a failure
  (`applyAuxBlockOutcome_cross_extras`), which the tenth check and `NoFailure`
  refute (`cross_refuted`);
* a compiled block's claim is its key or a projection name, owned by a member
  (`Claims.runBlock_owned`, the driver's view of the input carrying its names,
  `namedEnv_view`), so the block is in the closure (`owned_sub`,
  `Condense.condense_scc`, `Condense.closure_path`). -/

namespace Ix.Cert.ClosureClaims

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
    {clo : Ix.Name} {r : BlockResult} {c : BlockState}
    {cn : Array Ix.Name} {cf : Option (Array Ix.Name × String)} {im : Option String}
    {na : Option (BlockResult × BlockState)} {nf : Option String}
    (h : auxBlockOutcome cenv lo all = .promoted (some (clo, r, c)) cn cf im na nf) :
    ∃ layout : Option Ixon.AuxLayout, clo ∈ cn ∧
      runBlock cenv (cn.foldl (fun s n => s.insert n) {}) clo = .ok (r, c, layout) := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · revert h
    refine loop_bind_mem _ _ _ _ (fun _ : Array Ix.Name => True)
      (fun o : AuxBlockOutcome => o = .promoted (some (clo, r, c)) cn cf im na nf →
        ∃ layout : Option Ixon.AuxLayout, clo ∈ cn ∧
          runBlock cenv (cn.foldl (fun s n => s.insert n) {}) clo = .ok (r, c, layout))
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
  · exact m.2 y h
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
    (clo : Ix.Name) (result : BlockResult) (cache : BlockState)
    (cn : Array Ix.Name) (cf : Option (Array Ix.Name × String)) (im : Option String)
    (na : Option (BlockResult × BlockState)) (nf : Option String) {y : Ix.Name} (hy : y ∈ cn) :
    ExtraOrFail (applyAuxBlockOutcome acc lo all
      (.promoted (some (clo, result, cache)) cn cf im na nf)).1.cenv y := by
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
  rw [inputsNamed h k ci hk]
  exact BEq.symm hxk

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



/-- **The claims of a closure**: when `compileReport` returns, every resolved name
`n ↦ a` outside the final aux map that a closure `sub` with no failure holds is
published at `a` and is a primary claim of `runBlock` on a whole condensation block
of `sub` under its key, against a state of the fold's own run (`OnRun`) that the
final environment follows; its bytes `b` are stored at `a`, and the claim is the
block compile's (`BlockCompiled`). -/
theorem compileReport_owned {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {roots : List Ix.Name} {sub : Ix.Environment} (h : compileReport env = .ok (ixe, failures))
    (hcl : IsClosure env roots sub) (nofail : NoFailure failures sub) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      FoldRun { consts := env.consts } blocks cenv cenv₀ sched ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        cenv.auxNameToAddr.contains n = false → (sub.consts.get? n).isSome = true →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult) (c : BlockState)
          (layout : Option Ixon.AuxLayout) (b : ByteArray),
          OnRun blocks sched (FoldState.init cenv₀ blocks sched) snap ∧ blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧ (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
          runBlock snap.cenv all (blockKey rep all) = .ok (r, c, layout) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          BlockCompiled snap.cenv all (blockKey rep all) n a b := by
  obtain ⟨cenv, hu, pub⟩ := Ix.Cert.resolvedPublished h
  obtain ⟨bytes, cenv₀, sched, -, hrun, henv, prov⟩ := compileUnchecked_provenance hu
  refine ⟨cenv, _, cenv₀, sched, hu, rfl, hrun, fun n a hn hnaux hs => ⟨pub n a hn, ?_⟩⟩
  rcases prov n a hn with hx | ⟨b, hc, hb⟩
  · rw [hnaux] at hx; cases hx
  obtain ⟨snap, pre, rep, all, hrun_snap, -, hm, hall, hpost, hclaim⟩ := hc
  have hsnap := onRun_reach hrun_snap
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env hsnap, henv, view_get, input_get]
  have hnamed : Ix.Cert.Claims.NamedEnv snap.cenv.env := by
    rw [reach_env hsnap, henv]
    exact namedEnv_view h
  have hfinal : Mono snap.cenv cenv := hm.trans ((applyAuxBlockOutcome_mono _ _ _ _).trans hpost)
  generalize ho : auxBlockOutcome snap.cenv (blockKey rep all) all = o at hclaim hpost
  cases o with
  | compiled r c =>
    obtain ⟨layout, hr⟩ := auxBlockOutcome_compiled ho
    obtain ⟨m, hmA, hms⟩ : ∃ m, all.contains m = true ∧ InSub sub m := by
      rcases claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact ⟨_, blockKey_mem (condense_nonempty hall), e ▸ hs⟩
      · obtain ⟨m, hm, hms, -⟩ :=
          owned_sub h hcl hE (e ▸ hs) (Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
        exact ⟨m, hm, hms⟩
    have hsub : ∀ x, all.contains x = true → InSub sub x := fun x hx =>
      closure_path hcl (condense_scc hall hmA hx) hms
    exact ⟨snap, rep, all, r, c, layout, b, hrun_snap, hall, hfinal, hsub, hr, hclaim, hb,
      runBlock_compiled hr hclaim⟩
  | promoted cs cn cf im na nf =>
    rcases cs with _ | ⟨clo, r, c⟩
    · exact False.elim hclaim
    · exfalso
      obtain ⟨layout, hclo, hr⟩ := auxBlockOutcome_cross_names ho
      have marks : ∀ y ∈ cn, ExtraOrFail cenv y := fun y hy =>
        (applyAuxBlockOutcome_cross_extras pre _ all clo r c cn cf im na nf hy).mono hpost
      refine cross_refuted h hu hcl nofail hE marks hn hnaux hs ?_
      rcases claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact .inl (e ▸ hclo)
      · exact .inr (e ▸ Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
  | failed msg => exact False.elim hclaim

end Ix.Cert.ClosureClaims
