import Ix.Cert.Resolution
import Ix.Cert.Claims
import Ix.Cert.Condense
import Ix.Cert.Closure

/-! # The claims of a closure

`Ix.Cert.Resolution.compileReport_claim` gives each resolved name as a
primary claim of a block compile (`BlockCompiled`). This file places the block
in the closure, for every such name of a closure `sub` that has no failure
(`compileReport_owned`): a compiled block's claim is its key or a projection
name, owned by a member (`Claims.runBlock_owned`, the driver's view of the
input carrying its names, `namedEnv_view`), so the block is in the closure
(`owned_sub`, `Condense.condense_scc`, `Condense.closure_path`). -/

namespace Ix.Cert.ClosureClaims

open Ix Ix.CompileM Ix.Cert.Resolution Ix.Cert.Condense
open Ix.Compile.ExactKey (ExactName)

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

/-- **The driver's view of the input carries its names** (the eighth check). -/
theorem namedEnv_view {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    Ix.Cert.Claims.NamedEnv { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } := by
  intro x ci hx
  rw [view_get, input_get, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hx
  obtain ⟨k, hxk, hk⟩ := hx
  rw [inputsNamed h k ci hk]
  exact BEq.symm hxk

/-- **The claims of a closure**: when `compileReport` returns, every resolved name
`n ↦ a` that a closure `sub` holds is published at `a` and is a
primary claim of `runBlock` on a whole condensation block of `sub` under its key,
against a state of the fold's own run (`OnRun`) that the final environment
follows; its bytes `b` are stored at `a`, and the claim is the block compile's
(`BlockCompiled`). -/
theorem compileReport_owned {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {roots : List Ix.Name} {sub : Ix.Environment} (h : compileReport env = .ok (ixe, failures))
    (hcl : IsClosure env roots sub) :
    ∃ (cenv : CompileEnv) (blocks : Ix.CondensedBlocks) (cenv₀ : CompileEnv) (sched : FoldSchedule),
      compileUnchecked env = .ok (ixe, failures, cenv) ∧
      blocks = Ix.CondenseM.run (groundSplit { consts := env.consts }).1 ∧
      FoldRun { consts := env.consts } blocks cenv cenv₀ sched ∧
      ∀ (n : ExactName) (a : Address), cenv.nameToAddr.get? n = some a →
        (sub.consts.get? n).isSome = true →
        (ixe.named.get? n).map (·.addr) = some a ∧
        ∃ (snap : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult) (c : BlockState)
          (b : ByteArray),
          OnRun blocks sched (FoldState.init cenv₀ blocks sched) snap ∧ blocks.blocks.get? rep = some all ∧
          Mono snap.cenv cenv ∧ (∀ x, all.contains x = true → (sub.consts.get? x).isSome = true) ∧
          runBlock snap.cenv all (blockKey rep all) = .ok (r, c) ∧
          (n, a, b) ∈ claimWrites (blockKey rep all) r ∧
          ixe.consts.get? a = some { buf := b, len := b.size } ∧
          BlockCompiled snap.cenv all (blockKey rep all) n a b := by
  obtain ⟨cenv, hu, pub⟩ := Ix.Cert.resolvedPublished h
  obtain ⟨bytes, cenv₀, sched, -, hrun, henv, prov⟩ := compileUnchecked_provenance hu
  refine ⟨cenv, _, cenv₀, sched, hu, rfl, hrun, fun n a hn hs => ⟨pub n a hn, ?_⟩⟩
  obtain ⟨b, hc, hb⟩ := prov n a hn
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
    have hr := auxBlockOutcome_compiled ho
    obtain ⟨m, hmA, hms⟩ : ∃ m, all.contains m = true ∧ InSub sub m := by
      rcases claim_name hclaim with e | ⟨row, hrow, e⟩
      · exact ⟨_, blockKey_mem (condense_nonempty hall), e ▸ hs⟩
      · obtain ⟨m, hm, hms, -⟩ :=
          owned_sub h hcl hE (e ▸ hs) (Ix.Cert.Claims.runBlock_owned hnamed hr row hrow)
        exact ⟨m, hm, hms⟩
    have hsub : ∀ x, all.contains x = true → InSub sub x := fun x hx =>
      closure_path hcl (condense_scc hall hmA hx) hms
    exact ⟨snap, rep, all, r, c, b, hrun_snap, hall, hfinal, hsub, hr, hclaim, hb,
      runBlock_compiled hr hclaim⟩
  | failed msg => exact False.elim hclaim

end Ix.Cert.ClosureClaims
