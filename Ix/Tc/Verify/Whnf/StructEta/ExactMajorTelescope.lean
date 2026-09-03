import Ix.Tc.Verify.Whnf.StructEta.ScopedTelescope

/-!
# Exact major-premise telescope restoration

The semantic telescope proof in `ScopedTelescope` tracks temporary binders
through an arbitrary well-formed callback table.  Concrete generated
recursors need a sharper fact: when every inspected term is already a
forall, WHNF takes its read-only quick exit, the major declaration is
physically loaded, and the finalizer removes exactly the binders introduced
by the scan, `getMajorInductiveId` returns the caller's complete checker
state unchanged.

This module proves that fact from:

* an exact relation generated only by successful `pushLocal` calls;
* the inverse `popLocal` transition and exact `restoreDepth` iteration;
* a pure syntactic certificate for the fixed prefix and direct major; and
* the production forall-WHNF and eager-lookup execution equations.

No semantic state model is widened to admit the temporary telescope.
-/

namespace Ix.Tc

/-- Exact state stack generated exclusively by successful `pushLocal`
calls.  Unlike `ScratchLamExtension`, this relation retains the operational
predecessor state needed to prove exact restoration. -/
inductive ExactLocalExtension (base : TcState .anon) :
    Nat → TcState .anon → Prop
  | zero : ExactLocalExtension base 0 base
  | succ {n : Nat} {current next : TcState .anon} {ty : KExpr .anon} :
      ExactLocalExtension base n current →
      TcM.pushLocal ty current = .ok () next →
      ExactLocalExtension base (n + 1) next

/-- Popping immediately after a successful lambda-local push reconstructs
every field of the predecessor checker state, including its context digest
and digest stack. -/
theorem TcM.popLocal_pushLocal_exact
    {ty : KExpr .anon} {before after : TcState .anon}
    (run : TcM.pushLocal ty before = .ok () after) :
    TcM.popLocal after = .ok () before := by
  simp only [TcM.pushLocal, get, set, pure] at run
  cases run
  unfold TcM.popLocal
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ _ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) _ = .ok _ _ from rfl]
  change (set _ : TcM .anon Unit) _ = _
  simp [set]
  cases before
  rfl

namespace ExactLocalExtension

/-- Local pushes do not change the kernel environment. -/
theorem env_eq {base : TcState .anon} :
    ∀ {n after}, ExactLocalExtension base n after → after.env = base.env
  | _, _, .zero => rfl
  | _, _, .succ prior run => by
      rw [(scratch_pushLocal_run run).1, env_eq prior]

/-- The operational extension index is the exact context-size delta. -/
theorem ctx_size {base : TcState .anon} :
    ∀ {n after}, ExactLocalExtension base n after →
      after.ctx.size = base.ctx.size + n
  | _, _, .zero => by omega
  | _, _, .succ prior run => by
      rw [(scratch_pushLocal_run run).2.1, Array.size_push, ctx_size prior]
      omega

/-- The explicit restoration loop removes an exact local extension and
reconstructs the complete base state. -/
theorem restoreDepth_go_exact {base : TcState .anon} {n after}
    (extension : ExactLocalExtension base n after) :
    TcM.restoreDepth.go base.ctx.size n after = .ok () base := by
  induction extension with
  | zero => rfl
  | @succ n current after ty prior pushRun ih =>
      have gt : after.ctx.size > base.ctx.size := by
        rw [ctx_size (.succ prior pushRun)]
        omega
      rw [TcM.restoreDepth.go.eq_2]
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ after = _
      unfold EStateM.bind
      rw [show (get : TcM .anon (TcState .anon)) after =
        .ok after after from rfl]
      simp only [gt, if_true]
      change EStateM.bind TcM.popLocal
        (fun _ => TcM.restoreDepth.go base.ctx.size _) after = _
      unfold EStateM.bind
      rw [TcM.popLocal_pushLocal_exact pushRun]
      exact ih

/-- Public `restoreDepth` computes exactly the extension index and then
returns the complete base state. -/
theorem restoreDepth_exact {base : TcState .anon} {n after}
    (extension : ExactLocalExtension base n after) :
    TcM.restoreDepth base.ctx.size after = .ok () base := by
  rw [TcM.restoreDepth_apply]
  have count : after.ctx.size - base.ctx.size = n := by
    rw [ctx_size extension]
    omega
  rw [count]
  exact restoreDepth_go_exact extension

end ExactLocalExtension

namespace TcM

/-- A physically loaded constant takes the eager, state-preserving lookup
path; no lazy-ingress authority is involved. -/
theorem tryGetConst_loaded_run
    {state : TcState .anon} {id : KId .anon} {constant : KConst .anon}
    (loaded : state.env.get? id = some constant) :
    TcM.tryGetConst id state = .ok (some constant) state := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state from rfl]
  simp only [loaded]
  rfl

end TcM

namespace RecM

/-- Pure syntactic certificate for a fixed forall prefix immediately followed
by a forall whose domain has a constant head.  Declaration classification is
kept separate and witnessed by the eager environment lookup. -/
def directMajorAfterForalls : Nat → KExpr .anon → Option (KId .anon)
  | 0, .all _ _ dom _ _ =>
      match dom.collectSpine.1 with
      | .const id _ _ => some id
      | _ => none
  | fuel + 1, .all _ _ _ body _ => directMajorAfterForalls fuel body
  | _, _ => none

/-- A method table is observationally pure on the production forall quick
exit. -/
def ForallWhnfPure (methods : Methods .anon) : Prop :=
  ∀ (name bi dom body info) (state : TcState .anon),
    methods.whnf (.all name bi dom body info) state =
      .ok (.all name bi dom body info) state

/-- Peeling a syntactically certified prefix performs exactly one local push
per forall and leaves a direct-major certificate for the resulting term. -/
theorem peelMajorForalls_direct_exact
    {methods : Methods .anon} (pureForall : ForallWhnfPure methods) :
    ∀ (fuel : Nat) {source : KExpr .anon} {id : KId .anon}
        {base current : TcState .anon} {n : Nat},
      ExactLocalExtension base n current →
      directMajorAfterForalls fuel source = some id →
      ∃ result after,
        (peelMajorForalls fuel source).run methods current =
            .ok result after ∧
          ExactLocalExtension base (n + fuel) after ∧
          directMajorAfterForalls 0 result = some id
  | 0, source, id, base, current, n, extension, shape => by
      exact ⟨source, current, rfl, by simpa using extension, shape⟩
  | fuel + 1, source, id, base, current, n, extension, shape => by
      cases source <;> try simp [directMajorAfterForalls] at shape
      case all name bi dom body info =>
          obtain ⟨afterPush, pushRun⟩ := scratch_pushLocal_ok dom current
          obtain ⟨result, after, recursiveRun, recursiveExtension,
              resultShape⟩ :=
            peelMajorForalls_direct_exact pureForall fuel
              (.succ extension pushRun) shape
          refine ⟨result, after, ?_, ?_, resultShape⟩
          · rw [scratch_peelMajorForalls_succ_run,
              scratch_bind_ok (pureForall name bi dom body info current)]
            rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self,
              scratch_bind_ok pushRun, recursiveRun]
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              recursiveExtension

/-- Invert the zero-prefix certificate into the exact forall and spine
equations consumed by the production scan step. -/
theorem directMajorAfterForalls_zero_inv
    {source : KExpr .anon} {id : KId .anon}
    (shape : directMajorAfterForalls 0 source = some id) :
    ∃ name bi dom body info us headInfo args,
      source = .all name bi dom body info ∧
        dom.collectSpine = (.const id us headInfo, args) := by
  cases source <;> try simp [directMajorAfterForalls] at shape
  case all name bi dom body info =>
    rcases spine : dom.collectSpine with ⟨head, args⟩
    cases head <;> simp_all

/-- A direct certified major premise is found in the first bounded scan step,
using only a pure forall WHNF and a physically loaded inductive declaration. -/
theorem scanMajorInductive_direct_exact
    {methods : Methods .anon} (pureForall : ForallWhnfPure methods)
    {source : KExpr .anon} {id : KId .anon}
    {base current : TcState .anon} {n : Nat}
    (extension : ExactLocalExtension base n current)
    (shape : directMajorAfterForalls 0 source = some id)
    (loaded : ∃ lvls params indices memberIdx isUnsafe block ty ctors,
      base.env.get? id =
        some (.indc () () lvls params indices isUnsafe block memberIdx ty
          ctors ())) :
    (scanMajorInductive 9 source).run methods current = .ok id current := by
  obtain ⟨name, bi, dom, body, info, us, headInfo, args, rfl, spine⟩ :=
    directMajorAfterForalls_zero_inv shape
  obtain ⟨lvls, params, indices, memberIdx, isUnsafe, block, ty, ctors,
    loaded⟩ := loaded
  have currentLoaded :
      current.env.get? id =
        some (.indc () () lvls params indices isUnsafe block memberIdx
          ty ctors ()) := by
    rw [ExactLocalExtension.env_eq extension]
    exact loaded
  have lookup := TcM.tryGetConst_loaded_run currentLoaded
  rw [show 9 = 8 + 1 by omega,
    scratch_scanMajorInductive_succ_run,
    scratch_bind_ok (pureForall name bi dom body info current)]
  simp only [scanMajorInductiveStep, spine]
  rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self,
    scratch_bind_ok lookup]
  rfl

/-- Exact state-neutrality of the production major scanner on a certified
direct-major telescope. -/
theorem getMajorInductiveId_direct_exact
    {methods : Methods .anon} (pureForall : ForallWhnfPure methods)
    {source : KExpr .anon} {skip : UInt64} {id : KId .anon}
    {state : TcState .anon}
    (shape : directMajorAfterForalls skip.toNat source = some id)
    (loaded : ∃ lvls params indices memberIdx isUnsafe block ty ctors,
      state.env.get? id =
        some (.indc () () lvls params indices isUnsafe block memberIdx ty
          ctors ())) :
    (getMajorInductiveId source skip).run methods state = .ok id state := by
  obtain ⟨result, after, peelRun, extension, resultShape⟩ :=
    peelMajorForalls_direct_exact (methods := methods) pureForall skip.toNat
      (ExactLocalExtension.zero (base := state)) shape
  have scanRun :=
    scanMajorInductive_direct_exact pureForall extension resultShape loaded
  have bodyRun :
      (((do
        let ty ← peelMajorForalls skip.toNat source
        scanMajorInductive 9 ty) : RecM .anon (KId .anon)).run methods) state =
          .ok id after := by
    rw [ReaderT.run_bind, scratch_bind_ok peelRun, scanRun]
  have cleanup := ExactLocalExtension.restoreDepth_exact extension
  rw [scratch_getMajorInductiveId_run]
  exact scratch_tryFinally_ok bodyRun cleanup

end RecM
end Ix.Tc
