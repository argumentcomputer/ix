import Ix.Cert.Statement
import IxC.Kernel.Verify.Cached.ReferenceUnder

/-! # Ixon acceptance at the reference level, under an axiom policy

`Ix.Cert.IxonAcceptsRef` is acceptance by the strict fold: it admits no user
axiom. A claim whose context names user axioms (`Ix.ClaimContext.axioms =
some _`) is stated with `IxonAcceptsRefUnder .allowUser` instead: the same
preparation, the role table's admission under the policy
(`Ix.Kernel.Admission.admitAxiomPolicy`: `sorryAx`, `propext` and
`Classical.choice` bound), and the pure fold under the policy at some fuel
(`Ix.Kernel.Cached.AcceptsRefUnder`). At `strict` it is `IxonAcceptsRef`
(`ixonAcceptsRefUnder_strict`). -/

namespace Ix.Cert

open Ix.Kernel (Env)
open Ix.Kernel.Admission (Limits Binding)

/-- **An edge the fold follows that the references do not show**, under the role
table `t`: `GroundEdge` parameterized by `t` instead of the default table. -/
def GroundEdgeAt (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) (a b : Address) : Prop :=
  ixe.consts.contains b = true ∧
    ∃ s, t.addressOf? s = some b ∧
      ((∃ r p, t.addressOf? r = some p ∧ s ∈ groundRoles r ∧
          (p = a ∨ ∃ c, recordAt ixe p = some c ∧ ownerOf p c = a)) ∨
        ∃ c, recordAt ixe a = some c ∧ s ∈ literalRoles c)

/-- `a` is in the compiled closure of the seed addresses `S` under the role table `t`. -/
inductive CompiledReachAt (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) (S : Address → Prop) :
    Address → Prop
  | seed {a : Address} : S a → ixe.consts.contains a = true → CompiledReachAt t ixe S a
  | step {a b : Address} : CompiledReachAt t ixe S a → RecordEdge ixe a b → CompiledReachAt t ixe S b
  | ground {a b : Address} : CompiledReachAt t ixe S a → GroundEdgeAt t ixe a b →
      CompiledReachAt t ixe S b
  | recursor {a b : Address} : CompiledReachAt t ixe S a → RecursorEdge ixe a b →
      CompiledReachAt t ixe S b

/-- `order` lists the compiled closure of `S` under the role table `t`, each record once,
and no record before one it references. -/
structure ClosureOrderAt (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) (S : Address → Prop)
    (order : List Address) : Prop where
  nodup : order.Nodup
  complete : ∀ a, a ∈ order ↔ CompiledReachAt t ixe S a
  ordered : order.Pairwise fun a b => ¬ RecordRef ixe a b

/-- **Ixon acceptance at the reference level under an axiom policy**:
`IxonAcceptsRef`, with the role table admitted under `policy` and the pure
fold run under `policy`. -/
def IxonAcceptsRefUnder (policy : Ix.Kernel.Cached.AxiomPolicy) (binding : Binding) (limits : Limits)
    (ixe : Ixon.Env) (S : Address → Prop) (order : List Address) (envA : Env .anon) : Prop :=
  ClosureOrder ixe S order ∧
    ∃ t pre ev ds, Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t ∧
      Ix.Kernel.Admission.admitAxiomPolicy policy t = .ok () ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (recordsOf ixe order)
        (blobsOf ixe order) (hintsOf ixe) = .ok (ev, ds) ∧
      Ix.Kernel.Cached.AcceptsRefUnder policy .verified ev ds.toList envA

/-- **At `strict` it is `IxonAcceptsRef`.** -/
theorem ixonAcceptsRefUnder_strict {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    IxonAcceptsRefUnder .strict binding limits ixe S order envA ↔
      IxonAcceptsRef binding limits ixe S order envA := by
  constructor
  · rintro ⟨closure, t, pre, ev, ds, admitted, -, prelude, prepared, accepted⟩
    exact ⟨closure, t, pre, ev, ds, admitted, prelude, prepared,
      Ix.Kernel.Cached.acceptsRefUnder_strict.mp accepted⟩
  · rintro ⟨closure, t, pre, ev, ds, admitted, prelude, prepared, accepted⟩
    exact ⟨closure, t, pre, ev, ds, admitted, rfl, prelude, prepared,
      Ix.Kernel.Cached.acceptsRefUnder_strict.mpr accepted⟩

/-- **An `IxonAcceptsRefUnder` whose prepared declarations contain no user
axioms is an `IxonAcceptsRef`.** -/
theorem ixonAcceptsRef_of_under_nil {policy : Ix.Kernel.Cached.AxiomPolicy} {binding : Binding}
    {limits : Limits} {ixe : Ixon.Env} {S : Address → Prop} {order : List Address}
    {envA : Env .anon}
    (h : IxonAcceptsRefUnder policy binding limits ixe S order envA)
    (hnone : ∀ t pre ev ds,
      Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t →
      Ix.Kernel.Reader.preludeFor t = .ok pre →
      Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (recordsOf ixe order)
        (blobsOf ixe order) (hintsOf ixe) = .ok (ev, ds) →
      Ix.Kernel.userAxiomsOfDecls ds.toList = []) :
    IxonAcceptsRef binding limits ixe S order envA := by
  rcases h with ⟨closure, t, pre, ev, ds, admitted, -, prelude, prepared, accepted⟩
  exact ⟨closure, t, pre, ev, ds, admitted, prelude, prepared,
    (Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil (hnone t pre ev ds admitted prelude prepared)).mp
      accepted⟩

end Ix.Cert
