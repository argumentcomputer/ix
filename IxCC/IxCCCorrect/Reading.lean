import IxCC.Src.KernelFront.Accept
import IxCK.Kernel.Denotes
import IxCCGrounding.Syntax

/-!
# What the statements read of an admission (`IxCCCorrect.Reading`)

The statements read two things of the kernel's admission of the committed environment: the
kernel environment their `∀ V M : Ix.Kernel.Model V kenv` ranges over, and the key the kernel's
reader gives an address (`EnvReading`). Neither needs the kernel's type checker: the statements
hold in every model whatever the verdict, and the verdict only makes them non-vacuous, which
`Admits` now asks for directly (`HasModel`).

**`readEnv`: IxCK's reader, with the install half of its fold, no type checking.** No entry of
IxCK returns the installed environment without the checker: `Src.KernelFront.accept` reads the
records (`Ix.Kernel.Admission.readStream`) and then runs `Ix.Kernel.Cached.checkDecls`, whose phase A
(`annotDeclStep` over the declarations) installs each declaration with the binder data the kernel's
terms carry, and whose phase B (`checkPendingTasks`), `checkUnits` and the tier's typing
(`checkTierC`) are the checks. So `readEnv` is defined here from IxCK's own functions: the entry's
byte admission (`preflight`, `uniqueKeys`, `authenticate`), the role table (`admitBinding`), the
prelude, the decode (`decodeWithin`), the reader (`readStream` over the logical records), and phase A
alone (`installDecls`), keyed by the same reader context (`streamContext`) the accepted reading has
(`Src.KernelFront.Accepted.ctx`). `IxCCCorrect.AdmitsKernel` proves that IxCK's accept gives this
reading (`readEnv_of_accept`).
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.Grounding (KEnv KKey)

universe w

/-- **What the statements read of an admission**: the kernel environment and the reader's key of an
address. -/
structure EnvReading where
  kenv : KEnv
  keyAt : Ixon.Address → Option KKey

/-- **`kenv` has a model in every set theory** (at universe `w`): the form IxCK's model-existence
theorem gives an accepted environment (`Ix.Kernel.Admission.checkBytesTiered_has_model`) and IxVM's
consistency statement gives its reading (`ConsistentReadOver`). Together with a set theory with the
kernel's universes it makes every statement over the models of `kenv` non-vacuous. -/
def HasModel.{u} (kenv : KEnv) : Prop :=
  ∀ (V : Type u) [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V kenv)

/-- **Phase A of the kernel's declaration fold** (`Ix.Kernel.Cached.checkDecls`): install every
declaration (`annotDeclStep`, at the verified mode), without phase B (the pending checks), the unit
checks, or anything after. -/
def installDecls (ev : Ix.Kernel.Evidences .anon) (ds : Array (Ix.Kernel.Declaration .anon))
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except (Ix.Kernel.CheckError .anon × Nat) KEnv := do
  let (p, _) ← (ds.foldlM (Ix.Kernel.Cached.annotDeclStep .verified ev)
    (0, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty, #[])) { core := cfg.core }
  pure p.2.1.env

/-- **The reading part of the tiered entry** (`Ix.Kernel.Admission.checkBytesTieredUsing` up to
the reader, then `installDecls`): byte admission, the role table, the prelude, the decode, the reader
over the logical records, the install. No typing. -/
def readCore (prelude : Ix.Kernel.RoleTable → Except String (Ix.Kernel.Reader.Prelude .anon))
    (hash : ByteArray → _root_.Address) (binding : Ix.Kernel.Admission.Binding)
    (limits : Ix.Kernel.Admission.Limits) (records : Ix.Kernel.Admission.Records)
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint) :
    Except Ix.Kernel.Admission.TierError KEnv := do
  (Ix.Kernel.Admission.preflight limits records blobs).mapError
    (.entry ∘ Ix.Kernel.Admission.Error.ofBytes)
  (Ix.Kernel.Admission.uniqueKeys records blobs).mapError
    (.entry ∘ Ix.Kernel.Admission.Error.ofBytes)
  (Ix.Kernel.Admission.authenticate hash records blobs).mapError
    (.entry ∘ Ix.Kernel.Admission.Error.ofBytes)
  let t ← (Ix.Kernel.Admission.admitBinding hash binding).mapError (.entry ∘ .binding)
  let pre ← (prelude t).mapError (.entry ∘ .prelude)
  let constants ← (Ix.Kernel.Admission.decodeWithin limits records).mapError
    (.entry ∘ Ix.Kernel.Admission.Error.ofBytes)
  let (ev, decls) ← (Ix.Kernel.Admission.readStream hash t pre
    (Ix.Kernel.Admission.partitionTier constants).1 blobs hint).mapError .entry
  (installDecls ev (Ix.Kernel.Frontend.preparePrelude pre.ix decls) limits.fold).mapError
    fun (e, i) => .entry (.kernel e i)

/-- **The reading of prepared inputs**: the envelope's blobs, the records decoded, the envelope's
hints over them, `readCore`, and the reader's keys under the prepared table and prelude. -/
def readPrepared (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits)
    (p : Src.KernelFront.Prepared) : Except Src.KernelFront.Refusal EnvReading := do
  let blobs := Src.KernelFront.blobsOf env
  let constants ← (Ix.Kernel.Admission.decodeWithin limits p.records).mapError
    fun e => Src.KernelFront.Refusal.ofError (Ix.Kernel.Admission.Error.ofBytes e)
  let hints := Src.KernelFront.HintTable.of env.hints constants
  let kenv ← (readCore (Src.KernelFront.preludeSource p.pre) Src.KernelFront.hash p.binding limits
    p.records blobs hints.lookup).mapError (Src.KernelFront.Refusal.ofTierError p.records)
  pure { kenv,
         keyAt := fun a => ((Ix.Kernel.Admission.streamContext Src.KernelFront.hash p.table p.pre
           constants blobs hints.lookup).keyAt (Src.KernelFront.kaddr a)).toOption }

/-- **IxCK's reader on a decoded environment, without type checking**: the entry's inputs
(`Src.KernelFront.prepare`: the binding section, the admitted table, the artifact's prelude, the
records in the kernel's check order), then `readPrepared`. -/
def readEnv (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Src.KernelFront.Refusal EnvReading := do
  let p ← Src.KernelFront.prepare env limits
  readPrepared env limits p

end IxCC.Correct
