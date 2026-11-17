import Ix.IxVM.Consistency.TableValid
import IxC.Kernel.Audit.Axioms

/-! # The composed consistency statement, frozen

`#print` freezes the public statement of the IxVM consistency proof,
`IxVM.Consistency.CircuitComposed`, the statements it is derived from (`ComposedSpec`,
`CircuitConsistentOn`, `BindingSpecOn`, `TypingSpecOn`, `SourceSoundBounded`), and every
definition they read from the statement modules `Ix.IxVM.Consistency.TableValid`,
`StatementRel`, `Statement` and `ReaderFootprint`. The two structurally recursive functions
among them are frozen by their unfolding equations (`#check`). `#guard_kernel_axioms` freezes
the axioms the six statements reach: the standard three, `propext`, `Classical.choice` and
`Quot.sound`. A change to any of them fails the build, so the statement cannot drift silently.
The module is outside any namespace, so every name prints in full.

The module imports the statement modules and the axiom check, and nothing of the proof: it
builds whether or not the proof does.

How the six fit together. `CircuitComposed` is the statement to read. It follows from
`CircuitConsistentOn` (`IxVM.Consistency.circuitComposed_of_halves`): the two halves,
`BindingSpecOn` and `TypingSpecOn`, of the deployed circuit, for one `Facts`. A half of the
circuit follows from the same half of every bounded source derivation, `SourceSoundBounded`
(`IxVM.Consistency.circuitSound_of_bounded`).

What this module does not freeze. A definition the statements read from another module
appears here by name only. `Ix.IxVM.Refinement.Audit` freezes the ones of
`Ix.IxVM.Refinement.Statement` (`CircuitSound`, `Hashed`, `View.HashedCollision`,
`packDigest`, `Digest`, `digestValue`, `verifyClaim`) and `View`. The kernel's definitions
(`Ix.Kernel.Model`, `Ix.Kernel.Denotes`, `Ix.Kernel.SetTheory`,
`Ix.Kernel.Admission.admitBinding`, the expression reader, the pinned basis, the committed
role data), the role schedule (`Ix.SpecDigest.groups`), the claim and Ixon formats and the
circuit `IxVM.source` are not frozen here. -/

/-! ## The statements -/

/--
info: def IxVM.Consistency.CircuitComposed.{u} : Prop :=
IxVM.Refinement.CircuitSound fun callsB dB =>
  IxVM.Refinement.CircuitSound fun callsA dA => IxVM.Consistency.ComposedSpec callsA callsB dA dB
-/
#guard_msgs in
#print IxVM.Consistency.CircuitComposed

/--
info: def IxVM.Consistency.ComposedSpec.{u} : List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
  List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → IxVM.Refinement.Digest → Prop :=
fun callsA callsB dA dB =>
  ∀ (bytesB : ByteArray) (spec a : Address),
    Ix.Claim.de bytesB = Except.ok (Ix.Claim.binding spec a) →
      IxVM.Refinement.packDigest (Address.blake3Pure bytesB) = dB →
        ∀ (bytesA : ByteArray) (cA : Ix.Claim),
          Ix.Claim.de bytesA = Except.ok cA →
            IxVM.Refinement.packDigest (Address.blake3Pure bytesA) = dA →
              IxVM.Consistency.InScopeTyping cA →
                ∀ (ctx : Ix.ClaimContext),
                  cA.context? = some ctx →
                    ctx.binding = a →
                      ∀ (V : IxVM.Refinement.View) (seeds : List Address),
                        IxVM.Consistency.ClaimSeeds cA V seeds →
                          V.HashedCollision (bytesA :: bytesB :: IxVM.Consistency.committedFootprint)
                              (callsA ++ callsB) ∨
                            ∃ tb t R envT,
                              IxVM.Refinement.Hashed callsB tb ∧
                                Ix.Kernel.Admission.admitBinding Address.admissionHash { address := a, bytes := tb } =
                                    Except.ok t ∧
                                  IxVM.Consistency.AllBound t ∧
                                    IxVM.Consistency.LoadedBy callsB R ∧
                                      IxVM.Consistency.TableShape t (fun x => True) R envT ∧
                                        IxVM.Consistency.ConsistentReadOver callsA t R envT seeds
-/
#guard_msgs in
#print IxVM.Consistency.ComposedSpec

/--
info: def IxVM.Consistency.CircuitConsistentOn.{u} : Prop :=
∃ Facts,
  IxVM.Refinement.CircuitSound (IxVM.Consistency.BindingSpecOn Facts) ∧
    IxVM.Refinement.CircuitSound (IxVM.Consistency.TypingSpecOn Facts)
-/
#guard_msgs in
#print IxVM.Consistency.CircuitConsistentOn

/--
info: def IxVM.Consistency.BindingSpecOn.{u} : (Ix.Kernel.RoleTable →
    (ℕ → Prop) → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop) →
  List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop :=
fun Facts calls d =>
  ∀ (bytes : ByteArray) (spec a : Address),
    Ix.Claim.de bytes = Except.ok (Ix.Claim.binding spec a) →
      IxVM.Refinement.packDigest (Address.blake3Pure bytes) = d →
        ∀ (V : IxVM.Refinement.View),
          V.HashedCollision (bytes :: IxVM.Consistency.committedFootprint) calls ∨
            ∃ tb t R env,
              IxVM.Refinement.Hashed calls tb ∧
                Ix.Kernel.Admission.admitBinding Address.admissionHash { address := a, bytes := tb } = Except.ok t ∧
                  IxVM.Consistency.AllBound t ∧
                    IxVM.Consistency.LoadedBy calls R ∧ IxVM.Consistency.TableWitness Facts t (fun x => True) R env
-/
#guard_msgs in
#print IxVM.Consistency.BindingSpecOn

/--
info: def IxVM.Consistency.TypingSpecOn.{u} : (Ix.Kernel.RoleTable →
    (ℕ → Prop) → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop) →
  List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop :=
fun Facts calls d =>
  ∀ (bytes : ByteArray) (c : Ix.Claim),
    Ix.Claim.de bytes = Except.ok c →
      IxVM.Refinement.packDigest (Address.blake3Pure bytes) = d →
        IxVM.Consistency.InScopeTyping c →
          ∀ (V : IxVM.Refinement.View) (seeds : List Address),
            IxVM.Consistency.ClaimSeeds c V seeds →
              ∀ (ctx : Ix.ClaimContext),
                c.context? = some ctx →
                  ∀ (tb : ByteArray) (t : Ix.Kernel.RoleTable),
                    Ix.Kernel.Admission.admitBinding Address.admissionHash { address := ctx.binding, bytes := tb } =
                        Except.ok t →
                      ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env Ix.Kernel.Mode.anon),
                        IxVM.Consistency.TableWitness Facts t (fun x => True) R envT →
                          IxVM.Consistency.CollisionWith V (bytes :: tb :: IxVM.Consistency.committedFootprint) R
                              calls ∨
                            IxVM.Consistency.ConsistentReadOver calls t R envT seeds
-/
#guard_msgs in
#print IxVM.Consistency.TypingSpecOn

/--
info: def IxVM.Consistency.SourceSoundBounded : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
    IxVM.Refinement.Digest → Prop) →
  Prop :=
fun P =>
  ∀ (d : IxVM.Refinement.Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
    (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
    Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d] []
        value heap calls →
      IxVM.Consistency.Bounded calls → P calls d
-/
#guard_msgs in
#print IxVM.Consistency.SourceSoundBounded

/-! ## What the statements read from `Ix.IxVM.Consistency.TableValid` -/

/--
info: def IxVM.Consistency.roleGroup : ℕ → List Ix.Kernel.Role :=
fun g => Ix.SpecDigest.groups[g]?.getD []
-/
#guard_msgs in
#print IxVM.Consistency.roleGroup

/--
info: def IxVM.Consistency.groupNeeded : ℕ → List Ix.Kernel.Role :=
fun g => Ix.SpecDigest.groupNeeds (IxVM.Consistency.roleGroup g)
-/
#guard_msgs in
#print IxVM.Consistency.groupNeeded

/--
info: def IxVM.Consistency.preludeRoles : List Ix.Kernel.Role :=
List.flatMap id Ix.Kernel.preludeShape
-/
#guard_msgs in
#print IxVM.Consistency.preludeRoles

/--
info: def IxVM.Consistency.PreludePinned : Ix.Kernel.RoleTable → Prop :=
fun t =>
  ∃ b₀ t₀,
    Ix.Kernel.Admission.defaultBinding = Except.ok b₀ ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash b₀ = Except.ok t₀ ∧
        ∀ r ∈ IxVM.Consistency.preludeRoles, t.addressOf? r = t₀.addressOf? r
-/
#guard_msgs in
#print IxVM.Consistency.PreludePinned

/--
info: def IxVM.Consistency.AllBound : Ix.Kernel.RoleTable → Prop :=
fun t => ∀ (r : Ix.Kernel.Role), (t.addressOf? r).isSome = true
-/
#guard_msgs in
#print IxVM.Consistency.AllBound

/--
info: def IxVM.Consistency.quotRole : Ix.Kernel.Role → Bool :=
fun x =>
  match x with
  | Ix.Kernel.Role.quot => true
  | Ix.Kernel.Role.quotMk => true
  | Ix.Kernel.Role.quotLift => true
  | Ix.Kernel.Role.quotInd => true
  | Ix.Kernel.Role.quotSound => true
  | x => false
-/
#guard_msgs in
#print IxVM.Consistency.quotRole

/--
info: def IxVM.Consistency.walkedRole : Ix.Kernel.Role → Bool :=
fun r =>
  match r.spec with
  | Ix.Kernel.Spec.block decls => !IxVM.Consistency.quotRole r
  | Ix.Kernel.Spec.ops type eqs => true
  | Ix.Kernel.Spec.eqns levels type eqs => true
  | x => false
-/
#guard_msgs in
#print IxVM.Consistency.walkedRole

/--
info: def IxVM.Consistency.shapeAnchors : List Ix.Kernel.Role :=
[Ix.Kernel.Role.string, Ix.Kernel.Role.stringOfList, Ix.Kernel.Role.list, Ix.Kernel.Role.listNil,
  Ix.Kernel.Role.listCons, Ix.Kernel.Role.char, Ix.Kernel.Role.charOfNat, Ix.Kernel.Role.bool, Ix.Kernel.Role.boolTrue,
  Ix.Kernel.Role.boolFalse]
-/
#guard_msgs in
#print IxVM.Consistency.shapeAnchors

/--
info: def IxVM.Consistency.modelRead : Ix.Kernel.Role → Prop :=
fun r => IxVM.Consistency.walkedRole r = true ∨ r ∈ IxVM.Consistency.shapeAnchors
-/
#guard_msgs in
#print IxVM.Consistency.modelRead

/--
info: def IxVM.Consistency.standardAxioms : List Ix.Kernel.Role :=
[Ix.Kernel.Role.propext, Ix.Kernel.Role.choice]
-/
#guard_msgs in
#print IxVM.Consistency.standardAxioms

/--
info: def IxVM.Consistency.keptRole : Ix.Kernel.Role → Prop :=
fun r => IxVM.Consistency.modelRead r ∨ r ∈ IxVM.Consistency.standardAxioms
-/
#guard_msgs in
#print IxVM.Consistency.keptRole

/--
info: def IxVM.Consistency.axiomRoles : List Ix.Kernel.Role :=
[Ix.Kernel.Role.propext, Ix.Kernel.Role.choice, Ix.Kernel.Role.quotSound]
-/
#guard_msgs in
#print IxVM.Consistency.axiomRoles

/--
info: def IxVM.Consistency.EnvSelfHashed : Ixon.Env → Prop :=
fun R =>
  (∀ (a : Address) (lc : Ixon.LazyConstant), R.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
    ∀ (a : Address) (bytes : ByteArray), R.blobs.get? a = some bytes → Address.blake3Pure bytes = a
-/
#guard_msgs in
#print IxVM.Consistency.EnvSelfHashed

/--
info: def IxVM.Consistency.UsedClosed : Ixon.Env → Prop :=
fun R =>
  (∀ (a : Address) (c : Ixon.Constant),
      IxVM.Consistency.recordOf R a = some c →
        (IxVM.Consistency.recordOf R (Ix.Cert.ownerOf a c)).isSome = true ∧
          ∀ i ∈ IxVM.Consistency.usedRefIdxs c,
            ∀ (x : Address), c.refs[i]? = some x → (IxVM.Consistency.recordOf R x).isSome = true) ∧
    ∀ (B : Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst),
      IxVM.Consistency.recordOf R B = some c →
        c.info = Ixon.ConstantInfo.muts ms →
          ∀ (i : ℕ) (m : Ixon.MutConst),
            ms[i]? = some m →
              IxVM.Consistency.recordOf R (IxVM.Consistency.memberAddr B i m) =
                  some (IxVM.Consistency.memberProjection B i m) ∧
                ∀ (ind : Ixon.Inductive),
                  m = Ixon.MutConst.indc ind →
                    ∀ j < ind.ctors.size,
                      IxVM.Consistency.recordOf R (IxVM.Consistency.ctorAddr B i j) =
                        some (IxVM.Consistency.constructorProjection B i j)
-/
#guard_msgs in
#print IxVM.Consistency.UsedClosed

/--
info: def IxVM.Consistency.committedRows : List (Address × ByteArray) :=
List.filterMap
  (fun row =>
    (Ix.Kernel.Reader.addressOfHex row.1).bind fun a => Option.map (fun bytes => (a, bytes)) (bytesOfHex row.2))
  Ix.Kernel.Reader.RoleData.prelude.toList
-/
#guard_msgs in
#print IxVM.Consistency.committedRows

/--
info: def IxVM.Consistency.AgreesCommitted : Ixon.Env → Prop :=
fun R =>
  ∀ p ∈ IxVM.Consistency.committedRows, ∀ (lc : Ixon.LazyConstant), R.consts.get? p.1 = some lc → lc.rawBytes = p.2
-/
#guard_msgs in
#print IxVM.Consistency.AgreesCommitted

/--
info: def IxVM.Consistency.PinnedBasis : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun ci => ∃ kind, ci ∈ kind.declsA
-/
#guard_msgs in
#print IxVM.Consistency.PinnedBasis

/--
info: def IxVM.Consistency.KeptIn : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.Store → (Address → Option ByteArray) → Address → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun t store blob a ci =>
  (∀ (c : Ixon.Constant) (ax : Ixon.Axiom),
      store a = some c →
        c.info = Ixon.ConstantInfo.axio ax →
          ∃ r ∈ IxVM.Consistency.axiomRoles, IxVM.Consistency.keyOf t a = Ix.Kernel.Key.role r) ∧
    ∃ ci₀, IxVM.Consistency.ReadsIn t store blob a ci₀ ∧ IxVM.Consistency.StoredAs ci ci₀
-/
#guard_msgs in
#print IxVM.Consistency.KeptIn

/--
info: structure IxVM.Consistency.ReadingOf (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
  (env : Ix.Kernel.Env Ix.Kernel.Mode.anon) : Prop
number of parameters: 3
fields:
  IxVM.Consistency.ReadingOf.nodup : (List.map (fun x => x.name) env.consts).Nodup
  IxVM.Consistency.ReadingOf.provenance : ∀ ci ∈ (IxVM.Consistency.claimedEnv env).consts,
      (∃ tbl, ci = Ix.Kernel.ConstantInfo.projInfo tbl) ∨
        IxVM.Consistency.PinnedBasis ci ∨
          ∃ a, IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci
  IxVM.Consistency.ReadingOf.stored : ∀ (a : Address),
      (∃ ci₀, IxVM.Consistency.Reads t R a ci₀) →
        ∃ ci,
          env.find? (IxVM.Consistency.keyOf t a) = some ci ∧
            (IxVM.Consistency.PinnedBasis ci ∨
              ∃ ci₀, IxVM.Consistency.Reads t R a ci₀ ∧ IxVM.Consistency.StoredAs ci ci₀)
constructor:
  IxVM.Consistency.ReadingOf.mk {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon}
    (nodup : (List.map (fun x => x.name) env.consts).Nodup)
    (provenance :
      ∀ ci ∈ (IxVM.Consistency.claimedEnv env).consts,
        (∃ tbl, ci = Ix.Kernel.ConstantInfo.projInfo tbl) ∨
          IxVM.Consistency.PinnedBasis ci ∨
            ∃ a, IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci)
    (stored :
      ∀ (a : Address),
        (∃ ci₀, IxVM.Consistency.Reads t R a ci₀) →
          ∃ ci,
            env.find? (IxVM.Consistency.keyOf t a) = some ci ∧
              (IxVM.Consistency.PinnedBasis ci ∨
                ∃ ci₀, IxVM.Consistency.Reads t R a ci₀ ∧ IxVM.Consistency.StoredAs ci ci₀)) :
    IxVM.Consistency.ReadingOf t R env
-/
#guard_msgs in
#print IxVM.Consistency.ReadingOf

/--
info: structure IxVM.Consistency.TableShape.{u} (t : Ix.Kernel.RoleTable) (G : ℕ → Prop) (R : Ixon.Env)
  (env : Ix.Kernel.Env Ix.Kernel.Mode.anon) : Prop
number of parameters: 4
fields:
  IxVM.Consistency.TableShape.needsClosed : ∀ (g : ℕ),
      G g → ∀ r ∈ IxVM.Consistency.groupNeeded g, G (Ix.SpecDigest.groupOf r)
  IxVM.Consistency.TableShape.bound : ∀ (g : ℕ),
      G g → ∀ r ∈ IxVM.Consistency.roleGroup g, (t.addressOf? r).isSome = true
  IxVM.Consistency.TableShape.prelude : IxVM.Consistency.PreludePinned t
  IxVM.Consistency.TableShape.literals : IxVM.Refinement.LiteralSupportBound t
  IxVM.Consistency.TableShape.hashed : IxVM.Consistency.EnvSelfHashed R
  IxVM.Consistency.TableShape.usedClosed : IxVM.Consistency.UsedClosed R
  IxVM.Consistency.TableShape.committed : IxVM.Consistency.AgreesCommitted R
  IxVM.Consistency.TableShape.zeroFree : R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      R.blobs.get? Ix.HostAdmission.Merkle.padding = none
  IxVM.Consistency.TableShape.kept : ∀ (g : ℕ) (r : Ix.Kernel.Role) (a : Address),
      G g →
        r ∈ IxVM.Consistency.roleGroup g →
          IxVM.Consistency.keptRole r →
            t.addressOf? r = some a →
              ∃ ci,
                env.find? (Ix.Kernel.Key.role r) = some ci ∧
                  (IxVM.Consistency.PinnedBasis ci ∨
                    IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci)
  IxVM.Consistency.TableShape.reading : IxVM.Consistency.ReadingOf t R env
  IxVM.Consistency.TableShape.pins : ∀ (kind : Ix.Kernel.BasisKind), ∀ ci ∈ kind.declsA, ci ∈ env.consts
  IxVM.Consistency.TableShape.preludeKept : ∀ (g : ℕ) (r : Ix.Kernel.Role) (a : Address),
      G g →
        r ∈ IxVM.Consistency.roleGroup g →
          r ∈ IxVM.Consistency.preludeRoles →
            t.addressOf? r = some a →
              ∃ ci,
                env.find? (Ix.Kernel.Key.role r) = some ci ∧
                  (IxVM.Consistency.PinnedBasis ci ∨
                    IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci)
  IxVM.Consistency.TableShape.model : ∀ (W : Type u) [inst : Ix.Kernel.SetTheory W],
      Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env))
constructor:
  IxVM.Consistency.TableShape.mk.{u} {t : Ix.Kernel.RoleTable} {G : ℕ → Prop} {R : Ixon.Env}
    {env : Ix.Kernel.Env Ix.Kernel.Mode.anon}
    (needsClosed : ∀ (g : ℕ), G g → ∀ r ∈ IxVM.Consistency.groupNeeded g, G (Ix.SpecDigest.groupOf r))
    (bound : ∀ (g : ℕ), G g → ∀ r ∈ IxVM.Consistency.roleGroup g, (t.addressOf? r).isSome = true)
    (prelude : IxVM.Consistency.PreludePinned t) (literals : IxVM.Refinement.LiteralSupportBound t)
    (hashed : IxVM.Consistency.EnvSelfHashed R) (usedClosed : IxVM.Consistency.UsedClosed R)
    (committed : IxVM.Consistency.AgreesCommitted R)
    (zeroFree :
      R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧ R.blobs.get? Ix.HostAdmission.Merkle.padding = none)
    (kept :
      ∀ (g : ℕ) (r : Ix.Kernel.Role) (a : Address),
        G g →
          r ∈ IxVM.Consistency.roleGroup g →
            IxVM.Consistency.keptRole r →
              t.addressOf? r = some a →
                ∃ ci,
                  env.find? (Ix.Kernel.Key.role r) = some ci ∧
                    (IxVM.Consistency.PinnedBasis ci ∨
                      IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci))
    (reading : IxVM.Consistency.ReadingOf t R env)
    (pins : ∀ (kind : Ix.Kernel.BasisKind), ∀ ci ∈ kind.declsA, ci ∈ env.consts)
    (preludeKept :
      ∀ (g : ℕ) (r : Ix.Kernel.Role) (a : Address),
        G g →
          r ∈ IxVM.Consistency.roleGroup g →
            r ∈ IxVM.Consistency.preludeRoles →
              t.addressOf? r = some a →
                ∃ ci,
                  env.find? (Ix.Kernel.Key.role r) = some ci ∧
                    (IxVM.Consistency.PinnedBasis ci ∨
                      IxVM.Consistency.KeptIn t (IxVM.Consistency.recordOf R) (fun x => R.blobs.get? x) a ci))
    (model :
      ∀ (W : Type u) [inst : Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env))) :
    IxVM.Consistency.TableShape t G R env
-/
#guard_msgs in
#print IxVM.Consistency.TableShape

/--
info: structure IxVM.Consistency.TableWitness.{u}
  (Facts : Ix.Kernel.RoleTable → (ℕ → Prop) → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop)
  (t : Ix.Kernel.RoleTable) (G : ℕ → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env Ix.Kernel.Mode.anon) : Prop
number of parameters: 5
fields:
  IxVM.Consistency.TableWitness.shape : IxVM.Consistency.TableShape t G R env
  IxVM.Consistency.TableWitness.facts : Facts t G R env
constructor:
  IxVM.Consistency.TableWitness.mk.{u}
    {Facts : Ix.Kernel.RoleTable → (ℕ → Prop) → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop}
    {t : Ix.Kernel.RoleTable} {G : ℕ → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon}
    (shape : IxVM.Consistency.TableShape t G R env) (facts : Facts t G R env) :
    IxVM.Consistency.TableWitness Facts t G R env
-/
#guard_msgs in
#print IxVM.Consistency.TableWitness

/--
info: def IxVM.Consistency.storeOver : Ixon.Env → Ixon.Env → Ix.Kernel.Reader.Store :=
fun E₀ R a => (IxVM.Consistency.recordOf E₀ a).orElse fun x => IxVM.Consistency.recordOf R a
-/
#guard_msgs in
#print IxVM.Consistency.storeOver

/--
info: def IxVM.Consistency.blobOver : Ixon.Env → Ixon.Env → Address → Option ByteArray :=
fun E₀ R a => (E₀.blobs.get? a).orElse fun x => R.blobs.get? a
-/
#guard_msgs in
#print IxVM.Consistency.blobOver

/--
info: def IxVM.Consistency.ConsistentReadOver.{u} : List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
  Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env Ix.Kernel.Mode.anon → List Address → Prop :=
fun calls t R envT seeds =>
  ∃ E₀ env,
    IxVM.Consistency.LoadedBy calls E₀ ∧
      (List.map (fun x => x.name) env.consts).Nodup ∧
        (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
          (∀ ci ∈ (IxVM.Consistency.claimedEnv env).consts,
              (∃ tbl, ci = Ix.Kernel.ConstantInfo.projInfo tbl) ∨
                IxVM.Consistency.PinnedBasis ci ∨
                  ∃ a,
                    IxVM.Consistency.KeptIn t (IxVM.Consistency.storeOver E₀ R) (IxVM.Consistency.blobOver E₀ R) a ci) ∧
            (∀ a ∈ seeds,
                ∀ (a' : Address),
                  IxVM.Consistency.SeedConstant E₀ a a' →
                    ∃ ci,
                      env.find? (IxVM.Consistency.keyOf t a') = some ci ∧
                        (IxVM.Consistency.PinnedBasis ci ∨
                          IxVM.Consistency.KeptIn t (IxVM.Consistency.storeOver E₀ R) (IxVM.Consistency.blobOver E₀ R)
                            a' ci)) ∧
              ∀ (W : Type u) [inst : Ix.Kernel.SetTheory W],
                Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env))
-/
#guard_msgs in
#print IxVM.Consistency.ConsistentReadOver

/--
info: def IxVM.Consistency.committedFootprint : List ByteArray :=
IxVM.Consistency.committedImages ++ IxVM.Consistency.committedProjImages
-/
#guard_msgs in
#print IxVM.Consistency.committedFootprint

/--
info: def IxVM.Consistency.CollisionWith : IxVM.Refinement.View →
  List ByteArray → Ixon.Env → List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Prop :=
fun V extra R calls =>
  V.HashedCollision extra calls ∨
    (∃ x held bytes,
        ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) ∧
          IxVM.Refinement.Hashed calls bytes ∧ bytes ≠ held ∧ Address.blake3Pure bytes = x) ∨
      ∃ x held image,
        ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) ∧
          IxVM.Consistency.HashedBlockProjImage calls image ∧ image ≠ held ∧ Address.blake3Pure image = x
-/
#guard_msgs in
#print IxVM.Consistency.CollisionWith

/--
info: def IxVM.Consistency.InScopeTyping : Ix.Claim → Prop :=
fun x =>
  match x with
  | Ix.Claim.check ctx const asm => ctx.axioms = none ∧ asm = none ∧ ctx.literalClass = false
  | Ix.Claim.checkEnv ctx root asm => ctx.axioms = none ∧ asm = none ∧ ctx.literalClass = false
  | x => False
-/
#guard_msgs in
#print IxVM.Consistency.InScopeTyping

/-! ## What the statements read from `Ix.IxVM.Consistency.StatementRel` -/

/--
info: def IxVM.Consistency.keyOf : Ix.Kernel.RoleTable → Address → Ix.Kernel.Key Ix.Kernel.Mode.anon :=
fun t a =>
  match Array.find? (fun x => x.2 == a) t.bound with
  | some (r, snd) => Ix.Kernel.Key.role r
  | none => Ix.Kernel.Key.id a
-/
#guard_msgs in
#print IxVM.Consistency.keyOf

/--
info: def IxVM.Consistency.recordOf : Ixon.Env → Address → Option Ixon.Constant :=
fun E a => (E.consts.get? a).bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption
-/
#guard_msgs in
#print IxVM.Consistency.recordOf

/--
info: def IxVM.Consistency.memberAddr : Address → ℕ → Ixon.MutConst → Address :=
fun B i m => Address.blake3Pure (Ixon.serConstant (IxVM.Consistency.memberProjection B i m))
-/
#guard_msgs in
#print IxVM.Consistency.memberAddr

/--
info: def IxVM.Consistency.ctorAddr : Address → ℕ → ℕ → Address :=
fun B i j => Address.blake3Pure (Ixon.serConstant (IxVM.Consistency.constructorProjection B i j))
-/
#guard_msgs in
#print IxVM.Consistency.ctorAddr

/--
info: def IxVM.Consistency.keyRecord : Ixon.Constant :=
{ info := Ixon.ConstantInfo.axio { isUnsafe := false, lvls := 0, typ := Ixon.Expr.sort 0 }, sharing := #[], refs := #[],
  univs := #[] }
-/
#guard_msgs in
#print IxVM.Consistency.keyRecord

/--
info: def IxVM.Consistency.readCtx : Ix.Kernel.RoleTable →
  (Address → Option ByteArray) → Ix.Kernel.Reader.Ctx Ix.Kernel.Mode.anon :=
fun t blob =>
  { store := fun x => some IxVM.Consistency.keyRecord, blob := blob,
    roles := Ix.Kernel.Reader.bindingsOf (fun x => some IxVM.Consistency.keyRecord) t, index := { } }
-/
#guard_msgs in
#print IxVM.Consistency.readCtx

/--
info: def IxVM.Consistency.exprReader : Ix.Kernel.RoleTable →
  (Address → Option ByteArray) →
    Ixon.Constant →
      (ℕ → Ix.Kernel.LevelParam) →
        (ℕ → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key Ix.Kernel.Mode.anon))) →
          Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon :=
fun t blob src param self => Ix.Kernel.Reader.MemberReader.mk' (IxVM.Consistency.readCtx t blob) src param self
-/
#guard_msgs in
#print IxVM.Consistency.exprReader

/--
info: def IxVM.Consistency.soloSelf : Ix.Kernel.RoleTable →
  Address → ℕ → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key Ix.Kernel.Mode.anon)) :=
fun t a k => if (k == 0) = true then some (pure (IxVM.Consistency.keyOf t a)) else none
-/
#guard_msgs in
#print IxVM.Consistency.soloSelf

/--
info: def IxVM.Consistency.blockSelf : Ix.Kernel.RoleTable →
  Address → Array Ixon.MutConst → ℕ → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key Ix.Kernel.Mode.anon)) :=
fun t B ms k => Option.map (fun m => pure (IxVM.Consistency.keyOf t (IxVM.Consistency.memberAddr B k m))) ms[k]?
-/
#guard_msgs in
#print IxVM.Consistency.blockSelf

/--
info: def IxVM.Consistency.DefnShape : Ix.DefKind →
  Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon →
    Ix.Kernel.Expr Ix.Kernel.Mode.anon → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun kind cv value ci₀ =>
  match kind with
  | Ix.DefKind.defn => ∃ hint, ci₀ = Ix.Kernel.ConstantInfo.defnInfo cv value hint
  | Ix.DefKind.thm => ci₀ = Ix.Kernel.ConstantInfo.thmInfo cv value
  | Ix.DefKind.opaq => ci₀ = Ix.Kernel.ConstantInfo.axiomInfo cv
-/
#guard_msgs in
#print IxVM.Consistency.DefnShape

/--
info: def IxVM.Consistency.DefnReads : Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
  Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Definition → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun mr name d ci₀ =>
  ∃ ty value,
    mr.read d.typ = Except.ok ty ∧
      mr.read d.value = Except.ok value ∧
        IxVM.Consistency.DefnShape d.kind { name := name, levelParams := List.range d.lvls.toNat, type := ty } value ci₀
-/
#guard_msgs in
#print IxVM.Consistency.DefnReads

/--
info: def IxVM.Consistency.AxiomReads : Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
  Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Axiom → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun mr name ax ci₀ =>
  IxVM.Consistency.inertKey name = false ∧
    ∃ ty,
      mr.read ax.typ = Except.ok ty ∧
        ci₀ = Ix.Kernel.ConstantInfo.axiomInfo { name := name, levelParams := List.range ax.lvls.toNat, type := ty }
-/
#guard_msgs in
#print IxVM.Consistency.AxiomReads

/--
info: def IxVM.Consistency.quotSlot : Ix.QuotKind → Ix.Kernel.QuotKind :=
fun x =>
  match x with
  | Ix.QuotKind.type => Ix.Kernel.QuotKind.type
  | Ix.QuotKind.ctor => Ix.Kernel.QuotKind.ctor
  | Ix.QuotKind.lift => Ix.Kernel.QuotKind.lift
  | Ix.QuotKind.ind => Ix.Kernel.QuotKind.ind
-/
#guard_msgs in
#print IxVM.Consistency.quotSlot

/--
info: def IxVM.Consistency.QuotReads : Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
  Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Quotient → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun mr name q ci₀ =>
  ∃ ty,
    mr.read q.typ = Except.ok ty ∧
      Ix.Kernel.quotPinHit (IxVM.Consistency.quotSlot q.kind)
            { name := name, levelParams := List.range q.lvls.toNat, type := ty } =
          true ∧
        Ix.Kernel.BasisKind.quotK.declsA[(IxVM.Consistency.quotSlot q.kind).slot]? = some ci₀
-/
#guard_msgs in
#print IxVM.Consistency.QuotReads

/--
info: def IxVM.Consistency.IndReads : Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
  Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Inductive → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun mr name ind ci₀ =>
  ∃ ty caps,
    mr.read ind.typ = Except.ok ty ∧
      ci₀ = Ix.Kernel.ConstantInfo.indInfo { name := name, levelParams := List.range ind.lvls.toNat, type := ty } caps
-/
#guard_msgs in
#print IxVM.Consistency.IndReads

/--
info: def IxVM.Consistency.CtorReads : Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
  Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Constructor → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun mr name ct ci₀ =>
  ∃ ty,
    mr.read ct.typ = Except.ok ty ∧
      ci₀ =
        Ix.Kernel.ConstantInfo.ctorInfo { name := name, levelParams := List.range ct.lvls.toNat, type := ty }
          ct.params.toNat ct.fields.toNat
-/
#guard_msgs in
#print IxVM.Consistency.CtorReads

/--
info: def IxVM.Consistency.MemberAt : Ix.Kernel.Reader.Store →
  Address → Ixon.Constant → Address → Ixon.Constant → Array Ixon.MutConst → ℕ → Ixon.MutConst → Prop :=
fun store a c B cb ms i m =>
  store B = some cb ∧
    cb.info = Ixon.ConstantInfo.muts ms ∧
      ms[i]? = some m ∧
        c = IxVM.Consistency.memberProjection B i m ∧
          a = IxVM.Consistency.memberAddr B i m ∧ IxVM.Consistency.InLogic cb
-/
#guard_msgs in
#print IxVM.Consistency.MemberAt

/--
info: IxVM.Consistency.lastBinderDom.eq_def : ∀ (x : Ix.Kernel.Expr Ix.Kernel.Mode.anon),
  IxVM.Consistency.lastBinderDom x =
    match x with
    | d.forallE b m =>
      match b with
      | type.forallE body m => IxVM.Consistency.lastBinderDom b
      | x => some d
    | x => none
-/
#guard_msgs in
#check @IxVM.Consistency.lastBinderDom.eq_def

/--
info: def IxVM.Consistency.headKey : Ix.Kernel.Expr Ix.Kernel.Mode.anon → Option (Ix.Kernel.Key Ix.Kernel.Mode.anon) :=
fun e =>
  match e.getAppFn with
  | Ix.Kernel.Expr.const k us => some k
  | x => none
-/
#guard_msgs in
#print IxVM.Consistency.headKey

/--
info: def IxVM.Consistency.binderDom : ℕ → Ix.Kernel.Expr Ix.Kernel.Mode.anon → Option (Ix.Kernel.Expr Ix.Kernel.Mode.anon) :=
fun n ty =>
  match Ix.Kernel.Expr.stripPis n ty with
  | some (fst, d.forallE body m) => some d
  | x => none
-/
#guard_msgs in
#print IxVM.Consistency.binderDom

/--
info: def IxVM.Consistency.familyKey : Ixon.Recursor →
  Ix.Kernel.Expr Ix.Kernel.Mode.anon → Option (Ix.Kernel.Key Ix.Kernel.Mode.anon) :=
fun rc ty =>
  (IxVM.Consistency.binderDom rc.params.toNat ty).bind fun motive =>
    (IxVM.Consistency.lastBinderDom motive).bind IxVM.Consistency.headKey
-/
#guard_msgs in
#print IxVM.Consistency.familyKey

/--
info: def IxVM.Consistency.majorKey : Ixon.Recursor →
  Ix.Kernel.Expr Ix.Kernel.Mode.anon → Option (Ix.Kernel.Key Ix.Kernel.Mode.anon) :=
fun rc ty =>
  (IxVM.Consistency.binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty).bind
    IxVM.Consistency.headKey
-/
#guard_msgs in
#print IxVM.Consistency.majorKey

/--
info: def IxVM.Consistency.IndKeyAt : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.Store → Ix.Kernel.Key Ix.Kernel.Mode.anon → Address → ℕ → Ixon.Inductive → Prop :=
fun t store k B i ind =>
  ∃ a c p cb ms,
    k = IxVM.Consistency.keyOf t a ∧
      store a = some c ∧
        c.info = Ixon.ConstantInfo.iPrj p ∧
          B = p.block ∧ i = p.idx.toNat ∧ IxVM.Consistency.MemberAt store a c B cb ms i (Ixon.MutConst.indc ind)
-/
#guard_msgs in
#print IxVM.Consistency.IndKeyAt

/--
info: def IxVM.Consistency.RuleReads : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.MemberReader Ix.Kernel.Mode.anon →
    Address → ℕ → Ixon.RecursorRule × ℕ → Ix.Kernel.RecRule Ix.Kernel.Mode.anon → Prop :=
fun t mr Bm im ru rl =>
  ∃ rhs,
    mr.read ru.1.rhs = Except.ok rhs ∧
      rl =
        { ctor := IxVM.Consistency.keyOf t (IxVM.Consistency.ctorAddr Bm im ru.2), nfields := ru.1.fields.toNat,
          ctorParams := 0, fire := Ix.Kernel.RecRuleFire.inert, rhs := rhs }
-/
#guard_msgs in
#print IxVM.Consistency.RuleReads

/--
info: def IxVM.Consistency.RecReads : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.Store →
    (Address → Option ByteArray) →
      Ixon.Constant →
        (ℕ → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key Ix.Kernel.Mode.anon))) →
          Ix.Kernel.Key Ix.Kernel.Mode.anon → Ixon.Recursor → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun t store blob src self name rc ci₀ =>
  ∃ tyP ty kF kM B Bm i im ind indM ps rules,
    (IxVM.Consistency.exprReader t blob src id self).read rc.typ = Except.ok tyP ∧
      IxVM.Consistency.familyKey rc tyP = some kF ∧
        IxVM.Consistency.IndKeyAt t store kF B i ind ∧
          IxVM.Consistency.majorKey rc tyP = some kM ∧
            IxVM.Consistency.IndKeyAt t store kM Bm im indM ∧
              ps = Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat) ∧
                (IxVM.Consistency.exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read rc.typ =
                    Except.ok ty ∧
                  rc.rules.size = indM.ctors.size ∧
                    List.Forall₂
                        (IxVM.Consistency.RuleReads t
                          (IxVM.Consistency.exprReader t blob src (Ix.Kernel.Reader.recParam ps) self) Bm im)
                        rc.rules.toList.zipIdx rules ∧
                      ci₀ =
                        Ix.Kernel.ConstantInfo.recInfo { name := name, levelParams := ps, type := ty }
                          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
                          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules
-/
#guard_msgs in
#print IxVM.Consistency.RecReads

/--
info: def IxVM.Consistency.ReadsRecord : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.Store →
    (Address → Option ByteArray) →
      Address → Ixon.Constant → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Ixon.ConstantInfo → Prop :=
fun t store blob a c ci₀ x =>
  match x with
  | Ixon.ConstantInfo.defn d =>
    IxVM.Consistency.InLogic c ∧
      IxVM.Consistency.DefnReads (IxVM.Consistency.exprReader t blob c id (IxVM.Consistency.soloSelf t a))
        (IxVM.Consistency.keyOf t a) d ci₀
  | Ixon.ConstantInfo.axio ax =>
    IxVM.Consistency.InLogic c ∧
      IxVM.Consistency.AxiomReads (IxVM.Consistency.exprReader t blob c id fun x => none) (IxVM.Consistency.keyOf t a)
        ax ci₀
  | Ixon.ConstantInfo.quot q =>
    IxVM.Consistency.QuotReads (IxVM.Consistency.exprReader t blob c id fun x => none) (IxVM.Consistency.keyOf t a) q
      ci₀
  | Ixon.ConstantInfo.recr rc =>
    IxVM.Consistency.InLogic c ∧
      IxVM.Consistency.RecReads t store blob c (IxVM.Consistency.soloSelf t a) (IxVM.Consistency.keyOf t a) rc ci₀
  | Ixon.ConstantInfo.dPrj p =>
    ∃ cb ms d,
      IxVM.Consistency.MemberAt store a c p.block cb ms p.idx.toNat (Ixon.MutConst.defn d) ∧
        IxVM.Consistency.DefnReads (IxVM.Consistency.exprReader t blob cb id (IxVM.Consistency.blockSelf t p.block ms))
          (IxVM.Consistency.keyOf t a) d ci₀
  | Ixon.ConstantInfo.iPrj p =>
    ∃ cb ms ind,
      IxVM.Consistency.MemberAt store a c p.block cb ms p.idx.toNat (Ixon.MutConst.indc ind) ∧
        IxVM.Consistency.IndReads (IxVM.Consistency.exprReader t blob cb id (IxVM.Consistency.blockSelf t p.block ms))
          (IxVM.Consistency.keyOf t a) ind ci₀
  | Ixon.ConstantInfo.cPrj p =>
    ∃ cb ms ind ct,
      store p.block = some cb ∧
        cb.info = Ixon.ConstantInfo.muts ms ∧
          ms[p.idx.toNat]? = some (Ixon.MutConst.indc ind) ∧
            ind.ctors[p.cidx.toNat]? = some ct ∧
              ct.cidx.toNat = p.cidx.toNat ∧
                c = IxVM.Consistency.constructorProjection p.block p.idx.toNat p.cidx.toNat ∧
                  a = IxVM.Consistency.ctorAddr p.block p.idx.toNat p.cidx.toNat ∧
                    IxVM.Consistency.InLogic cb ∧
                      IxVM.Consistency.CtorReads
                        (IxVM.Consistency.exprReader t blob cb id (IxVM.Consistency.blockSelf t p.block ms))
                        (IxVM.Consistency.keyOf t a) ct ci₀
  | Ixon.ConstantInfo.rPrj p =>
    ∃ cb ms rc,
      IxVM.Consistency.MemberAt store a c p.block cb ms p.idx.toNat (Ixon.MutConst.recr rc) ∧
        IxVM.Consistency.RecReads t store blob cb (IxVM.Consistency.blockSelf t p.block ms) (IxVM.Consistency.keyOf t a)
          rc ci₀
  | Ixon.ConstantInfo.muts a => False
-/
#guard_msgs in
#print IxVM.Consistency.ReadsRecord

/--
info: def IxVM.Consistency.ReadsIn : Ix.Kernel.RoleTable →
  Ix.Kernel.Reader.Store → (Address → Option ByteArray) → Address → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun t store blob a ci₀ => ∃ c, store a = some c ∧ IxVM.Consistency.ReadsRecord t store blob a c ci₀ c.info
-/
#guard_msgs in
#print IxVM.Consistency.ReadsIn

/--
info: def IxVM.Consistency.Reads : Ix.Kernel.RoleTable →
  Ixon.Env → Address → Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun t E a ci₀ => IxVM.Consistency.ReadsIn t (IxVM.Consistency.recordOf E) (fun x => E.blobs.get? x) a ci₀
-/
#guard_msgs in
#print IxVM.Consistency.Reads

/--
info: def IxVM.Consistency.SeedConstant : Ixon.Env → Address → Address → Prop :=
fun E₀ a a' =>
  (a' = a ∧
      ∀ (c : Ixon.Constant) (ms : Array Ixon.MutConst),
        IxVM.Consistency.recordOf E₀ a = some c → c.info ≠ Ixon.ConstantInfo.muts ms) ∨
    ∃ c ms i m,
      IxVM.Consistency.recordOf E₀ a = some c ∧
        c.info = Ixon.ConstantInfo.muts ms ∧
          ms[i]? = some m ∧
            (a' = IxVM.Consistency.memberAddr a i m ∨
              ∃ ind j, m = Ixon.MutConst.indc ind ∧ j < ind.ctors.size ∧ a' = IxVM.Consistency.ctorAddr a i j)
-/
#guard_msgs in
#print IxVM.Consistency.SeedConstant

/--
info: def IxVM.Consistency.HashedBlockProjImage : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → ByteArray → Prop :=
fun calls image =>
  ∃ blk cb ms,
    IxVM.Refinement.Hashed calls blk ∧
      Ixon.deConstantExact blk = Except.ok cb ∧
        cb.info = Ixon.ConstantInfo.muts ms ∧
          ((∃ i,
              image =
                Ixon.serConstant
                  { info := Ixon.ConstantInfo.iPrj { idx := i, block := Address.blake3Pure blk }, sharing := #[],
                    refs := #[], univs := #[] }) ∨
            ∃ i j,
              image =
                Ixon.serConstant
                  { info := Ixon.ConstantInfo.cPrj { idx := i, cidx := j, block := Address.blake3Pure blk },
                    sharing := #[], refs := #[], univs := #[] })
-/
#guard_msgs in
#print IxVM.Consistency.HashedBlockProjImage

/-! ## What the statements read from `Ix.IxVM.Consistency.Statement` -/

/--
info: def IxVM.Consistency.ROMAddressesAtMost : {G : Type} → Aiur.ROM G → ℕ → Prop :=
fun {G} rom n => ∃ addrs, addrs.length ≤ n ∧ ∀ e ∈ rom.entries, e.1 ∈ addrs
-/
#guard_msgs in
#print IxVM.Consistency.ROMAddressesAtMost

/--
info: def IxVM.Consistency.Bounded : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Prop :=
fun calls =>
  ∃ rom,
    rom.Valid ∧ IxVM.Consistency.ROMAddressesAtMost rom (2 ^ 39) ∧ Aiur.Generic.SourceSemantics.CallsInROM rom calls
-/
#guard_msgs in
#print IxVM.Consistency.Bounded

/--
info: def IxVM.Consistency.ClaimSeeds : Ix.Claim → IxVM.Refinement.View → List Address → Prop :=
fun x x_1 x_2 =>
  match x, x_1, x_2 with
  | Ix.Claim.check ctx a assumptions, V, seeds => V.trees = [] ∧ seeds = [a]
  | Ix.Claim.checkEnv ctx root assumptions, V, seeds =>
    ∃ t, V.trees = [t] ∧ IxVM.Refinement.treeRoot t = root ∧ seeds = IxVM.Refinement.treeLeaves t
  | x, x_3, x_4 => False
-/
#guard_msgs in
#print IxVM.Consistency.ClaimSeeds

/--
info: def IxVM.Consistency.LoadedBy : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Ixon.Env → Prop :=
fun calls E =>
  (∀ (a : Address) (lc : Ixon.LazyConstant),
      E.consts.get? a = some lc → IxVM.Refinement.Hashed calls lc.rawBytes ∧ Address.blake3Pure lc.rawBytes = a) ∧
    ∀ (a : Address) (bytes : ByteArray),
      E.blobs.get? a = some bytes → IxVM.Refinement.Hashed calls bytes ∧ Address.blake3Pure bytes = a
-/
#guard_msgs in
#print IxVM.Consistency.LoadedBy

/--
info: IxVM.Consistency.exprRefIdxs.eq_def : ∀ (x : Ixon.Expr),
  IxVM.Consistency.exprRefIdxs x =
    match x with
    | Ixon.Expr.ref i a => [i.toNat]
    | Ixon.Expr.prj i a e => i.toNat :: IxVM.Consistency.exprRefIdxs e
    | f.app a => IxVM.Consistency.exprRefIdxs f ++ IxVM.Consistency.exprRefIdxs a
    | t.lam b => IxVM.Consistency.exprRefIdxs t ++ IxVM.Consistency.exprRefIdxs b
    | t.all b => IxVM.Consistency.exprRefIdxs t ++ IxVM.Consistency.exprRefIdxs b
    | Ixon.Expr.letE nonDep a t v b =>
      IxVM.Consistency.exprRefIdxs t ++ IxVM.Consistency.exprRefIdxs v ++ IxVM.Consistency.exprRefIdxs b
    | x => []
-/
#guard_msgs in
#check @IxVM.Consistency.exprRefIdxs.eq_def

/--
info: def IxVM.Consistency.mutRefIdxs : Ixon.MutConst → List ℕ :=
fun x =>
  match x with
  | Ixon.MutConst.defn d => IxVM.Consistency.exprRefIdxs d.typ ++ IxVM.Consistency.exprRefIdxs d.value
  | Ixon.MutConst.indc i =>
    IxVM.Consistency.exprRefIdxs i.typ ++ List.flatMap (fun c => IxVM.Consistency.exprRefIdxs c.typ) i.ctors.toList
  | Ixon.MutConst.recr r =>
    IxVM.Consistency.exprRefIdxs r.typ ++ List.flatMap (fun rl => IxVM.Consistency.exprRefIdxs rl.rhs) r.rules.toList
-/
#guard_msgs in
#print IxVM.Consistency.mutRefIdxs

/--
info: def IxVM.Consistency.usedRefIdxs : Ixon.Constant → List ℕ :=
fun c =>
  List.flatMap IxVM.Consistency.exprRefIdxs c.sharing.toList ++
    match c.info with
    | Ixon.ConstantInfo.defn d => IxVM.Consistency.exprRefIdxs d.typ ++ IxVM.Consistency.exprRefIdxs d.value
    | Ixon.ConstantInfo.recr r =>
      IxVM.Consistency.exprRefIdxs r.typ ++ List.flatMap (fun rl => IxVM.Consistency.exprRefIdxs rl.rhs) r.rules.toList
    | Ixon.ConstantInfo.axio a => IxVM.Consistency.exprRefIdxs a.typ
    | Ixon.ConstantInfo.quot q => IxVM.Consistency.exprRefIdxs q.typ
    | Ixon.ConstantInfo.muts ms => List.flatMap IxVM.Consistency.mutRefIdxs ms.toList
    | x => []
-/
#guard_msgs in
#print IxVM.Consistency.usedRefIdxs

/--
info: inductive IxVM.Consistency.Annotates : Ix.Kernel.Expr Ix.Kernel.Mode.anon → Ix.Kernel.Expr Ix.Kernel.Mode.anon → Prop
number of parameters: 0
constructors:
IxVM.Consistency.Annotates.bvar : ∀ {i : ℕ}, IxVM.Consistency.Annotates (Ix.Kernel.Expr.bvar i) (Ix.Kernel.Expr.bvar i)
IxVM.Consistency.Annotates.fvar : ∀ {i : ℕ} {ty' ty : Ix.Kernel.Expr Ix.Kernel.Mode.anon},
  IxVM.Consistency.Annotates ty' ty → IxVM.Consistency.Annotates (Ix.Kernel.Expr.fvar i ty') (Ix.Kernel.Expr.fvar i ty)
IxVM.Consistency.Annotates.sort : ∀ {l : Ix.Kernel.Level},
  IxVM.Consistency.Annotates (Ix.Kernel.Expr.sort l) (Ix.Kernel.Expr.sort l)
IxVM.Consistency.Annotates.const : ∀ {n : Ix.Kernel.Key Ix.Kernel.Mode.anon} {us : List Ix.Kernel.Level},
  IxVM.Consistency.Annotates (Ix.Kernel.Expr.const n us) (Ix.Kernel.Expr.const n us)
IxVM.Consistency.Annotates.lit : ∀ {l : Ix.Kernel.Literal},
  IxVM.Consistency.Annotates (Ix.Kernel.Expr.lit l) (Ix.Kernel.Expr.lit l)
IxVM.Consistency.Annotates.app : ∀ {f' f a' a : Ix.Kernel.Expr Ix.Kernel.Mode.anon},
  IxVM.Consistency.Annotates f' f → IxVM.Consistency.Annotates a' a → IxVM.Consistency.Annotates (f'.app a') (f.app a)
IxVM.Consistency.Annotates.lam : ∀ {ty' ty b' b : Ix.Kernel.Expr Ix.Kernel.Mode.anon} {m' m : Ix.Kernel.BinderMeta},
  IxVM.Consistency.Annotates ty' ty →
    IxVM.Consistency.Annotates b' b → IxVM.Consistency.Annotates (ty'.lam b' m') (ty.lam b m)
IxVM.Consistency.Annotates.forallE : ∀ {ty' ty b' b : Ix.Kernel.Expr Ix.Kernel.Mode.anon} {m' m : Ix.Kernel.BinderMeta},
  IxVM.Consistency.Annotates ty' ty →
    IxVM.Consistency.Annotates b' b → IxVM.Consistency.Annotates (ty'.forallE b' m') (ty.forallE b m)
IxVM.Consistency.Annotates.proj : ∀ {s : Ix.Kernel.Key Ix.Kernel.Mode.anon} {i : ℕ}
  {e' e : Ix.Kernel.Expr Ix.Kernel.Mode.anon},
  IxVM.Consistency.Annotates e' e → IxVM.Consistency.Annotates (Ix.Kernel.Expr.proj s i e') (Ix.Kernel.Expr.proj s i e)
IxVM.Consistency.Annotates.letE : ∀ {e' ty v b : Ix.Kernel.Expr Ix.Kernel.Mode.anon} {m : Ix.Kernel.LetMeta},
  IxVM.Consistency.Annotates e' (b.instantiate1Lift v) → IxVM.Consistency.Annotates e' (ty.letE v b m)
-/
#guard_msgs in
#print IxVM.Consistency.Annotates

/--
info: def IxVM.Consistency.inertKey : Ix.Kernel.Key Ix.Kernel.Mode.anon → Bool :=
fun x =>
  match x with
  | Ix.Kernel.Key.role r => r.inert
  | x => false
-/
#guard_msgs in
#print IxVM.Consistency.inertKey

/--
info: def IxVM.Consistency.ValStored : Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon →
  Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon → Prop :=
fun cv cv₀ => cv.name = cv₀.name ∧ cv.levelParams = cv₀.levelParams ∧ IxVM.Consistency.Annotates cv.type cv₀.type
-/
#guard_msgs in
#print IxVM.Consistency.ValStored

/--
info: def IxVM.Consistency.RuleStored : Ix.Kernel.RecRule Ix.Kernel.Mode.anon →
  Ix.Kernel.RecRule Ix.Kernel.Mode.anon → Prop :=
fun rl rl₀ => rl.ctor = rl₀.ctor ∧ rl.nfields = rl₀.nfields ∧ IxVM.Consistency.Annotates rl.rhs rl₀.rhs
-/
#guard_msgs in
#print IxVM.Consistency.RuleStored

/--
info: def IxVM.Consistency.StoredAs : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon →
  Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Prop :=
fun ci ci₀ =>
  IxVM.Consistency.ValStored ci.toConstantVal ci₀.toConstantVal ∧
    match ci, ci₀ with
    | Ix.Kernel.ConstantInfo.axiomInfo val, Ix.Kernel.ConstantInfo.axiomInfo val_1 => True
    | Ix.Kernel.ConstantInfo.defnInfo val v h, Ix.Kernel.ConstantInfo.defnInfo val_1 v₀ h₀ =>
      IxVM.Consistency.Annotates v v₀ ∧ h = h₀
    | Ix.Kernel.ConstantInfo.thmInfo val v, Ix.Kernel.ConstantInfo.thmInfo val_1 v₀ => IxVM.Consistency.Annotates v v₀
    | Ix.Kernel.ConstantInfo.indInfo val caps, Ix.Kernel.ConstantInfo.indInfo val_1 caps_1 => True
    | Ix.Kernel.ConstantInfo.ctorInfo val nP nF, Ix.Kernel.ConstantInfo.ctorInfo val_1 nP₀ nF₀ => nP = nP₀ ∧ nF = nF₀
    | Ix.Kernel.ConstantInfo.recInfo val mI rP rules, Ix.Kernel.ConstantInfo.recInfo val_1 mI₀ rP₀ rules₀ =>
      mI = mI₀ ∧ rP = rP₀ ∧ List.Forall₂ IxVM.Consistency.RuleStored rules rules₀
    | x, x_1 => False
-/
#guard_msgs in
#print IxVM.Consistency.StoredAs

/--
info: def IxVM.Consistency.InLogicMut : Ixon.MutConst → Prop :=
fun x =>
  match x with
  | Ixon.MutConst.defn d => Ix.Kernel.Reader.safetyDecline d = none
  | Ixon.MutConst.indc i => i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false
  | Ixon.MutConst.recr r => r.isUnsafe = false
-/
#guard_msgs in
#print IxVM.Consistency.InLogicMut

/--
info: def IxVM.Consistency.InLogic : Ixon.Constant → Prop :=
fun c =>
  match c.info with
  | Ixon.ConstantInfo.defn d => Ix.Kernel.Reader.safetyDecline d = none
  | Ixon.ConstantInfo.recr r => r.isUnsafe = false
  | Ixon.ConstantInfo.axio a => a.isUnsafe = false
  | Ixon.ConstantInfo.muts ms => ∀ m ∈ ms.toList, IxVM.Consistency.InLogicMut m
  | x => True
-/
#guard_msgs in
#print IxVM.Consistency.InLogic

/--
info: def IxVM.Consistency.isModelAux : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon → Bool :=
fun ci =>
  match ci.name, ci with
  | base.aux d, Ix.Kernel.ConstantInfo.projInfo tbl => false
  | base.aux d, x => true
  | x, x_1 => false
-/
#guard_msgs in
#print IxVM.Consistency.isModelAux

/--
info: def IxVM.Consistency.claimedEnv : Ix.Kernel.Env Ix.Kernel.Mode.anon → Ix.Kernel.Env Ix.Kernel.Mode.anon :=
fun env => { consts := List.filter (fun ci => !IxVM.Consistency.isModelAux ci) env.consts }
-/
#guard_msgs in
#print IxVM.Consistency.claimedEnv

/--
info: def IxVM.Consistency.committedImages : List ByteArray :=
List.filterMap bytesOfHex
  (List.map (fun x => x.2)
    (Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence ++ Ix.Kernel.Reader.RoleData.blobs).toList)
-/
#guard_msgs in
#print IxVM.Consistency.committedImages

/-! ## What the statements read from `Ix.IxVM.Consistency.ReaderFootprint` -/

/--
info: def IxVM.Consistency.memberProjection : Address → ℕ → Ixon.MutConst → Ixon.Constant :=
fun owner i member =>
  {
    info :=
      match member with
      | Ixon.MutConst.defn a => Ixon.ConstantInfo.dPrj { idx := i.toUInt64, block := owner }
      | Ixon.MutConst.indc a => Ixon.ConstantInfo.iPrj { idx := i.toUInt64, block := owner }
      | Ixon.MutConst.recr a => Ixon.ConstantInfo.rPrj { idx := i.toUInt64, block := owner },
    sharing := #[], refs := #[], univs := #[] }
-/
#guard_msgs in
#print IxVM.Consistency.memberProjection

/--
info: def IxVM.Consistency.constructorProjection : Address → ℕ → ℕ → Ixon.Constant :=
fun owner i j =>
  { info := Ixon.ConstantInfo.cPrj { idx := i.toUInt64, cidx := j.toUInt64, block := owner }, sharing := #[],
    refs := #[], univs := #[] }
-/
#guard_msgs in
#print IxVM.Consistency.constructorProjection

/--
info: def IxVM.Consistency.memberProjectionImages : Address → Ixon.MutConst → ℕ → List ByteArray :=
fun owner member i =>
  Ixon.serConstant (IxVM.Consistency.memberProjection owner i member) ::
    match member with
    | Ixon.MutConst.indc ind =>
      List.map (fun j => Ixon.serConstant (IxVM.Consistency.constructorProjection owner i j))
        (List.range ind.ctors.size)
    | x => []
-/
#guard_msgs in
#print IxVM.Consistency.memberProjectionImages

/--
info: def IxVM.Consistency.recordProjectionImages : Address → Ixon.Constant → List ByteArray :=
fun owner constant =>
  match constant.info with
  | Ixon.ConstantInfo.muts members =>
    List.flatMap
      (fun x =>
        match x with
        | (member, i) => IxVM.Consistency.memberProjectionImages owner member i)
      members.toList.zipIdx
  | x => []
-/
#guard_msgs in
#print IxVM.Consistency.recordProjectionImages

/--
info: def IxVM.Consistency.rawProjectionImages : Address → ByteArray → List ByteArray :=
fun owner bytes =>
  match Ixon.deConstantExact bytes with
  | Except.ok constant => IxVM.Consistency.recordProjectionImages owner constant
  | Except.error a => []
-/
#guard_msgs in
#print IxVM.Consistency.rawProjectionImages

/--
info: def IxVM.Consistency.committedProjImages : List ByteArray :=
List.flatMap
  (fun row =>
    match Ix.Kernel.Reader.addressOfHex row.1, bytesOfHex row.2 with
    | some owner, some bytes => IxVM.Consistency.rawProjectionImages owner bytes
    | x, x_1 => [])
  (Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence).toList
-/
#guard_msgs in
#print IxVM.Consistency.committedProjImages

/-! ## Axioms

The six statements reach the three standard axioms and no other. -/

#guard_kernel_axioms IxVM.Consistency.CircuitComposed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Consistency.ComposedSpec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Consistency.CircuitConsistentOn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Consistency.BindingSpecOn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Consistency.TypingSpecOn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Consistency.SourceSoundBounded [propext, Classical.choice, Quot.sound]
