import Ix.IxVM.Refinement.Statement
import Ix.IxVM.Refinement.KernelLevels
import IxC.Kernel.MainTheorem
import IxC.Kernel.Model.Fold
import IxC.Kernel.Model.Denotes
import IxC.Kernel.Model.Iota
import IxC.Kernel.Verify.EnvGuards
import IxC.Kernel.Rules.Rel
import Aiur.WireMemory
import Aiur.Memory.Partition

/-! # `IxVM.consistent`: the IxVM circuit accepts only claims with a model

The consistency of what the deployed IxVM circuit accepts, reduced to one
obligation per layer of the verifier. Claims outside `InScope` (assumed leaves,
another role table or user axioms, `eval`) are not covered.

## The statement (`CircuitConsistent`)

Suppose the verifier's checks hold for the deployed IxVM circuit on at most
`2^39` rows (`CircuitSound`, reused from `Ix.IxVM.Refinement.Statement`), for a
public claim digest whose claim is `check` or `checkEnv` that validates its role
table, with no user axioms and no assumed leaves (`InScope`), and every role table
the reader reads it under (the default table, or one the kernel admits with its
bound constants checked: `ReaderTable`, `TableAdmitted`). Then either the run
hashed a BLAKE3 collision, exhibited from the
trace (`View.HashedCollision`, reused), or there is an environment `env` that

* is read from the records the run loaded (`LoadedBy`: every record and blob is a
  byte string the run hashed, under its BLAKE3 address; `Draws` lets the reading
  add recursor records the run did not load, as `AcceptsIn` does), through the
  kernel's own reading of Ixon records (`ReadIn`: `admitBinding`,
  `ClosureOrderAt`, `preludeFor`, `prepareWith`: the statement trusts the kernel's
  reader), installed declaration by declaration (`Installs`, `InstallStep`),
  each constant stored as the reader declares it: of the declared kind, with an
  annotation of its type, and with the declaration's own value, counts and
  recursor rules (`StoredAs`, `Annotates`);
* contains each claimed constant at its key, stored as declared (`SeedStored`).
  Every seed is in Lean's logic and none is an inert axiom:
  IxVM refuses a claim whose seed record, or its block, is unsafe or `partial`
  (`OutsideLogicAt`), or whose seed the role table binds to an inert role
  (`InertAt`: `sorryAx` and Lean's compiler-trust axioms, which install nothing),
  both in `KernelClaim::assert_claimable`, and L6 carries the refusals
  (`ClaimPhase`);
* has a claimed sub-environment (`claimedEnv`: without the model families'
  auxiliary constants) with a model in every set theory:
  `∀ V, Nonempty (Ix.Kernel.Model V (claimedEnv env))`.

A model (`Ix.Kernel.Model`, `IxC/Kernel/Denotes.lean`) interprets every claimed
constant as a set: a member of what its type denotes, with `False` empty, `Eq`
equality, every definition what its value denotes, every recursor rule
computing as Lean's does, structure and unit-like η at the families that have
them, every projection reading the structure's own table, and the kernel's `Nat`
operations computing on literals as Lean's functions, with `Nat.add`'s recurrences at
every natural. Because the environment
stores each declaration's own value and rules, a claimed definition means what the
reader's value means, not just some inhabitant of its type: a definition
`P := False` is false in every model, and no claimed constant can prove it. The
structure's docstring lists which of Lean's definitional equalities it carries
as laws and which hold in every model by the reading.

Corollary (`ConsistentRead.seeds_not_false`): no claimed constant has type
`False`.

## The reduction (`IxVM.consistent`)

`IxVM.consistent` proves `CircuitConsistent` from eight named obligations, `L0` to
`L7`, one per layer of the verifier:

| Layer | Obligation | Content |
|---|---|---|
| L0 circuit to source | `L0` | the Aiur headline with "at most `2^39` distinct memoized calls" (`MemoCallsAtMost`) added to its conclusion |
| L1 bytes to records | `L1` = `Records` | every record load returns the reading of bytes the run hashed under that address |
| L2 levels | `L2` = `Levels` | `level_leq`/`level_equal` sound for `Level.eval` with no depth hypothesis, and exact at zero |
| L3 term operations | `L3` | given `Levels`, `Terms`: substitution and lifting refine the kernel's |
| L4 core | `L4` | given L1 to L3, `Core`: whnf, conversion and inference refine `Rules.Red`, `DefEq`, `Infer` |
| L5 declarations | `L5` | given L1 to L4, `Decls`: each accepted declaration's install preserves an invariant giving `EnvModelOk` |
| L6 claims and roles | `L6` | given L1, `ClaimPhase`: an in-scope claim's run refused seeds outside Lean's logic and walked the closure of its seeds under the reader's role table |
| L7 assembly | `L7` | given L1, L5, L6: the source-level statement |

Layers communicate through `Seams`, the representation relations the layer
proofs share. Choosing them (above all the representation of IxVM heap terms as
kernel terms) is the layer proofs' main design task; every obligation is stated
relative to them, so each layer's job is fixed once they are. Whatever seams are
chosen, the composition proves the concrete `CircuitConsistent`, which does not
mention them.

`circuitSound_of_sourceSound` concludes `CircuitSound` from a source statement
over *every* derivation, so it cannot hand the source level a bound on the
derivation the trace gives. The source proofs need one: IxVM compares list lengths
as field elements, which a derivation with more than `2^32` calls could wrap.
`circuitSound_of_bounded` is
its bounded form, from `L0`; `sourceSoundBounded_of_sourceSound` shows the
unbounded statement is the special case. -/

universe u

namespace IxVM.Consistency

open IxVM.Refinement
open Aiur.Generic.SourceSemantics (Call ObsFn CallsInROM)
open Ix (Claim ClaimContext AssumptionTree)
open Ix.Kernel.Admission (Binding)


/-! ## L0: the circuit gives a derivation with at most `2^39` distinct memoized calls -/

/-- **A call the compiler inlines** (`Aiur.Generic.Specialized.inlineNames`'s
test): its callee's declaration is marked `inline`. Inlined calls have no memo
rows of their own, so the call bound does not count them. -/
def inlineCall {G : Type} [DecidableEq G] (s : Aiur.Generic.Source G) (name : String) : Bool :=
  match Aiur.Generic.Instance.ofSymbol name with
  | .error _ => false
  | .ok key => (s.program.findFunction? key.name).any (·.isInline)

/-- **At most `n` distinct memoized calls**, up to representation in the ROM:
at most `n` keys (a callee and argument values) cover every call that is not
inlined, each key's values representing the call's arguments relative to the
heap at the call. Two calls a memo row serves alike share a key, so the
derivation the trace gives has at most as many keys as memo rows. -/
def MemoCallsAtMost {G : Type} [DecidableEq G] (s : Aiur.Generic.Source G) (rom : Aiur.ROM G)
    (calls : List (Call G)) (n : Nat) : Prop :=
  ∃ keys : List (String × List (Aiur.Value G)), keys.length ≤ n ∧
    ∀ c ∈ calls, inlineCall s c.name = false →
      ∃ k ∈ keys, k.1 = c.name ∧ List.Forall₂ (Aiur.Represents rom c.heap) c.args k.2

/-- **Obligation L0** (Aiur): the depth-grouped Goldilocks observed
headline (`Aiur.Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`,
frozen in `Aiur.Audit`), with one more conjunct: the derivation it gives has at
most `2^39` distinct memoized calls (`MemoCallsAtMost`). Every other hypothesis
and conjunct is the headline's, verbatim. -/
def L0 : Prop :=
  ∀ {id : String → Except String Nat} {source : Aiur.Generic.Source IxVM.F} {entries : List String}
    {specialized : Aiur.Generic.Specialized source entries}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (prepared : Aiur.Optimized.Physical.Prepared compiled.artifact) {cfg : Aiur.Optimized.Depth.Config},
    Aiur.Optimized.Depth.Certified cfg prepared.system → cfg.bits ≤ 24 →
    ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg prepared.system) id),
    plan.WellFormedActivation →
    ∀ {name : String}, name ∈ entries →
    ∀ {rom : Aiur.WidthROM IxVM.F}, rom.Valid →
    ∀ {args : List (Aiur.SourceValue IxVM.F)} {result : Aiur.Value IxVM.F}
      {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F},
      Aiur.Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
    ∀ {root : Aiur.Circuit.Message IxVM.F},
      Aiur.Optimized.Depth.erase cfg root =
          Aiur.Circuit.Erasure.message compiled.system
            { channel := name, args := wires, result := output } →
      root.channel ∉ cfg.names →
    ∀ {rows : List (Aiur.Circuit.WeightedRow IxVM.F)}, rows.length ≤ 2 ^ 39 →
      plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok () →
      Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues args) →
      Aiur.WireValue.decode specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F) (calls : List (Call IxVM.F)),
        ObsFn source.world name args [] value heap calls ∧
          Aiur.Represents (compiled.traceROM rom) heap value result ∧
          CallsInROM (compiled.traceROM rom) calls ∧
          MemoCallsAtMost source (compiled.traceROM rom) calls (2 ^ 39)

/-- **A bounded derivation**: its calls, read in some valid ROM, have at most
`2^39` distinct memoized calls. The ROM must be valid (no address holds two
values): in an invalid one, lists of different lengths could share a key, and the
bound would say nothing. A sub-derivation of a bounded derivation is bounded (its
calls are among the derivation's). -/
def Bounded (calls : List (Call IxVM.F)) : Prop :=
  ∃ rom : Aiur.ROM IxVM.F, rom.Valid ∧ MemoCallsAtMost IxVM.source rom calls (2 ^ 39)

/-- **Source-level soundness for `P`, over bounded derivations**: `SourceSound`
restricted to observed `verify_claim` derivations with at most `2^39` distinct
memoized calls. -/
def SourceSoundBounded (P : List (Call IxVM.F) → Digest → Prop) : Prop :=
  ∀ (d : Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
    (calls : List (Call IxVM.F)),
    ObsFn IxVM.source.world verifyClaim [digestValue d] [] value heap calls → Bounded calls →
      P calls d

/-- The unbounded source statement is the special case. -/
theorem sourceSoundBounded_of_sourceSound {P : List (Call IxVM.F) → Digest → Prop}
    (sound : SourceSound P) : SourceSoundBounded P :=
  fun d value heap calls observed _ => sound d value heap calls observed

/-- **The circuit statement from the bounded source statement**, through `L0`:
`circuitSound_of_sourceSound` with the bound handed down. -/
theorem circuitSound_of_bounded (h0 : L0) {P : List (Call IxVM.F) → Digest → Prop}
    (sound : SourceSoundBounded P) : CircuitSound P := by
  intro id specialized compiled physical cfg certified bits plan activated rom valid d wires output
    result signed root rooted outside rows bound checked arguments decoded
  obtain ⟨value, heap, calls, observed, -, carried, memo⟩ :=
    h0 compiled physical certified bits plan activated (List.mem_singleton.mpr rfl) valid signed
      rooted outside bound checked arguments decoded
  exact ⟨value, heap, calls, observed, carried, sound d value heap calls observed
    ⟨compiled.traceROM rom, Aiur.WireROM.decode_valid (Aiur.WidthROM.toWireROM_valid valid _ _), memo⟩⟩

/-! ## The claims in scope -/

/-- **The claims covered**: `check` and `checkEnv` that validate their role table
(`bindingAssumed = false`, validator 3), name no user axioms and assume no
leaves. Which tables are covered is `ReaderTable`'s. -/
def InScope : Claim → Prop
  | .check ctx _ asm => ctx.bindingAssumed = false ∧ ctx.axioms = none ∧ asm = none
  | .checkEnv ctx _ asm => ctx.bindingAssumed = false ∧ ctx.axioms = none ∧ asm = none
  | _ => False

/-- **A claim's seeds, and the view its reader holds**: for `check ctx a`, the
seed `a` and no tree; for `checkEnv ctx root`, the leaves of a tree whose root is
`root`, the view holding that tree. The view's records are the reader's (the role
table's constants, for `ReaderTable`). The collision escape is relative to the
view, so a reader's tree or record whose image collides with what the run hashed
is covered. -/
def ClaimSeeds : Claim → View → List Address → Prop
  | .check _ a _, V, seeds => V.trees = [] ∧ seeds = [a]
  | .checkEnv _ root _, V, seeds =>
    ∃ t, V.trees = [t] ∧ treeRoot t = root ∧ seeds = treeLeaves t
  | _, _, _ => False

/-- **The role table the reader reads a claim under**: a binding `b` at the
claim's address, which is the default table (`Ix.Kernel.Admission.defaultBinding`)
or a table the kernel admits with its bound constants checked in the reader's
records (`TableAdmitted`). -/
def ReaderTable (c : Claim) (V : View) (b : Binding) : Prop :=
  (∃ ctx, c.context? = some ctx ∧ b.address = ctx.binding) ∧
    (Ix.Kernel.Admission.defaultBinding = .ok b ∨ TableAdmitted V b)

/-! ## The environment read from the records the run loaded -/

/-- **The records the run loaded**: every record and blob of `E` is a byte string
the derivation hashed (`Hashed`), stored under its pure BLAKE3 address. -/
def LoadedBy (calls : List (Call IxVM.F)) (E : Ixon.Env) : Prop :=
  (∀ a lc, E.consts.get? a = some lc →
    Hashed calls lc.rawBytes ∧ Address.blake3Pure lc.rawBytes = a) ∧
  (∀ a bytes, E.blobs.get? a = some bytes → Hashed calls bytes ∧ Address.blake3Pure bytes = a)

/-- **The kernel's reading of the closure of `seeds` in `E`** under the role
table `b` (the trusted component, as `AcceptsIn` uses it): the table
admitted, the compiled closure in an order with no record before one it
references, the table's prelude, and `prepareWith`'s evidence and declarations.
The closure also starts from the theorems the table's evidence names that `E`
holds, so that an operation's evidence reads from the records the run loaded (a
table's evidence theorems need not be among the claim's references). -/
def ReadIn (b : Binding) (E : Ixon.Env) (seeds : Address → Prop)
    (ev : Ix.Kernel.Evidences .anon) (ds : Array (Ix.Kernel.Declaration .anon)) : Prop :=
  ∃ (t : Ix.Kernel.RoleTable) (order : List Address) (pre : Ix.Kernel.Reader.Prelude .anon)
    (limits : Ix.Kernel.Admission.Limits),
    Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t ∧
    Ix.Cert.ClosureOrderAt t E
      (fun a => seeds a ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList) order ∧
    Ix.Kernel.Reader.preludeFor t = .ok pre ∧
    Ix.Kernel.Admission.prepareWith Address.admissionHash b pre limits (Ix.Cert.recordsOf E order)
      (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) = .ok (ev, ds)

/-- **`t'` is an annotation of `t`**: the same term up to binder metadata (the
checker's annotation pass writes each binder's `pw` datum), with every `let`
replaced by its reduct (the pass ζ-reduces). A wrong annotation denotes nothing
(`Ix.Kernel.Denotes`), so a model of an environment storing `t'` certifies it. -/
inductive Annotates : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon → Prop
  | bvar {i : Nat} : Annotates (.bvar i) (.bvar i)
  | fvar {i : Nat} {ty' ty : Ix.Kernel.Expr .anon} :
      Annotates ty' ty → Annotates (.fvar i ty') (.fvar i ty)
  | sort {l : Ix.Kernel.Level} : Annotates (.sort l) (.sort l)
  | const {n : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level} :
      Annotates (.const n us) (.const n us)
  | lit {l : Ix.Kernel.Literal} : Annotates (.lit l) (.lit l)
  | app {f' f a' a : Ix.Kernel.Expr .anon} :
      Annotates f' f → Annotates a' a → Annotates (.app f' a') (.app f a)
  | lam {ty' ty b' b : Ix.Kernel.Expr .anon} {m' m : Ix.Kernel.BinderMeta} :
      Annotates ty' ty → Annotates b' b → Annotates (.lam ty' b' m') (.lam ty b m)
  | forallE {ty' ty b' b : Ix.Kernel.Expr .anon} {m' m : Ix.Kernel.BinderMeta} :
      Annotates ty' ty → Annotates b' b → Annotates (.forallE ty' b' m') (.forallE ty b m)
  | proj {s : Ix.Kernel.Key .anon} {i : Nat} {e' e : Ix.Kernel.Expr .anon} :
      Annotates e' e → Annotates (.proj s i e') (.proj s i e)
  | letE {e' ty v b : Ix.Kernel.Expr .anon} {m : Ix.Kernel.LetMeta} :
      Annotates e' (b.instantiate1 v) → Annotates e' (.letE ty v b m)

/-- An annotation of a constant is the constant. -/
theorem Annotates.const_inv {t' : Ix.Kernel.Expr .anon} {n : Ix.Kernel.Key .anon}
    {us : List Ix.Kernel.Level} (h : Annotates t' (.const n us)) : t' = .const n us := by
  cases h with
  | const => rfl

/-- **The key of an inert axiom role** (`Ix.Kernel.Role.inert`: `sorryAx` and Lean's
compiler-trust axioms). The kernel's fold installs nothing for such a declaration, and
no accepted constant uses one. -/
def inertKey : Ix.Kernel.Key .anon → Bool
  | .role r => r.inert
  | _ => false

/-- **The constants a declaration installs**, as the reader declares them, by
`Ix.Kernel.Semantics.DeclRun`'s dispatch: a definition, a theorem and an axiom
install themselves; an opaque installs an axiom of its type (the kernel never
unfolds an opaque, so it keeps no value); a block the fold recognises as pinned
installs its pin, and any other block its members; the quotient package's `type`
record installs the pinned quotient block, and its other records install nothing
of their own, nor does the `Quot.sound` record (a slot of that block), nor an
inert axiom role's record (`inertKey`: the fold installs nothing for `sorryAx` and
declines Lean's compiler-trust axioms). -/
def installs : Ix.Kernel.Declaration .anon → List (Ix.Kernel.ConstantInfo .anon)
  | .axiomDecl cv =>
    if cv.name = Ix.Kernel.quotSoundName ∨ inertKey cv.name = true then [] else [.axiomInfo cv]
  | .defnDecl cv value hint => [.defnInfo cv value hint]
  | .thmDecl cv value => [.thmInfo cv value]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .basisDecl kind => kind.declsA
  | .indDecl block _ =>
    match Ix.Kernel.basisPinHit block with
    | some kind => kind.declsA
    | none => block
  | .quotDecl k _ =>
    match k with
    | .type => Ix.Kernel.BasisKind.quotK.declsA
    | _ => []

/-- **`cv` stores `cv₀`**: the same name and level parameters, and an annotation
of its type. -/
def ValStored (cv cv₀ : Ix.Kernel.ConstantVal .anon) : Prop :=
  cv.name = cv₀.name ∧ cv.levelParams = cv₀.levelParams ∧ Annotates cv.type cv₀.type

/-- **A recursor rule stored as declared**: the same constructor and field count,
and an annotation of its right-hand side. The rule's other fields are what the
kernel computes at install (the constructor's parameter count, how the rule
fires, its K, η and parameter bits); no law of `Ix.Kernel.Model` reads them. -/
def RuleStored (rl rl₀ : Ix.Kernel.RecRule .anon) : Prop :=
  rl.ctor = rl₀.ctor ∧ rl.nfields = rl₀.nfields ∧ Annotates rl.rhs rl₀.rhs

/-- **`ci` is the declared constant `ci₀`, stored**: of the same kind, with its
name, level parameters and annotated type (`ValStored`), and with the
declaration's own data: a definition's annotated value and its reducibility
hint, a theorem's annotated value, a constructor's parameter and field counts,
a recursor's argument counts (the major premise's position and the rule
prefix's length) and its rules, one for one (`RuleStored`). An inductive type's
capability record (its η, unit-like and K verdicts) is the kernel's, not the
declaration's. The one law of `Ix.Kernel.Model` that reads it, unit-like η
(`UnitLikeLaw`), applies where the flag is set, so the flag can add to a model's
laws and remove none. -/
def StoredAs (ci ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ValStored ci.toConstantVal ci₀.toConstantVal ∧
    match ci, ci₀ with
    | .axiomInfo _, .axiomInfo _ => True
    | .defnInfo _ v h, .defnInfo _ v₀ h₀ => Annotates v v₀ ∧ h = h₀
    | .thmInfo _ v, .thmInfo _ v₀ => Annotates v v₀
    | .indInfo _ _, .indInfo _ _ => True
    | .ctorInfo _ nP nF, .ctorInfo _ nP₀ nF₀ => nP = nP₀ ∧ nF = nF₀
    | .recInfo _ mI rP rules, .recInfo _ mI₀ rP₀ rules₀ =>
      mI = mI₀ ∧ rP = rP₀ ∧ List.Forall₂ RuleStored rules rules₀
    | _, _ => False

/-- A stored constant has the declared constant's name. -/
theorem StoredAs.name_eq {ci ci₀ : Ix.Kernel.ConstantInfo .anon} (h : StoredAs ci ci₀) :
    ci.name = ci₀.name :=
  h.1.1

/-- **One declaration's install, by shape**: the environment grows at the front
by fresh constants with distinct keys: every constant the declaration installs,
stored as declared (`StoredAs`), and constants the kernel derives (projection
tables and functions, model artifacts) at derived keys (`Key.aux`). -/
def InstallStep (env : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon)
    (env₂ : Ix.Kernel.Env .anon) : Prop :=
  ∃ new : List (Ix.Kernel.ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
    (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
    (∀ ci₀ ∈ installs d, ∃ ci ∈ new, StoredAs ci ci₀) ∧
    (∀ ci ∈ new, (∃ ci₀ ∈ installs d, ci₀.name = ci.name) ∨ ∃ k t, ci.name = .aux k t)

/-- **The environment the declarations install**, in order, from the empty one. -/
inductive Installs : List (Ix.Kernel.Declaration .anon) → Ix.Kernel.Env .anon → Prop
  | nil : Installs [] Ix.Kernel.Env.empty
  | snoc {ds : List (Ix.Kernel.Declaration .anon)} {d : Ix.Kernel.Declaration .anon}
      {env env₂ : Ix.Kernel.Env .anon} :
      Installs ds env → InstallStep env d env₂ → Installs (ds ++ [d]) env₂

/-- `a` holds a block record in `E` (in `ConsistentRead`, the records the run
loaded, so a supplemented recursor record cannot stand in for a seed): the
claim covers the block's members, which `Installs` stores. -/
def IsBlockAt (E : Ixon.Env) (a : Address) : Prop :=
  ∃ c ms, Ix.Cert.recordAt E a = some c ∧ c.info = .muts ms

/-- **A claimed constant, stored as declared**: at the key the role table gives
the address (`AddressKey`), a declaration of `ds` installs a constant `ci₀` (the
reader's), and `env` stores that key as `ci₀` (`StoredAs`). -/
def SeedStored (b : Binding) (ds : Array (Ix.Kernel.Declaration .anon)) (env : Ix.Kernel.Env .anon)
    (a : Address) : Prop :=
  ∃ (k : Ix.Kernel.Key .anon) (ci₀ ci : Ix.Kernel.ConstantInfo .anon),
    AddressKey b a k ∧ ci₀.name = k ∧ (∃ d ∈ ds.toList, ci₀ ∈ installs d) ∧
    env.find? k = some ci ∧ StoredAs ci ci₀

/-- A block member in Lean's logic, by the reader's safety policy
(`Ix.Kernel.Reader.safetyDecline`, `readInductive`). -/
def InLogicMut : Ixon.MutConst → Prop
  | .defn d => Ix.Kernel.Reader.safetyDecline d = none
  | .indc i => i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false
  | .recr r => r.isUnsafe = false

/-- **A record in Lean's logic**, by the reader's safety policy: not an unsafe
or `partial` definition, an unsafe opaque, an unsafe axiom, recursor or
inductive, nor a block holding one (`Ix.Kernel.Reader.safetyDeclineOf`,
`readInductive`, `readRecord`). The reader declines the others, and must:
Lean's kernel accepts an unsafe constant of any type, `False` included. IxVM
refuses a claim whose seed is not in Lean's logic (`OutsideLogicAt`,
`KernelClaim::assert_claimable`). -/
def InLogic (c : Ixon.Constant) : Prop :=
  match c.info with
  | .defn d => Ix.Kernel.Reader.safetyDecline d = none
  | .recr r => r.isUnsafe = false
  | .axio a => a.isUnsafe = false
  | .muts ms => ∀ m ∈ ms.toList, InLogicMut m
  | _ => True

/-- **`a` holds a record outside Lean's logic** in `E`: the record, or the block
it projects from, is not `InLogic`. IxVM refuses a `check` or `checkEnv` claim
with such a seed (`KernelClaim::assert_claimable`: its `record_unsafe` is exactly
`¬ InLogic`), which L6's `ClaimPhase` states; it keeps safe constants
from referencing unsafe ones (`KernelCheck::is_unsafe_ci`, `assert_safety`). -/
def OutsideLogicAt (E : Ixon.Env) (a : Address) : Prop :=
  ∃ c, Ix.Cert.recordAt E a = some c ∧
    (¬ InLogic c ∨ ∃ cb, Ix.Cert.recordAt E (Ix.Cert.ownerOf a c) = some cb ∧ ¬ InLogic cb)

/-- **`a` is an inert axiom of the role table `t`**: `t` binds an inert role
(`Ix.Kernel.Role.inert`: `sorryAx` and Lean's compiler-trust axioms) to it. Such a
declaration installs nothing (`installs`, as the kernel's fold), so no claim can
certify it: IxVM refuses it as a seed (`KernelClaim::assert_claimable`'s
`role_is_inert`), which L6 states (`ClaimPhase`). -/
def InertAt (t : Ix.Kernel.RoleTable) (a : Address) : Prop :=
  ∃ r : Ix.Kernel.Role, r.inert = true ∧ t.addressOf? r = some a

/-- **A constant of a model family**: an auxiliary key (`Key.aux`) that is not a
projection table. Model families (the in-process modeller's `_model`
declarations, their ι and projection theorems) are the checker's means; a
projection table is how a claimed type's projections read (`Denotes`'
`proj_table` rule looks the table up at `projTableName T`, itself an auxiliary
key), so it stays. -/
def isModelAux (ci : Ix.Kernel.ConstantInfo .anon) : Bool :=
  match ci.name, ci with
  | .aux _ _, .projInfo _ => false
  | .aux _ _, _ => true
  | _, _ => false

/-- **The claimed sub-environment**: `env` without the model families'
constants. Its constants are those the claimed closure's records install, with
their projection tables. -/
def claimedEnv (env : Ix.Kernel.Env .anon) : Ix.Kernel.Env .anon :=
  ⟨env.consts.filter fun ci => !isModelAux ci⟩

/-- **The consistency conclusion**: an environment read from the records the run
loaded, under the role table `b`, from the claim's seeds, installing every
declaration as declared (`Installs`) and storing every claimed constant, whose
claimed sub-environment (`claimedEnv`: without the model families' auxiliary
constants, which the run checks as advice) has a model in every set theory. A
block seed is covered by its members, which are stored. Every seed is in Lean's
logic and none is an inert axiom (`InertAt`; such an axiom installs nothing): IxVM refuses the
others (`KernelClaim::assert_claimable`, carried by L6). -/
def ConsistentRead (calls : List (Call IxVM.F)) (b : Binding) (seeds : List Address) : Prop :=
  ∃ (E₀ E : Ixon.Env) (ev : Ix.Kernel.Evidences .anon)
    (ds : Array (Ix.Kernel.Declaration .anon)) (env : Ix.Kernel.Env .anon),
    LoadedBy calls E₀ ∧ Draws E E₀ ∧
    ReadIn b E (fun a => a ∈ seeds) ev ds ∧ Installs ds.toList env ∧
    (∀ a ∈ seeds, IsBlockAt E₀ a ∨ SeedStored b ds env a) ∧
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V (claimedEnv env))

/-- **The images the reading takes from the kernel's committed data**, not from the
run: the records and blobs behind every reading (`Ix.Kernel.Reader.RoleData`: the
prelude, the default table's evidence records and their blobs). The run loads them
by address, so a different byte string it hashes at one of their addresses is a
collision with them (`View.HashedCollision`). -/
def committedImages : List ByteArray :=
  ((Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence ++
      Ix.Kernel.Reader.RoleData.blobs).toList.map (·.2)).filterMap bytesOfHex

/-- **What a verify_claim derivation establishes**: for every claim byte string
whose digest packs to `d` and decodes to an in-scope claim, every reader's view of
its seeds and every role table the reader reads it under (`ReaderTable`), the run
hashed a collision (with the claim's bytes, the table's, the view's data or the
committed images the reading uses, `committedImages`), or `ConsistentRead`. -/
def ConsistencySpec (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScope c →
      ∀ (V : View) (seeds : List Address) (b : Binding), ClaimSeeds c V seeds →
        ReaderTable c V b →
        V.HashedCollision (bytes :: b.bytes :: committedImages) calls ∨
          ConsistentRead.{u} calls b seeds

/-- **The deployed IxVM circuit accepts only claims whose claimed environment has a
model**: `CircuitSound` of `ConsistencySpec`. -/
def CircuitConsistent : Prop := CircuitSound ConsistencySpec.{u}

/-! ## The corollary: no claimed constant has type `False` -/

/-- **No claimed constant has type `False`**, in every set theory: the read
environment is consistent (`Ix.Kernel.Consistent`), and every claimed constant
that is not a block has a reader's type, and a stored type, other than `False`. -/
theorem ConsistentRead.seeds_not_false (V : Type u) [Ix.Kernel.SetTheory V]
    {calls : List (Call IxVM.F)} {b : Binding} {seeds : List Address}
    (h : ConsistentRead.{u} calls b seeds) :
    ∃ (E : Ixon.Env) (ds : Array (Ix.Kernel.Declaration .anon))
      (env : Ix.Kernel.Env .anon), Ix.Kernel.Consistent (claimedEnv env) ∧
      ∀ a ∈ seeds, IsBlockAt E a ∨
        ∃ (k : Ix.Kernel.Key .anon) (ci₀ ci : Ix.Kernel.ConstantInfo .anon),
          AddressKey b a k ∧ ci₀.name = k ∧ (∃ d ∈ ds.toList, ci₀ ∈ installs d) ∧
          env.find? k = some ci ∧
          ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
          ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] := by
  obtain ⟨E, -, -, ds, env, -, -, -, -, hseeds, hmodel⟩ := h
  have hcons : Ix.Kernel.Consistent (claimedEnv env) := Ix.Kernel.consistent_of_model V (hmodel V)
  refine ⟨E, ds, env, hcons, fun a ha => ?_⟩
  rcases hseeds a ha with hblock | ⟨k, ci₀, ci, hkey, hname, hdecl, hfind, hst⟩
  · exact Or.inl hblock
  · have hmem0 : ci ∈ env.consts := List.mem_of_find?_eq_some hfind
    have hname' : ci.name = k := by
      have := List.find?_some hfind
      simpa using this
    have hnaux : isModelAux ci = false := by
      unfold isModelAux
      rw [hname']
      rcases hkey with rfl | ⟨t, r, -, -, rfl⟩ <;> rfl
    have hmem : ci ∈ (claimedEnv env).consts :=
      List.mem_filter.mpr ⟨hmem0, by simp [hnaux]⟩
    have hci : ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
      fun hf => hcons ci hmem hf
    refine Or.inr ⟨k, ci₀, ci, hkey, hname, hdecl, hfind, fun hf => ?_, hci⟩
    have hann := hst.1.2.2
    rw [hf] at hann
    exact hci hann.const_inv

/-- The corollary for every derivation the statement covers. -/
theorem ConsistencySpec.no_false (V : Type u) [Ix.Kernel.SetTheory V]
    {calls : List (Call IxVM.F)} {d : Digest} (h : ConsistencySpec.{u} calls d)
    {bytes : ByteArray} {c : Claim} (hde : Claim.de bytes = .ok c)
    (hd : packDigest (Address.blake3Pure bytes) = d) (hc : InScope c)
    {W : View} {seeds : List Address} {b : Binding} (hs : ClaimSeeds c W seeds)
    (hb : ReaderTable c W b) :
    W.HashedCollision (bytes :: b.bytes :: committedImages) calls ∨
      ∃ (E : Ixon.Env) (ds : Array (Ix.Kernel.Declaration .anon))
        (env : Ix.Kernel.Env .anon), Ix.Kernel.Consistent (claimedEnv env) ∧
        ∀ a ∈ seeds, IsBlockAt E a ∨
          ∃ (k : Ix.Kernel.Key .anon) (ci₀ ci : Ix.Kernel.ConstantInfo .anon),
            AddressKey b a k ∧ ci₀.name = k ∧ (∃ d ∈ ds.toList, ci₀ ∈ installs d) ∧
            env.find? k = some ci ∧
            ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
            ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
  (h bytes c hde hd hc W seeds b hs hb).elim Or.inl
    fun hr => Or.inr (ConsistentRead.seeds_not_false V hr)

/-! ## The kernel's model invariant at the ends of the fold -/

/-- The empty environment carries the kernel's fold invariant
(`Ix.Kernel.Model.foldPM`'s start). -/
theorem envModelOk_empty (V : Type u) [Ix.Kernel.SetTheory V] :
    Ix.Kernel.Model.EnvModelOk V .verified (Ix.Kernel.Env.empty : Ix.Kernel.Env .anon) :=
  ⟨⟨Ix.Kernel.Model.EnvModelM.empty V .verified⟩, Ix.Kernel.EtaFamiliesClosed.empty⟩

/-- The fold invariant gives a model (`Ix.Kernel.model_exists`'s last step). -/
theorem model_of_envModelOk {V : Type u} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.Model.EnvModelOk V .verified env) : Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨⟨m⟩, -⟩ := h
  exact ⟨Ix.Kernel.Model.Model.ofEnvModelM m⟩

/-! ## The seams between the layers -/

/-- **The representation relations the layer proofs share.** Choosing them is the
layer proofs' main design task. Each obligation below is stated relative to
them. -/
structure Seams where
  /-- (L1, L6) The IxVM value `v` (a `Bytes::AddressRef`) holds the address `a`. -/
  addr : Aiur.Heap IxVM.F → Aiur.SourceValue IxVM.F → Address → Prop
  /-- (L1 → L4, L5) The value `ptr` (`&KernelTypes::KConstantInfo`) points to
  IxVM's converted constant of the record bytes `bytes`, which represents the
  kernel reader's reading of them. -/
  loaded : Aiur.Heap IxVM.F → Aiur.SourceValue IxVM.F → ByteArray → Prop
  /-- (L3, L4) In the kernel environment `env` read from the Ixon records `E`, at
  opening depth `depth` and under `binders` local binders, the IxVM value `v` (a
  `KernelTypes::KExpr`) represents the kernel term `t` (whose loose bound
  variables are the local binders). It pairs each binder with its validated `pw`
  datum, and relates levels up to semantic equality. -/
  term : Ixon.Env → Ix.Kernel.Env .anon → (depth binders : Nat) →
    Aiur.Heap IxVM.F → Aiur.SourceValue IxVM.F → Ix.Kernel.Expr .anon → Prop
  /-- (L4) The role context `rc` (`KernelRoles::RoleCtx`) and the context list
  `types` represent the environment `env` read from `E` and the opening depth
  `depth`, with the types of the opened variables. -/
  ctx : Ixon.Env → Ix.Kernel.Env .anon → Nat → Aiur.Heap IxVM.F →
    (rc types : Aiur.SourceValue IxVM.F) → Prop
  /-- (L6 → L7) The derivation's claim phase, under the role table `t`, walked
  the closure of `seeds` in the loaded records `E` and checked every constant of
  that closure and of the table's role closure (`KernelClaim::run_check_transitive`,
  `run_check_env`, `KernelRoles::load_role_ctx`). L7 reads the walked closure with
  the kernel's reader (`ReadIn`), which declines a record outside Lean's logic, so
  the instance L7 uses must also say that every walked record is in Lean's logic:
  the seeds by the claim's refusal (`ClaimPhase`), the others by `assert_safety`
  (a safe constant references none outside) and by a uniform-safety check on
  every walked block (without it a safe seed can reach an unsafe member of a
  block whose members differ in safety). -/
  Walked : List (Call IxVM.F) → Ix.Kernel.RoleTable → Ixon.Env → List Address → Prop
  /-- (L7 → L5) The
  derivation contains IxVM's accepting checks of every constant the declaration
  `d` installs, against records whose reading installed `env`. -/
  Checked : List (Call IxVM.F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop

variable (S : Seams)

/-! ## L1 to L7 -/

/-- **L1's content: a record load returns the reading of bytes the run hashed**
(`Ingress::get_ci` → `load_verified_constant`, `IxonDeserialize`, `Convert`,
`Blake3`): every bounded derivation of `get_ci` on an address returns a pointer to
the converted constant of a byte string its calls hashed under that address. -/
def Records : Prop :=
  ∀ (args : List (Aiur.SourceValue IxVM.F)) (heap after : Aiur.Heap IxVM.F)
    (ptr : Aiur.SourceValue IxVM.F) (cs : List (Call IxVM.F)),
    ObsFn IxVM.source.world "Ingress::get_ci" args heap ptr after cs → Bounded cs →
    ∀ (v : Aiur.SourceValue IxVM.F) (a : Address), args = [v] → S.addr heap v a →
      ∃ bytes, Hashed cs bytes ∧ Address.blake3Pure bytes = a ∧ S.loaded after ptr bytes

/-- **Obligation L1** (bytes to records). -/
def L1 : Prop := Records S

/-- **L2's content: the level comparisons are sound for `Level.eval`, with no
depth hypothesis, and the zero test is exact** (`KernelLevels`): on bounded
derivations (the bound replaces a hypothesis `levelDepth < 2^32`: lengths are
compared as field elements),
`level_leq = 1` gives `≤` and `level_equal = 1` gives `=` at every assignment,
and `level_equal(l, Zero) = 0` refutes that `l` is zero at every assignment (the
zero test `k_infer_proj` relies on). Levels are represented by the
level slice's `RepKLevel`. -/
def Levels : Prop :=
  (∀ (a b : Aiur.SourceValue IxVM.F) (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F))
      (la lb : Ix.Kernel.Level),
    ObsFn IxVM.source.world "KernelLevels::level_leq" [a, b] heap (.field 1) after cs →
    Bounded cs → KernelLevels.RepKLevel heap la a → KernelLevels.RepKLevel heap lb b →
      ∀ φ, Ix.Kernel.Level.eval φ la ≤ Ix.Kernel.Level.eval φ lb) ∧
  (∀ (a b : Aiur.SourceValue IxVM.F) (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F))
      (la lb : Ix.Kernel.Level),
    ObsFn IxVM.source.world "KernelLevels::level_equal" [a, b] heap (.field 1) after cs →
    Bounded cs → KernelLevels.RepKLevel heap la a → KernelLevels.RepKLevel heap lb b →
      ∀ φ, Ix.Kernel.Level.eval φ la = Ix.Kernel.Level.eval φ lb) ∧
  (∀ (a b : Aiur.SourceValue IxVM.F) (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F))
      (la : Ix.Kernel.Level),
    ObsFn IxVM.source.world "KernelLevels::level_equal" [a, b] heap (.field 0) after cs →
    Bounded cs → KernelLevels.RepKLevel heap la a → KernelLevels.RepKLevel heap .zero b →
      ¬ ∀ φ, Ix.Kernel.Level.eval φ la = 0)

/-- **Obligation L2** (levels). -/
def L2 : Prop := Levels

/-- **L3's content: substitution and lifting refine the kernel's**
(`KernelSubst`): instantiating a body's bound variable with a term represents the
kernel's `instantiate1`, and lifting a term over one binder represents the same
kernel term one depth deeper (the kernel's opened variables are absolute). The
level instantiation `expr_inst_levels` is related up to the level equivalence the
term seam uses, and is not stated here. -/
def Terms : Prop :=
  (∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (n : Nat) (e arg r : Aiur.SourceValue IxVM.F)
      (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F)) (tb ta : Ix.Kernel.Expr .anon),
    ObsFn IxVM.source.world "KernelSubst::expr_inst1" [e, arg, .field 0] heap r after cs →
    Bounded cs → S.term E env n 1 heap e tb → S.term E env n 0 heap arg ta →
      S.term E env n 0 after r (tb.instantiate1 ta)) ∧
  (∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (n : Nat) (e r : Aiur.SourceValue IxVM.F)
      (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F)) (t : Ix.Kernel.Expr .anon),
    ObsFn IxVM.source.world "KernelSubst::expr_lift" [e, .field 1, .field 0] heap r after cs →
    Bounded cs → S.term E env n 0 heap e t → S.term E env (n + 1) 0 after r t)

/-- **Obligation L3** (term operations), given L2. -/
def L3 : Prop := Levels → Terms S

/-- **L4's content: the core is sound against the rules tier**:
on represented inputs, every bounded derivation of `whnf(e) = e'` gives
`Rules.Red env d e e'`, of `is_def_eq(a, b) = 1` gives `Rules.DefEq env d a b`
(nothing is claimed for `0`), and of `infer(e) = t` gives
`Rules.Infer env .full d e t`, unless the derivation hashed a collision with the
records `env` was read from (`Ingress::get_ci` reloads records inside the
core).

`Rules.*` is the kernel's rules tier. Where IxVM's core makes a move the kernel's
own checker does not, the tier has a rule for it with its own soundness proof:
`Red.deltaThm` (a theorem unfolds to its value, with the value's typing as
premises) and `Red.eqProof` (an equation's proof rewrites its left side, sound by
the `eq_law` input); further moves are added the same way. The statement is over
the program as it ships: IxVM checks a typing certificate for the argument at
binders whose datum may be `Prop`, as `Red.beta` requires, and `Core` is proved of
that program. -/
def Core : Prop :=
  ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (d : Nat) (rc types : Aiur.SourceValue IxVM.F)
    (heap after : Aiur.Heap IxVM.F) (cs : List (Call IxVM.F)),
    S.ctx E env d heap rc types → Bounded cs →
    (∀ (e r : Aiur.SourceValue IxVM.F) (te : Ix.Kernel.Expr .anon),
      ObsFn IxVM.source.world "KernelWhnf::whnf" [rc, e, types] heap r after cs →
      S.term E env d 0 heap e te →
        View.HashedCollision { env := E } [] cs ∨
        ∃ te', S.term E env d 0 after r te' ∧ Ix.Kernel.Rules.Red env d te te') ∧
    (∀ (a b : Aiur.SourceValue IxVM.F) (ta tb : Ix.Kernel.Expr .anon),
      ObsFn IxVM.source.world "KernelDefEq::k_is_def_eq" [rc, a, b, types] heap (.field 1) after cs →
      S.term E env d 0 heap a ta → S.term E env d 0 heap b tb →
        View.HashedCollision { env := E } [] cs ∨ Ix.Kernel.Rules.DefEq env d ta tb) ∧
    (∀ (e r : Aiur.SourceValue IxVM.F) (te : Ix.Kernel.Expr .anon),
      ObsFn IxVM.source.world "KernelInfer::k_infer" [rc, e, types] heap r after cs →
      S.term E env d 0 heap e te →
        View.HashedCollision { env := E } [] cs ∨
        ∃ tt, S.term E env d 0 after r tt ∧ Ix.Kernel.Rules.Infer env .full d te tt)

/-- **Obligation L4** (core), given L1 to L3. -/
def L4 : Prop := Records S → Levels → Terms S → Core S

/-- **Stored theorem values read as their constants**: every stored theorem's value
reads, is graded, and interprets as its constant's leaf, at every assignment.
`Red.deltaThm` does not need it (it carries the value's typing and is sound by
proof irrelevance); an install that stores the annotated value can keep it
(`Ix.Kernel.Model.ThmValOk`). The environment model keeps no such equation (the
kernel never unfolds a theorem), and the kernel's install stores a theorem's raw
record value (`Semantics.DeclThmRun`). -/
def ThmVal {V : Type u} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (m : Ix.Kernel.Model.EnvModel V env) : Prop :=
  ∀ (ψ : Ix.Kernel.LevelParam → Nat) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon),
    Ix.Kernel.ConstantInfo.thmInfo cv value ∈ env.consts →
      ∃ va, Ix.Kernel.Model.denoteMeta m.acval env ψ 0 value = some va ∧
        (∀ ρ : Nat → V, Ix.Kernel.Model.WellDenotedV V ρ va) ∧
        ∀ ρ : Nat → V, Ix.Kernel.Semantics.interp V ρ va =
          Ix.Kernel.Semantics.interp V ρ (m.acval cv.name ψ)

/-- **L5's content: each accepted declaration preserves an invariant that
gives the model** (against `Ix.Kernel.Model.declStep_preserves`): there is an
invariant, holding at the empty environment and giving the kernel's fold
invariant `EnvModelOk` (hence a model, `model_of_envModelOk`), such that if a
bounded derivation checked the declaration `d` against `env`, then `d` installs
into some `env₂` (`InstallStep`: every constant `d` declares, stored as declared),
and in every set theory the invariant at `env` gives it at `env₂`. So the
environment L5 stores is the reader's: a definition with its own annotated value,
a recursor with its own rules, an opaque as an axiom.

L5 chooses the invariant. It must carry what the soundness of L4's rules reads
at each prefix (`Rules.RulesInputs`, which `RulesInputs.ofSem` builds from
`EnvModelM`). The fold over derivations (`Ix.Kernel.Model.foldRules`) keeps
`EnvModelT`, `EnvModelM` with stored theorem values read. -/
def Decls : Prop :=
  ∃ Inv : (V : Type u) → [Ix.Kernel.SetTheory V] → Ix.Kernel.Env .anon → Prop,
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V Ix.Kernel.Env.empty) ∧
    (∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      Inv V env → Ix.Kernel.Model.EnvModelOk V .verified env) ∧
    ∀ (calls : List (Call IxVM.F)) (env : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon),
      Bounded calls → S.Checked calls env d →
        ∃ env₂, InstallStep env d env₂ ∧
          ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env → Inv V env₂

/-- **Obligation L5** (declarations), given L1 to L4. -/
def L5 : Prop := Records S → Levels → Terms S → Core S → Decls.{u} S

/-- **L6's content: an in-scope claim's run read its role table, refused seeds
outside Lean's logic and inert seeds, and walked the closure of its seeds**
(`KernelClaim`, `KernelRoles`, `KernelRoleSpec`): for a bounded `verify_claim`
derivation, every claim byte string with the public digest that decodes to an
in-scope claim, every reader's view of its seeds and every role table the reader
reads it under (`ReaderTable`), the run hashed a collision, or the table admits
(`t`), no seed's loaded record or block is unsafe or `partial` and no seed is an
inert axiom of `t` (`InertAt`; the refusals of `KernelClaim::assert_claimable`,
which runs after the context loads and before any walk; both records are loaded,
so they are in `LoadedBy calls E₀`), and the run walked the closure of the seeds
in records it loaded, under `t` (`Seams.Walked`). -/
def ClaimPhase : Prop :=
  ∀ (d : Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
    (calls : List (Call IxVM.F)),
    ObsFn IxVM.source.world verifyClaim [digestValue d] [] value heap calls → Bounded calls →
    ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
      packDigest (Address.blake3Pure bytes) = d → InScope c →
      ∀ (V : View) (seeds : List Address) (b : Binding), ClaimSeeds c V seeds →
        ReaderTable c V b →
        V.HashedCollision (bytes :: b.bytes :: committedImages) calls ∨
        ∃ (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env),
          Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t ∧
          LoadedBy calls E₀ ∧ (∀ a ∈ seeds, ¬ OutsideLogicAt E₀ a ∧ ¬ InertAt t a) ∧
          S.Walked calls t E₀ seeds

/-- **Obligation L6** (claims and roles), given L1. -/
def L6 : Prop := Records S → ClaimPhase S

/-- **Obligation L7** (assembly, the `IxVM` module): from L1, L5 and L6, the
source-level statement. Its job: read the walked closure with the kernel's
reader (`ReadIn`), order the checked declarations by the reading, produce
`Seams.Checked` for each at its prefix, fold `Decls`'s invariant from the empty environment to a
model (through `EnvModelOk` and `model_of_envModelOk`), restrict it to the claimed
sub-environment (`claimedEnv`, `claimedModel`: `Denotes` agrees between `env` and
`claimedEnv env` on terms that mention no model-family key, the lookups and projection
tables being the same; the claimed types and definitions' values mention none), and
place the seeds (`SeedStored`). -/
def L7 : Prop := Records S → Decls.{u} S → ClaimPhase S → SourceSoundBounded ConsistencySpec.{u}

end IxVM.Consistency

open IxVM.Consistency in
/-- **`IxVM.consistent`**: the deployed IxVM circuit accepts only claims whose
claimed environment has a model (`CircuitConsistent`), from one obligation per
layer, whatever the seams between them. -/
theorem IxVM.consistent (S : Seams) (h0 : L0) (h1 : L1 S) (h2 : L2) (h3 : L3 S) (h4 : L4 S)
    (h5 : L5.{u} S) (h6 : L6 S) (h7 : L7.{u} S) : CircuitConsistent.{u} :=
  have terms : Terms S := h3 h2
  have core : Core S := h4 h1 h2 terms
  have decls : Decls.{u} S := h5 h1 h2 terms core
  circuitSound_of_bounded h0 (h7 h1 decls (h6 h1))
