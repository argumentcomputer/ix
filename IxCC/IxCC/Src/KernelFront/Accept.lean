import IxCC.Ixon.V3.Env
import IxCC.Src.KernelFront.Order
import IxCK.Kernel.Admission.Tier

/-! # Acceptance of an environment by the certified kernel

The kernel front end's first step: the environment IxCC decoded
(`V3.decodeAnonymousEnv`, IxCC's framing of the `.ixe` envelope, which the
kernel package does not frame) is handed, record for record and byte for byte,
to the certified kernel's tiered entry, which authenticates, reads, checks and
installs it:

    role-bound envelope → records and blobs by address, the binding section
      → the artifact's prelude records, the check order (`Order`, untrusted)
      → `Ix.Kernel.Admission.checkBytesTieredUsing`:
          byte admission of every record, the role table's admission,
          canonical decoding, the partition into logical and tier records,
          `checkConstantsWith` (the kernel's reader and the verified fold
          `Ix.Kernel.Cached.checkDecls .verified`) over the logical records,
          the typing tier over the `partial` and `unsafe` definitions

The tiered entry is the whole-artifact entry `ix check-lean` admits a
role-bound artifact with: a closure Lean's compiler wrote holds `partial` and
`unsafe` definitions (the compiler's companions of other definitions), which
the logical entry alone (`checkBytesWith`) declines. Its logical part is
`checkConstantsWith` unchanged, so every theorem about that entry applies to
the logical environment as stated (`Ix.Kernel.Admission.checkConstantsTiered_ok`:
the reading's fidelity, a model, a strong model through
`Ix.Kernel.Cached.checkDecls_strongModel`); the tier constants are typed with
every tier constant opaque and are absent from the logical environment, and no
logical record names one (the entry's fence). IxCC's own policy then refuses a
program that reaches a tier constant (`Src.Admit`, codes `partial` and
`unsafe`).

The hash is IxCC's pure BLAKE3 (`hash`), the function IxCC authenticates with;
the prelude is the artifact's own records of the prelude roles, read by the
kernel's reader under the artifact's table, as `ix check-lean` admits an
artifact; the limits are IxCC's decoder's caps (`defaultLimits`), so the
entry's batch limits never refuse what ingress let through.

Besides the entry's verdict the front end keeps the reader's declarations of
the logical records and the tier reader's declarations of the tier records
(`Accepted.decls`, `Accepted.tierDecls`): the reading the annotator asks the
kernel about. They are the reader's output on the same inputs as the entry's
(`Accepted.read`, `Accepted.tierRead`).

Only role-bound environments are accepted: the kernel admits a closure only
under a role table. A closure the kernel declines or rejects is refused with
the kernel's reason (`Refusal`). -/

namespace IxCC.Src.KernelFront

open Ix.Kernel (ConstRef Role)

/-- The kernel entry's content hash: IxCC's pure BLAKE3
(`IxCC.Ixon.Address.blake3Pure`), with the kernel's address type. -/
def hash (bytes : ByteArray) : KAddr := ⟨(Ixon.Address.blake3Pure bytes).hash⟩

/-- The kernel's address of one of IxCC's. -/
def kaddr (a : Ixon.Address) : KAddr := ⟨a.hash⟩

/-- The entry's batch limits: IxCC's decoder's caps (16,384 constants and as
many blobs, 16 MiB in all, 1 MiB per record, its universe-node budget), so a
closure IxCC's ingress read passes the entry's preflight. -/
def defaultLimits : Ix.Kernel.Admission.Limits :=
  { maxRecords := 16384, maxBlobs := 16384, maxTotalBytes := 16 * 1024 * 1024,
    maxRecordBytes := 1024 * 1024, maxRecordUnivNodes := Ixon.V3.univNodeLimit }

/-- Where the front end refused an environment. -/
inductive Stage where
  /-- the envelope is not role-bound -/
  | envelope
  /-- byte admission or decoding -/
  | bytes
  /-- the role table's admission -/
  | binding
  /-- the table binds a role to no member of the closure, or a member twice;
  or the prepared inputs are not the envelope's -/
  | coverage
  /-- the artifact's prelude records -/
  | prelude
  /-- the kernel's reader -/
  | read
  /-- the verified fold, the fence or the typing tier -/
  | kernel
  deriving Repr, BEq, Inhabited

def Stage.word : Stage → String
  | .envelope => "envelope" | .bytes => "bytes" | .binding => "binding"
  | .coverage => "coverage" | .prelude => "prelude" | .read => "read" | .kernel => "kernel"

/-- The kernel's two declines of policy, not of typing: the artifact uses
`sorryAx` (the kernel installs nothing for it), or holds an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. Both are the kernel's
`CheckError.notImplemented`, which has no constructor of its own for either,
so they are told apart by the leading prose part of its structured message
(`MsgPart.text`), not by the rendered line. -/
inductive PolicyDecline where
  | sorryAx
  | nonStandardAxiom
  deriving Repr, BEq, Inhabited

/-- The policy decline a kernel failure is, if it is one. -/
def policyOf : Ix.Kernel.CheckError .anon → Option PolicyDecline
  | .notImplemented (.text s _ :: _) =>
    if s.startsWith "use of the sorryAx axiom" then some .sorryAx
    else if s.startsWith "non-standard axiom" then some .nonStandardAxiom
    else none
  | _ => none

/-- A refusal, with the kernel's own classification where it gave one
(`Ix.Kernel.Admission.TierError.outcome`: a reject where the input is shown
wrong, a decline otherwise), and the record it names where the kernel's error
names one by address or by its position among the records (for the census;
an error at a declaration of the logical fold names a declaration, not a
record). -/
structure Refusal where
  stage : Stage
  outcome : Option Ix.Kernel.Admission.Outcome := none
  message : String
  record : Option KAddr := none
  /-- The kernel's policy decline, if the refusal is one (`policyOf`). -/
  policy : Option PolicyDecline := none
  deriving Inhabited

def Refusal.render (r : Refusal) : String :=
  let o := match r.outcome with
    | some .rejected => " (rejected)"
    | some .declined => " (declined)"
    | none => ""
  s!"kernel front end, {r.stage.word}{o}: {r.message}"

/-- A plain-words line for the kernel's two policy declines, which `ixcc` prints
after the kernel's own line. -/
def PolicyDecline.explain : PolicyDecline → String
  | .sorryAx =>
    "the artifact holds a use of `sorry` (`sorryAx`) somewhere among its records; the certified \
    kernel accepts an artifact only whole, so every root of it is refused, reached or not \
    (IxCC/docs/compile-boundary.md, \"What ingress refuses, and how\")"
  | .nonStandardAxiom =>
    "the artifact holds an axiom other than `propext`, `Classical.choice` and `Quot.sound` \
    somewhere among its records; the certified kernel accepts an artifact only whole, so \
    every root of it is refused, reached or not (IxCC/docs/compile-boundary.md, \"What \
    ingress refuses, and how\")"

/-- The refusal as ingress reports it: the kernel's line, and for a policy
decline one more line in plain words (`PolicyDecline.explain`). -/
def Refusal.report (r : Refusal) : String :=
  match r.policy with
  | some p => r.render ++ "\n" ++ p.explain
  | none => r.render

instance : ToString Refusal := ⟨Refusal.render⟩

/-- A logical entry's failure as a refusal. -/
def Refusal.ofError (e : Ix.Kernel.Admission.Error) : Refusal :=
  let stage : Stage := match e with
    | .limit _ | .duplicate .. | .mismatch .. | .decode .. => .bytes
    | .binding _ => .binding
    | .prelude _ | .preludeCopy => .prelude
    | .read .. => .read
    | .kernel .. | .axiomRoleUnbound _ => .kernel
  let record : Option KAddr := match e with
    | .duplicate _ _ a | .mismatch _ _ a | .decode _ a _ => some a
    | _ => none
  let policy : Option PolicyDecline := match e with
    | .kernel ce _ => policyOf ce
    | _ => none
  { stage, outcome := some e.outcome, message := toString e, record, policy }

/-- A tiered entry's failure as a refusal, a record position read back to the
record's address. -/
def Refusal.ofTierError (records : Ix.Kernel.Admission.Records)
    (e : Ix.Kernel.Admission.TierError) : Refusal :=
  let at_ (i : Nat) : String := match records[i]? with
    | some (a, _) => s!" (record {a})"
    | none => ""
  match e with
  | .entry e' => { Refusal.ofError e' with outcome := some e.outcome }
  | .fence a _ => { stage := .kernel, outcome := some e.outcome, message := toString e, record := some a }
  | .read i _ => { stage := .read, outcome := some e.outcome, message := toString e ++ at_ i,
                   record := records[i]?.map (·.1) }
  | .tier ce i => { stage := .kernel, outcome := some e.outcome, message := toString e ++ at_ i,
                     record := records[i]?.map (·.1), policy := policyOf ce }

/-- The closure's records and blobs by address, sorted, in the kernel's types. -/
def recordsOf (env : Ixon.V3.Env) : Array (KAddr × ByteArray) :=
  (env.consts.toArray.map fun (a, b) => (kaddr a, b)).qsort fun x y => x.1.cmpBytes y.1 == .lt

def blobsOf (env : Ixon.V3.Env) : List (KAddr × ByteArray) :=
  ((env.blobs.toArray.map fun (a, b) => (kaddr a, b)).qsort fun x y => x.1.cmpBytes y.1 == .lt).toList

/-- The records sorted by address, as `recordsOf` gives them: what the
acceptance compares the ordered records with. -/
def sortRecords (records : List (KAddr × ByteArray)) : List (KAddr × ByteArray) :=
  (records.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList

/-- The prelude source the entry is given: the artifact's own prelude. -/
def preludeSource (pre : Ix.Kernel.Reader.Prelude .anon) :
    Ix.Kernel.RoleTable → Except String (Ix.Kernel.Reader.Prelude .anon) :=
  fun _ => .ok pre

/-- What the kernel accepted: the entry's inputs in the order they were
supplied, its verdict, and the reading the annotator asks the kernel about,
with the runs that produced them. -/
structure Accepted where
  binding : Ix.Kernel.Admission.Binding
  table : Ix.Kernel.RoleTable
  pre : Ix.Kernel.Reader.Prelude .anon
  limits : Ix.Kernel.Admission.Limits
  /-- The closure's records, in check order. -/
  records : Ix.Kernel.Admission.Records
  blobs : Ix.Kernel.Ingress.Blobs
  /-- The logical environment the entry installed. -/
  env : Ix.Kernel.Env .anon
  /-- The tier constants (the `partial` and `unsafe` definitions), typed. -/
  tier : List (Ix.Kernel.Tier.TierConst .anon)
  /-- **The entry's accept.** -/
  accepted : Ix.Kernel.Admission.checkBytesTieredUsing (preludeSource pre) hash binding limits
    records blobs = .ok (env, tier)
  /-- The records, decoded by the kernel's canonical decoder, in check order. -/
  constants : List (KAddr × KConstant)
  decoded : Ix.Kernel.Admission.decodeRecords limits records = .ok constants
  /-- The reader's declarations of the logical records, behind the prelude:
  what the fold ran over. -/
  evidence : Ix.Kernel.Evidences .anon
  readDecls : Array (Ix.Kernel.Declaration .anon)
  read : Ix.Kernel.Admission.readStream hash table pre
    (Ix.Kernel.Admission.partitionTier constants).1 blobs = .ok (evidence, readDecls)
  /-- The tier reader's declarations of the tier records. -/
  tierDecls : Array (Nat × Ix.Kernel.Tier.TierDecl .anon)
  tierRead : Ix.Kernel.Admission.readTier
    (Ix.Kernel.Admission.streamContext hash table pre constants blobs (fun _ => none))
    (Ix.Kernel.Admission.partitionTier constants).2 = .ok tierDecls

/-- The declarations the fold ran over: the reader's, behind the prelude. -/
def Accepted.decls (a : Accepted) : Array (Ix.Kernel.Declaration .anon) :=
  Ix.Kernel.Frontend.preparePrelude a.pre.ix a.readDecls

/-- The reader's context for the accepted records: the stores, the role
bindings and the keys the reading gave every reference
(`Ix.Kernel.Admission.streamContext`, as the entry builds it for the tier
reader). -/
def Accepted.ctx (a : Accepted) : Ix.Kernel.Reader.Ctx .anon :=
  Ix.Kernel.Admission.streamContext hash a.table a.pre a.constants a.blobs (fun _ => none)

/-- The entry's inputs before it runs: the binding section, the admitted
table, the artifact's prelude and the records in check order. Every one is a
choice of the host's (`Order`); the entry's theorems hold for each. -/
structure Prepared where
  binding : Ix.Kernel.Admission.Binding
  table : Ix.Kernel.RoleTable
  pre : Ix.Kernel.Reader.Prelude .anon
  records : Ix.Kernel.Admission.Records

/-- **The entry's inputs for a decoded environment** (untrusted): the
role-bound envelope's binding section, the table it admits, the artifact's own
prelude records read under it, and the closure's records in the kernel's check
order (`Order.wholeEnv`). -/
def prepare (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits) : Except Refusal Prepared := do
  let some b := env.binding
    | throw { stage := .envelope, message := "the kernel admits only role-bound environments (0xE5); this one is unbound" }
  let binding : Ix.Kernel.Admission.Binding := ⟨kaddr b.address, b.bytes⟩
  let sorted := recordsOf env
  let blobs := blobsOf env
  let table ← (Ix.Kernel.Admission.admitBinding hash binding).mapError fun e =>
    Refusal.ofError (.binding e)
  let decoded ← (Ix.Kernel.Admission.decodeRecords limits sorted.toList).mapError fun e =>
    Refusal.ofError (Ix.Kernel.Admission.Error.ofBytes e)
  let store : RecordStore := decoded.foldl (fun m (a, c) => m.insert a c) {}
  (Order.checkBindings table store).mapError fun m => { stage := .coverage, message := m }
  let preRecords ← (Order.preludeRecords table (store[·]?) Ix.Kernel.preludeShape).mapError
    fun m => { stage := .prelude, message := m }
  let pre : Ix.Kernel.Reader.Prelude .anon ←
    (Ix.Kernel.Reader.readPrelude table preRecords #[] blobs).mapError
      fun m => { stage := .prelude, message := m }
  (Ix.Kernel.Reader.checkPreludeShape pre).mapError fun m => { stage := .prelude, message := m }
  (Ix.Kernel.Reader.checkFallbackRecursors pre).mapError fun m => { stage := .prelude, message := m }
  let order := Order.wholeEnv table pre decoded.toArray
  unless order.size == sorted.size do
    throw { stage := .coverage, message := s!"the check order covers {order.size} of {sorted.size} records" }
  let bytesAt : Std.HashMap KAddr ByteArray := sorted.foldl (fun m (a, x) => m.insert a x) {}
  let mut ordered : Array (KAddr × ByteArray) := Array.mkEmpty order.size
  for a in order do
    let some x := bytesAt[a]? | throw { stage := .coverage, message := s!"unknown ordered record {a}" }
    ordered := ordered.push (a, x)
  pure { binding, table, pre, records := ordered.toList }

/-- **What an acceptance of `env` is about**: the environment is role-bound;
the entry ran on its binding section, on exactly its records (sorted by
address the entry's records are the envelope's) and on exactly its blobs, at
the given batch limits. -/
def AcceptedFrom (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits) (a : Accepted) : Prop :=
  ∃ b, env.binding = some b ∧ (a.binding.address = kaddr b.address ∧ a.binding.bytes = b.bytes) ∧
    sortRecords a.records = (recordsOf env).toList ∧ a.blobs = blobsOf env ∧ a.limits = limits

/-- **The kernel's entry on prepared inputs**: refused unless the binding is
the envelope's and the records are exactly the envelope's (the same
address-and-bytes pairs, in the check order), then the tiered entry, refused
with the kernel's reason; then the reader's declarations of the same inputs,
which the annotator asks about. -/
def acceptPrepared (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits) (p : Prepared) :
    Except Refusal { a : Accepted // AcceptedFrom env limits a } :=
  match hb : env.binding with
  | none => throw { stage := .envelope, message := "the kernel admits only role-bound environments (0xE5); this one is unbound" }
  | some b =>
    if h1 : p.binding.address = kaddr b.address ∧ p.binding.bytes = b.bytes then
      if h2 : sortRecords p.records = (recordsOf env).toList then
        let blobs := blobsOf env
        match ha : Ix.Kernel.Admission.checkBytesTieredUsing (preludeSource p.pre) hash p.binding limits
            p.records blobs with
        | .error e => throw (Refusal.ofTierError p.records e)
        | .ok (kenv, tier) =>
          match hd : Ix.Kernel.Admission.decodeRecords limits p.records with
          | .error e => throw (Refusal.ofError (Ix.Kernel.Admission.Error.ofBytes e))
          | .ok constants =>
            match hr : Ix.Kernel.Admission.readStream hash p.table p.pre
                (Ix.Kernel.Admission.partitionTier constants).1 blobs with
            | .error e => throw (Refusal.ofError e)
            | .ok (evidence, readDecls) =>
              match ht : Ix.Kernel.Admission.readTier
                  (Ix.Kernel.Admission.streamContext hash p.table p.pre constants blobs (fun _ => none))
                  (Ix.Kernel.Admission.partitionTier constants).2 with
              | .error (i, e) => throw (Refusal.ofTierError p.records (.read i e))
              | .ok tierDecls =>
                pure ⟨{ binding := p.binding, table := p.table, pre := p.pre, limits,
                        records := p.records, blobs, env := kenv, tier, accepted := ha,
                        constants, decoded := hd, evidence, readDecls, read := hr,
                        tierDecls, tierRead := ht },
                      ⟨b, hb, h1, h2, rfl, rfl⟩⟩
      else throw { stage := .coverage, message := "the ordered records are not the envelope's records" }
    else throw { stage := .coverage, message := "the prepared binding is not the envelope's" }

/-- **The kernel's acceptance of a decoded environment.** Refuses an unbound
envelope, and refuses with the kernel's reason whatever the kernel's entry
does not accept. -/
def accept (env : Ixon.V3.Env) (limits : Ix.Kernel.Admission.Limits := defaultLimits) :
    Except Refusal Accepted := do
  let p ← prepare env limits
  let a ← acceptPrepared env limits p
  pure a.val

/-- **What an acceptance is.** The environment is role-bound; the kernel's
tiered entry ran on its binding section, on exactly its records (sorted by
address they are the envelope's) and on exactly its blobs, at IxCC's hash, and
accepted them, installing the accepted logical environment. Every theorem of
the tiered entry then applies (`Ix.Kernel.Admission.checkBytesTieredUsing_ok`,
`checkConstantsTiered_ok`). -/
theorem accept_spec {env : Ixon.V3.Env} {limits : Ix.Kernel.Admission.Limits} {a : Accepted}
    (h : accept env limits = .ok a) :
    AcceptedFrom env limits a ∧
      Ix.Kernel.Admission.checkBytesTieredUsing (preludeSource a.pre) hash a.binding a.limits
        a.records a.blobs = .ok (a.env, a.tier) := by
  refine ⟨?_, a.accepted⟩
  unfold accept at h
  cases hp : prepare env limits with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    cases hq : acceptPrepared env limits p with
    | error e => simp [hp, hq, bind, Except.bind] at h
    | ok q =>
      simp only [hp, hq, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact q.property

end IxCC.Src.KernelFront
