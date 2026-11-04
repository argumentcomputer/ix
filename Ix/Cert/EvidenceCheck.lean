import Ix.Cert.EvidenceReading
import Ix.Cert.Statement
import Ix.LeanIngress.Rename
import IxC.Kernel.Admission

/-! # Quotient Source's bundle against the role table's evidence, on an artifact

Quotient Source reads the default table's own evidence records by name
(`Ix.RoleEvidence.quotientBundle`). Renamed onto an artifact's keys, its proofs are the
ones the Ixon reader resolves from the table in a closure's reading context, provided
the artifact and the committed data agree as this module checks (`evidenceCheck`, part
of the artifact checks), on the artifact plus the committed data only:

* **shape**: at every operation role, the bundle's evidence is the table's entries, each
  proof the bundle's reading of the record at the entry's address (`expectedOf`);
* **records**: every such record is a safe theorem record whose statement and value
  read by name, whose value does not end in a projection of its last binder, which the
  reader's fallback holds at its address and the artifact holds there, if at all,
  identically;
* **names**: every name a record cites renames (onto the fiber representatives, then to
  the artifact's addresses) to the key the reader gives the cited address over the
  artifact's store, and no other bound role address resolves to that reference;
* **blobs**: every blob a record cites is the artifact's, if the artifact has one there,
  and the fallback's first;
* **reach**: every address a well-founded operation's records cite lies in the compiled
  closure of the operation's address (references, projections' blocks and the
  operation's ground), or resolves alike from the reader's fallback alone; and no
  operation's address is a fallback record.

`evidenceCheck_sound` turns the executed check into `Agree`. -/

-- Records are compared whole: the artifact's copy of a fallback record must be the fallback's.
deriving instance DecidableEq for Ixon.Univ
deriving instance DecidableEq for Ixon.Expr
deriving instance DecidableEq for Ixon.Definition, Ixon.RecursorRule, Ixon.Recursor, Ixon.Axiom,
  Ixon.Quotient, Ixon.Constructor, Ixon.Inductive, Ixon.InductiveProj, Ixon.ConstructorProj,
  Ixon.RecursorProj, Ixon.DefinitionProj
deriving instance DecidableEq for Ixon.MutConst
deriving instance DecidableEq for Ixon.ConstantInfo
deriving instance DecidableEq for Ixon.Constant

namespace Ix.Cert.EvidenceCheck

open Ix.Kernel Ix.Kernel.Reader Ix.RoleEvidence Ix.Cert.EvidenceReading

/-! ## The objects compared -/

/-- The table's evidence entries for role `r`, as `Evidences.of` looks them up. -/
def tableOf (t : RoleTable) (r : Role) : List (Evidence Address) :=
  match t.evidence.toList.find? (·.1 == r) with
  | some (_, es) => es.toList
  | none => []

/-- The proof addresses among the table's entries for role `r`. -/
def proofAddrs (t : RoleTable) (r : Role) : List Address :=
  (tableOf t r).filterMap fun
    | .proof a => some a
    | .defeq => none

/-- The record the quotient bundle holds at `a`. -/
def bundleRecord (b : Bundle) (a : Address) : Option Ixon.Constant :=
  (b.records.find? (·.1 == a)).map (·.2)

/-- The operation roles: the structural and the well-founded `Nat` operations. -/
def opRoles : List Role :=
  [.natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle,
   .natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight]

/-- What the bundle's evidence for role `r` must read as: the table's entries, each proof
the bundle's reading of the record at its address, under the record's name. -/
def expectedOf (b : Bundle) (t : RoleTable) (r : Role) :
    Option (List (Evidence (Key .source × Ix.Kernel.Expr .source))) :=
  (tableOf t r).mapM fun
    | .defeq => some .defeq
    | .proof a => do
      let c ← bundleRecord b a
      let n ← b.names[a]?
      let p ← (b.proofOf c).toOption
      pure (.proof (ofLeanName n, p))

/-- The reader's fallback store: the prelude's records, then the evidence's (`contextOf`'s
fallback, first of each address). -/
def fallbackStore (preA : Prelude .anon) : Store :=
  let fm := recordMap (preA.records ++ preA.evidence)
  fun a => fm[a]?

/-- The artifact's store, behind the reader's fallback. -/
def fullStore (ixe : Ixon.Env) (preA : Prelude .anon) : Store :=
  let fb := fallbackStore preA
  fun a => Ix.Cert.recordAt ixe a <|> fb a

/-- The first fallback blob at `x` (`contextOf`'s blob map keeps the first). -/
def firstBlob (blobs : List (Address × ByteArray)) (x : Address) : Option ByteArray :=
  (blobs.find? (·.1 == x)).map (·.2)

/-! ## The compiled closure of an operation's address, computed -/

/-- The records the record at `a` needs (`RecordEdge`): its block, if `a` is a projection,
and the records of its reference table the artifact holds. -/
def recordSuccs (ixe : Ixon.Env) (a : Address) : List Address :=
  match Ix.Cert.recordAt ixe a with
  | some c =>
    (if Ix.Cert.ownerOf a c = a then [] else [Ix.Cert.ownerOf a c]) ++
      c.refs.toList.filter (ixe.consts.contains ·)
  | none => []

/-- One round of the closure: the new successors of the frontier. -/
def reachStep (ixe : Ixon.Env) (s : Std.HashSet Address) (frontier : List Address) :
    Std.HashSet Address × List Address :=
  frontier.foldl (fun acc a =>
    (recordSuccs ixe a).foldl (fun (acc : Std.HashSet Address × List Address) x =>
      if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) acc) (s, [])

/-- The closure, round by round, for at most `fuel` rounds. -/
def reachLoop (ixe : Ixon.Env) : Nat → Std.HashSet Address → List Address → Std.HashSet Address
  | 0, s, _ => s
  | fuel + 1, s, frontier =>
    if frontier.isEmpty then s
    else
      let (s', frontier') := reachStep ixe s frontier
      reachLoop ixe fuel s' frontier'

/-- The seeds of an operation's closure: its address, and the addresses of the roles its
install reads (`groundRoles`) that the artifact holds. -/
def reachSeeds (ixe : Ixon.Env) (t : RoleTable) (r : Role) (a : Address) : List Address :=
  a :: (Ix.Cert.groundRoles r).filterMap fun s => do
    let g ← t.addressOf? s
    if ixe.consts.contains g then some g else none

/-- **The compiled closure of the operation `r` at `a`**, computed (sound for
`CompiledReach` from `a`, `reach_sound`; complete only within its rounds). -/
def reachOf (ixe : Ixon.Env) (t : RoleTable) (r : Role) (a : Address) : Std.HashSet Address :=
  let seeds := reachSeeds ixe t r a
  reachLoop ixe (ixe.consts.size + 1) (seeds.foldl (·.insert ·) {}) seeds

/-! ## The check -/

/-- The conditions on a name `n` the record cites at `x`: it renames to the key the reader
gives `x` over the artifact's store, `x` resolves, no other bound role address resolves to
the same reference, and `x` lies in the operation's closure or resolves alike from the
fallback alone. -/
def citedOk (full fb : Store) (roles : Bindings .anon) (bound : List (Role × Address))
    (inReach : Address → Bool) (rename : Key .source → Key .anon) (x : Address) (n : Lean.Name) : Bool :=
  match resolve full x with
  | none => false
  | some R =>
    decide (keyOfAddress full roles x = some (rename (ofLeanName n))) &&
      bound.all (fun e => !decide (resolve full e.2 = some R) || decide (e.2 = x)) &&
      (inReach x || decide (resolve fb x = some R))

/-- The conditions on a blob the record cites at `x`: the artifact's, if any, and the
fallback's first. -/
def blobOk (ixe : Ixon.Env) (fbBlobs : List (Address × ByteArray)) (x : Address) (bs : ByteArray) : Bool :=
  (match ixe.blobs.get? x with
    | none => true
    | some bs' => decide (bs' = bs)) &&
    decide (firstBlob fbBlobs x = some bs)

/-- The conditions on the record at the proof address `a`. -/
def recordOk (ixe : Ixon.Env) (b : Bundle) (full fb : Store) (roles : Bindings .anon)
    (bound : List (Role × Address)) (fbBlobs : List (Address × ByteArray))
    (inReach : Address → Bool) (rename : Key .source → Key .anon) (a : Address) : Bool :=
  match bundleRecord b a with
  | none => false
  | some c =>
    match c.info with
    | .defn d =>
      decide (d.kind = .thm) && decide (fb a = some c) &&
        (match Ix.Cert.recordAt ixe a with
          | none => true
          | some c' => decide (c' = c)) &&
        (match b.proofOf c, typeOf b c with
          | .ok p, .ok _ =>
            match Ix.Kernel.Frontend.lamBody p with
            | .proj _ _ (.bvar 0) => false
            | _ => true
          | _, _ => false) &&
        c.refs.toList.all (fun x =>
          (match b.names[x]? with
            | some n => citedOk full fb roles bound inReach rename x n
            | none => true) &&
          (match b.blobs[x]? with
            | some bs => blobOk ixe fbBlobs x bs
            | none => true))
    | _ => false

/-- **The check**, over the objects it compares: the artifact `ixe`, the table `t` it is
compiled under, the quotient bundle `b`, the admitted table `tA` and its prelude `preA`. -/
def check (ixe : Ixon.Env) (t : RoleTable) (b : Bundle) (tA : RoleTable) (preA : Prelude .anon) : Bool :=
  let fb := fallbackStore preA
  let full := fullStore ixe preA
  let roles : Bindings .anon := bindingsOf full tA
  let bound := tA.bound.toList
  let ρ := Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t)
  let src := Ix.LeanIngress.sourceAddrs ixe
  let ba := Ix.LeanIngress.bundleAddrs b
  let f : Mode.Id .source → Mode.Id .anon := fun n =>
    match src[n]? with
    | some a => a
    | none => (ba[n]?).getD default
  let rename := renameKey ρ f
  let ev := quotientEvidence ()
  Role.all.all (fun r => decide (t.addressOf? r = tA.addressOf? r)) &&
    opRoles.all (fun r =>
      decide (expectedOf b tA r = some (ev.of r)) &&
        (match tA.addressOf? r with
          | some a => decide (fb a = none) &&
            -- an operation the artifact holds: its records
            (if (Ix.Cert.recordAt ixe a).isSome then
              let reach := reachOf ixe t r a
              let inReach := fun x => reach.contains x && (Ix.Cert.recordAt ixe x).isSome
              (proofAddrs tA r).all (recordOk ixe b full fb roles bound preA.blobs inReach rename)
            else true)
          | none => true)) &&
    -- every fallback record the artifact holds, it holds identically
    (preA.records ++ preA.evidence).toList.all (fun (a, _) =>
      match Ix.Cert.recordAt ixe a, fb a with
      | some c', some c => decide (c' = c)
      | _, _ => true)

/-- The evidence check over given sources of the bundle, the binding and the prelude. -/
def evidenceCheckOf (bundle : Except String Bundle) (binding : Except String Ix.Kernel.Admission.Binding)
    (prelude : RoleTable → Except String (Prelude .anon)) (t : RoleTable) (ixe : Ixon.Env) :
    Except String Unit :=
  match bundle, binding with
  | .ok b, .ok bd =>
    match Ix.Kernel.Admission.admitBinding Address.admissionHash bd with
    | .ok tA =>
      match prelude tA with
      | .ok preA =>
        if check ixe t b tA preA then .ok ()
        else .error "evidence check: the quotient bundle does not agree with the role table's evidence on the artifact"
      | .error e => .error e
    | .error _ => .error "evidence check: the default binding does not admit"
  | .error e, _ => .error e
  | _, .error e => .error e

/-- **The evidence check** (part of the artifact checks): the quotient bundle, the
admitted default table and its prelude, then `check`. -/
def evidenceCheck (t : RoleTable) (ixe : Ixon.Env) : Except String Unit :=
  evidenceCheckOf (quotientBundle ()) Ix.Kernel.Admission.defaultBinding preludeFor t ixe


/-! ## What the check gives -/

/-- **A name a record cites, agreeing**: `x` resolves over the artifact's store, its key
there is the name's renaming, no other bound role address resolves to the same reference,
and `x` lies in the compiled closure of the operation's address (where the artifact holds
that address) or resolves alike from the fallback alone. -/
def CitedAgree (ixe : Ixon.Env) (t : RoleTable) (b : Bundle) (tA : RoleTable) (preA : Prelude .anon)
    (r : Role) (x : Address) (n : Lean.Name) : Prop :=
  ∃ R, resolve (fullStore ixe preA) x = some R ∧
    keyOfAddress (fullStore ixe preA) (bindingsOf (md := .anon) (fullStore ixe preA) tA) x =
      some (renameKey (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t))
        (Ix.LeanIngress.evAddr ixe b) (ofLeanName n)) ∧
    (∀ e ∈ tA.bound.toList, resolve (fullStore ixe preA) e.2 = some R → e.2 = x) ∧
    ((∀ a, tA.addressOf? r = some a →
        Ix.Cert.CompiledReach ixe (· = a) x ∧ (Ix.Cert.recordAt ixe x).isSome) ∨
      resolve (fallbackStore preA) x = some R)

/-- **A proof record, agreeing**: the conditions `recordOk` checks. -/
def RecordAgree (ixe : Ixon.Env) (t : RoleTable) (b : Bundle) (tA : RoleTable) (preA : Prelude .anon)
    (r : Role) (a : Address) : Prop :=
  ∃ c d p T, bundleRecord b a = some c ∧ c.info = .defn d ∧ d.kind = .thm ∧
    fallbackStore preA a = some c ∧ (Ix.Cert.recordAt ixe a = none ∨ Ix.Cert.recordAt ixe a = some c) ∧
    b.proofOf c = .ok p ∧ typeOf b c = .ok T ∧
    (∀ s i, Ix.Kernel.Frontend.lamBody p ≠ .proj s i (.bvar 0)) ∧
    (∀ x ∈ c.refs, ∀ n, b.names[x]? = some n → CitedAgree ixe t b tA preA r x n) ∧
    (∀ x ∈ c.refs, ∀ bs, b.blobs[x]? = some bs →
      (ixe.blobs.get? x = none ∨ ixe.blobs.get? x = some bs) ∧ firstBlob preA.blobs x = some bs)

/-- **What the evidence check gives** on the artifact `ixe` compiled under `t`, for the
quotient bundle `b`, the admitted table `tA` and its prelude `preA`. -/
structure Agree (ixe : Ixon.Env) (t : RoleTable) (b : Bundle) (tA : RoleTable) (preA : Prelude .anon) :
    Prop where
  addrs : ∀ r, t.addressOf? r = tA.addressOf? r
  shape : ∀ r ∈ opRoles, expectedOf b tA r = some ((quotientEvidence ()).of r)
  opAddr : ∀ r ∈ opRoles, ∀ a, tA.addressOf? r = some a → fallbackStore preA a = none
  fallback : ∀ a c c', fallbackStore preA a = some c → Ix.Cert.recordAt ixe a = some c' → c' = c
  records : ∀ r ∈ opRoles, ∀ A, tA.addressOf? r = some A → (Ix.Cert.recordAt ixe A).isSome →
    ∀ a ∈ proofAddrs tA r, RecordAgree ixe t b tA preA r a

/-! ## Soundness of the computed closure -/

theorem recordSuccs_edge {ixe : Ixon.Env} {a x : Address} (h : x ∈ recordSuccs ixe a) :
    Ix.Cert.RecordEdge ixe a x := by
  unfold recordSuccs at h
  cases hc : Ix.Cert.recordAt ixe a with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    refine ⟨c, hc, ?_⟩
    rcases List.mem_append.mp h with h | h
    · split at h
      · cases h
      · rename_i hne
        rw [List.mem_singleton] at h
        exact .inl ⟨h.symm, fun e => hne (by rw [← h]; exact e)⟩
    · rw [List.mem_filter] at h
      exact .inr ⟨Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp h.1), h.2⟩

theorem reachStep_sound {ixe : Ixon.Env} {P : Address → Prop}
    (hP : ∀ a x, P a → x ∈ recordSuccs ixe a → P x) :
    ∀ (frontier : List Address) (acc : Std.HashSet Address × List Address),
      (∀ x, acc.1.contains x = true → P x) → (∀ x ∈ acc.2, P x) → (∀ a ∈ frontier, P a) →
      let out := frontier.foldl (fun acc a =>
        (recordSuccs ixe a).foldl (fun (acc : Std.HashSet Address × List Address) x =>
          if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) acc) acc
      (∀ x, out.1.contains x = true → P x) ∧ (∀ x ∈ out.2, P x)
  | [], acc, h1, h2, _ => ⟨h1, h2⟩
  | a :: frontier, acc, h1, h2, hf => by
    simp only [List.foldl_cons]
    have inner : ∀ (xs : List Address) (acc : Std.HashSet Address × List Address),
        (∀ x ∈ xs, P x) → (∀ x, acc.1.contains x = true → P x) → (∀ x ∈ acc.2, P x) →
        let out := xs.foldl (fun (acc : Std.HashSet Address × List Address) x =>
          if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) acc
        (∀ x, out.1.contains x = true → P x) ∧ (∀ x ∈ out.2, P x) := by
      intro xs
      induction xs with
      | nil => intro acc _ h1 h2; exact ⟨h1, h2⟩
      | cons x xs ih =>
        intro acc hx h1 h2
        simp only [List.foldl_cons]
        apply ih _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        · split
          · exact h1
          · intro y hy
            rw [Std.HashSet.contains_insert] at hy
            rcases Bool.or_eq_true_iff.mp hy with hy | hy
            · rw [← beq_iff_eq.mp hy]; exact hx x (List.mem_cons_self ..)
            · exact h1 y hy
        · split
          · exact h2
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx _ (List.mem_cons_self ..)
            · exact h2 y hy
    obtain ⟨o1, o2⟩ := inner (recordSuccs ixe a) acc
      (fun x hx => hP a x (hf a (List.mem_cons_self ..)) hx) h1 h2
    exact reachStep_sound hP frontier _ o1 o2 (fun b hb => hf b (List.mem_cons_of_mem _ hb))

theorem reachLoop_sound {ixe : Ixon.Env} {P : Address → Prop}
    (hP : ∀ a x, P a → x ∈ recordSuccs ixe a → P x) :
    ∀ (fuel : Nat) (s : Std.HashSet Address) (frontier : List Address),
      (∀ x, s.contains x = true → P x) → (∀ a ∈ frontier, P a) →
      ∀ x, (reachLoop ixe fuel s frontier).contains x = true → P x
  | 0, s, _, hs, _ => by simpa [reachLoop] using hs
  | fuel + 1, s, frontier, hs, hf => by
    unfold reachLoop
    split
    · exact hs
    · have h := reachStep_sound hP frontier (s, []) hs (by simp) hf
      exact reachLoop_sound hP fuel _ _ h.1 h.2

/-- **The computed closure is in the compiled closure** of the operation's address, where
the artifact holds that address and the table compiled under is the default one. -/
theorem reach_sound {ixe : Ixon.Env} {t : RoleTable} {r : Role} {a : Address}
    (htab : Ix.Kernel.Reader.defaultTable = .ok t) (hr : t.addressOf? r = some a)
    (ha : ixe.consts.contains a = true) {x : Address} (hx : (reachOf ixe t r a).contains x = true) :
    Ix.Cert.CompiledReach ixe (· = a) x := by
  have hseed : ∀ y ∈ reachSeeds ixe t r a, Ix.Cert.CompiledReach ixe (· = a) y := by
    intro y hy
    have root : Ix.Cert.CompiledReach ixe (· = a) a := .seed rfl ha
    rcases List.mem_cons.mp hy with rfl | hy
    · exact root
    · obtain ⟨s, hs, hg⟩ := List.mem_filterMap.mp hy
      cases hgs : t.addressOf? s with
      | none => simp [hgs] at hg
      | some g =>
        have hgy : g ∈ ixe.consts ∧ g = y := by simpa [hgs] using hg
        obtain ⟨hmem, rfl⟩ := hgy
        have hc : ixe.consts.contains g = true := Std.HashMap.mem_iff_contains.mp hmem
        exact .ground root ⟨hc, t, htab, s, hgs, .inl ⟨r, a, hr, hs, .inl rfl⟩⟩
  unfold reachOf at hx
  refine reachLoop_sound (fun a x ha hx => .step ha (recordSuccs_edge hx)) _ _ _ ?_ hseed x hx
  intro y hy
  have : ∀ (l : List Address) (s : Std.HashSet Address), (∀ z, s.contains z = true → z ∈ reachSeeds ixe t r a) →
      (∀ z ∈ l, z ∈ reachSeeds ixe t r a) →
      ∀ z, (l.foldl (·.insert ·) s).contains z = true → z ∈ reachSeeds ixe t r a := by
    intro l
    induction l with
    | nil => intro s hs _ z hz; exact hs z hz
    | cons w l ih =>
      intro s hs hl z hz
      simp only [List.foldl_cons] at hz
      refine ih _ ?_ (fun z hz => hl z (List.mem_cons_of_mem _ hz)) z hz
      intro z hz
      rw [Std.HashSet.contains_insert] at hz
      rcases Bool.or_eq_true_iff.mp hz with hz | hz
      · rw [← beq_iff_eq.mp hz]; exact hl w (List.mem_cons_self ..)
      · exact hs z hz
  exact hseed y (this _ {} (by simp) (fun z hz => hz) y hy)


/-! ## Soundness of the check -/

theorem citedOk_sound {full fb : Store} {roles : Bindings .anon} {bound : List (Role × Address)}
    {inReach : Address → Bool} {rename : Key .source → Key .anon} {x : Address} {n : Lean.Name}
    (h : citedOk full fb roles bound inReach rename x n = true) :
    ∃ R, resolve full x = some R ∧ keyOfAddress full roles x = some (rename (ofLeanName n)) ∧
      (∀ e ∈ bound, resolve full e.2 = some R → e.2 = x) ∧
      (inReach x = true ∨ resolve fb x = some R) := by
  unfold citedOk at h
  split at h
  · cases h
  · rename_i R hR
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at h
    obtain ⟨⟨hk, hb⟩, hr⟩ := h
    refine ⟨R, hR, hk, fun e he hre => ?_, hr⟩
    rcases hb e he with h | h
    · exact absurd hre h
    · exact h

theorem blobOk_sound {ixe : Ixon.Env} {fbBlobs : List (Address × ByteArray)} {x : Address} {bs : ByteArray}
    (h : blobOk ixe fbBlobs x bs = true) :
    (ixe.blobs.get? x = none ∨ ixe.blobs.get? x = some bs) ∧ firstBlob fbBlobs x = some bs := by
  unfold blobOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  have h1 := h.1
  split at h1
  · rename_i hn; exact .inl hn
  · rename_i bs' hs
    simp only [decide_eq_true_eq] at h1
    exact .inr (by rw [hs, h1])

theorem recordOk_sound {ixe : Ixon.Env} {b : Bundle} {full fb : Store} {roles : Bindings .anon}
    {bound : List (Role × Address)} {fbBlobs : List (Address × ByteArray)}
    {inReach : Address → Bool} {rename : Key .source → Key .anon} {a : Address}
    (h : recordOk ixe b full fb roles bound fbBlobs inReach rename a = true) :
    ∃ c d p T, bundleRecord b a = some c ∧ c.info = .defn d ∧ d.kind = .thm ∧ fb a = some c ∧
      (Ix.Cert.recordAt ixe a = none ∨ Ix.Cert.recordAt ixe a = some c) ∧
      b.proofOf c = .ok p ∧ typeOf b c = .ok T ∧
      (∀ s i, Ix.Kernel.Frontend.lamBody p ≠ .proj s i (.bvar 0)) ∧
      (∀ x ∈ c.refs, ∀ n, b.names[x]? = some n →
        ∃ R, resolve full x = some R ∧ keyOfAddress full roles x = some (rename (ofLeanName n)) ∧
          (∀ e ∈ bound, resolve full e.2 = some R → e.2 = x) ∧
          (inReach x = true ∨ resolve fb x = some R)) ∧
      (∀ x ∈ c.refs, ∀ bs, b.blobs[x]? = some bs →
        (ixe.blobs.get? x = none ∨ ixe.blobs.get? x = some bs) ∧ firstBlob fbBlobs x = some bs) := by
  unfold recordOk at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · rename_i d hd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hk, hfb⟩, hart⟩, hpt⟩, hrefs⟩ := h
      have hart' : Ix.Cert.recordAt ixe a = none ∨ Ix.Cert.recordAt ixe a = some c := by
        split at hart
        · rename_i hn; exact .inl hn
        · rename_i c' hs
          simp only [decide_eq_true_eq] at hart
          exact .inr (by rw [hs, hart])
      split at hpt
      · rename_i p T hp hT
        refine ⟨c, d, p, T, hc, hd, hk, hfb, hart', hp, hT, ?_, ?_, ?_⟩
        · intro s i he
          rw [he] at hpt
          cases hpt
        · intro x hx n hn
          have hx' := List.all_eq_true.mp hrefs x (by simpa using hx)
          simp only [Bool.and_eq_true, hn] at hx'
          exact citedOk_sound hx'.1
        · intro x hx bs hbs
          have hx' := List.all_eq_true.mp hrefs x (by simpa using hx)
          simp only [Bool.and_eq_true, hbs] at hx'
          exact blobOk_sound hx'.2
      · cases hpt
    · cases h

theorem recordMap_mem : ∀ (l : List (Address × Ixon.Constant)) (m : Std.HashMap Address Ixon.Constant)
    {a : Address} {c : Ixon.Constant},
    (l.foldl (fun m (p : Address × Ixon.Constant) => if m.contains p.1 then m else m.insert p.1 p.2) m)[a]? = some c →
      m[a]? = some c ∨ (a, c) ∈ l
  | [], m, _, _, h => .inl h
  | p :: l, m, a, c, h => by
    simp only [List.foldl_cons] at h
    rcases recordMap_mem l _ h with h | h
    · split at h
      · exact .inl h
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i he
          have he : p.1 = a := beq_iff_eq.mp he
          cases h
          exact .inr (by rw [← he]; exact List.mem_cons_self ..)
        · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem fallbackStore_mem {preA : Prelude .anon} {a : Address} {c : Ixon.Constant}
    (h : fallbackStore preA a = some c) : (a, c) ∈ (preA.records ++ preA.evidence).toList := by
  unfold fallbackStore recordMap at h
  rw [← Array.foldl_toList] at h
  rcases recordMap_mem _ {} h with h | h
  · simp at h
  · exact h

/-- A passing evidence check over given sources passes `check` on their objects. -/
theorem evidenceCheckOf_ok {bundle : Except String Bundle}
    {bindingE : Except String Ix.Kernel.Admission.Binding} {prelude : RoleTable → Except String (Prelude .anon)}
    {t : RoleTable} {ixe : Ixon.Env} (h : evidenceCheckOf bundle bindingE prelude t ixe = .ok ())
    {b : Bundle} {binding : Ix.Kernel.Admission.Binding} {tA : RoleTable} {preA : Prelude .anon}
    (hb : bundle = .ok b) (hbind : bindingE = .ok binding)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA)
    (hpre : prelude tA = .ok preA) : check ixe t b tA preA = true := by
  subst hb hbind
  unfold evidenceCheckOf at h
  simp only [hadm, hpre] at h
  cases hc : check ixe t b tA preA
  · simp [hc] at h
  · rfl

/-- A passing evidence check passes `check` on the committed objects. -/
theorem evidenceCheck_ok {t : RoleTable} {ixe : Ixon.Env} (h : evidenceCheck t ixe = .ok ())
    {b : Bundle} {binding : Ix.Kernel.Admission.Binding}
    {tA : RoleTable} {preA : Prelude .anon} (hb : quotientBundle () = .ok b)
    (hbind : Ix.Kernel.Admission.defaultBinding = .ok binding)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA)
    (hpre : preludeFor tA = .ok preA) : check ixe t b tA preA = true := by
  unfold evidenceCheck at h
  exact evidenceCheckOf_ok h hb hbind hadm hpre

/-- What a passing `check` gives. -/
theorem agree_of_check {t : RoleTable} {ixe : Ixon.Env}
    (htab : Ix.Kernel.Reader.defaultTable = .ok t) {b : Bundle}
    {tA : RoleTable} {preA : Prelude .anon} (hc : check ixe t b tA preA = true) : Agree ixe t b tA preA := by
  unfold check at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨haddrs, hops⟩, hfall⟩ := hc
  have addrs : ∀ r, t.addressOf? r = tA.addressOf? r := fun r => haddrs r (Role.mem_all r)
  refine ⟨addrs, fun r hr => (hops r hr).1, ?_, ?_, ?_⟩
  · intro r hr a ha
    have h2 := (hops r hr).2
    rw [ha] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.1
  · intro a c c' hfa hra
    have hm := fallbackStore_mem hfa
    have h3 := hfall (a, c) hm
    simp only [hra, hfa, decide_eq_true_eq] at h3
    exact h3
  · intro r hr A hra hsome a hp
    have h2 := (hops r hr).2
    rw [hra] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq, hsome, ↓reduceIte] at h2
    have hrec := recordOk_sound (List.all_eq_true.mp h2.2 a hp)
    obtain ⟨c, d, p, T, h1, h2', h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrec
    refine ⟨c, d, p, T, h1, h2', h3, h4, h5, h6, h7, h8, fun x hx n hn => ?_, h10⟩
    obtain ⟨R, hR, hk, hu, hreach⟩ := h9 x hx n hn
    refine ⟨R, hR, hk, hu, ?_⟩
    rcases hreach with hin | hfb
    · refine .inl fun a' ha' => ?_
      rw [hra] at ha'
      cases ha'
      simp only [Bool.and_eq_true] at hin
      have hcont : ixe.consts.contains A = true := by
        obtain ⟨cA, hcA⟩ := Option.isSome_iff_exists.mp hsome
        unfold Ix.Cert.recordAt at hcA
        cases hg : ixe.consts.get? A with
        | none => rw [hg] at hcA; cases hcA
        | some lc =>
          rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hg]; rfl
      exact ⟨reach_sound htab ((addrs r).trans hra) hcont hin.1, hin.2⟩
    · exact .inr hfb

/-- **The evidence check is sound**: where it passes on an artifact compiled under the
default table `t`, the quotient bundle, the admitted default table and its prelude agree
with the artifact as `Agree` states. -/
theorem evidenceCheck_sound {t : RoleTable} {ixe : Ixon.Env} (h : evidenceCheck t ixe = .ok ())
    (htab : Ix.Kernel.Reader.defaultTable = .ok t) {b : Bundle} {binding : Ix.Kernel.Admission.Binding}
    {tA : RoleTable} {preA : Prelude .anon} (hb : quotientBundle () = .ok b)
    (hbind : Ix.Kernel.Admission.defaultBinding = .ok binding)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA)
    (hpre : preludeFor tA = .ok preA) : Agree ixe t b tA preA :=
  agree_of_check htab (evidenceCheck_ok h hb hbind hadm hpre)

/-- **The evidence premise**: on the artifact `ixe` compiled under the default table `t`,
the committed quotient bundle, the admitted default table and its prelude agree with the
artifact as `Agree` states. Given by the passing evidence check (`evidenceAgrees_of_check`). -/
def EvidenceAgrees (t : RoleTable) (ixe : Ixon.Env) : Prop :=
  Ix.Kernel.Reader.defaultTable = .ok t →
    ∀ (b : Bundle) (binding : Ix.Kernel.Admission.Binding) (tA : RoleTable) (preA : Prelude .anon),
      quotientBundle () = .ok b → Ix.Kernel.Admission.defaultBinding = .ok binding →
      Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok tA →
      preludeFor tA = .ok preA → Agree ixe t b tA preA

/-- A passing evidence check gives the evidence premise. -/
theorem evidenceAgrees_of_check {t : RoleTable} {ixe : Ixon.Env} (h : evidenceCheck t ixe = .ok ()) :
    EvidenceAgrees t ixe :=
  fun htab _ _ _ _ hb hbind hadm hpre => evidenceCheck_sound h htab hb hbind hadm hpre

end Ix.Cert.EvidenceCheck

/-- info: 'Ix.Cert.EvidenceCheck.evidenceAgrees_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.EvidenceCheck.evidenceAgrees_of_check
