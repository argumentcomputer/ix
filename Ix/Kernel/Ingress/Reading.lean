/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Types
import Ix.Kernel.Const
import Std.Data.TreeMap.Lemmas

/-! # Exact readings of anonymous Ixon input

These relations describe the supplied tables and expression constructors,
independently of the bounded reader. Addresses are opaque keys; byte/hash
authentication is a separate contract. Only the ordinary Lean binder modes
have a reading at K3. Sharing is read against a strictly earlier prefix.
-/

namespace Ix.Kernel.Ingress

abbrev Constants := List (Address × Ixon.Constant)
abbrev Blobs := List (Address × ByteArray)

def isProjection : Ixon.ConstantInfo → Bool
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => true
  | _ => false

/-- First lookup in the supplied finite store. The environment driver checks
key uniqueness before reading declarations. -/
def lookup (store : List (Address × α)) (address : Address) : Option α :=
  match store with
  | [] => none
  | (key, value) :: rest => if key = address then some value else lookup rest address

/-! ## Indexed stores

`lookup` is the specification: the first entry with the key. A `StoreIndex`
answers the same question from hash buckets (`find_build`), so a reader can
resolve every reference without scanning the store. -/

/-- A store's entries by the hash of their key (`Hashable Address`, the
address's leading bytes), in store order within a bucket. -/
structure StoreIndex (α : Type) where
  buckets : Std.TreeMap UInt64 (List (Address × α)) compare

namespace StoreIndex

variable {α : Type}

def cons (idx : StoreIndex α) (entry : Address × α) : StoreIndex α :=
  let h := hash entry.1
  ⟨idx.buckets.insert h (entry :: idx.buckets.getD h [])⟩

def build (store : List (Address × α)) : StoreIndex α :=
  store.foldr (fun entry idx => idx.cons entry) ⟨∅⟩

def find (idx : StoreIndex α) (address : Address) : Option α :=
  lookup (idx.buckets.getD (hash address) []) address

theorem getD_cons (idx : StoreIndex α) (entry : Address × α) (h : UInt64) :
    (idx.cons entry).buckets.getD h [] =
      if hash entry.1 = h then entry :: idx.buckets.getD h [] else idx.buckets.getD h [] := by
  simp only [cons, Std.TreeMap.getD_insert]
  by_cases he : hash entry.1 = h
  · rw [ite_eq_left (Std.LawfulEqCmp.compare_eq_iff_eq.2 he), ite_eq_left he, he]
  · rw [ite_eq_right (fun hc => he (Std.LawfulEqCmp.eq_of_compare hc)), ite_eq_right he]

theorem getD_build (store : List (Address × α)) (h : UInt64) :
    (build store).buckets.getD h [] = store.filter (fun entry => hash entry.1 == h) := by
  induction store with
  | nil => simp [build, Std.TreeMap.getD_emptyc]
  | cons entry store ih =>
    rw [show build (entry :: store) = (build store).cons entry from rfl, getD_cons, ih,
      List.filter_cons]
    by_cases he : hash entry.1 = h <;> simp [he]

theorem lookup_filter_hash (store : List (Address × α)) (address : Address) :
    lookup (store.filter (fun entry => hash entry.1 == hash address)) address =
      lookup store address := by
  induction store with
  | nil => rfl
  | cons entry store ih =>
    obtain ⟨key, value⟩ := entry
    by_cases hk : key = address
    · subst hk; simp [lookup]
    · by_cases hh : hash key = hash address
      · simp [hh, lookup, hk, ih]
      · simp [hh, lookup, hk, ih]

theorem find_build (store : List (Address × α)) (address : Address) :
    (build store).find address = lookup store address := by
  rw [find, getD_build, lookup_filter_hash]

end StoreIndex

/-- Membership of an address in a list, by `DecidableEq`. -/
def memAddress (key : Address) (keys : List Address) : Bool := keys.any fun k => decide (k = key)

theorem memAddress_iff {key : Address} {keys : List Address} : memAddress key keys = true ↔ key ∈ keys := by
  simp [memAddress]

/-- Key uniqueness by hash buckets of the keys seen so far. -/
def nodupKeys {α : Type} (store : List (Address × α)) : Bool :=
  go store ∅
where
  go : List (Address × α) → Std.TreeMap UInt64 (List Address) compare → Bool
    | [], _ => true
    | (key, _) :: rest, seen =>
      let bucket := seen.getD (hash key) []
      if memAddress key bucket then false else go rest (seen.insert (hash key) (key :: bucket))

theorem nodupKeys_go_iff {α : Type} (store : List (Address × α))
    (seen : Std.TreeMap UInt64 (List Address) compare) :
    nodupKeys.go store seen = true ↔
      (store.map Prod.fst).Nodup ∧ ∀ entry ∈ store, entry.1 ∉ seen.getD (hash entry.1) [] := by
  induction store generalizing seen with
  | nil => simp [nodupKeys.go]
  | cons entry store ih =>
    obtain ⟨key, value⟩ := entry
    simp only [nodupKeys.go]
    by_cases hin : key ∈ seen.getD (hash key) []
    · rw [ite_eq_left (memAddress_iff.2 hin)]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hall
      exact hall (key, value) List.mem_cons_self hin
    · rw [ite_eq_right (fun h => hin (memAddress_iff.1 h)), ih]
      have hget : ∀ e : Address × α,
          (seen.insert (hash key) (key :: seen.getD (hash key) [])).getD (hash e.1) [] =
            if hash key = hash e.1 then key :: seen.getD (hash e.1) [] else
              seen.getD (hash e.1) [] := by
        intro e
        rw [Std.TreeMap.getD_insert]
        by_cases h : hash key = hash e.1
        · rw [ite_eq_left (Std.LawfulEqCmp.compare_eq_iff_eq.2 h), ite_eq_left h, h]
        · rw [ite_eq_right (fun hc => h (Std.LawfulEqCmp.eq_of_compare hc)), ite_eq_right h]
      simp only [hget, List.map_cons]
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩, fun e he => ?_⟩
        · obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
          have := hall e he
          rw [hek, ite_eq_left rfl] at this
          exact this List.mem_cons_self
        · rcases List.mem_cons.1 he with rfl | he
          · exact hin
          · have := hall e he
            by_cases h : hash key = hash e.1
            · rw [ite_eq_left h] at this
              simp only [List.mem_cons, not_or] at this
              exact this.2
            · rwa [ite_eq_right h] at this
      · rintro ⟨hnd, hall⟩
        refine ⟨(List.nodup_cons.1 hnd).2, fun e he => ?_⟩
        have hk : e.1 ≠ key := fun h => (List.nodup_cons.1 hnd).1 (List.mem_map.2 ⟨e, he, h⟩)
        have := hall e (List.mem_cons_of_mem _ he)
        by_cases h : hash key = hash e.1
        · rw [ite_eq_left h]
          simp only [List.mem_cons, not_or]
          exact ⟨hk, this⟩
        · rwa [ite_eq_right h]

theorem nodupKeys_iff {α : Type} (store : List (Address × α)) :
    nodupKeys store = true ↔ (store.map Prod.fst).Nodup := by
  rw [nodupKeys, nodupKeys_go_iff]; simp [Std.TreeMap.getD_emptyc]

/-- Exact structural universe reading; no normalization changes its spelling. -/
def levelTree : Ixon.Univ → VLevel
  | .zero => .zero
  | .succ u => .succ (levelTree u)
  | .max u v => .max (levelTree u) (levelTree v)
  | .imax u v => .imax (levelTree u) (levelTree v)
  | .var i => .param i.toNat

/-- Little-endian natural-number payload, including the empty encoding of zero.
Canonical byte spelling is a separate K4 condition. -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- A projection constant carries no expression tables. -/
def emptyTables (source : Ixon.Constant) : Bool :=
  source.sharing.isEmpty && source.refs.isEmpty && source.univs.isEmpty

/-- Resolve a supplied record, checking its projection owner, variant, member
position, and constructor position. The source need not already be in the
store; the writer uses this to validate newly reconstructed projections. -/
def referenceSourceBy (find : Address → Option Ixon.Constant) (address : Address)
    (source : Ixon.Constant) : Option (ConstRef Address) :=
  match source.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member address 0)
  | .muts _ => none
  | .dPrj p => do
    if !emptyTables source then none else do
    let owner ← find p.block
    let .muts members := owner.info | none
    let .defn _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .iPrj p => do
    if !emptyTables source then none else do
    let owner ← find p.block
    let .muts members := owner.info | none
    let .indc _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .rPrj p => do
    if !emptyTables source then none else do
    let owner ← find p.block
    let .muts members := owner.info | none
    let .recr _ ← members[p.idx.toNat]? | none
    return .member p.block p.idx.toNat
  | .cPrj p => do
    if !emptyTables source then none else do
    let owner ← find p.block
    let .muts members := owner.info | none
    let .indc ind ← members[p.idx.toNat]? | none
    let ctor ← ind.ctors[p.cidx.toNat]?
    if ctor.cidx = p.cidx then return .ctor p.block p.idx.toNat p.cidx.toNat
    else none

/-- `referenceSourceBy` against the first-match lookup in a store. -/
def referenceSource (store : Constants) (address : Address) (source : Ixon.Constant) :
    Option (ConstRef Address) :=
  referenceSourceBy (lookup store) address source

/-- Resolve one stored address through a lookup function. -/
def referenceBy (find : Address → Option Ixon.Constant) (address : Address) :
    Option (ConstRef Address) := do
  let source ← find address
  referenceSourceBy find address source

/-- Resolve one stored address. A mutual block itself is not a constant
reference. No projection address is reconstructed by hashing. -/
def reference (store : Constants) (address : Address) : Option (ConstRef Address) :=
  referenceBy (lookup store) address

/-- Tables and finite input stores for one declaration. The literal family is
an explicit choice; the kernel subsequently checks its natural-number fact. -/
structure Context where
  constants : Constants
  blobs : Blobs
  owner : Address
  source : Ixon.Constant
  natFamily : Option (ConstRef Address) := none
  /-- Lookup in `constants`, possibly through an index. -/
  findConstant : Address → Option Ixon.Constant := lookup constants
  findConstant_eq : ∀ address, findConstant address = lookup constants address := by
    intro; rfl
  /-- Lookup in `blobs`, possibly through an index. -/
  findBlob : Address → Option ByteArray := lookup blobs
  findBlob_eq : ∀ address, findBlob address = lookup blobs address := by intro; rfl

namespace Context

/-- A context over the given stores, looked up directly. -/
def ofStores (constants : Constants) (blobs : Blobs) (owner : Address) (source : Ixon.Constant)
    (natFamily : Option (ConstRef Address) := none) : Context :=
  { constants, blobs, owner, source, natFamily }

/-- Replace a context's blob store. -/
def withBlobs (ctx : Context) (blobs : Blobs) : Context :=
  ofStores ctx.constants blobs ctx.owner ctx.source ctx.natFamily

def level (ctx : Context) (index : UInt64) : Option VLevel :=
  (ctx.source.univs[index.toNat]?).map levelTree

def levels (ctx : Context) (indices : List UInt64) : Option (List VLevel) :=
  indices.mapM ctx.level

/-- The lookups are the store lookups, whatever index answers them. -/
theorem findConstant_funext (ctx : Context) : ctx.findConstant = lookup ctx.constants :=
  funext ctx.findConstant_eq

theorem findBlob_funext (ctx : Context) : ctx.findBlob = lookup ctx.blobs :=
  funext ctx.findBlob_eq

def external (ctx : Context) (index : UInt64) : Option (ConstRef Address) := do
  let address ← ctx.source.refs[index.toNat]?
  referenceBy ctx.findConstant address

theorem external_eq (ctx : Context) (index : UInt64) :
    ctx.external index = (do
      let address ← ctx.source.refs[index.toNat]?
      reference ctx.constants address) := by
  simp only [external, reference, findConstant_funext]

/-- Recursive references name positions of this block, never positions of a
different owner. Only definition and recursor singletons may refer to self. -/
def recursive (ctx : Context) (index : UInt64) : Option (ConstRef Address) :=
  match ctx.source.info with
  | .muts members =>
    if index.toNat < members.size then some (.member ctx.owner index.toNat) else none
  | .defn _ | .recr _ =>
    if index = 0 then some (.member ctx.owner 0) else none
  | _ => none

def blob (ctx : Context) (index : UInt64) : Option ByteArray := do
  let address ← ctx.source.refs[index.toNat]?
  ctx.findBlob address

theorem blob_eq (ctx : Context) (index : UInt64) :
    ctx.blob index = (do
      let address ← ctx.source.refs[index.toNat]?
      lookup ctx.blobs address) := by
  simp only [blob, findBlob_funext]

/-- Contexts agreeing on their stores and record agree; the lookup functions
are determined by the stores. -/
theorem ext_stores {a b : Context} (hc : a.constants = b.constants) (hb : a.blobs = b.blobs)
    (ho : a.owner = b.owner) (hs : a.source = b.source) (hf : a.natFamily = b.natFamily) :
    a = b := by
  have hfa := a.findConstant_funext
  have hfb := b.findConstant_funext
  have hba := a.findBlob_funext
  have hbb := b.findBlob_funext
  cases a; cases b
  simp only at hc hb ho hs hf hfa hfb hba hbb
  subst hc hb ho hs hf hfa hfb hba hbb
  rfl

end Context

/-- A constructor-by-constructor reading, including all table resolutions.
Ixon v3 contracts are erased, as at upstream `Ix.Tc`'s erased typing
boundary: a lambda's binder contract, a forall's binder and result contracts,
and a let's dependency bit, value or shared-borrow kind, and binder contract.
Typing, conversion, and the set model do not observe them; the egress layout
retains them, so records reproduce exactly. -/
inductive ExprReads (ctx : Context) : Nat → Ixon.Expr → VExpr Address → Prop where
  | var : ExprReads ctx limit (.var i) (.bvar i.toNat)
  | sort : ctx.level i = some level → ExprReads ctx limit (.sort i) (.sort level)
  | ref : ctx.external i = some ref → ctx.levels us.toList = some levels →
      ExprReads ctx limit (.ref i us) (.const ref levels)
  | recur : ctx.recursive i = some ref → ctx.levels us.toList = some levels →
      ExprReads ctx limit (.recur i us) (.const ref levels)
  | nat : ctx.blob i = some bytes → ctx.natFamily = some family →
      ExprReads ctx limit (.nat i) (.natLit family (natural bytes))
  | app : ExprReads ctx limit f f' → ExprReads ctx limit a a' →
      ExprReads ctx limit (.app f a) (.app f' a')
  | lam : ExprReads ctx limit type type' → ExprReads ctx limit body body' →
      ExprReads ctx limit (.lam contract type body) (.lam type' body')
  | all : ExprReads ctx limit type type' → ExprReads ctx limit body body' →
      ExprReads ctx limit (.all contract result type body) (.forallE type' body')
  | letE : ExprReads ctx limit type type' → ExprReads ctx limit value value' →
      ExprReads ctx limit body body' →
      ExprReads ctx limit (.letE contract type value body) (.letE type' value' body')
  | prj : ctx.external i = some ref → ExprReads ctx limit value value' →
      ExprReads ctx limit (.prj i field value) (.proj ref field.toNat value')
  | share : i.toNat < limit → ctx.source.sharing[i.toNat]? = some value →
      ExprReads ctx i.toNat value value' → ExprReads ctx limit (.share i) value'

/-- The table reading is independent of reader fuel or search strategy. -/
theorem ExprReads.deterministic {ctx : Context} {limit : Nat} {input : Ixon.Expr}
    {left right : VExpr Address} (h : ExprReads ctx limit input left)
    (other : ExprReads ctx limit input right) : left = right := by
  induction h generalizing right <;> cases other <;> simp_all
  all_goals repeat first | apply And.intro | apply_assumption

def safety : Ix.DefinitionSafety → Safety
  | .safe => .safe
  | .unsaf => .unsafe
  | .part => .partial

def unsafeFlag (flag : Bool) : Safety := if flag then .unsafe else .safe

def kind : Ix.DefKind → DefKind
  | .defn => .definition
  | .opaq => .opaque
  | .thm => .theorem

def quotientKind : Ix.QuotKind → QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

abbrev ExpressionReads (ctx : Context) := ExprReads ctx ctx.source.sharing.size

inductive DefinitionReads (ctx : Context) (source : Ixon.Definition) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type → ExpressionReads ctx source.value value →
      DefinitionReads ctx source
        (.defn source.lvls.toNat (kind source.kind) type value (safety source.safety))

/-- The stored constructor index must equal its position in the owner's
constructor array. All remaining fields have an exact structural reading. -/
def ConstructorReads (ctx : Context) (source : Ixon.Constructor × Nat)
    (target : Ctor Address) : Prop :=
  source.1.cidx.toNat = source.2 ∧
  target.uvars = source.1.lvls.toNat ∧ target.nparams = source.1.params.toNat ∧
  target.nfields = source.1.fields.toNat ∧ target.safety = unsafeFlag source.1.isUnsafe ∧
  ExpressionReads ctx source.1.typ target.type

def RuleReads (ctx : Context) (source : Ixon.RecursorRule) (target : RecRule Address) : Prop :=
  target.nfields = source.fields.toNat ∧ ExpressionReads ctx source.rhs target.rhs

inductive RecursorReads (ctx : Context) (source : Ixon.Recursor) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type →
      Forall₂ (RuleReads ctx) source.rules.toList rules →
      RecursorReads ctx source (.recursor source.lvls.toNat source.params.toNat
        source.indices.toNat source.motives.toNat source.minors.toNat type rules
        source.k (unsafeFlag source.isUnsafe))

inductive InductiveReads (ctx : Context) (source : Ixon.Inductive) : Const Address → Prop where
  | mk : ExpressionReads ctx source.typ type →
      Forall₂ (ConstructorReads ctx) source.ctors.toList.zipIdx ctors →
      InductiveReads ctx source (.induct source.lvls.toNat source.params.toNat
        source.indices.toNat type ctors (unsafeFlag source.isUnsafe))

inductive MemberReads (ctx : Context) : Ixon.MutConst → Const Address → Prop where
  | defn : DefinitionReads ctx d c → MemberReads ctx (.defn d) c
  | indc : InductiveReads ctx d c → MemberReads ctx (.indc d) c
  | recr : RecursorReads ctx d c → MemberReads ctx (.recr d) c

/-- Exact declaration fields and ordered member identities. Projection records
name declarations in their owning block and are validated separately. -/
inductive InfoReads (ctx : Context) : Ixon.ConstantInfo → Block Address → Prop where
  | defn : DefinitionReads ctx d c → InfoReads ctx (.defn d) ⟨[c]⟩
  | recr : RecursorReads ctx d c → InfoReads ctx (.recr d) ⟨[c]⟩
  | axio : ExpressionReads ctx d.typ type →
      InfoReads ctx (.axio d) ⟨[.axiom d.lvls.toNat type (unsafeFlag d.isUnsafe)]⟩
  | quot : ExpressionReads ctx d.typ type →
      InfoReads ctx (.quot d) ⟨[.quot (quotientKind d.kind) d.lvls.toNat type]⟩
  | muts : Forall₂ (MemberReads ctx) members.toList constants →
      InfoReads ctx (.muts members) ⟨constants⟩

abbrev BlockReads (ctx : Context) := InfoReads ctx ctx.source.info

/-! ## Determinism

Each reading relation relates a record to at most one kernel declaration. -/

theorem forall₂_deterministic {α γ : Type} {R : α → γ → Prop}
    (unique : ∀ x y z, R x y → R x z → y = z) :
    ∀ {xs : List α} {ys zs : List γ}, Forall₂ R xs ys → Forall₂ R xs zs → ys = zs
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons hx hxs, .cons hy hys => by
    rw [unique _ _ _ hx hy, forall₂_deterministic unique hxs hys]

theorem DefinitionReads.deterministic {ctx : Context} {source : Ixon.Definition}
    {left right : Const Address} (h : DefinitionReads ctx source left)
    (other : DefinitionReads ctx source right) : left = right := by
  cases h with
  | mk ht hv => cases other with
    | mk ht' hv' =>
      obtain rfl := ExprReads.deterministic ht ht'
      obtain rfl := ExprReads.deterministic hv hv'
      rfl

theorem ConstructorReads.deterministic {ctx : Context} {source : Ixon.Constructor × Nat}
    {left right : Ctor Address} (h : ConstructorReads ctx source left)
    (other : ConstructorReads ctx source right) : left = right := by
  obtain ⟨-, hu, hp, hf, hs, ht⟩ := h
  obtain ⟨-, hu', hp', hf', hs', ht'⟩ := other
  have same := ExprReads.deterministic ht ht'
  cases left; cases right
  simp_all

theorem RuleReads.deterministic {ctx : Context} {source : Ixon.RecursorRule}
    {left right : RecRule Address} (h : RuleReads ctx source left)
    (other : RuleReads ctx source right) : left = right := by
  obtain ⟨hn, hr⟩ := h
  obtain ⟨hn', hr'⟩ := other
  have same := ExprReads.deterministic hr hr'
  cases left; cases right
  simp_all

theorem RecursorReads.deterministic {ctx : Context} {source : Ixon.Recursor}
    {left right : Const Address} (h : RecursorReads ctx source left)
    (other : RecursorReads ctx source right) : left = right := by
  cases h with
  | mk ht hr => cases other with
    | mk ht' hr' =>
      obtain rfl := ExprReads.deterministic ht ht'
      obtain rfl := forall₂_deterministic (R := RuleReads ctx) (fun _ _ _ h h' => RuleReads.deterministic h h') hr hr'
      rfl

theorem InductiveReads.deterministic {ctx : Context} {source : Ixon.Inductive}
    {left right : Const Address} (h : InductiveReads ctx source left)
    (other : InductiveReads ctx source right) : left = right := by
  cases h with
  | mk ht hc => cases other with
    | mk ht' hc' =>
      obtain rfl := ExprReads.deterministic ht ht'
      obtain rfl := forall₂_deterministic (R := ConstructorReads ctx) (fun _ _ _ h h' => ConstructorReads.deterministic h h') hc hc'
      rfl

theorem MemberReads.deterministic {ctx : Context} {source : Ixon.MutConst}
    {left right : Const Address} (h : MemberReads ctx source left)
    (other : MemberReads ctx source right) : left = right := by
  cases h with
  | defn h => cases other with | defn h' => exact h.deterministic h'
  | indc h => cases other with | indc h' => exact h.deterministic h'
  | recr h => cases other with | recr h' => exact h.deterministic h'

theorem InfoReads.deterministic {ctx : Context} {source : Ixon.ConstantInfo}
    {left right : Block Address} (h : InfoReads ctx source left)
    (other : InfoReads ctx source right) : left = right := by
  cases h with
  | defn h => cases other with | defn h' => rw [h.deterministic h']
  | recr h => cases other with | recr h' => rw [h.deterministic h']
  | axio h => cases other with
    | axio h' => obtain rfl := ExprReads.deterministic h h'; rfl
  | quot h => cases other with
    | quot h' => obtain rfl := ExprReads.deterministic h h'; rfl
  | muts h => cases other with
    | muts h' => rw [forall₂_deterministic (R := MemberReads ctx) (fun _ _ _ h h' => MemberReads.deterministic h h') h h']

theorem BlockReads.deterministic {ctx : Context} {left right : Block Address}
    (h : BlockReads ctx left) (other : BlockReads ctx right) : left = right :=
  InfoReads.deterministic h other

/-- A projection record has no declaration reading. -/
theorem InfoReads.not_projection {ctx : Context} {source : Ixon.ConstantInfo}
    {block : Block Address} (h : InfoReads ctx source block) : isProjection source = false := by
  cases h <;> rfl

end Ix.Kernel.Ingress
