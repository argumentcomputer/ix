import IxC.Kernel.Model.GuardClassifier
import IxC.Kernel.Model.GuardClassifierErase
import IxC.Kernel.Verify.Cached.NormalizeRef
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.Assembly.TypingStore
import IxVMRefinement.Assembly.BareState

/-! # The guard classifier's address-keyed raw-record dictionary

This dictionary reads types and definition values directly from decoded records and literal
blobs. It does not consult a typed environment, role binding, recursor model or validation limit.
Member projections select their containing block and canonical binder-root offset. Recursors
are read at positional universes, as the runtime payload presents them to the classifier.

Positive record/blob extension preserves every successful lookup. The two sides can therefore
be embedded in their common collision-free raw store before comparing classifier results.
-/

namespace IxVM.Refinement.GuardRaw

open IxVM.Consistency
open Ix.Kernel (Expr Key Level)
open Ix.Kernel.GuardClassifier (Lookup)

/-- This is only an address-naming device for the expression reader, not an admitted table. -/
def addressTable : Ix.Kernel.RoleTable := ⟨Ix.Kernel.specVersion, #[], #[]⟩

theorem addressTable_key (a : _root_.Address) : keyOf addressTable a = .id a := rfl

/-- The naming table is well formed, though deliberately not a full admitted table. -/
theorem addressTable_check : addressTable.check = .ok () := by decide +kernel

/-- One raw expression root, including the record-local data needed by its canonical reader. -/
structure Root where
  source : Ixon.Constant
  self : Nat → Option (Ix.Kernel.Reader.ReadM (Key .anon))
  offset : Nat
  levels : Nat
  expression : Ixon.Expr

abbrev Records := _root_.Address → Option Ixon.Constant
abbrev Blobs := _root_.Address → Option ByteArray

private theorem bind_preserved {α β : Type} {a b : Option α} {f g : α → Option β}
    (ha : ∀ x, a = some x → b = some x)
    (hf : ∀ x y, f x = some y → g x = some y)
    {r : β} (h : a.bind f = some r) : b.bind g = some r := by
  obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨x, ha x hx, hf x r hr⟩

/-- Select a root from one member, using its offset in the whole block's binder table. -/
def memberRoot (store : Records) (B : _root_.Address) (i : Nat)
    (select : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)) : Option Root := do
  let cb ← store B
  let .muts ms := cb.info | none
  let m ← ms[i]?
  let (off, nl, e) ← select m
  pure ⟨cb, blockSelf addressTable B ms, Ingress.mutsRootOffset ms.toList i + off, nl, e⟩

def definitionType : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)
  | .defn d => some (0, d.lvls.toNat, d.typ)
  | _ => none

def inductiveType : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)
  | .indc ind => some (0, ind.lvls.toNat, ind.typ)
  | _ => none

def recursorType : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)
  | .recr rc => some (0, rc.lvls.toNat, rc.typ)
  | _ => none

def constructorType (j : Nat) : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)
  | .indc ind => (ind.ctors[j]?).map fun ct => (1 + j, ct.lvls.toNat, ct.typ)
  | _ => none

def definitionValue : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)
  | .defn d => match d.kind with
      | .defn => some (1, d.lvls.toNat, d.value)
      | _ => none
  | _ => none

/-- The declared type at an address. A projection is resolved by its own kind, never guessed. -/
def typeRoot (store : Records) (a : _root_.Address) : Option Root := do
  let c ← store a
  match c.info with
  | .defn d => pure ⟨c, soloSelf addressTable a, 0, d.lvls.toNat, d.typ⟩
  | .recr r => pure ⟨c, soloSelf addressTable a, 0, r.lvls.toNat, r.typ⟩
  | .axio x => pure ⟨c, fun _ => none, 0, x.lvls.toNat, x.typ⟩
  | .quot q => pure ⟨c, fun _ => none, 0, q.lvls.toNat, q.typ⟩
  | .dPrj p => memberRoot store p.block p.idx.toNat definitionType
  | .iPrj p => memberRoot store p.block p.idx.toNat inductiveType
  | .rPrj p => memberRoot store p.block p.idx.toNat recursorType
  | .cPrj p => memberRoot store p.block p.idx.toNat (constructorType p.cidx.toNat)
  | .muts _ => none

/-- Only a definition value is unfoldable. Theorem/opaque bodies are not classifier inputs. -/
def valueRoot (store : Records) (a : _root_.Address) : Option Root := do
  let c ← store a
  match c.info with
  | .defn d => match d.kind with
      | .defn => pure ⟨c, soloSelf addressTable a, 1, d.lvls.toNat, d.value⟩
      | _ => none
  | .dPrj p => memberRoot store p.block p.idx.toNat definitionValue
  | _ => none

/-- Canonical unannotated address-keyed syntax. The classifier never reads binder/let metadata;
lets remain explicit, so this data reader requires no typing or closedness hypothesis. -/
def readRoot (blob : Blobs) (root : Root) : Option (Expr .anon) :=
  ((exprReader addressTable blob root.source id root.self).read root.expression).toOption.map
    Expr.eraseMeta

/-- A literal sort root reads directly, without a binder plan or a typing hypothesis. -/
theorem readRoot_sort {blob : Blobs} {root : Root} {i : UInt64} {u : Ixon.Univ}
    (he : root.expression = .sort i) (hu : root.source.univs[i.toNat]? = some u) :
    readRoot blob root = some (.sort (Ix.Kernel.Reader.convUniv id u)) := by
  have hecx := (Ingress.memberReader_mk'_eq (readCtx addressTable blob) root.source id root.self).1
  unfold readRoot exprReader Ix.Kernel.Reader.MemberReader.read
  rw [hecx, he]
  simp [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.level, hu]
  exact ⟨.sort (Ix.Kernel.Reader.convUniv id u), rfl, rfl⟩

/-- A successful dictionary answer checks universe arity and instantiates that raw reading. -/
noncomputable def answer (blob : Blobs) (root : Option Root) (us : List Level) :
    Option (Expr .anon) := do
  let root ← root
  if us.length = root.levels then
    (readRoot blob root).map (fun e => e.instantiateLevelParams (List.range root.levels) us)
  else none

/-- The classifier's concrete raw dictionary. Only address keys are accepted. -/
noncomputable def lookup (store : Records) (blob : Blobs) : Lookup .anon where
  typeOf k us := match k with
    | .id a => answer blob (typeRoot store a) us
    | _ => none
  valueOf k us := match k with
    | .id a => answer blob (valueRoot store a) us
    | _ => none

noncomputable def ofStore (E : Ixon.Env) : Lookup .anon :=
  lookup (recordOf E) (fun x => E.blobs.get? x)

/-- Selecting a member uses only the positive answer at the containing block. -/
theorem memberRoot_mono {store store' : Records}
    (hs : ∀ a c, store a = some c → store' a = some c)
    {B : _root_.Address} {i : Nat} {select : Ixon.MutConst → Option (Nat × Nat × Ixon.Expr)}
    {r : Root} (h : memberRoot store B i select = some r) : memberRoot store' B i select = some r :=
  bind_preserved (hs B) (fun _ _ h => h) h

theorem typeRoot_mono {store store' : Records}
    (hs : ∀ a c, store a = some c → store' a = some c)
    {a : _root_.Address} {r : Root} (h : typeRoot store a = some r) : typeRoot store' a = some r := by
  refine bind_preserved (hs a) ?_ h
  intro c r hr
  cases hc : c.info <;> simp only [hc] at hr ⊢
  case dPrj p => exact memberRoot_mono hs hr
  case iPrj p => exact memberRoot_mono hs hr
  case rPrj p => exact memberRoot_mono hs hr
  case cPrj p => exact memberRoot_mono hs hr
  all_goals exact hr

theorem valueRoot_mono {store store' : Records}
    (hs : ∀ a c, store a = some c → store' a = some c)
    {a : _root_.Address} {r : Root} (h : valueRoot store a = some r) : valueRoot store' a = some r := by
  refine bind_preserved (hs a) ?_ h
  intro c r hr
  cases hc : c.info <;> simp only [hc] at hr ⊢
  case dPrj p => exact memberRoot_mono hs hr
  all_goals exact hr

/-- Only successful literal blob reads require transport; metadata erasure is store independent. -/
theorem readRoot_mono {blob blob' : Blobs}
    (hb : ∀ a bytes, blob a = some bytes → blob' a = some bytes)
    {r : Root} {e : Expr .anon} (h : readRoot blob r = some e) : readRoot blob' r = some e := by
  obtain ⟨v, hv, heq⟩ := Option.map_eq_some_iff.mp h
  have hr := Typing.toOption_eq_some hv
  have hr' := ReaderReads.exprReader_mono hb hr
  apply Option.map_eq_some_iff.mpr
  exact ⟨v, by rw [hr']; rfl, heq⟩

/-- An actual raw conversion produces a dictionary reading without an InLogic, typed-environment
or closed-term premise. This is the data producer needed for arbitrary classifier loads. -/
theorem readRoot_of_rawConv {blob : Blobs} {root : Root}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Aiur.Heap IxVM.F} {kp : Aiur.SourceValue IxVM.F}
    (raw : Ingress.RawConvExpr root.source.refs.toList recurAddrs root.source.univs.toList
      root.source.sharing.toList blobs h 4294967295 root.expression kp)
    (hself : ∀ i x, recurAddrs[i]? = some x → ∃ m k, root.self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs) :
    ∃ e, readRoot blob root = some e := by
  obtain ⟨v, hv⟩ := LoadedReads.exprReader_read_ok addressTable_check raw hself hblob
  refine ⟨v.eraseMeta, ?_⟩
  unfold readRoot
  rw [hv]
  rfl

theorem answer_mono {blob blob' : Blobs} {r r' : Option Root}
    (hb : ∀ a bytes, blob a = some bytes → blob' a = some bytes)
    (hr : ∀ root, r = some root → r' = some root)
    {us : List Level} {e : Expr .anon} (h : answer blob r us = some e) :
    answer blob' r' us = some e := by
  refine bind_preserved hr ?_ h
  intro root e he
  by_cases hn : us.length = root.levels
  · rw [ite_eq_left hn] at he ⊢
    obtain ⟨v, hv, heq⟩ := Option.map_eq_some_iff.mp he
    exact Option.map_eq_some_iff.mpr ⟨v, readRoot_mono hb hv, heq⟩
  · rw [ite_eq_right hn] at he ⊢
    exact he

/-- Positive agreement of actual records and blobs supplies the classifier lookup extension. -/
theorem lookup_extends {store store' : Records} {blob blob' : Blobs}
    (hs : ∀ a c, store a = some c → store' a = some c)
    (hb : ∀ a bytes, blob a = some bytes → blob' a = some bytes) :
    (lookup store blob).Extends (lookup store' blob') := by
  constructor
  · intro k us e h
    cases k with
    | id a => exact answer_mono hb (fun _ h => typeRoot_mono hs h) h
    | role _ => exact h
    | aux _ _ => exact h
  · intro k us e h
    cases k with
    | id a => exact answer_mono hb (fun _ h => valueRoot_mono hs h) h
    | role _ => exact h
    | aux _ _ => exact h

/-- Both raw stores map into their left-biased union when overlapping records and blobs agree. -/
theorem common_lookup {E R : Ixon.Env}
    (hr : ∀ a c c', recordOf E a = some c → recordOf R a = some c' → c = c')
    (hb : ∀ a b b', E.blobs.get? a = some b → R.blobs.get? a = some b' → b = b') :
    (ofStore E).Extends (lookup (storeOver E R) (blobOver E R)) ∧
    (ofStore R).Extends (lookup (storeOver E R) (blobOver E R)) :=
  ⟨lookup_extends (fun _ _ h => ReaderReads.storeOver_left h)
      (fun _ _ h => ReaderReads.blobOver_left h),
    lookup_extends (fun _ _ h => ReaderReads.storeOver_right hr h)
      (fun _ _ h => ReaderReads.blobOver_right hb h)⟩

/-- Two successful raw-store classifications agree from record/blob agreement alone. -/
theorem sortSignature_agree {E R : Ixon.Env}
    (hr : ∀ a c c', recordOf E a = some c → recordOf R a = some c' → c = c')
    (hb : ∀ a b b', E.blobs.get? a = some b → R.blobs.get? a = some b' → b = b')
    {fuel : Nat} {ctx : List (Expr .anon)} {e : Expr .anon} {s t : Level}
    (hs : Ix.Kernel.GuardClassifier.sortSignature (ofStore E) fuel ctx e = some s)
    (ht : Ix.Kernel.GuardClassifier.sortSignature (ofStore R) fuel ctx e = some t) : s = t :=
  Ix.Kernel.GuardClassifier.sortSignature_agree (common_lookup hr hb).1 (common_lookup hr hb).2 hs ht

/-- Raw-byte preservation gives record preservation even when cached decoded values differ. -/
theorem records_of_bytes {E E' : Ixon.Env}
    (hraw : ∀ a lc, E.consts.get? a = some lc →
      ∃ lc', E'.consts.get? a = some lc' ∧ lc'.rawBytes = lc.rawBytes) :
    ∀ a c, recordOf E a = some c → recordOf E' a = some c := by
  intro a c hc
  obtain ⟨lc, hget, hdec⟩ := Typing.recordOf_some hc
  obtain ⟨lc', hget', hbytes⟩ := hraw a lc hget
  apply Typing.recordOf_of_get hget'
  rw [hbytes]
  exact hdec

/-- The concrete store lookup extends when bytes and literal blobs extend. -/
theorem ofStore_extends_of_bytes {E E' : Ixon.Env}
    (hraw : ∀ a lc, E.consts.get? a = some lc →
      ∃ lc', E'.consts.get? a = some lc' ∧ lc'.rawBytes = lc.rawBytes)
    (hb : ∀ a bytes, E.blobs.get? a = some bytes → E'.blobs.get? a = some bytes) :
    (ofStore E).Extends (ofStore E') :=
  lookup_extends (records_of_bytes hraw) hb

/-- Every raw root answer is in the chosen metadata-free canonical syntax. -/
theorem readRoot_erased {blob : Blobs} {root : Root} {e : Expr .anon}
    (h : readRoot blob root = some e) : e.eraseMeta = e := by
  obtain ⟨v, _, heq⟩ := Option.map_eq_some_iff.mp h
  subst heq
  exact Expr.eraseMeta_idem v

/-- The raw reader introduces no free-variable annotations. Its variables are de Bruijn indices. -/
theorem readRoot_noFvar {blob : Blobs} {root : Root} {e : Expr .anon}
    (h : readRoot blob root = some e) : e.hasFvar = false := by
  obtain ⟨v, hv, heq⟩ := Option.map_eq_some_iff.mp h
  subst heq
  rw [Ix.Kernel.GuardClassifier.eraseMeta_hasFvar]
  exact Assembly.memberReader_read_noFvar (Typing.toOption_eq_some hv)

private theorem recordOf_eq_cached {E : Ixon.Env} (hd : Ingress.EnvDecoded E) (a : _root_.Address) :
    recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hdec⟩ := hd a lc hget
    change (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hdec, hc]
    rfl

/-- The witness-store interface itself supplies a raw dictionary extension, at every limit. -/
theorem ofStore_extends_recordsFor {R E : Ixon.Env} (h : Typing.RecordsFor R E) :
    (ofStore R).Extends (ofStore E) :=
  lookup_extends
    (fun a c hc => (recordOf_eq_cached h.1 a).trans (h.2.1 a c hc))
    h.2.2.1

/-- Collision exclusion supplies agreement of the run and witness dictionaries. -/
theorem common_lookup_of_noCollision
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {E₀ R : Ixon.Env}
    {V : View} {extra : List ByteArray}
    (hload : LoadedBy calls E₀) (hnc : ¬ CollisionWith V extra R calls) :
    (ofStore E₀).Extends (lookup (storeOver E₀ R) (blobOver E₀ R)) ∧
    (ofStore R).Extends (lookup (storeOver E₀ R) (blobOver E₀ R)) :=
  common_lookup (Typing.records_agree hload hnc) (Typing.blobs_agree hload hnc)

/-- A small real definition record: `def _ : Type := Prop`, with no references or binders. -/
def sortDefinition : Ixon.Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := .sort 1, value := .sort 0 }
    sharing := #[], refs := #[], univs := #[.zero, .succ .zero] }

/-- Its singleton raw-record map. No admitted typed environment is assumed. -/
def sortDefinitionRecords (a : _root_.Address) : Records :=
  fun x => if x = a then some sortDefinition else none

/-- The raw dictionary reads the declared type of the concrete definition. -/
theorem sortDefinition_type (a : _root_.Address) :
    (lookup (sortDefinitionRecords a) (fun _ => none)).typeOf (.id a) [] =
      some (.sort (.succ .zero)) := by
  let root : Root := ⟨sortDefinition, soloSelf addressTable a, 0, 0, .sort 1⟩
  have hr : typeRoot (sortDefinitionRecords a) a = some root := by
    simp [typeRoot, sortDefinitionRecords, sortDefinition, root]
  have hd : readRoot (fun _ => none) root = some (.sort (.succ .zero)) :=
    readRoot_sort (u := .succ .zero) rfl (by rfl)
  change answer (fun _ => none) (typeRoot (sortDefinitionRecords a) a) [] = _
  rw [hr]
  change (readRoot (fun _ => none) root).map
    (fun e => e.instantiateLevelParams [] []) = _
  rw [hd]
  rfl

/-- The same dictionary reads its definition value, independently of any model. -/
theorem sortDefinition_value (a : _root_.Address) :
    (lookup (sortDefinitionRecords a) (fun _ => none)).valueOf (.id a) [] =
      some (.sort .zero) := by
  let root : Root := ⟨sortDefinition, soloSelf addressTable a, 1, 0, .sort 0⟩
  have hr : valueRoot (sortDefinitionRecords a) a = some root := by
    simp [valueRoot, sortDefinitionRecords, sortDefinition, root]
  have hd : readRoot (fun _ => none) root = some (.sort .zero) :=
    readRoot_sort (u := .zero) rfl (by rfl)
  change answer (fun _ => none) (valueRoot (sortDefinitionRecords a) a) [] = _
  rw [hr]
  change (readRoot (fun _ => none) root).map
    (fun e => e.instantiateLevelParams [] []) = _
  rw [hd]
  rfl


end IxVM.Refinement.GuardRaw
