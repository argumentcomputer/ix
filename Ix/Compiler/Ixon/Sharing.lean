import Ix.Compiler.Ixon.Sharing.Basic
import Ix.Compiler.Ixon.Sharing.Compress
import Ix.Compiler.Ixon.Const
import Ix.Compiler.Ixon.DecodeCheck
import Ix.Compiler.Ixon.Work

/-!
# Canonical sharing

S1/S2 provide the decoder-enforced layer-1 invariant and proved left-to-right
inlining. `Sharing.Compress` adds the collision-safe deterministic compressor,
exact serializer audit, and layer-2 canonicality by recompression:

`compress (inline constant) == constant`.

Keeping those layers separate is deliberate. Byte decoding cheaply rejects
cycles, forward/out-of-bounds references, aliases, and dead/singleton entries;
the semantic address boundary pays for exact compressor-image validation.
-/

namespace Ix.Compiler.Ixon.Sharing

/-- Inline each embedded expression in the constant's authoritative body
order. This is the semantic input expected by the future compressor. -/
def inlineBodies (c : Constant) : Array Expr :=
  c.info.exprs.toArray.map (inlineExpr c.sharing)

/-- Inlining is body-for-body: it changes expressions, not their authoritative
enumeration order. -/
theorem inlineBodies_size (c : Constant) :
    (inlineBodies c).size = c.info.exprs.length := by
  simp [inlineBodies]

/-- Decoder-accepted constants have no sharing nodes after their complete body
enumeration is inlined. This is the constant-level S2 theorem consumed by the
next evaluator-coherence proof. -/
theorem inlineBodies_shareFree (c : Constant)
    (h : c.sharingWF = true) :
    (inlineBodies c).all shareFree = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < c.info.exprs.toArray.size := by
    simpa [inlineBodies] using hi
  change shareFree ((c.info.exprs.toArray.map (inlineExpr c.sharing))[i]) = true
  rw [Array.getElem_map (inlineExpr c.sharing) hi]
  apply shareFree_inlineExpr_of_layer1 c.sharing c.info.exprs.toArray
    c.info.exprs.toArray[i]
  · simpa [Constant.sharingWF] using h
  · exact Array.mem_def.mp (Array.getElem_mem hi')

theorem canonical_components (bodies table : Array Expr)
    (h : canonical bodies table = true) :
    compress? (bodies.map (inlineExpr table)) =
      some ⟨bodies, table⟩ := by
  unfold canonical at h
  split at h
  · contradiction
  · cases hc : compress? (bodies.map (inlineExpr table)) with
    | none => simp [hc] at h
    | some out =>
      simp [hc] at h
      rcases h with ⟨hbodies, htable⟩
      subst bodies
      subst table
      rfl

/-- The exact compressor recognizer admits at most one representation of an
expanded body array. -/
theorem canonical_eq_of_expanded_eq
    {leftBodies leftTable rightBodies rightTable : Array Expr}
    (hleft : canonical leftBodies leftTable = true)
    (hright : canonical rightBodies rightTable = true)
    (hexpanded : leftBodies.map (inlineExpr leftTable) =
      rightBodies.map (inlineExpr rightTable)) :
    leftBodies = rightBodies ∧ leftTable = rightTable := by
  have hl := canonical_components leftBodies leftTable hleft
  have hr := canonical_components rightBodies rightTable hright
  rw [hexpanded] at hl
  rw [hr] at hl
  cases hl
  exact ⟨rfl, rfl⟩

theorem layer1_of_canonical (bodies table : Array Expr)
    (h : canonical bodies table = true) :
    layer1WF table bodies = true := by
  exact layer1_compress _ _ (canonical_components bodies table h)

end Ix.Compiler.Ixon.Sharing

namespace Ix.Compiler.Ixon

/-- Exact layer-2 sharing canonicality for the complete constant body order. -/
def Constant.canonicalSharing (c : Constant) : Bool :=
  Sharing.canonical c.info.exprs.toArray c.sharing

/-- Content address of an exactly recompression-canonical, checked constant.
Raw, merely layer-1, count-truncating, or locally malformed constants remain
serializable for codec fixtures but cannot cross this identity boundary. -/
def Constant.address? (c : Constant) : Option Address :=
  if c.canonicalSharing && DecodeCheck.checkedWF c then
    some (.blake3 (ser c))
  else none

/-- Resource policy for constructed constants entering the semantic address
boundary.  Local validation and exact recompression have separate limits
because both execute the layer-1 predicate. -/
structure Constant.AddressLimits where
  ingress : DecodeCheck.Limits := {}
  sharing : Sharing.ResourceLimits := {}
  deriving BEq, DecidableEq, Repr

def Constant.defaultAddressLimits : Constant.AddressLimits := {}

inductive Constant.AddressError where
  | wireNotRepresentable
  | invalid (error : DecodeCheck.Error)
  | resource (exceeded : Work.Exceeded)
  | nonCanonicalSharing
  deriving BEq, DecidableEq, Repr

/-- Corpus-facing constructed-value address boundary.  It checks wire/local
validity first, computes sharing-expansion size without allocating it, and
only then runs exact recompression and BLAKE3.  `address?` remains the
transparent proof-facing predicate. -/
def Constant.addressCheckedWith (limits : Constant.AddressLimits)
    (c : Constant) : Except Constant.AddressError Address :=
  if !DecodeCheck.wireConstantWF c then
    .error .wireNotRepresentable
  else
    match DecodeCheck.checkConstantWith limits.ingress c with
    | .error error => .error (.invalid error)
    | .ok _ =>
      match Sharing.canonicalWith limits.sharing c.info.exprs.toArray
          c.sharing with
      | .error exceeded => .error (.resource exceeded)
      | .ok false => .error .nonCanonicalSharing
      | .ok true => .ok (.blake3 (ser c))

def Constant.addressChecked (c : Constant) :
    Except Constant.AddressError Address :=
  c.addressCheckedWith Constant.defaultAddressLimits

/-- Address boundary for bytes produced by the pinned upstream ixon-v2
writer.  It preserves the upstream address exactly while admitting only the
deterministic upstream compressor image; Ix.Compiler's stronger local sharing
policy and `addressCheckedWith` remain unchanged. -/
def Constant.addressIxonV2CheckedWith (limits : Constant.AddressLimits)
    (c : Constant) : Except Constant.AddressError Address :=
  if !DecodeCheck.wireConstantWF c then
    .error .wireNotRepresentable
  else
    match DecodeCheck.checkIxonV2ConstantWith limits.ingress c with
    | .error error => .error (.invalid error)
    | .ok _ =>
      match Sharing.ixonV2CanonicalWith limits.sharing c.info.exprs.toArray
          c.sharing with
      | .error exceeded => .error (.resource exceeded)
      | .ok false => .error .nonCanonicalSharing
      | .ok true => .ok (.blake3 (ser c))

def Constant.addressIxonV2Checked (c : Constant) :
    Except Constant.AddressError Address :=
  c.addressIxonV2CheckedWith Constant.defaultAddressLimits

theorem Constant.addressCheckedWith_sound {limits : Constant.AddressLimits}
    {c : Constant} {address : Address}
    (h : c.addressCheckedWith limits = .ok address) :
    c.wireWF ∧ DecodeCheck.checkConstant c = .ok () ∧
      c.canonicalSharing = true ∧ address = .blake3 (ser c) := by
  unfold Constant.addressCheckedWith at h
  split at h
  · contradiction
  · rename_i hwire
    have hwire' : DecodeCheck.wireConstantWF c = true := by
      simpa using hwire
    cases hcheck : DecodeCheck.checkConstantWith limits.ingress c with
    | error error => simp [hcheck] at h
    | ok result =>
      cases result
      cases hcanonical : Sharing.canonicalWith limits.sharing
          c.info.exprs.toArray c.sharing with
      | error exceeded => simp [hcheck, hcanonical] at h
      | ok canonical =>
        cases canonical with
        | false => simp [hcheck, hcanonical] at h
        | true =>
          simp [hcheck, hcanonical] at h
          exact ⟨(DecodeCheck.wireConstantWF_eq_true_iff c).mp hwire',
            DecodeCheck.checkConstant_of_checkConstantWith hcheck,
            Sharing.canonicalWith_true hcanonical, h.symm⟩

theorem Constant.addressIxonV2CheckedWith_sound
    {limits : Constant.AddressLimits} {c : Constant} {address : Address}
    (h : c.addressIxonV2CheckedWith limits = .ok address) :
    c.wireWF ∧ DecodeCheck.checkIxonV2Constant c = .ok () ∧
      Sharing.ixonV2Canonical c.info.exprs.toArray c.sharing = true ∧
      address = .blake3 (ser c) := by
  unfold Constant.addressIxonV2CheckedWith at h
  split at h
  · contradiction
  · rename_i hwire
    have hwire' : DecodeCheck.wireConstantWF c = true := by
      simpa using hwire
    cases hcheck : DecodeCheck.checkIxonV2ConstantWith limits.ingress c with
    | error error => simp [hcheck] at h
    | ok result =>
      cases result
      cases hcanonical : Sharing.ixonV2CanonicalWith limits.sharing
          c.info.exprs.toArray c.sharing with
      | error exceeded => simp [hcheck, hcanonical] at h
      | ok canonical =>
        cases canonical with
        | false => simp [hcheck, hcanonical] at h
        | true =>
          simp [hcheck, hcanonical] at h
          exact ⟨(DecodeCheck.wireConstantWF_eq_true_iff c).mp hwire',
            DecodeCheck.checkIxonV2Constant_of_checkIxonV2ConstantWith hcheck,
            Sharing.ixonV2CanonicalWith_true hcanonical, h.symm⟩

/-! ## Canonical semantic identity -/

namespace ConstantIdentityLaws

def mapDefinition (f : Expr → Expr) (d : Definition) : Definition :=
  { d with typ := f d.typ, value := f d.value }

def mapRule (f : Expr → Expr) (r : RecursorRule) : RecursorRule :=
  { r with rhs := f r.rhs }

def mapRecursor (f : Expr → Expr) (r : Recursor) : Recursor :=
  { r with typ := f r.typ, rules := r.rules.map (mapRule f) }

def mapAxiom (f : Expr → Expr) (a : Axiom) : Axiom :=
  { a with typ := f a.typ }

def mapQuotient (f : Expr → Expr) (q : Quotient) : Quotient :=
  { q with typ := f q.typ }

def mapConstructor (f : Expr → Expr) (c : Constructor) : Constructor :=
  { c with typ := f c.typ }

def mapInductive (f : Expr → Expr) (i : Inductive) : Inductive :=
  { i with typ := f i.typ, ctors := i.ctors.map (mapConstructor f) }

def mapMutConst (f : Expr → Expr) : MutConst → MutConst
  | .defn d => .defn (mapDefinition f d)
  | .indc i => .indc (mapInductive f i)
  | .recr r => .recr (mapRecursor f r)

def mapInfo (f : Expr → Expr) : ConstantInfo → ConstantInfo
  | .defn d => .defn (mapDefinition f d)
  | .recr r => .recr (mapRecursor f r)
  | .axio a => .axio (mapAxiom f a)
  | .quot q => .quot (mapQuotient f q)
  | .cPrj p => .cPrj p
  | .rPrj p => .rPrj p
  | .iPrj p => .iPrj p
  | .dPrj p => .dPrj p
  | .muts ms => .muts (ms.map (mapMutConst f))

def eraseInfo : ConstantInfo → ConstantInfo :=
  mapInfo (fun _ => .sort 0)

def restoreRules : List RecursorRule → List Expr →
    Option (List RecursorRule × List Expr)
  | [], xs => some ([], xs)
  | _, [] => none
  | rule :: rules, rhs :: xs => do
    let (restored, suffix) ← restoreRules rules xs
    return ({ rule with rhs := rhs } :: restored, suffix)

def restoreCtors : List Constructor → List Expr →
    Option (List Constructor × List Expr)
  | [], xs => some ([], xs)
  | _, [] => none
  | ctor :: ctors, typ :: xs => do
    let (restored, suffix) ← restoreCtors ctors xs
    return ({ ctor with typ := typ } :: restored, suffix)

def restoreDefinition (d : Definition) : List Expr →
    Option (Definition × List Expr)
  | typ :: value :: suffix => some ({ d with typ := typ, value := value }, suffix)
  | _ => none

def restoreRecursor (r : Recursor) : List Expr →
    Option (Recursor × List Expr)
  | [] => none
  | typ :: xs => do
    let (rules, suffix) ← restoreRules r.rules.toList xs
    return ({ r with typ := typ, rules := rules.toArray }, suffix)

def restoreAxiom (a : Axiom) : List Expr → Option (Axiom × List Expr)
  | [] => none
  | typ :: suffix => some ({ a with typ := typ }, suffix)

def restoreQuotient (q : Quotient) : List Expr → Option (Quotient × List Expr)
  | [] => none
  | typ :: suffix => some ({ q with typ := typ }, suffix)

def restoreConstructor (c : Constructor) : List Expr →
    Option (Constructor × List Expr)
  | [] => none
  | typ :: suffix => some ({ c with typ := typ }, suffix)

def restoreInductive (i : Inductive) : List Expr →
    Option (Inductive × List Expr)
  | [] => none
  | typ :: xs => do
    let (ctors, suffix) ← restoreCtors i.ctors.toList xs
    return ({ i with typ := typ, ctors := ctors.toArray }, suffix)

def restoreMutConst (m : MutConst) (xs : List Expr) :
    Option (MutConst × List Expr) :=
  match m with
  | .defn d => do
    let (d, suffix) ← restoreDefinition d xs
    return (.defn d, suffix)
  | .indc i => do
    let (i, suffix) ← restoreInductive i xs
    return (.indc i, suffix)
  | .recr r => do
    let (r, suffix) ← restoreRecursor r xs
    return (.recr r, suffix)

def restoreMuts : List MutConst → List Expr →
    Option (List MutConst × List Expr)
  | [], xs => some ([], xs)
  | member :: members, xs => do
    let (member, afterMember) ← restoreMutConst member xs
    let (members, suffix) ← restoreMuts members afterMember
    return (member :: members, suffix)

def restoreInfo (shape : ConstantInfo) (xs : List Expr) :
    Option (ConstantInfo × List Expr) :=
  match shape with
  | .defn d => do
    let (d, suffix) ← restoreDefinition d xs
    return (.defn d, suffix)
  | .recr r => do
    let (r, suffix) ← restoreRecursor r xs
    return (.recr r, suffix)
  | .axio a => do
    let (a, suffix) ← restoreAxiom a xs
    return (.axio a, suffix)
  | .quot q => do
    let (q, suffix) ← restoreQuotient q xs
    return (.quot q, suffix)
  | .cPrj p => some (.cPrj p, xs)
  | .rPrj p => some (.rPrj p, xs)
  | .iPrj p => some (.iPrj p, xs)
  | .dPrj p => some (.dPrj p, xs)
  | .muts ms => do
    let (ms, suffix) ← restoreMuts ms.toList xs
    return (.muts ms.toArray, suffix)

def replaceInfoExprs? (shape : ConstantInfo) (xs : List Expr) :
    Option ConstantInfo := do
  let (info, suffix) ← restoreInfo shape xs
  if suffix.isEmpty then some info else none

theorem restoreRules_spec (rules : List RecursorRule) (suffix : List Expr) :
    restoreRules rules (rules.map (·.rhs) ++ suffix) = some (rules, suffix) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih => simp [restoreRules, ih]

theorem restoreCtors_spec (ctors : List Constructor) (suffix : List Expr) :
    restoreCtors ctors (ctors.map (·.typ) ++ suffix) = some (ctors, suffix) := by
  induction ctors with
  | nil => rfl
  | cons ctor ctors ih => simp [restoreCtors, ih]

theorem restoreDefinition_spec (d : Definition) (suffix : List Expr) :
    restoreDefinition d (d.exprs ++ suffix) = some (d, suffix) := by
  simp [restoreDefinition, Definition.exprs]

theorem restoreRecursor_spec (r : Recursor) (suffix : List Expr) :
    restoreRecursor r (r.exprs ++ suffix) = some (r, suffix) := by
  simp [restoreRecursor, Recursor.exprs, restoreRules_spec]

theorem restoreAxiom_spec (a : Axiom) (suffix : List Expr) :
    restoreAxiom a (a.exprs ++ suffix) = some (a, suffix) := by
  simp [restoreAxiom, Axiom.exprs]

theorem restoreQuotient_spec (q : Quotient) (suffix : List Expr) :
    restoreQuotient q (q.exprs ++ suffix) = some (q, suffix) := by
  simp [restoreQuotient, Quotient.exprs]

theorem restoreConstructor_spec (c : Constructor) (suffix : List Expr) :
    restoreConstructor c (c.exprs ++ suffix) = some (c, suffix) := by
  simp [restoreConstructor, Constructor.exprs]

theorem flatMap_constructorExprs (ctors : List Constructor) :
    ctors.flatMap Constructor.exprs = ctors.map (·.typ) := by
  induction ctors with
  | nil => rfl
  | cons ctor ctors ih => simp [Constructor.exprs, ih]

theorem restoreInductive_spec (i : Inductive) (suffix : List Expr) :
    restoreInductive i (i.exprs ++ suffix) = some (i, suffix) := by
  rw [show i.exprs = i.typ :: i.ctors.toList.flatMap Constructor.exprs by
    rfl]
  rw [flatMap_constructorExprs]
  simp [restoreInductive, restoreCtors_spec]

theorem restoreMutConst_spec (m : MutConst) (suffix : List Expr) :
    restoreMutConst m (m.exprs ++ suffix) = some (m, suffix) := by
  cases m with
  | defn d => simp [restoreMutConst, MutConst.exprs, restoreDefinition_spec]
  | indc i => simp [restoreMutConst, MutConst.exprs, restoreInductive_spec]
  | recr r => simp [restoreMutConst, MutConst.exprs, restoreRecursor_spec]

theorem restoreMuts_spec (members : List MutConst) (suffix : List Expr) :
    restoreMuts members (members.flatMap MutConst.exprs ++ suffix) =
      some (members, suffix) := by
  induction members with
  | nil => rfl
  | cons member members ih =>
    simp [restoreMuts, restoreMutConst_spec, ih, List.append_assoc]

theorem restoreInfo_spec (info : ConstantInfo) (suffix : List Expr) :
    restoreInfo info (info.exprs ++ suffix) = some (info, suffix) := by
  cases info with
  | defn d => simp [restoreInfo, ConstantInfo.exprs, restoreDefinition_spec]
  | recr r => simp [restoreInfo, ConstantInfo.exprs, restoreRecursor_spec]
  | axio a => simp [restoreInfo, ConstantInfo.exprs, restoreAxiom_spec]
  | quot q => simp [restoreInfo, ConstantInfo.exprs, restoreQuotient_spec]
  | cPrj p => simp [restoreInfo, ConstantInfo.exprs]
  | rPrj p => simp [restoreInfo, ConstantInfo.exprs]
  | iPrj p => simp [restoreInfo, ConstantInfo.exprs]
  | dPrj p => simp [restoreInfo, ConstantInfo.exprs]
  | muts ms => simp [restoreInfo, ConstantInfo.exprs, restoreMuts_spec]

theorem replaceInfoExprs?_self (info : ConstantInfo) :
    replaceInfoExprs? info info.exprs = some info := by
  have hrestore : restoreInfo info info.exprs = some (info, []) := by
    simpa using restoreInfo_spec info []
  simp [replaceInfoExprs?, hrestore]

theorem restoreRules_mapRule (f : Expr → Expr) (rules : List RecursorRule)
    (xs : List Expr) :
    restoreRules (rules.map (mapRule f)) xs = restoreRules rules xs := by
  induction rules generalizing xs with
  | nil => rfl
  | cons rule rules ih =>
    cases xs <;> simp [restoreRules, mapRule, ih]

theorem restoreCtors_mapConstructor (f : Expr → Expr) (ctors : List Constructor)
    (xs : List Expr) :
    restoreCtors (ctors.map (mapConstructor f)) xs = restoreCtors ctors xs := by
  induction ctors generalizing xs with
  | nil => rfl
  | cons ctor ctors ih =>
    cases xs <;> simp [restoreCtors, mapConstructor, ih]

theorem restoreDefinition_map (f : Expr → Expr) (d : Definition)
    (xs : List Expr) :
    restoreDefinition (mapDefinition f d) xs = restoreDefinition d xs := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> rfl

theorem restoreRecursor_map (f : Expr → Expr) (r : Recursor)
    (xs : List Expr) :
    restoreRecursor (mapRecursor f r) xs = restoreRecursor r xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [restoreRecursor, mapRecursor, restoreRules_mapRule]

theorem restoreAxiom_map (f : Expr → Expr) (a : Axiom) (xs : List Expr) :
    restoreAxiom (mapAxiom f a) xs = restoreAxiom a xs := by
  cases xs <;> rfl

theorem restoreQuotient_map (f : Expr → Expr) (q : Quotient) (xs : List Expr) :
    restoreQuotient (mapQuotient f q) xs = restoreQuotient q xs := by
  cases xs <;> rfl

theorem restoreConstructor_map (f : Expr → Expr) (c : Constructor)
    (xs : List Expr) :
    restoreConstructor (mapConstructor f c) xs = restoreConstructor c xs := by
  cases xs <;> rfl

theorem restoreInductive_map (f : Expr → Expr) (i : Inductive)
    (xs : List Expr) :
    restoreInductive (mapInductive f i) xs = restoreInductive i xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [restoreInductive, mapInductive, restoreCtors_mapConstructor]

theorem restoreMutConst_map (f : Expr → Expr) (member : MutConst)
    (xs : List Expr) :
    restoreMutConst (mapMutConst f member) xs = restoreMutConst member xs := by
  cases member with
  | defn d => simp [restoreMutConst, mapMutConst, restoreDefinition_map]
  | indc i => simp [restoreMutConst, mapMutConst, restoreInductive_map]
  | recr r => simp [restoreMutConst, mapMutConst, restoreRecursor_map]

theorem restoreMuts_map (f : Expr → Expr) (members : List MutConst)
    (xs : List Expr) :
    restoreMuts (members.map (mapMutConst f)) xs = restoreMuts members xs := by
  induction members generalizing xs with
  | nil => rfl
  | cons member members ih =>
    simp only [List.map_cons, restoreMuts]
    rw [restoreMutConst_map]
    cases hm : restoreMutConst member xs with
    | none => rfl
    | some result =>
      rcases result with ⟨restored, suffix⟩
      simp [ih]

theorem restoreInfo_map (f : Expr → Expr) (info : ConstantInfo)
    (xs : List Expr) :
    restoreInfo (mapInfo f info) xs = restoreInfo info xs := by
  cases info with
  | defn d => simp [restoreInfo, mapInfo, restoreDefinition_map]
  | recr r => simp [restoreInfo, mapInfo, restoreRecursor_map]
  | axio a => simp [restoreInfo, mapInfo, restoreAxiom_map]
  | quot q => simp [restoreInfo, mapInfo, restoreQuotient_map]
  | cPrj p => rfl
  | rPrj p => rfl
  | iPrj p => rfl
  | dPrj p => rfl
  | muts ms => simp [restoreInfo, mapInfo, restoreMuts_map]

theorem info_eq_of_erased_eq_of_exprs_eq (a b : ConstantInfo)
    (hs : eraseInfo a = eraseInfo b) (he : a.exprs = b.exprs) : a = b := by
  have ha := replaceInfoExprs?_self a
  have hb := replaceInfoExprs?_self b
  unfold replaceInfoExprs? at ha hb
  rw [← restoreInfo_map (fun _ => .sort 0) a a.exprs] at ha
  rw [← restoreInfo_map (fun _ => .sort 0) b b.exprs] at hb
  change restoreInfo (eraseInfo a) a.exprs >>= _ = some a at ha
  change restoreInfo (eraseInfo b) b.exprs >>= _ = some b at hb
  rw [hs, he] at ha
  rw [hb] at ha
  cases ha
  rfl

end ConstantIdentityLaws

/-- Apply a transformation to every authoritative expression root. These
maps preserve all declaration metadata and nested array structure. -/
def Definition.mapExprs (f : Expr → Expr) (d : Definition) : Definition :=
  ConstantIdentityLaws.mapDefinition f d

def RecursorRule.mapExprs (f : Expr → Expr)
    (r : RecursorRule) : RecursorRule :=
  ConstantIdentityLaws.mapRule f r

def Recursor.mapExprs (f : Expr → Expr) (r : Recursor) : Recursor :=
  ConstantIdentityLaws.mapRecursor f r

def Axiom.mapExprs (f : Expr → Expr) (a : Axiom) : Axiom :=
  ConstantIdentityLaws.mapAxiom f a

def Quotient.mapExprs (f : Expr → Expr) (q : Quotient) : Quotient :=
  ConstantIdentityLaws.mapQuotient f q

def Constructor.mapExprs (f : Expr → Expr) (c : Constructor) : Constructor :=
  ConstantIdentityLaws.mapConstructor f c

def Inductive.mapExprs (f : Expr → Expr) (i : Inductive) : Inductive :=
  ConstantIdentityLaws.mapInductive f i

def MutConst.mapExprs (f : Expr → Expr) (m : MutConst) : MutConst :=
  ConstantIdentityLaws.mapMutConst f m

def ConstantInfo.mapExprs (f : Expr → Expr)
    (info : ConstantInfo) : ConstantInfo :=
  ConstantIdentityLaws.mapInfo f info

namespace ConstantInfo

/-- All non-expression fields and expression-slot structure, represented by
replacing every embedded expression root with a fixed placeholder. -/
def identityShape (info : ConstantInfo) : ConstantInfo :=
  ConstantIdentityLaws.eraseInfo info

theorem eq_of_identityShape_eq_of_exprs_eq (left right : ConstantInfo)
    (hshape : left.identityShape = right.identityShape)
    (hexprs : left.exprs = right.exprs) : left = right := by
  exact ConstantIdentityLaws.info_eq_of_erased_eq_of_exprs_eq left right
    hshape hexprs

end ConstantInfo

namespace Constant

/-- Fully inline every authoritative expression root and clear the sharing
table while preserving the constant's metadata, refs, and universes. -/
def inlineSharing (c : Constant) : Constant :=
  { info := c.info.mapExprs (Sharing.inlineExpr c.sharing)
    sharing := #[]
    refs := c.refs
    univs := c.univs }

/-- Sharing-independent semantic view of a constant. The body array contains
all embedded expression roots in authoritative order after full inlining. -/
structure InlinedView where
  infoShape : ConstantInfo
  bodies : Array Expr
  refs : Array Address
  univs : Array Univ
  deriving BEq, Repr

def inlinedView (c : Constant) : InlinedView :=
  { infoShape := c.info.identityShape
    bodies := Sharing.inlineBodies c
    refs := c.refs
    univs := c.univs }

/-- The exact executable address-gate domain: layer-2 canonical sharing plus
the checked writer's wire and local-semantic domain. -/
def Addressable (c : Constant) : Prop :=
  c.canonicalSharing = true ∧ DecodeCheck.checkedWF c = true

theorem sharingWF_of_canonicalSharing (c : Constant)
    (h : c.canonicalSharing = true) : c.sharingWF = true := by
  change Sharing.layer1WF c.sharing c.info.exprs.toArray = true
  exact Sharing.layer1_of_canonical c.info.exprs.toArray c.sharing h

theorem eq_of_ser_eq (left right : Constant)
    (hleftWire : left.wireWF) (hrightWire : right.wireWF)
    (hleftSharing : left.sharingWF = true)
    (hrightSharing : right.sharingWF = true)
    (hbytes : ser left = ser right) : left = right := by
  have hleft := roundtripLaw left hleftWire hleftSharing
  have hright := roundtripLaw right hrightWire hrightSharing
  rw [hbytes, hright] at hleft
  exact (Except.ok.inj hleft).symm

/-- Exact layer-2 canonicality makes the sharing-independent view injective:
one semantic constant has one compressed representation. -/
theorem eq_of_inlinedView_eq_of_canonicalSharing (left right : Constant)
    (hleft : left.canonicalSharing = true)
    (hright : right.canonicalSharing = true)
    (hview : left.inlinedView = right.inlinedView) : left = right := by
  have hshape := congrArg InlinedView.infoShape hview
  have hbodies := congrArg InlinedView.bodies hview
  have hrefs := congrArg InlinedView.refs hview
  have hunivs := congrArg InlinedView.univs hview
  change left.info.identityShape = right.info.identityShape at hshape
  change Sharing.inlineBodies left = Sharing.inlineBodies right at hbodies
  change left.refs = right.refs at hrefs
  change left.univs = right.univs at hunivs
  have hcomponents := Sharing.canonical_eq_of_expanded_eq hleft hright hbodies
  have hexprs : left.info.exprs = right.info.exprs := by
    have hlists := congrArg Array.toList hcomponents.1
    simpa using hlists
  have hinfo := ConstantInfo.eq_of_identityShape_eq_of_exprs_eq
    left.info right.info hshape hexprs
  cases left
  cases right
  simp_all

/-- Equal accepted addresses identify equal constants under only the explicit
pairwise no-collision premise for their two serialized preimages. -/
theorem eq_of_address?_eq (left right : Constant)
    (hleft : left.Addressable) (hright : right.Addressable)
    (hcollision : Address.Blake3NoCollision (ser left) (ser right))
    (haddress : left.address? = right.address?) : left = right := by
  have hhash : Address.blake3 (ser left) = Address.blake3 (ser right) := by
    simpa [address?, hleft.1, hleft.2, hright.1, hright.2] using haddress
  have hbytes := hcollision hhash
  exact eq_of_ser_eq left right
    (DecodeCheck.wireWF_of_checkedWF hleft.2)
    (DecodeCheck.wireWF_of_checkedWF hright.2)
    (sharingWF_of_canonicalSharing left hleft.1)
    (sharingWF_of_canonicalSharing right hright.1) hbytes

/-- On locally checked, wire-representable, layer-2-canonical constants,
equality of fully inlined semantics is equivalent to equality of addresses,
modulo the exact pairwise BLAKE3 no-collision premise. -/
theorem inlinedView_eq_iff_address?_eq (left right : Constant)
    (hleft : left.Addressable) (hright : right.Addressable)
    (hcollision : Address.Blake3NoCollision (ser left) (ser right)) :
    left.inlinedView = right.inlinedView ↔ left.address? = right.address? := by
  constructor
  · intro hview
    have heq := eq_of_inlinedView_eq_of_canonicalSharing left right
      hleft.1 hright.1 hview
    subst right
    rfl
  · intro haddress
    exact congrArg inlinedView
      (eq_of_address?_eq left right hleft hright hcollision haddress)

/-! Pure regression for the semantic view. It deliberately avoids evaluating
the BLAKE3-dependent canonical compressor in the elaborator. -/

private def inlinedViewSharedFixture : Constant :=
  { info := .axio
      { isUnsafe := false, lvls := 0
        typ := .app (.share 0) (.share 0) }
    sharing := #[.sort 0]
    refs := #[]
    univs := #[] }

private def inlinedViewExpandedFixture : Constant :=
  { info := .axio
      { isUnsafe := false, lvls := 0
        typ := .app (.sort 0) (.sort 0) }
    sharing := #[]
    refs := #[]
    univs := #[] }

#guard inlinedViewSharedFixture != inlinedViewExpandedFixture
#guard inlinedViewSharedFixture.inlinedView ==
  inlinedViewExpandedFixture.inlinedView

end Constant

end Ix.Compiler.Ixon
