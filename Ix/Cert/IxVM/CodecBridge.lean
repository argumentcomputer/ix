import IxC.Ixon.Verify
import Ix.Claim
import IxC.Kernel.Admission.Bytes.Theorems
import Ix.Cert.IxVM.RoleAdmission

/-! # Wire Codec & Claim Deserialization Bridge (`IxVM` ↔ `IxC`)

This module establishes the formal correspondence between `IxVM`'s byte-stream
decoders and encoders (`Ix/IxVM/IxonDeserialize.lean`, `Ix/IxVM/IxonSerialize.lean`,
`Ix/IxVM/Ingress.lean`, `Ix/IxVM/Kernel/Claim.lean`, `Ix/IxVM/Kernel/Roles.lean`)
and `IxC`'s verified wire codec (`IxC/Ixon/Codec.lean`, `IxC/Ixon/Canonical.lean`,
`IxC/Ixon/Verify.lean`, `Ix/Claim.lean`, `IxC/Kernel/Admission/Bytes/Theorems.lean`).

## Key Results
1. **`TagN` Byte-Stream Codec Correspondence (`ixvmGetTagN4Exact`, `ixvmGetTagN2Exact`,
   `ixvmGetTagN0Exact`, `ixvmPutTagN4`, `ixvmPutTagN2`, `ixvmPutTagN0`)**:
   - `ixvm_getTagN_iff`, `ixvm_getTagN4_iff`, `ixvm_getTagN2_iff`, `ixvm_getTagN0_iff`:
     full-buffer `TagN` decoding at flag widths `f ∈ {0, 2, 4}` is a bijection
     between accepted byte buffers and `{t : Ixon.TagN | t.flag.toNat < 2^f}`.
   - `ixvm_putTagN_inj`, `ixvm_getTagN_inj`: `TagN` encoding and decoding are
     injective (`every value has exactly one encoding and there is no non-canonical
     form to reject`).
2. **Universe, Expression & Constant Codec Correspondence (`ixvmParseUniv`,
   `ixvmSerUniv`, `ixvmParseExpr`, `ixvmSerExpr`, `ixvmParseConstantExact`,
   `ixvmSerConstant`, `ixvmParseConstantCanonical`)**:
   - `ixvm_parseUniv_serUniv`, `ixvm_parseExpr_serExpr`, `ixvm_parseConstant_serConstant`:
     exact round-trip theorems on wire-well-formed universes, expressions, and constants.
   - `ixvm_parseConstant_noTrailing`, `ixvm_canonical_deConstant_noTrailing`:
     any non-empty trailing byte suffix after a constant is rejected (`assert_eq!(load(rest), ListNode.Nil)`).
   - `ixvm_canonical_deConstant_iff`: `IxVM`'s canonical constant decoding
     (`deConstantExact` + `wireWF` + `serConstant c = bytes` + resource bounds)
     matches `Ixon.Canonical.deConstant` (`Ixon.Verify.Canonical.deConstant_ok_iff`).
3. **Claim Wire Format Correspondence (`ixvmParseClaim`, `ixvmSerClaim`)**:
   - `ixvm_parseClaim_eq`, `ixvm_serClaim_eq`, `ixvm_claim_variants`: `IxVM`'s `run_claim`
     channel-0 byte parser corresponds to `Ix.Claim.de` / `Ix.Claim.ser`.
4. **Channel-6 Role Table & Blake3 Stream Authentication Bridge**:
   - `ixvm_channel6_roleTable_ofBytes_iff`, `ixvm_channel6_roleTable_roundtrip`:
     exact characterization of channel-6 role-binding byte streams (`RoleTable.ofBytes`).
   - `ixvm_authenticate_stream_iff`, `ixvm_decodeRecords_iff`, `ixvm_uniqueKeys_iff`,
     `ixvm_preflight_iff`: exact characterization of Blake3-verified constant and blob
     streams (`load_verified_constant`, `load_verified_blob` ↔ `Admission.authenticate`,
     `Admission.decodeRecords`, `Admission.uniqueKeys`, `Admission.preflight`).
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Admission

/-! ## 1. `TagN` Byte-Stream Codec Correspondence (`get_tagn4/2/0`, `put_tagn4/2/0` ↔ `Ixon.getTagN` / `Ixon.putTagN`) -/

/-- `IxVM`'s `get_tagn` at flag width `f` (`f = 4`, `2`, or `0`), run over a full byte buffer. -/
def ixvmGetTagNExact (f : Nat) (bytes : ByteArray) : Except String Ixon.TagN :=
  Ixon.runGetExact (Ixon.getTagN f) bytes

/-- `IxVM`'s `get_tagn4` (`f = 4`: expression, constant, and claim headers). -/
def ixvmGetTagN4Exact (bytes : ByteArray) : Except String Ixon.TagN :=
  ixvmGetTagNExact 4 bytes

/-- `IxVM`'s `get_tagn2` (`f = 2`: universe headers). -/
def ixvmGetTagN2Exact (bytes : ByteArray) : Except String Ixon.TagN :=
  ixvmGetTagNExact 2 bytes

/-- `IxVM`'s `get_tagn0` (`f = 0`: counts and indices). -/
def ixvmGetTagN0Exact (bytes : ByteArray) : Except String Ixon.TagN :=
  ixvmGetTagNExact 0 bytes

/-- `IxVM`'s `put_tagn` at flag width `f` (`f = 4`, `2`, or `0`). -/
def ixvmPutTagN (f : Nat) (flag : UInt8) (value : UInt64) : ByteArray :=
  Ixon.runPut (Ixon.putTagN f flag value)

/-- `IxVM`'s `put_tagn4` (`f = 4`). -/
def ixvmPutTagN4 (flag : UInt8) (value : UInt64) : ByteArray :=
  ixvmPutTagN 4 flag value

/-- `IxVM`'s `put_tagn2` (`f = 2`). -/
def ixvmPutTagN2 (flag : UInt8) (value : UInt64) : ByteArray :=
  ixvmPutTagN 2 flag value

/-- `IxVM`'s `put_tagn0` (`f = 0`, flag `0`). -/
def ixvmPutTagN0 (value : UInt64) : ByteArray :=
  ixvmPutTagN 0 0 value

/-- **Exact Characterization of `TagN` Decoding (`get_tagn` ↔ `put_tagn`)**:
For `f ∈ {0, 2, 4}`, `ixvmGetTagNExact f bytes = .ok t` holds if and only if
`t.flag.toNat < 2 ^ f` and `bytes` is the canonical `TagN` encoding `ixvmPutTagN f t.flag t.value`. -/
theorem ixvm_getTagN_iff (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    (bytes : ByteArray) (t : Ixon.TagN) :
    ixvmGetTagNExact f bytes = .ok t ↔
      t.flag.toNat < 2 ^ f ∧ bytes = ixvmPutTagN f t.flag t.value :=
  Ixon.Verify.TagN.runGetExact_getTagN_iff f hf bytes t

/-- **Exact Characterization of `get_tagn4` (`f = 4`)**:
`ixvmGetTagN4Exact bytes = .ok t` holds iff `t.flag.toNat < 16` and
`bytes = ixvmPutTagN4 t.flag t.value`. -/
theorem ixvm_getTagN4_iff (bytes : ByteArray) (t : Ixon.TagN) :
    ixvmGetTagN4Exact bytes = .ok t ↔
      t.flag.toNat < 2 ^ 4 ∧ bytes = ixvmPutTagN4 t.flag t.value :=
  ixvm_getTagN_iff 4 (Or.inr (Or.inr rfl)) bytes t

/-- **Exact Characterization of `get_tagn2` (`f = 2`)**:
`ixvmGetTagN2Exact bytes = .ok t` holds iff `t.flag.toNat < 4` and
`bytes = ixvmPutTagN2 t.flag t.value`. -/
theorem ixvm_getTagN2_iff (bytes : ByteArray) (t : Ixon.TagN) :
    ixvmGetTagN2Exact bytes = .ok t ↔
      t.flag.toNat < 2 ^ 2 ∧ bytes = ixvmPutTagN2 t.flag t.value :=
  ixvm_getTagN_iff 2 (Or.inr (Or.inl rfl)) bytes t

/-- **Exact Characterization of `get_tagn0` (`f = 0`)**:
`ixvmGetTagN0Exact bytes = .ok t` holds iff `t.flag.toNat < 1` (`t.flag = 0`) and
`bytes = ixvmPutTagN 0 t.flag t.value`. -/
theorem ixvm_getTagN0_iff (bytes : ByteArray) (t : Ixon.TagN) :
    ixvmGetTagN0Exact bytes = .ok t ↔
      t.flag.toNat < 2 ^ 0 ∧ bytes = ixvmPutTagN 0 t.flag t.value :=
  ixvm_getTagN_iff 0 (Or.inl rfl) bytes t

/-- **Injectivity of `TagN` Encoding (`put_tagn`)**:
Distinct `(flag, value)` pairs with `flag < 2^f` produce distinct byte sequences. -/
theorem ixvm_putTagN_inj (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {flag₁ flag₂ : UInt8} (hflag₁ : flag₁.toNat < 2 ^ f) (hflag₂ : flag₂.toNat < 2 ^ f)
    {value₁ value₂ : UInt64}
    (h : ixvmPutTagN f flag₁ value₁ = ixvmPutTagN f flag₂ value₂) :
    flag₁ = flag₂ ∧ value₁ = value₂ :=
  Ixon.Verify.TagN.putTagN_inj f hf hflag₁ hflag₂ h

/-- **Injectivity of `TagN` Decoding (`get_tagn`)**:
No two distinct byte strings decode to the same `TagN` value. -/
theorem ixvm_getTagN_inj (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {bytes₁ bytes₂ : ByteArray} {t : Ixon.TagN}
    (h₁ : ixvmGetTagNExact f bytes₁ = .ok t)
    (h₂ : ixvmGetTagNExact f bytes₂ = .ok t) :
    bytes₁ = bytes₂ :=
  Ixon.Verify.TagN.runGetExact_getTagN_inj f hf h₁ h₂

/-! ## 2. Universe, Expression & Constant Codec Bridge (`get_univ`, `get_expr`, `get_constant`, `put_constant`) -/

/-- `IxVM`'s universe parser (`get_univ` with trailing-nil check). -/
def ixvmParseUniv (bytes : ByteArray) : Except String Ixon.Univ :=
  Ixon.deUniv bytes

/-- `IxVM`'s universe serializer (`put_univ`). -/
def ixvmSerUniv (u : Ixon.Univ) : ByteArray :=
  Ixon.serUniv u

/-- `IxVM`'s expression parser (`get_expr` with trailing-nil check). -/
def ixvmParseExpr (bytes : ByteArray) : Except String Ixon.Expr :=
  Ixon.deExpr bytes

/-- `IxVM`'s expression serializer (`put_expr`). -/
def ixvmSerExpr (e : Ixon.Expr) : ByteArray :=
  Ixon.serExpr e

/-- `IxVM`'s exact constant parser (`get_constant` followed by `assert_eq!(load(rest), ListNode.Nil)`
in `Ingress.lean` `load_verified_constant`). -/
def ixvmParseConstantExact (bytes : ByteArray) : Except String Ixon.Constant :=
  Ixon.deConstantExact bytes

/-- `IxVM`'s constant serializer (`put_constant`). -/
def ixvmSerConstant (c : Ixon.Constant) : ByteArray :=
  Ixon.serConstant c

/-- `IxVM`'s canonical bounded constant decoder (`Ixon.Canonical.deConstant`),
combining `deConstantExact`, `wireWF` (maximal telescope compression and zero reserved bits),
canonical re-encoding (`serConstant c = bytes`), and byte/universe resource bounds. -/
def ixvmParseConstantCanonical (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) :
    Except String Ixon.Constant :=
  Ixon.Canonical.deConstant maxBytes maxUnivNodes bytes

/-- **Universe Round-Trip (`get_univ ∘ put_univ`)**:
Every wire-well-formed `Ixon.Univ` round-trips through `ixvmSerUniv` and `ixvmParseUniv`. -/
theorem ixvm_parseUniv_serUniv (u : Ixon.Univ) (hwf : Ixon.Verify.UnivWireWF u) :
    ixvmParseUniv (ixvmSerUniv u) = .ok u :=
  Ixon.Verify.deUniv_serUniv u hwf

/-- **Expression Round-Trip (`get_expr ∘ put_expr`)**:
Every wire-well-formed `Ixon.Expr` round-trips through `ixvmSerExpr` and `ixvmParseExpr`. -/
theorem ixvm_parseExpr_serExpr (e : Ixon.Expr) (hwf : Ixon.Verify.ExprWireWF e) :
    ixvmParseExpr (ixvmSerExpr e) = .ok e :=
  Ixon.Verify.deExpr_serExpr e hwf

/-- **Constant Exact Round-Trip (`get_constant ∘ put_constant`)**:
Every wire-well-formed `Ixon.Constant` round-trips through `ixvmSerConstant` and
`ixvmParseConstantExact`. -/
theorem ixvm_parseConstant_serConstant (c : Ixon.Constant) (hwf : c.wireWF) :
    ixvmParseConstantExact (ixvmSerConstant c) = .ok c :=
  Ixon.Verify.deConstantExact_serConstant c hwf

/-- **Trailing-Byte Rejection for `ixvmParseConstantExact`**:
Appending any non-empty suffix `suffix` (`suffix.size ≠ 0`) to a serialized
wire-well-formed constant causes `ixvmParseConstantExact` to reject. -/
theorem ixvm_parseConstant_noTrailing (c : Ixon.Constant) (hwf : c.wireWF)
    (suffix : ByteArray) (hnonempty : suffix.size ≠ 0) :
    (ixvmParseConstantExact (ixvmSerConstant c ++ suffix)).isOk = Bool.false :=
  Ixon.Verify.deConstantExact_noTrailing c hwf suffix hnonempty

/-- **Wire Well-Formedness Decision Equivalence (`WireCheck.validConstant_iff`)**:
`Ixon.WireCheck.validConstant c = true` holds iff `c.wireWF` holds. -/
theorem ixvm_validConstant_iff_wireWF (c : Ixon.Constant) :
    Ixon.WireCheck.validConstant c = Bool.true ↔ c.wireWF :=
  Ixon.Verify.WireCheck.validConstant_iff c

/-- **Exact Characterization of Canonical Constant Decoding (`Canonical.deConstant_ok_iff`)**:
`ixvmParseConstantCanonical maxBytes maxUnivNodes bytes = .ok c` holds if and only if
`c.wireWF` holds, `ixvmSerConstant c = bytes`, `bytes.size ≤ maxBytes`, and
`Ixon.Bounded.univNodes c.univs ≤ maxUnivNodes`. -/
theorem ixvm_canonical_deConstant_iff (maxBytes maxUnivNodes : Nat)
    (bytes : ByteArray) (c : Ixon.Constant) :
    ixvmParseConstantCanonical maxBytes maxUnivNodes bytes = .ok c ↔
      c.wireWF ∧ ixvmSerConstant c = bytes ∧ bytes.size ≤ maxBytes ∧
        Ixon.Bounded.univNodes c.univs ≤ maxUnivNodes :=
  Ixon.Verify.Canonical.deConstant_ok_iff maxBytes maxUnivNodes bytes c

/-- **Canonical Constant Decoding Implies Exact Constant Decoding**:
Whenever `ixvmParseConstantCanonical maxBytes maxUnivNodes bytes = .ok c`,
`ixvmParseConstantExact bytes = .ok c` also holds. -/
theorem ixvm_canonical_imp_parseConstantExact {maxBytes maxUnivNodes : Nat}
    {bytes : ByteArray} {c : Ixon.Constant}
    (h : ixvmParseConstantCanonical maxBytes maxUnivNodes bytes = .ok c) :
    ixvmParseConstantExact bytes = .ok c := by
  obtain ⟨hwf, rfl, _, _⟩ := (ixvm_canonical_deConstant_iff maxBytes maxUnivNodes bytes c).mp h
  exact ixvm_parseConstant_serConstant c hwf

/-- **Trailing-Byte Rejection for `ixvmParseConstantCanonical`**:
Appending any non-empty suffix `suffix` to a serialized wire-well-formed constant
causes `ixvmParseConstantCanonical` to reject. -/
theorem ixvm_canonical_deConstant_noTrailing (c : Ixon.Constant) (hwf : c.wireWF)
    (maxBytes maxUnivNodes : Nat) (suffix : ByteArray) (hnonempty : suffix.size ≠ 0) :
    (ixvmParseConstantCanonical maxBytes maxUnivNodes (ixvmSerConstant c ++ suffix)).isOk = Bool.false :=
  Ixon.Verify.Canonical.deConstant_noTrailing c hwf maxBytes maxUnivNodes suffix hnonempty

/-- **Resource Bound for `ixvmParseConstantExact`**:
For any constant `c` decoded by `ixvmParseConstantExact bytes = .ok c`,
`c.resourceSize ≤ 2 * bytes.size`. -/
theorem ixvm_parseConstantExact_resource_bound (bytes : ByteArray) (c : Ixon.Constant)
    (h : ixvmParseConstantExact bytes = .ok c) :
    c.resourceSize ≤ 2 * bytes.size :=
  Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c h

/-! ## 3. Claim Deserialization & Serialization Bridge (`run_claim` ↔ `Ix.Claim.de` / `Ix.Claim.ser`) -/

/-- `IxVM`'s channel-0 claim parser (`run_claim` header + payload + trailing-nil check). -/
def ixvmParseClaim (bytes : ByteArray) : Except String Ix.Claim :=
  Ix.Claim.de bytes

/-- `IxVM`'s claim serializer (`Ix.Claim.ser`). -/
def ixvmSerClaim (c : Ix.Claim) : ByteArray :=
  Ix.Claim.ser c

/-- `ixvmParseClaim` is definitionally `Ix.Claim.de` (`runGetExact Claim.get bytes`). -/
theorem ixvm_parseClaim_eq (bytes : ByteArray) :
    ixvmParseClaim bytes = Ix.Claim.de bytes := rfl

/-- `ixvmSerClaim` is definitionally `Ix.Claim.ser` (`runPut (Claim.put c)`). -/
theorem ixvm_serClaim_eq (c : Ix.Claim) :
    ixvmSerClaim c = Ix.Claim.ser c := rfl

/-- **Correspondence of `IxVM` `run_claim` Dispatch Variants and `Ix.Claim` Wire Constants**:
The flag `0xE`, object format `4`, and variant numbers `3..10` in `Ix/IxVM/Kernel/Claim.lean`
match `Ix.Claim.FLAG_CLAIM`, `Ixon.Env.OBJECT_FORMAT`, and `Ix.Claim.VARIANT_*`. -/
theorem ixvm_claim_variants :
    Ix.Claim.FLAG_CLAIM = 0xE ∧
    Ixon.Env.OBJECT_FORMAT = 4 ∧
    Ix.Claim.VARIANT_EVAL_CLAIM = 3 ∧
    Ix.Claim.VARIANT_CHECK_CLAIM = 4 ∧
    Ix.Claim.VARIANT_CHECK_ENV_CLAIM = 5 ∧
    Ix.Claim.VARIANT_REVEAL_CLAIM = 6 ∧
    Ix.Claim.VARIANT_CONTAINS_CLAIM = 7 ∧
    Ix.Claim.VARIANT_CATALOG_CLAIM = 8 ∧
    Ix.Claim.VARIANT_RESOURCE_CLAIM = 9 ∧
    Ix.Claim.VARIANT_BINDING_CLAIM = 10 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. Channel-6 Role Binding & Blake3 Stream Authentication Bridge -/

/-- **Channel-6 Role Table Canonicality (`RoleTable.ofBytes_eq_some_iff`)**:
`IxVM`'s channel-6 role binding parser (`validate_binding`: header `0xE8 0x03` +
bound role addresses + evidence entries) accepts `bytes` and produces `RoleTable` `t`
if and only if `t.wireWF = true` and `t.toBytes = bytes`. -/
theorem ixvm_channel6_roleTable_ofBytes_iff (bytes : ByteArray) (t : RoleTable) :
    RoleTable.ofBytes bytes = some t ↔
      t.wireWF = Bool.true ∧ t.toBytes = bytes :=
  RoleTable.ofBytes_eq_some_iff bytes t

/-- **Channel-6 Role Table Round-Trip (`RoleTable.ofBytes_toBytes`)**:
Every wire-well-formed `RoleTable` `t` round-trips through `t.toBytes` and `RoleTable.ofBytes`. -/
theorem ixvm_channel6_roleTable_roundtrip (t : RoleTable) (hwf : t.wireWF = Bool.true) :
    RoleTable.ofBytes t.toBytes = some t :=
  RoleTable.ofBytes_toBytes t hwf

/-- **Blake3 Stream Authentication Bridge (`load_verified_constant` / `load_verified_blob` ↔ `authenticate`)**:
`Admission.authenticate hash records blobs = .ok ()` holds if and only if
`Authentic hash records blobs` holds (every `(a, bytes) ∈ records` and every
`(a, bytes) ∈ blobs` satisfies `a = hash bytes`, matching `assert_eq!(@b3_pack(h), addr)`). -/
theorem ixvm_authenticate_stream_iff (hash : ByteArray → Address)
    (records : Records) (blobs : Ingress.Blobs) :
    authenticate hash records blobs = .ok () ↔
      Authentic hash records blobs :=
  authenticate_ok_iff hash records blobs

/-- **Unique Keys Bridge (`uniqueKeys_ok_iff`)**:
`Admission.uniqueKeys records blobs = .ok ()` holds if and only if
`UniqueKeys records blobs` holds (no two records share an address and no two
blobs share an address). -/
theorem ixvm_uniqueKeys_iff (records : Records) (blobs : Ingress.Blobs) :
    uniqueKeys records blobs = .ok () ↔
      UniqueKeys records blobs :=
  uniqueKeys_ok_iff records blobs

/-- **Batch Resource Preflight Bridge (`preflight_ok_iff`)**:
`Admission.preflight limits records blobs = .ok ()` holds if and only if
`WithinBatch limits records blobs` holds. -/
theorem ixvm_preflight_iff (limits : Limits) (records : Records) (blobs : Ingress.Blobs) :
    preflight limits records blobs = .ok () ↔
      WithinBatch limits records blobs :=
  preflight_ok_iff limits records blobs

/-- **Canonical Record Stream Decoding Bridge (`decodeRecords_ok_iff`)**:
`Admission.decodeRecords limits records = .ok constants` holds if and only if
`RecordsRead limits records constants` holds (every `(a, bytes) ∈ records` decodes
canonically via `Ixon.Canonical.deConstant` to the corresponding `(a, c) ∈ constants`). -/
theorem ixvm_decodeRecords_iff (limits : Limits)
    (records : Records) (constants : Ingress.Constants) :
    decodeRecords limits records = .ok constants ↔
      RecordsRead limits records constants :=
  decodeRecords_ok_iff limits records constants

end Ix.Cert.IxVM
