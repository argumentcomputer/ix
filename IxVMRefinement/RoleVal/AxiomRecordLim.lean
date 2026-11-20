import IxVMRefinement.RoleVal.AxiomRefsLim
import IxVMRefinement.Ingress.Decode
import IxVMRefinement.Ingress.Ingress

/-! # The record a standard axiom is bound to, from the role's validation

`KernelRoles::validate_role` loads the constant at the role's bound address with
`Ingress::get_ci` and hands it to `KernelRoles::validate_standard_axiom`, which matches it as
`KConstantInfo::Axiom(_, _, u)` and asserts `u = 0`.

* `Claim.get_ci_axiom_record`: an `Ingress::get_ci` run that returns an `Axiom` value loaded an
  axiom record (the run hashed its bytes, which decode exactly to it), and the value's safety
  field is the record's unsafe flag. Every other arm of the load returns a value of another
  constructor.
* `validate_role_axiom_record`, `ValidateRoleIn.axiom_record`: for a role specified as a
  standard axiom, the record at the role's bound address is a safe axiom record, decoded from
  bytes the validation hashed.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-! ### The conversions other than the axiom's return no `Axiom` value -/

private theorem convert_definition_ne_axiom {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_definition" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Axiom" vs := by
  intro hr
  match Obs.«Convert::convert_definition».obs ev with
  | .Definition (he242 := he) .. | .Opaque (he329 := he) .. | .Theorem (he373 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_quotient_ne_axiom {a₁ a₂ a₃ a₄ a₅ a₆ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_quotient" [a₁, a₂, a₃, a₄, a₅, a₆] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Axiom" vs := by
  intro hr
  match Obs.«Convert::convert_quotient».obs ev with
  | .run (he107 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_constructor_ne_axiom {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_constructor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h'
      cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Axiom" vs := by
  intro hr
  match Obs.«Convert::convert_constructor».obs ev with
  | .run (he134 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_recursor_ne_axiom {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_recursor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h'
      cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Axiom" vs := by
  intro hr
  match Obs.«Convert::convert_recursor».obs ev with
  | .run (he237 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

private theorem convert_inductive_ne_axiom {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_inductive" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h'
      cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Axiom" vs := by
  intro hr
  match Obs.«Convert::convert_inductive».obs ev with
  | .run (he128 := he) .. =>
    rw [hr] at he
    injection he with _ htag _
    exact absurd htag (by decide)

/-- **`Ingress::get_ci` returning an axiom value loaded an axiom record**: the run hashed fewer
than `2^32` bytes at the address, which decode exactly to a record whose info is an axiom, and
the safety field of the returned value is the axiom's unsafe flag. -/
theorem get_ci_axiom_record {a : Bytes.Address} {x_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls)
    {nl ty u : SourceValue F}
    (hld : loadValue h' r = .ok (.construct "KernelTypes::KConstantInfo" "Axiom" [nl, ty, u])) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant) (ax : Ixon.Axiom),
      rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧
      Ixon.deConstant rawBytes = .ok c ∧ Ixon.deConstantExact rawBytes = .ok c ∧
      c.info = .axio ax ∧ u = Ingress.repBoolField ax.isUnsafe := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (he219 := hr) (hm218 := hh) (ev225 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_axiom conv _)
  | .Defn_other (he340 := hr) (hm339 := hh) (ev346 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_axiom conv _)
  | .Quot (he532 := hr) (hm531 := hh) (ev538 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_quotient_ne_axiom conv _)
  | .Recr (he981 := hr) (hm980 := hh) (ev987 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self] at hld
    exact absurd (Except.ok.inj hld) (convert_recursor_ne_axiom conv _)
  | .DPrj (ev650 := ev650) .. =>
    match Obs.«Ingress::get_ci_dprj».obs ev650 with
    | .run (he230 := hr) (hm229 := hh) (ev236 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_definition_ne_axiom conv _)
  | .CPrj (ev800 := ev800) .. =>
    match Obs.«Ingress::get_ci_cprj».obs ev800 with
    | .run (he251 := hr) (hm250 := hh) (ev257 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_constructor_ne_axiom conv _)
  | .RPrj (ev896 := ev896) .. =>
    match Obs.«Ingress::get_ci_rprj».obs ev896 with
    | .run (he170 := hr) (hm169 := hh) (ev176 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_recursor_ne_axiom conv _)
  | .IPrj (ev720 := ev720) .. =>
    match Obs.«Ingress::get_ci_iprj».obs ev720 with
    | .run (he170 := hr) (hm169 := hh) (ev176 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self] at hld
      exact absurd (Except.ok.inj hld) (convert_inductive_ne_axiom conv _)
  | .Axio (x_axio := x_axio) (ev14 := ev14) (he441 := hr) (hm440 := hh) (ev447 := conv)
      (hc515 := hc) .. =>
    obtain ⟨-, bytes, c, hlen, hhs, haddr, hexact, hde, -, -, -, -, -, cRep⟩ :=
      Ingress.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨ax, hci, typPtr, hav, -⟩ := Ingress.repConstantInfo_axio_inv hinfo
    rw [hr, hh, loadValue_snoc_self] at hld
    match Obs.«Convert::convert_axiom».obs conv with
    | .run (hv15 := hx) (he107 := he) .. =>
      have hu₁ := hav.symm.trans hx
      injection hu₁ with _ _ hargs₁
      injection hargs₁ with hflag _
      have hv := Except.ok.inj hld
      rw [he] at hv
      injection hv with _ _ hargs₂
      injection hargs₂ with _ hargs₂
      injection hargs₂ with _ hargs₂
      injection hargs₂ with hu _
      refine ⟨⟨bytes.toArray⟩, c, ax, by simpa only [ByteArray.size, List.size_toArray] using hlen,
        Core.hashed_mono (by rw [hc]; intro x hx; simp [hx]) hhs, haddr, hde, hexact, hci, ?_⟩
      rw [← hu, hflag]

end IxVM.Refinement.Claim

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- **The record of a standard axiom, in the role's validation**: the record at the role's
bound address is decoded from bytes the validation hashed, and it is a safe axiom record. -/
theorem validate_role_axiom_record {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {ro : Ix.Kernel.Role} {x_rc x_tbl r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant) (ax : Ixon.Axiom),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ c.info = .axio ax ∧ ax.isUnsafe = false := by
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs288
      ev14 ev47 ld41 ev80 ev100 _ ev124 ev290 hc323 =>
    obtain ⟨-, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    obtain ⟨ab, hab, rfl⟩ := ha_m2
    match Obs.«KernelRoles::validate_standard_axiom».obs ev290 with
    | .run (hv15 := hci) (heq58 := hu) .. =>
      rw [hci] at ld41
      obtain ⟨rawBytes, c, ax, hsz, hh, hblk, hde, hdeE, hinfo, hu'⟩ :=
        Claim.get_ci_axiom_record hab ev47 ld41
      have hsafe : ax.isUnsafe = false := by
        cases hb : ax.isUnsafe with
        | false => rfl
        | true =>
          rw [hb, hu] at hu'
          have e : (Value.field (0 : F) : SourceValue F) = .field 1 := hu'
          exact absurd (Value.field.inj e) zero_ne_one
      have hsub : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => by rw [hc323]; simp [hm]
      exact ⟨_, rawBytes, c, ax, had, hsz, Claim.hashed_mono hsub hh, hblk, hde, hdeE, hinfo,
        hsafe⟩

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.axiom_record {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant) (ax : Ixon.Axiom),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ c.info = .axio ax ∧ ax.isUnsafe = false := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, ax, had, hsz, hh, hblk, hde, hdeE, hinfo, hsafe⟩ :=
    validate_role_axiom_record htbl ev hk
  exact ⟨a, rawBytes, c, ax, had, hsz, Claim.hashed_mono hsub hh, hblk, hde, hdeE, hinfo, hsafe⟩

/-- **The safety guard of a standard axiom's record, in the role's validation**: the record at
the role's bound address is decoded from bytes the validation hashed, and the validation
observed `KernelClaim::assert_safe_record_refs` on it under the role context at the group's
validation limit (`Claim.RecordRefsIn`). -/
theorem validate_role_axiom_guard {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (groupValLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      Claim.RecordRefsIn calls t bAddr (some (groupValLimit g)) a c := by
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs288
      ev14 ev47 _ ev80 ev100 _ ev124 ev290 hc323 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    have ext_h_m111 : Heap.Extends h m111 :=
      ext_ba.trans (ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends)))
    match Obs.«KernelRoles::validate_standard_axiom».obs ev290 with
    | .run (m60 := b60) (m128 := b128) (m141 := b141) (m207 := b207) (m192 := b192)
        (m304 := b304) (cs202 := cs_ld) (cs290 := cs_g) (ev72 := e72) (hm136 := hm)
        (ev109 := e109) (ev174 := e174) (ev153 := e153) (ev217 := e217) (ev204 := e204)
        (ev314 := e314) (ev292 := e292) (hc388 := hca) .. =>
      have ext_snoc : Heap.Extends b60 b128 := by
        rw [hm]
        exact Heap.Extends.snoc b60 _
      have ext_a : Heap.Extends m111 b141 :=
        e72.heap_extends.trans (ext_snoc.trans (e109.heap_extends.trans
          (e174.heap_extends.trans e153.heap_extends)))
      obtain ⟨ext_ba2, a', ha', had'⟩ :=
        role_bound_addr_uncond ((htbl.mono (ext_h_m111.trans ext_a)).toTableRep) e217
      have ha_eq : a' = a := by
        rw [had] at had'
        exact (Option.some.inj had').symm
      subst ha_eq
      obtain ⟨ext_ld, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        Claim.load_verified_constant_de ha' e204
      have ext_192 : Heap.Extends h b192 :=
        ext_h_m111.trans (ext_a.trans (ext_ba2.trans ext_ld))
      obtain ⟨ext_ba3, a'', ha'', had''⟩ :=
        role_bound_addr_uncond ((htbl.mono ext_192).toTableRep) e314
      have ha_eq' : a'' = a' := by
        rw [had] at had''
        exact (Option.some.inj had'').symm
      subst ha_eq'
      have hrc304 : Claim.RCLimRep t bAddr (some (groupValLimit g)) b304 x_rc :=
        hrc.mono (ext_192.trans ext_ba3)
      have hsub_g : ∀ cl ∈ cs_g, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      have hsub_ld : ∀ cl ∈ cs_ld, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      exact ⟨a'', rawBytes, c, had, hsz, Claim.hashed_mono hsub_ld hh_load, hblk, hde, hdeExact,
        _, _, _, _, _, _, _, hrc304, ha'', hrep.mono ext_ba3, e292, hsub_g⟩

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.axiom_guard {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      Claim.RecordRefsIn calls t bAddr (some (groupValLimit g)) a c := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, had, hsz, hh, hblk, hde, hdeE, hg⟩ :=
    validate_role_axiom_guard hrc htbl ev hk
  exact ⟨a, rawBytes, c, had, hsz, Claim.hashed_mono hsub hh, hblk, hde, hdeE, hg.mono hsub⟩

end IxVM.Refinement.RoleVal
