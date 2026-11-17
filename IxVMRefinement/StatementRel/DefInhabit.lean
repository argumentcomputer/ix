import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.StatementRel.ReadsMono
import IxC.Kernel.Model.Fold
import IxC.Kernel.Semantics.DeclRun

/-! # An inhabitant of the table-validity shape with a definition

`tableShape_def`: the default table is valid, in the public sense of `TableShape`, on the
basis and quotient groups, with a store that holds their 24 committed records and one more
record, a definition at an address the table binds no role to, and an environment that
stores the pins and that definition.

The record is `def _ : Nat := Nat.zero`, written against the committed addresses of `Nat`
and `Nat.zero`. Its bytes and its address are checked by evaluation (the canonical encoding
and the BLAKE3 hash, through the kernel mirrors of `IxVM.Refinement.RoleVal`). Its reading
(`def_reads`) is by the reader's own expression conversion. The model of the environment is
the kernel's: its executable checks of the definition at the basis environment are
evaluated (`defRun`), and the kernel's step theorem gives the model.

What this exercises beyond `tableShape_store`: `ReadingOf.stored` through its `StoredAs`
disjunct, with a real reading; `ReadingOf.provenance` through `KeptIn`; a store with a
record that is not a committed prelude row. The `kept` and `preludeKept` clauses still hold
through the pin: no role of the six groups has a constant that is not a pin.
-/

universe u

namespace IxVM.Refinement.DefInhabit

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.TableInhabit
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.StoreInhabit
open IxVM.Refinement.Claim (mkLazy mkLazy_rawBytes)

/-! ## The record -/

/-- The committed address of `Nat`. -/
def natAddr : _root_.Address := (committedDefaultRoleTable.addressOf? .nat).getD ⟨⟨#[]⟩⟩

/-- The committed address of `Nat.zero`. -/
def zeroAddr : _root_.Address := (committedDefaultRoleTable.addressOf? .natZero).getD ⟨⟨#[]⟩⟩

/-- The definition payload: type `refs[0]`, value `refs[1]`, no level parameters. -/
def defDefn : Ixon.Definition :=
  { kind := .defn, safety := .safe, lvls := 0, typ := .ref 0 #[], value := .ref 1 #[] }

/-- **The record**: `def _ : Nat := Nat.zero`. -/
def defRecord : Ixon.Constant :=
  { info := .defn defDefn, sharing := #[], refs := #[natAddr, zeroAddr], univs := #[] }

/-- The record's canonical bytes. -/
def defBytes : List UInt8 :=
  [208, 1, 0, 32, 0, 32, 1, 0, 2] ++ natAddr.hash.data.toList ++ zeroAddr.hash.data.toList ++
    [0, 0]

/-- The BLAKE3 hash of the record's bytes. -/
def defAddrBytes : List UInt8 :=
  [152, 12, 1, 57, 249, 159, 232, 66, 238, 178, 208, 163, 128, 212, 71, 251, 245, 147, 236,
   169, 172, 28, 73, 166, 87, 231, 184, 143, 238, 90, 235, 21]

/-- **The record's address.** -/
def defAddr : _root_.Address := mkAddr defAddrBytes

/-- The bytes are the record's canonical encoding (decided, by the encoder's mirror). -/
theorem defBytes_ok : checkConstBytesFast defRecord defBytes = true := by decide +kernel

/-- The address is the BLAKE3 hash of the bytes (decided, by the hash's mirror). -/
theorem defHash_ok : checkHashChunks [defBytes] defAddrBytes = true := by decide +kernel

theorem defRecord_ser :
    Ixon.serConstant defRecord = ⟨defBytes.toArray⟩ ∧ defRecord.wireWF := by
  obtain ⟨-, wire, encoded⟩ :=
    Ixon.Verify.Canonical.deConstant_spec _ _ _ _ (deConstant_of_checkConstBytesFast defBytes_ok)
  exact ⟨encoded, wire⟩

/-- **The record is stored under the BLAKE3 hash of its canonical bytes.** -/
theorem defAddr_hash : Address.blake3Pure (Ixon.serConstant defRecord) = defAddr := by
  have h := admissionHash_of_checkHashChunks defHash_ok
  have hf : [defBytes].flatten = defBytes := by simp
  rw [hf] at h
  rw [defRecord_ser.1, ← Address.admissionHash_eq]
  exact h

theorem defRecord_exact : Ixon.deConstantExact (Ixon.serConstant defRecord) = .ok defRecord :=
  Ixon.Verify.deConstantExact_serConstant defRecord defRecord_ser.2

/-- The address is not an address of the basis store (decided). -/
theorem defAddr_fresh : hasKey defAddr = false := by decide +kernel

/-- The address is not the address of a committed prelude record (decided). -/
theorem defAddr_notCommitted :
    committedPreludeList.any (fun e => e.1 == defAddr) = false := by decide +kernel

/-- The address is not the zero address (decided). -/
theorem defAddr_ne_padding : (defAddr == Ix.HostAdmission.Merkle.padding) = false := by
  decide +kernel

/-- The default table binds no role to the address (decided). -/
theorem defKey : keyOf committedDefaultRoleTable defAddr = Key.id defAddr := by decide +kernel

theorem natKey : keyOf committedDefaultRoleTable natAddr = Key.role .nat := by decide +kernel

theorem zeroKey : keyOf committedDefaultRoleTable zeroAddr = Key.role .natZero := by
  decide +kernel

/-- The records the definition uses are records of the basis store (decided). -/
theorem def_refs_in :
    (usedRefIdxs defRecord).all (fun i => (defRecord.refs[i]?).all hasKey) = true := by
  decide +kernel

/-! ## The store -/

/-- The record, with its canonical bytes. -/
def defLazy : Ixon.LazyConstant := mkLazy (Ixon.serConstant defRecord) defRecord

/-- **The store**: the basis store and the definition record. -/
def defStore : Ixon.Env := { consts := basisStore.consts.insert defAddr defLazy }

theorem defStore_get?_self : defStore.consts.get? defAddr = some defLazy := by
  show (basisStore.consts.insert defAddr defLazy).get? defAddr = some defLazy
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_insert_self

theorem defStore_get?_ne {a : _root_.Address} (h : a ≠ defAddr) :
    defStore.consts.get? a = basisStore.consts.get? a := by
  have hne : ¬ ((defAddr == a) = true) := fun hc => h (beq_iff_eq.mp hc).symm
  show (basisStore.consts.insert defAddr defLazy).get? a = basisStore.consts.get? a
  simp only [Std.HashMap.get?_eq_getElem?]
  rw [Std.HashMap.getElem?_insert, ite_eq_right hne]

theorem defStore_record_self : recordOf defStore defAddr = some defRecord := by
  have h1 : recordOf defStore defAddr = (Ixon.deConstantExact defLazy.rawBytes).toOption :=
    (congrArg (fun (o : Option Ixon.LazyConstant) =>
      o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) defStore_get?_self).trans rfl
  have h2 : Ixon.deConstantExact defLazy.rawBytes = .ok defRecord :=
    (congrArg Ixon.deConstantExact (mkLazy_rawBytes _ _)).trans defRecord_exact
  exact h1.trans ((congrArg Except.toOption h2).trans rfl)

theorem defStore_record_ne {a : _root_.Address} (h : a ≠ defAddr) :
    recordOf defStore a = recordOf basisStore a :=
  congrArg (fun (o : Option Ixon.LazyConstant) =>
    o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) (defStore_get?_ne h)

theorem ne_defAddr_of_record {y : _root_.Address} {v : Ixon.Constant}
    (h : recordOf basisStore y = some v) : y ≠ defAddr := by
  intro e
  rw [e] at h
  have hk : hasKey defAddr = true :=
    List.any_eq_true.mpr ⟨(defAddr, v), store_record_inv h, beq_self_eq_true defAddr⟩
  rw [defAddr_fresh] at hk
  cases hk

theorem defStore_record_mono {y : _root_.Address} {v : Ixon.Constant}
    (h : recordOf basisStore y = some v) : recordOf defStore y = some v :=
  (defStore_record_ne (ne_defAddr_of_record h)).trans h

theorem defStore_isSome_mono {y : _root_.Address}
    (h : (recordOf basisStore y).isSome = true) : (recordOf defStore y).isSome = true := by
  cases hv : recordOf basisStore y with
  | none =>
    rw [hv] at h
    have h' : false = true := h
    cases h'
  | some v => exact (congrArg Option.isSome (defStore_record_mono hv)).trans rfl

/-! ## The reading -/

private theorem ecx_keyAt_of {cx : Ctx .anon} {src : Ixon.Constant} {univs : Array CLevel}
    {self : Nat → Option (ReadM (CName .anon))} {i : UInt64} {a : _root_.Address}
    {k : CName .anon} (hr : src.refs[i.toNat]? = some a) (hk : cx.keyAt a = .ok k) :
    (⟨cx, src, univs, self⟩ : ECx .anon).keyAt i = .ok k := by
  simp only [ECx.keyAt, hr]
  exact hk

/-- **The reader's conversion of a reference with no level arguments**: the constant at the
key of the referenced address. -/
theorem read_ref {cx : Ctx .anon} {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName .anon))} {i : UInt64} {a : _root_.Address}
    {k : CName .anon} (hr : src.refs[i.toNat]? = some a) (hk : cx.keyAt a = .ok k) :
    (MemberReader.mk' cx src param self).read (.ref i #[]) = .ok (.const k []) := by
  obtain ⟨hecx, -⟩ := L1.memberReader_mk'_eq cx src param self
  unfold MemberReader.read
  rw [hecx]
  simp only [convExpr]
  exact Ix.CompileCert.Loop.except_bind_ok.mpr ⟨k, ecx_keyAt_of hr hk, rfl⟩

/-- **The definition, as declared and as stored**: under its address key, of type `Nat`,
with value `Nat.zero`. -/
def defConst : ConstantInfo .anon :=
  .defnInfo ⟨Key.id defAddr, [], .const (Key.role .nat) []⟩ (.const (Key.role .natZero) [])
    (.regular 0)

/-- **The record declares the definition**: a reading by the reader's own conversion. -/
theorem def_reads : Reads committedDefaultRoleTable defStore defAddr defConst := by
  have hk0 : (readCtx committedDefaultRoleTable (fun x => defStore.blobs.get? x)).keyAt natAddr =
      .ok (Key.role .nat) := by
    rw [← natKey]
    exact readCtx_keyAt committedDefaultRoleTable_check _ natAddr
  have hk1 : (readCtx committedDefaultRoleTable (fun x => defStore.blobs.get? x)).keyAt zeroAddr =
      .ok (Key.role .natZero) := by
    rw [← zeroKey]
    exact readCtx_keyAt committedDefaultRoleTable_check _ zeroAddr
  have hty : (exprReader committedDefaultRoleTable (fun x => defStore.blobs.get? x) defRecord id
      (soloSelf committedDefaultRoleTable defAddr)).read defDefn.typ =
        .ok (.const (Key.role .nat) []) :=
    read_ref (i := 0) (a := natAddr) rfl hk0
  have hval : (exprReader committedDefaultRoleTable (fun x => defStore.blobs.get? x) defRecord id
      (soloSelf committedDefaultRoleTable defAddr)).read defDefn.value =
        .ok (.const (Key.role .natZero) []) :=
    read_ref (i := 1) (a := zeroAddr) rfl hk1
  have hshape : DefnShape defDefn.kind
      ⟨Key.id defAddr, List.range defDefn.lvls.toNat, .const (Key.role .nat) []⟩
      (.const (Key.role .natZero) []) defConst :=
    Exists.intro (ReducibilityHint.regular 0) rfl
  have hdefn : DefnReads (exprReader committedDefaultRoleTable (fun x => defStore.blobs.get? x)
      defRecord id (soloSelf committedDefaultRoleTable defAddr))
      (keyOf committedDefaultRoleTable defAddr) defDefn defConst := by
    unfold DefnReads
    rw [defKey]
    exact ⟨_, _, hty, hval, hshape⟩
  have hlogic : InLogic defRecord := (rfl : Ix.Kernel.Reader.safetyDecline defDefn = none)
  exact Exists.intro defRecord (And.intro defStore_record_self (And.intro hlogic hdefn))

/-- The stored definition is the declared one, stored. -/
theorem def_storedAs : StoredAs defConst defConst :=
  And.intro (And.intro rfl (And.intro rfl Annotates.const)) (And.intro Annotates.const rfl)

/-! ## The environment and its model -/

/-- **The environment**: the definition, in front of the pinned basis constants. -/
def defEnv : Env .anon := ⟨defConst :: basisEnv.consts⟩

/-- The definition's header. -/
def defCv : ConstantVal .anon := ⟨Key.id defAddr, [], .const (Key.role .nat) []⟩

/-- The definition's value. -/
def defVal : Expr .anon := .const (Key.role .natZero) []

/-- A run that ends in a given value, decided. -/
def isOkEq.{a, b} {ε : Type a} {α : Type b} [DecidableEq α] : Except ε α → α → Bool
  | .ok t, x => decide (t = x)
  | .error _, _ => false

theorem ok_of_isOkEq.{a, b} {ε : Type a} {α : Type b} [DecidableEq α] {r : Except ε α}
    {x : α} (h : isOkEq r x = true) : r = .ok x := by
  cases r with
  | ok t =>
    have ht : t = x := of_decide_eq_true h
    rw [ht]
  | error _ =>
    have h' : false = true := h
    cases h'

/-- **The kernel's checks of the definition at the basis environment pass** (its executable
run at fuel 16, evaluated): the header is fresh and well formed, its type is a type, and the
value has that type. -/
theorem defRun :
    Ix.Kernel.Semantics.DeclDefnRun .verified 16 basisEnv defCv defVal (.regular 0) defEnv := by
  unfold Ix.Kernel.Semantics.DeclDefnRun
  refine ⟨defCv.type, defVal, ?_, ?_, rfl, fun h => absurd h (by decide +kernel),
    fun h => absurd h (by decide +kernel)⟩
  · unfold Ix.Kernel.Semantics.ConstantValRun
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, ok_of_isOkEq (by decide +kernel),
      by decide +kernel, by decide +kernel,
      ⟨.sort (.succ .zero), .succ .zero, ok_of_isOkEq (by decide +kernel),
        ok_of_isOkEq (by decide +kernel)⟩⟩
  · unfold Ix.Kernel.Semantics.ValueFrontRun
    exact ⟨by decide +kernel, by decide +kernel, ok_of_isOkEq (by decide +kernel),
      by decide +kernel, by decide +kernel,
      ⟨.const (Key.role .nat) [], ok_of_isOkEq (by decide +kernel),
        ok_of_isOkEq (by decide +kernel)⟩⟩

/-- The pinned basis environment carries the kernel's fold invariant. -/
theorem basisEnv_ok (W : Type u) [SetTheory W] :
    Ix.Kernel.Model.EnvModelOk W .verified basisEnv := by
  have step : ∀ {env env₂ : Env .anon} {kind : BasisKind},
      Ix.Kernel.Model.EnvModelOk W .verified env →
      Ix.Kernel.Semantics.DeclBasisRun env kind env₂ →
      Ix.Kernel.Model.EnvModelOk W .verified env₂ := by
    intro _ _ kind h hrun
    obtain ⟨⟨m⟩, hE⟩ := h
    exact Ix.Kernel.Model.declStep_preserves (F := 0) (d := .basisDecl kind) rfl m hE hrun
  exact step (step (step (step (step (step (envModelOk_empty W) basisRun_eq) basisRun_nat)
    basisRun_punit) basisRun_empty) basisRun_false) basisRun_quot

/-- **The environment with the definition carries the kernel's fold invariant.** -/
theorem defEnv_ok (W : Type u) [SetTheory W] : Ix.Kernel.Model.EnvModelOk W .verified defEnv := by
  obtain ⟨⟨m⟩, hE⟩ := basisEnv_ok W
  exact Ix.Kernel.Model.declStep_preserves (F := 16)
    (d := .defnDecl defCv defVal (.regular 0)) rfl m hE defRun

/-- **The environment with the definition has a model in every set theory.** -/
theorem defEnv_model (W : Type u) [SetTheory W] : Nonempty (Ix.Kernel.Model W defEnv) :=
  model_of_envModelOk (defEnv_ok W)

theorem defEnv_claimed : claimedEnv defEnv = defEnv := rfl

theorem defEnv_nodup : (defEnv.consts.map (·.name)).Nodup := by
  show ((defConst :: basisEnv.consts).map (·.name)).Nodup
  rw [List.map_cons, List.nodup_cons]
  refine ⟨fun hmem => ?_, basisEnv_nodup⟩
  have hn : basisEnv.consts.map (·.name) = basisRoleOrder.map Key.role := rfl
  rw [hn] at hmem
  obtain ⟨r, -, hr⟩ := List.mem_map.mp hmem
  have hr' : (Key.role r : Key .anon) = Key.id defAddr := hr
  cases hr'

theorem defEnv_find_def : defEnv.find? (Key.id defAddr) = some defConst :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := defEnv.consts) defEnv_nodup defConst
    List.mem_cons_self

theorem defEnv_find_basis {k : Key .anon} {ci : ConstantInfo .anon}
    (h : basisEnv.find? k = some ci) : defEnv.find? k = some ci := by
  have hmem : ci ∈ basisEnv.consts := List.mem_of_find?_eq_some h
  have hname : (ci.name == k) = true :=
    List.find?_some (p := fun x : ConstantInfo .anon => x.name == k) h
  have hk : ci.name = k := beq_iff_eq.mp hname
  have hf := Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := defEnv.consts) defEnv_nodup ci
    (List.mem_cons_of_mem _ hmem)
  rw [hk] at hf
  exact hf

/-! ## The clauses -/

theorem def_hashed : EnvSelfHashed defStore := by
  unfold EnvSelfHashed
  constructor
  · intro a lc h
    by_cases ha : a = defAddr
    · rw [ha] at h ⊢
      rw [defStore_get?_self] at h
      have e : defLazy = lc := Option.some.inj h
      rw [← e]
      show Address.blake3Pure (mkLazy (Ixon.serConstant defRecord) defRecord).rawBytes = defAddr
      rw [mkLazy_rawBytes]
      exact defAddr_hash
    · rw [defStore_get?_ne ha] at h
      exact store_hashed.1 a lc h
  · intro a _ h
    have hn : defStore.blobs.get? a = none := emptyMap_get? a
    rw [hn] at h
    cases h

theorem def_committed : AgreesCommitted defStore := by
  unfold AgreesCommitted
  intro p hp lc h
  by_cases hp1 : p.1 = defAddr
  · have hp' := hp
    rw [committedRows_eq] at hp'
    obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp'
    have he1 : e.1 = defAddr := (congrArg Prod.fst hpe).trans hp1
    have hk : committedPreludeList.any (fun e => e.1 == defAddr) = true :=
      List.any_eq_true.mpr ⟨e, he, beq_iff_eq.mpr he1⟩
    rw [defAddr_notCommitted] at hk
    cases hk
  · rw [defStore_get?_ne hp1] at h
    exact store_committed p hp lc h

theorem def_zeroFree :
    defStore.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      defStore.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
  have hne : Ix.HostAdmission.Merkle.padding ≠ defAddr := fun e => by
    have hb : (defAddr == Ix.HostAdmission.Merkle.padding) = true := beq_iff_eq.mpr e.symm
    rw [defAddr_ne_padding] at hb
    cases hb
  constructor
  · rw [defStore_get?_ne hne]
    exact store_zeroFree.1
  · exact emptyMap_get? Ix.HostAdmission.Merkle.padding

theorem def_usedClosed : UsedClosed defStore := by
  unfold UsedClosed
  constructor
  · intro a c hc
    by_cases ha : a = defAddr
    · rw [ha] at hc ⊢
      rw [defStore_record_self] at hc
      have e : defRecord = c := Option.some.inj hc
      rw [← e]
      constructor
      · exact (congrArg Option.isSome defStore_record_self).trans rfl
      · intro i hi x hx
        have h2 : (defRecord.refs[i]?).all hasKey = true := List.all_eq_true.mp def_refs_in i hi
        rw [hx] at h2
        exact defStore_isSome_mono (isSome_of_hasKey h2)
    · rw [defStore_record_ne ha] at hc
      obtain ⟨h1, h2⟩ := store_usedClosed.1 a c hc
      exact ⟨defStore_isSome_mono h1, fun i hi x hx => defStore_isSome_mono (h2 i hi x hx)⟩
  · intro B c ms hc hinfo i m hmi
    by_cases hB : B = defAddr
    · rw [hB, defStore_record_self] at hc
      have e : defRecord = c := Option.some.inj hc
      rw [← e] at hinfo
      have h' : Ixon.ConstantInfo.defn defDefn = Ixon.ConstantInfo.muts ms := hinfo
      cases h'
    · rw [defStore_record_ne hB] at hc
      obtain ⟨hm, hctor⟩ := store_usedClosed.2 B c ms hc hinfo i m hmi
      exact ⟨defStore_record_mono hm,
        fun ind hind j hj => defStore_record_mono (hctor ind hind j hj)⟩

/-- **The environment stores the definition as its record declares it** (`KeptIn`). -/
theorem def_keptIn :
    KeptIn committedDefaultRoleTable (recordOf defStore) (fun x => defStore.blobs.get? x) defAddr
      defConst := by
  unfold KeptIn
  refine ⟨fun _ _ hc hinfo => ?_, defConst, def_reads, def_storedAs⟩
  rw [defStore_record_self] at hc
  have e := Option.some.inj hc
  rw [← e] at hinfo
  have h' : Ixon.ConstantInfo.defn defDefn = Ixon.ConstantInfo.axio _ := hinfo
  cases h'

theorem def_stored : ∀ a, (∃ ci₀, Reads committedDefaultRoleTable defStore a ci₀) →
    ∃ ci, defEnv.find? (keyOf committedDefaultRoleTable a) = some ci ∧
      (PinnedBasis ci ∨
        ∃ ci₀, Reads committedDefaultRoleTable defStore a ci₀ ∧ StoredAs ci ci₀) := by
  intro a hr
  by_cases ha : a = defAddr
  · rw [ha, defKey]
    exact ⟨defConst, defEnv_find_def, Or.inr ⟨defConst, def_reads, def_storedAs⟩⟩
  · obtain ⟨_, c, hc, hread⟩ := hr
    rw [defStore_record_ne ha] at hc
    have hmem := store_record_inv hc
    have hF : (isMutsInfo c.info || isBasisKey (keyOf committedDefaultRoleTable a)) = true :=
      List.all_eq_true.mp keys_pinned (a, c) hmem
    have key : ∃ r ∈ basisRoleOrder, keyOf committedDefaultRoleTable a = .role r := by
      generalize c.info = info at hread hF
      cases info <;> first
        | exact False.elim hread
        | exact isBasisKey_role (k := keyOf committedDefaultRoleTable a) hF
    obtain ⟨r, hrole, hkey⟩ := key
    obtain ⟨ci, hfind, hpin⟩ := basisEnv_find hrole
    rw [hkey]
    exact ⟨ci, defEnv_find_basis hfind, Or.inl hpin⟩

/-! ## The inhabitant -/

/-- **The default table is valid, in the public sense, on the basis and quotient groups,
with a definition in the store and in the environment.** The definition is stored as its
record declares it, by a real reading. -/
theorem tableShape_def :
    TableShape.{u} committedDefaultRoleTable (fun g => g < 6) defStore defEnv := {
  needsClosed := (tableShape_store.{u}).needsClosed
  bound := (tableShape_store.{u}).bound
  prelude := preludePinned_default
  literals := committedDefaultRoleTable_literalSupportBound
  hashed := def_hashed
  usedClosed := def_usedClosed
  committed := def_committed
  zeroFree := def_zeroFree
  kept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := basisEnv_find (groupRole_basis hg hr)
    exact ⟨ci, defEnv_find_basis hfind, Or.inl hpin⟩
  reading := {
    nodup := defEnv_nodup
    provenance := fun ci hci => by
      rw [defEnv_claimed] at hci
      have hci' : ci ∈ defConst :: basisEnv.consts := hci
      rcases List.mem_cons.mp hci' with h | h
      · rw [h]
        exact Or.inr (Or.inr ⟨defAddr, def_keptIn⟩)
      · exact Or.inr (Or.inl (basisEnv_pinned ci h))
    stored := def_stored }
  pins := fun kind ci h => List.mem_cons_of_mem _ (basisEnv_pins kind ci h)
  preludeKept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := basisEnv_find (groupRole_basis hg hr)
    exact ⟨ci, defEnv_find_basis hfind, Or.inl hpin⟩
  model := fun W _ => by
    rw [defEnv_claimed]
    exact defEnv_model W }

end IxVM.Refinement.DefInhabit
