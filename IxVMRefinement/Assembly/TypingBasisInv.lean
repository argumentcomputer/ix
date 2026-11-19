import IxVMRefinement.Assembly.TypingFacts
import IxVMRefinement.Decl.DeclWalkedConst
import IxVMRefinement.StatementRel.BasisRowStore

/-! # The invariant's environment fields at the environment of the pins

`TableInhabit.basisEnv` is the environment the six basis installs leave: the nineteen pinned
constants of `Eq`, `Nat`, `PUnit`, `Empty`, `False` and the quotient package, keyed by their
roles under the committed default table. This module proves the fields of `Decl.PrefixInv`
there that are about the environment and the table alone, and the role and record companions
for every store of the basis records and every limit within the six basis groups:

* `basisEnv_decl`, `basisEnv_store`: the declaration layer's invariant and its store part, by
  the six basis steps (`basis_step_inv`, the step of `Decl.basisDecl_step_full` at the named
  environment);
* `basisEnv_unresolved`, `committedTable_wf`;
* `basisEnv_companions`: `Decl.CoreCompanions` for every store `E` of the basis records and
  every limit within the groups below 6. The role clauses are closed facts about the pins (or
  vacuous: no role of a later group is in force); the recursor clauses are closed facts about
  the seven stored recursors, decided by evaluation (`recRulesB`, `recPlainB`, `ruleHeadB`),
  and, for the major premise's record and the constructor keys of the rules, facts about the
  committed rows;
* `basisEnv_etaStable`: η typing of `PUnit`, the one η-capable family stored, in every
  extension (`Infer` is syntax directed at a constant).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (Role Key ConstantInfo ConstantVal BasisKind)
open Ix.Kernel.Semantics (DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ)
open IxVM.Refinement.TableInhabit (basisEnv)

/-- The committed default table. -/
abbrev ctab : Ix.Kernel.RoleTable := RoleVal.committedDefaultRoleTable

/-! ## The six basis steps at named environments -/

/-- **One basis block keeps the declaration and store invariants**, installed in front of the
environment at fresh keys (the step of `Decl.basisDecl_step_full`, at the environment it
names). -/
theorem basis_step_inv {env : Ix.Kernel.Env .anon} (kind : BasisKind)
    (heq : kind = .quotK → env.find? Ix.Kernel.eqName = some (Ix.Kernel.eqA (md := .anon)))
    (hfresh : ∀ ci ∈ (BasisKind.declsA kind : List (ConstantInfo .anon)),
      env.find? ci.name = none) :
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FullDeclInv V env →
      Decl.FullDeclInv V ⟨(BasisKind.declsA kind).reverse ++ env.consts⟩) ∧
    (Decl.FoldStoreInv env →
      Decl.FoldStoreInv ⟨(BasisKind.declsA kind).reverse ++ env.consts⟩) := by
  obtain ⟨hrun, hinst⟩ := Decl.basis_step_of_fresh (d := .basisDecl kind) kind rfl heq hfresh
  have hbase : ∀ ci ∈ (BasisKind.declsA kind (md := .anon)).reverse,
      Decl.isBaseKey ci.name = true := by
    intro ci hci
    exact List.all_eq_true.mp (Decl.basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  have hclean : Decl.CleanInstallStep env (.basisDecl kind)
      ⟨(BasisKind.declsA kind).reverse ++ env.consts⟩ :=
    Decl.CleanInstallStep.of_baseList hinst hbase
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.basisDecl kind)
      ⟨(BasisKind.declsA kind).reverse ++ env.consts⟩ := hrun
  exact ⟨fun V _ hInv => Decl.FullDeclInv.step_of_foldInv_clean hclean
      (Decl.foldInv_step_declRunJ (d := .basisDecl kind) (fun _ _ heq => nomatch heq) hdecl) V
      hInv,
    fun hS => Decl.foldStoreInv_step_declRunJ (d := .basisDecl kind) hS (fun _ _ heq => nomatch heq)
      hdecl⟩

/-- A key that is no role key of the roles keying an environment is not stored. -/
theorem find_none_of_roles {env : Ix.Kernel.Env .anon} {rs : List Role}
    (hn : env.consts.map (·.name) = rs.map Key.role) {k : Key .anon}
    (hk : ∀ r ∈ rs, k ≠ Key.role r) : env.find? k = none := by
  unfold Ix.Kernel.Env.find?
  rw [List.find?_eq_none]
  intro x hx hbeq
  have hxk : x.name = k := eq_of_beq hbeq
  have hmem : x.name ∈ env.consts.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hn, hxk] at hmem
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hmem
  exact hk r hr he.symm

/-- The constants of a block are fresh in an environment keyed by other roles. -/
theorem fresh_of_roles {env : Ix.Kernel.Env .anon} {rs : List Role}
    (hn : env.consts.map (·.name) = rs.map Key.role) {cs : List (ConstantInfo .anon)}
    (hcs : ∀ ci ∈ cs, ∃ r, ci.name = Key.role r ∧ r ∉ rs) :
    ∀ ci ∈ cs, env.find? ci.name = none := by
  intro ci hci
  obtain ⟨r, hr, hnr⟩ := hcs ci hci
  rw [hr]
  refine find_none_of_roles hn fun r' hr' he => hnr ?_
  rw [Key.role.inj he]
  exact hr'

private theorem fresh_eq :
    ∀ ci ∈ (BasisKind.declsA .eqK : List (ConstantInfo .anon)),
      (Ix.Kernel.Env.empty : Ix.Kernel.Env .anon).find? ci.name = none :=
  fun _ _ => rfl

private theorem fresh_nat :
    ∀ ci ∈ (BasisKind.declsA .natK : List (ConstantInfo .anon)),
      TableInhabit.basisEnv1.find? ci.name = none := by
  refine fresh_of_roles (rs := TableInhabit.roles1) rfl ?_
  intro ci hci
  simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨.nat, rfl, by decide⟩
  · exact ⟨.natZero, rfl, by decide⟩
  · exact ⟨.natSucc, rfl, by decide⟩
  · exact ⟨.natRec, rfl, by decide⟩

private theorem fresh_punit :
    ∀ ci ∈ (BasisKind.declsA .punitK : List (ConstantInfo .anon)),
      TableInhabit.basisEnv2.find? ci.name = none := by
  refine fresh_of_roles (rs := TableInhabit.roles2) rfl ?_
  intro ci hci
  simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨.punit, rfl, by decide⟩
  · exact ⟨.punitUnit, rfl, by decide⟩
  · exact ⟨.punitRec, rfl, by decide⟩

private theorem fresh_empty :
    ∀ ci ∈ (BasisKind.declsA .emptyK : List (ConstantInfo .anon)),
      TableInhabit.basisEnv3.find? ci.name = none := by
  refine fresh_of_roles (rs := TableInhabit.roles3) rfl ?_
  intro ci hci
  simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl
  · exact ⟨.empty, rfl, by decide⟩
  · exact ⟨.emptyRec, rfl, by decide⟩

private theorem fresh_false :
    ∀ ci ∈ (BasisKind.declsA .falseK : List (ConstantInfo .anon)),
      TableInhabit.basisEnv4.find? ci.name = none := by
  refine fresh_of_roles (rs := TableInhabit.roles4) rfl ?_
  intro ci hci
  simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl
  · exact ⟨.false, rfl, by decide⟩
  · exact ⟨.falseRec, rfl, by decide⟩

private theorem fresh_quot :
    ∀ ci ∈ (BasisKind.declsA .quotK : List (ConstantInfo .anon)),
      TableInhabit.basisEnv5.find? ci.name = none := by
  refine fresh_of_roles (rs := TableInhabit.roles5) rfl ?_
  intro ci hci
  simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl
  · exact ⟨.quot, rfl, by decide⟩
  · exact ⟨.quotMk, rfl, by decide⟩
  · exact ⟨.quotLift, rfl, by decide⟩
  · exact ⟨.quotInd, rfl, by decide⟩
  · exact ⟨.quotSound, rfl, by decide⟩

/-- **The declaration layer's invariant holds at the environment of the pins**, in every set
theory: the six basis steps from the empty environment. -/
theorem basisEnv_decl : ∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FullDeclInv V basisEnv := by
  intro V _
  have h1 : Decl.FullDeclInv V TableInhabit.basisEnv1 :=
    (basis_step_inv .eqK (fun h => nomatch h) fresh_eq).1 V (Decl.FullDeclInv.empty V)
  have h2 : Decl.FullDeclInv V TableInhabit.basisEnv2 :=
    (basis_step_inv .natK (fun h => nomatch h) fresh_nat).1 V h1
  have h3 : Decl.FullDeclInv V TableInhabit.basisEnv3 :=
    (basis_step_inv .punitK (fun h => nomatch h) fresh_punit).1 V h2
  have h4 : Decl.FullDeclInv V TableInhabit.basisEnv4 :=
    (basis_step_inv .emptyK (fun h => nomatch h) fresh_empty).1 V h3
  have h5 : Decl.FullDeclInv V TableInhabit.basisEnv5 :=
    (basis_step_inv .falseK (fun h => nomatch h) fresh_false).1 V h4
  exact (basis_step_inv .quotK (fun _ => TableInhabit.basisEnv5_eq) fresh_quot).1 V h5

/-- **The store part of the declaration layer's invariant holds at the environment of the
pins.** -/
theorem basisEnv_store : Decl.FoldStoreInv basisEnv := by
  have h1 : Decl.FoldStoreInv TableInhabit.basisEnv1 :=
    (basis_step_inv.{0} .eqK (fun h => nomatch h) fresh_eq).2 Decl.foldStoreInv_empty
  have h2 : Decl.FoldStoreInv TableInhabit.basisEnv2 :=
    (basis_step_inv.{0} .natK (fun h => nomatch h) fresh_nat).2 h1
  have h3 : Decl.FoldStoreInv TableInhabit.basisEnv3 :=
    (basis_step_inv.{0} .punitK (fun h => nomatch h) fresh_punit).2 h2
  have h4 : Decl.FoldStoreInv TableInhabit.basisEnv4 :=
    (basis_step_inv.{0} .emptyK (fun h => nomatch h) fresh_empty).2 h3
  have h5 : Decl.FoldStoreInv TableInhabit.basisEnv5 :=
    (basis_step_inv.{0} .falseK (fun h => nomatch h) fresh_false).2 h4
  exact (basis_step_inv.{0} .quotK (fun _ => TableInhabit.basisEnv5_eq) fresh_quot).2 h5

/-! ## The table and the unresolved key -/

theorem committedTable_wf : ctab.wf = true := by
  unfold Ix.Kernel.RoleTable.wf
  rw [RoleVal.committedDefaultRoleTable_check]
  rfl

/-- **The unresolved key is not stored**: every stored name is a role key. -/
theorem basisEnv_unresolved : basisEnv.find? Core.unresolvedKey = none :=
  find_none_of_roles (rs := TableInhabit.basisRoleOrder) rfl fun _ _ h => by cases h

/-! ## Lookups in the environment of the pins -/

/-- A stored constant is one of the nineteen pins, under its own name. -/
theorem basisEnv_find_mem {k : Key .anon} {ci : ConstantInfo .anon}
    (h : basisEnv.find? k = some ci) : ci ∈ basisEnv.consts ∧ ci.name = k :=
  ⟨List.mem_of_find?_eq_some h, Core.WhnfAux.name_of_find h⟩

/-- A pin is found under its name. -/
theorem basisEnv_find_self {ci : ConstantInfo .anon} (h : ci ∈ basisEnv.consts) :
    basisEnv.find? ci.name = some ci :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup TableInhabit.basisEnv_nodup ci h

/-- A stored key is the key of a basis role. -/
theorem basisEnv_find_role {k : Key .anon} {ci : ConstantInfo .anon}
    (h : basisEnv.find? k = some ci) : ∃ r ∈ TableInhabit.basisRoleOrder, k = Key.role r := by
  obtain ⟨hmem, hname⟩ := basisEnv_find_mem h
  have hk : ci.name ∈ basisEnv.consts.map (·.name) := List.mem_map.mpr ⟨ci, hmem, rfl⟩
  have hn : basisEnv.consts.map (·.name) = TableInhabit.basisRoleOrder.map Key.role := rfl
  rw [hn, hname] at hk
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hk
  exact ⟨r, hr, he.symm⟩

/-! ## The limit within the six basis groups -/

/-- **A role in force at a limit within the six basis groups is of one of them.** -/
theorem inForce_lt6 {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hlim : LimWithin (fun g => g < 6) ctab lim) {r : Role}
    (h : (⟨E, env, ctab, lim⟩ : Core.Ctx).inForce r) : Ix.SpecDigest.groupOf r < 6 :=
  hlim r h.1 h.2

set_option maxRecDepth 8192 in
/-- No `Nat` operation the core accelerates is of a basis group (decided over the roles). -/
theorem natOp_not_basis (r : Role) :
    (Key.role r : Key .anon) ∈ Ix.Kernel.Rules.natBinOpNames →
      Ix.SpecDigest.groupOf r < 6 → False := by
  cases r <;> decide +kernel

theorem string_group : ¬ Ix.SpecDigest.groupOf .string < 6 := by decide +kernel

theorem natAdd_group : ¬ Ix.SpecDigest.groupOf .natAdd < 6 := by decide +kernel

/-! ## The stored η-capable family -/

/-- The only stored family with the η capability is `PUnit` (decided over the pins). -/
theorem basisEnv_eta_punit :
    basisEnv.consts.all (fun ci => match ci with
      | .indInfo _ caps => !caps.eta || ci == Ix.Kernel.punitA
      | _ => true) = true := by
  decide +kernel

/-- **η typing at the environment of the pins is stable**: the one η-capable family is
`PUnit`, whose constructor `PUnit.unit` has no parameter and no field; `Infer` at a constant
is the constant's stored type, so in every extension the type of `PUnit.unit.{u}` is
`PUnit.{u}`. -/
theorem basisEnv_etaStable : Decl.EtaStable basisEnv := by
  intro T kc cvT cvc caps nP nF hT heta hkc hC env' hext d us args ty hlen _hcl hinf
  obtain ⟨hmemT, -⟩ := basisEnv_find_mem hT
  have hall := List.all_eq_true.mp basisEnv_eta_punit _ hmemT
  have hpu : ConstantInfo.indInfo cvT caps = Ix.Kernel.punitA := by
    simpa [heta] using hall
  have hkcEq : kc = Key.role .punitUnit := by
    cases hpu
    have h2 : (some (Key.role .punitUnit) : Option (Key .anon)) = some kc := hkc
    exact (Option.some.inj h2).symm
  subst hkcEq
  have hU : basisEnv.find? (Key.role .punitUnit) = some Ix.Kernel.punitUnitA :=
    basisEnv_find_self
      (TableInhabit.basisEnv_pins .punitK _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [hU] at hC
  have hC' : Ix.Kernel.punitUnitA = ConstantInfo.ctorInfo cvc nP nF := Option.some.inj hC
  have hTkey : T = Key.role .punit := by
    have := (basisEnv_find_mem hT).2
    rw [hpu] at this
    exact this.symm
  subst hTkey
  cases hC'
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst hargs
  have hU' := hext.find hU
  have hinf' : Ix.Kernel.Rules.Infer env' .io d (.const (Key.role .punitUnit) us) ty := hinf
  have hl1 : (Ix.Kernel.punitUnitA (md := .anon)).toConstantVal.levelParams.length = 1 := rfl
  cases hinf' with
  | const hf _ hus =>
    rw [hU'] at hf
    cases hf
    rw [hl1] at hus
    rcases us with _ | ⟨u, _ | ⟨_, _⟩⟩
    · simp at hus
    · exact .refl
    · simp at hus

/-! ## The records at the basis roles -/

/-- Every basis role is bound to the address of a row of the basis store (decided). -/
theorem basisRoles_rows :
    TableInhabit.basisRoleOrder.all (fun r => match ctab.addressOf? r with
      | some a => StoreInhabit.hasKey a
      | none => false) = true := by
  decide +kernel

/-- **The address a basis role's key names is that of a row**, which every store of the basis
records holds. -/
theorem basis_role_record {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {r : Role} (hr : r ∈ TableInhabit.basisRoleOrder) {p : _root_.Address}
    (hk : Core.keyOf ctab p = Key.role r) :
    ∃ cm, (p, cm) ∈ StoreInhabit.basisRows ∧ Ix.Cert.recordAt E p = some cm := by
  have ha : ctab.addressOf? r = some p := Core.addressOf_of_keyOf committedTable_wf hk
  have h1 := List.all_eq_true.mp basisRoles_rows r hr
  rw [ha] at h1
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp (StoreInhabit.isSome_of_hasKey h1)
  exact ⟨cm, StoreInhabit.store_record_inv hcm, hE.2.1 p cm hcm⟩

/-- The row the search at a row's address finds is that row. -/
theorem blockOf_of_mem {p : _root_.Address} {c : Ixon.Constant}
    (h : (p, c) ∈ StoreInhabit.basisRows) :
    RowReader.blockOf StoreInhabit.basisRows p = some (p, c) := by
  cases hb : RowReader.blockOf StoreInhabit.basisRows p with
  | none =>
    exfalso
    unfold RowReader.blockOf at hb
    have := List.find?_eq_none.mp hb (p, c) h
    simp at this
  | some row =>
    have hmem := RowReader.blockOf_mem hb
    have hrow : row ∈ StoreInhabit.basisRows := List.mem_of_find?_eq_some hb
    have h1 : (row.1 == p) = true :=
      List.find?_some (p := fun e : RowReader.Row => e.1 == p) hb
    have he : row.1 = p := beq_iff_eq.mp h1
    have h2 : row.2 = c := BasisReads.basisRowStore.snd_eq hmem h
    rw [← he, ← h2]

/-! ## The stored recursors -/

/-- The head of a stored recursor's major premise is a basis role's key (decided). -/
theorem basisEnv_majorHeads :
    basisEnv.consts.all (fun ci => match ci with
      | .recInfo cv mI _ _ =>
        match (Core.piDomAt mI cv.type).map (·.getAppFn) with
        | some (Ix.Kernel.Expr.const k _) => StoreInhabit.isBasisKey k
        | _ => true
      | _ => true) = true := by
  decide +kernel

theorem basisEnv_majorHead {k : Key .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    {rls : List (Ix.Kernel.RecRule .anon)} {p : _root_.Address} {us : List Core.KLevel}
    (hf : basisEnv.find? k = some (.recInfo cv mI rP rls))
    (hdom : (Core.piDomAt mI cv.type).map (·.getAppFn) =
      some (.const (Core.keyOf ctab p) us)) :
    ∃ r ∈ TableInhabit.basisRoleOrder, Core.keyOf ctab p = Key.role r := by
  have h1 := List.all_eq_true.mp basisEnv_majorHeads _ (basisEnv_find_mem hf).1
  simp only [hdom] at h1
  exact StoreInhabit.isBasisKey_role h1

/-- The constructor keys of every stored recursor's rules are distinct (decided). -/
theorem basisEnv_ruleCtorsNodup :
    basisEnv.consts.all (fun ci => match ci with
      | .recInfo _ _ _ rls => decide (rls.map (·.ctor)).Nodup
      | _ => true) = true := by
  decide +kernel

/-- **The rules of a recursor name the constructors of its major premise's record**: the
`j`-th rule's constructor key is the key of the row found for the `j`-th constructor
projection record of the major's inductive, when the major's record is an inductive
projection row. -/
def rulesProjB (ci : ConstantInfo .anon) : Bool :=
  match ci with
  | .recInfo cv mI _ rls =>
    match (Core.piDomAt mI cv.type).map (·.getAppFn) with
    | some (Ix.Kernel.Expr.const (Key.role r) _) =>
      match ctab.addressOf? r with
      | some p =>
        match RowReader.blockOf StoreInhabit.basisRows p with
        | some row =>
          match row.2.info with
          | .iPrj ip =>
            match RowReader.blockOf StoreInhabit.basisRows ip.block with
            | some eb =>
              match eb.2.info with
              | .muts ms =>
                match ms[ip.idx.toNat]? with
                | some (.indc ind) =>
                  decide (rls.length ≤ ind.ctors.size) &&
                    (List.range rls.length).all fun j =>
                      match rls[j]?, RowReader.findProjOf StoreInhabit.basisRows
                          (constructorProjection ip.block ip.idx.toNat j) with
                      | some rl, some e' => rl.ctor == Core.keyOf ctab e'.1
                      | _, _ => false
                | _ => false
              | _ => false
            | none => false
          | _ => true
        | none => false
      | none => false
    | some _ => false
    | none => true
  | _ => true

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem basisEnv_rulesProj : basisEnv.consts.all rulesProjB = true := by
  decide +kernel

/-- **What the rules of a stored recursor say of the major premise's record**: its `j`-th
rule's constructor is the key of the `j`-th constructor of the major's inductive. -/
theorem basisEnv_rulesProj_spec {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {k : Key .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    {rls : List (Ix.Kernel.RecRule .anon)} (hf : basisEnv.find? k = some (.recInfo cv mI rP rls))
    {p : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj} {us : List Core.KLevel}
    (hdom : (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (Core.keyOf ctab p) us))
    (hrec : Ix.Cert.recordAt E p = some cm) (hcm : cm.info = .iPrj ip)
    {j : Nat} {rl : Ix.Kernel.RecRule .anon} (hj : rls[j]? = some rl) :
    rl.ctor = Core.keyOf ctab (Core.cprjAddr ip.block ip.idx.toNat j) := by
  obtain ⟨r, hr, hk⟩ := basisEnv_majorHead hf hdom
  obtain ⟨cm', hmem', hrec'⟩ := basis_role_record hE hr hk
  have hcm' : cm = cm' := Option.some.inj (hrec.symm.trans hrec')
  subst hcm'
  have ha : ctab.addressOf? r = some p := Core.addressOf_of_keyOf committedTable_wf hk
  have hb := blockOf_of_mem hmem'
  have h2 := List.all_eq_true.mp basisEnv_rulesProj _ (basisEnv_find_mem hf).1
  rw [hk] at hdom
  simp only [rulesProjB, hdom, ha, hb, hcm] at h2
  split at h2
  next eb hbk =>
    split at h2
    next ms hms =>
      split at h2
      next ind hm =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h2
        obtain ⟨hlen, hall⟩ := h2
        have hjl : j < rls.length := by
          rcases Nat.lt_or_ge j rls.length with hl | hge
          · exact hl
          · rw [List.getElem?_eq_none hge] at hj
            cases hj
        have hjc : j < ind.ctors.size := Nat.lt_of_lt_of_le hjl hlen
        have hj2 := hall j (List.mem_range.mpr hjl)
        rw [hj] at hj2
        have hexp : constructorProjection ip.block ip.idx.toNat j ∈
            RowReader.expectedProjsOf BasisReads.basisRowStore.rows :=
          RowReader.mem_expected (RowReader.blockOf_mem hbk) hms hm _
            (RowReader.ctor_in_projs hjc)
        cases hfp : RowReader.findProjOf StoreInhabit.basisRows
            (constructorProjection ip.block ip.idx.toNat j) with
        | none => simp [hfp] at hj2
        | some e' =>
          simp only [hfp, beq_iff_eq] at hj2
          obtain ⟨-, -, h3⟩ := RowReader.found_spec BasisReads.basisRowStore hexp hfp
          exact hj2.trans (congrArg (Core.keyOf ctab) h3)
      next => simp at h2
    next => simp at h2
  next => simp at h2

/-- Every rule of a stored recursor that fires plainly matches the major premise's domain
(the shape `recPlain` asks), decided. -/
def recPlainB (ci : ConstantInfo .anon) : Bool :=
  match ci with
  | .recInfo cv mI rP rls =>
    rls.all fun rl =>
      !(rl.fire == .plain) ||
      match basisEnv.find? rl.ctor with
      | some (.ctorInfo cvj nP _) =>
        match Core.piDomAt mI cv.type with
        | some D =>
          (match D.getAppFn with
           | .const _ ls => ls == cvj.levelParams.map .param
           | _ => false) &&
          D.getAppArgs.take nP == (List.range nP).map (fun i => .bvar (mI - 1 - i)) &&
          D.getAppArgs.drop nP == (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
        | none => false
      | _ => true
  | _ => true

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem basisEnv_recPlain : basisEnv.consts.all recPlainB = true := by
  decide +kernel

/-- The constructor of every rule of a stored recursor builds the major premise's family
(the head `ruleCtorHead` asks), decided. -/
def ruleHeadB (ci : ConstantInfo .anon) : Bool :=
  match ci with
  | .recInfo cv mI _ rls =>
    rls.all fun rl =>
      match basisEnv.find? rl.ctor with
      | some (.ctorInfo cvj _ _) =>
        match (Core.piDomAt mI cv.type).map (·.getAppFn) with
        | some (Ix.Kernel.Expr.const T _) =>
          match (Ix.Kernel.Expr.piResult cvj.type).getAppFn with
          | .const T' _ => T' == T
          | _ => false
        | _ => true
      | _ => true
  | _ => true

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem basisEnv_ruleHead : basisEnv.consts.all ruleHeadB = true := by
  decide +kernel

/-! ## The companions -/

theorem basisEnv_natLit : Ix.Kernel.natLitSupported basisEnv = true := by decide +kernel

/-- **The role and record companions at the environment of the pins**, for every store of
the basis records and every limit within the six basis groups. -/
theorem basisEnv_companions {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {lim : Option Nat} (hlim : LimWithin (fun g => g < 6) ctab lim) :
    Decl.CoreCompanions ⟨E, basisEnv, ctab, lim⟩ where
  natLit := fun _ _ _ => basisEnv_natLit
  strLit := fun h => absurd (inForce_lt6 hlim h) string_group
  natOps := fun r h hm => (natOp_not_basis r hm (inForce_lt6 hlim h)).elim
  natAdd := fun h => absurd (inForce_lt6 hlim h) natAdd_group
  eqStored := fun _ =>
    ⟨_, basisEnv_find_self (TableInhabit.basisEnv_pins .eqK _ List.mem_cons_self)⟩
  quotBasis := fun _ ci hci => basisEnv_find_self (TableInhabit.basisEnv_pins .quotK ci hci)
  recMajorRecord := by
    intro k cv mI rP rls p us hf _ hdom
    obtain ⟨r, hr, hk⟩ := basisEnv_majorHead hf hdom
    obtain ⟨cm, -, hrec⟩ := basis_role_record hE hr hk
    exact ⟨cm, hrec⟩
  recRulesNodupAndProj := by
    intro k cv mI rP rls hf
    refine ⟨?_, fun p cm ip us hdom hrec hcm j rl hj =>
      basisEnv_rulesProj_spec hE hf hdom hrec hcm hj⟩
    have h1 := List.all_eq_true.mp basisEnv_ruleCtorsNodup _ (basisEnv_find_mem hf).1
    simpa using h1
  recPlain := by
    intro k cv mI rP rls rl cvj nP nF hf hrl hfire hc
    have h1 := List.all_eq_true.mp basisEnv_recPlain _ (basisEnv_find_mem hf).1
    simp only [recPlainB, List.all_eq_true] at h1
    have hc' : basisEnv.find? rl.ctor = some (.ctorInfo cvj nP nF) := hc
    have h2 := h1 rl hrl
    simp only [hfire, hc', beq_self_eq_true, Bool.not_true, Bool.false_or] at h2
    cases hD : Core.piDomAt mI cv.type with
    | none => simp [hD] at h2
    | some D =>
      simp only [hD, Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨hfn, htake⟩, hdrop⟩ := h2
      split at hfn
      next T ls hF =>
        simp only [beq_iff_eq] at hfn
        exact ⟨D, T, rfl, by rw [hF, hfn], htake, hdrop⟩
      next => simp at hfn
  ruleCtorHead := by
    intro k cv mI rP rls hf
    left
    intro rl cvj nP nF T us hrl hc hdom
    have h1 := List.all_eq_true.mp basisEnv_ruleHead _ (basisEnv_find_mem hf).1
    simp only [ruleHeadB, List.all_eq_true] at h1
    have hc' : basisEnv.find? rl.ctor = some (.ctorInfo cvj nP nF) := hc
    have h2 := h1 rl hrl
    simp only [hc', hdom] at h2
    split at h2
    next T' tus hP =>
      simp only [beq_iff_eq] at h2
      exact ⟨tus, by rw [hP, h2]⟩
    next => simp at h2

end IxVM.Refinement.Typing
