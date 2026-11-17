import IxVMRefinement.Assembly.L7
import IxVMRefinement.Decl.PrefixInv
import IxVMRefinement.StatementRel.ReadsMono
import Ix.IxVM.Consistency.TableValid

/-! # The claimed environment's model, from the provenance clause

The conclusion of the typing statement asks for a model of the claimed sub-environment: the
environment without the checker's auxiliary constants. A model of the whole environment
restricts to it when no claimed constant names an auxiliary key
(`IxVM.Consistency.claimedModel`). This module derives that condition from the provenance
clause of the conclusion itself: every claimed constant is a projection table, a pinned basis
constant, or stores what a record declares (`KeptIn`). No list of declarations or installs is
used.

* `readsIn_name`: a reading at the address `a` has the key of `a`. For a quotient record this
  is because the kernel's comparison with its pin keeps the name. So a constant that stores
  what the record at `a` declares is stored at the key of `a` (`keptIn_name`).
* `readsIn_nonAux`: a reading names no auxiliary key, in its own key, its type, its value or
  its rules: the reader keys every reference by a role or by an address.
* `basisDeclsA_nonAux` (the legacy assembly's, a decided fact): nor does a pinned constant.
* `claimedEnv_models_of_provenance`, `claimedEnv_models_of_prefixInv`: the model.

It also moves the provenance of a constant from the store it was read over to the store the
conclusion speaks of, the run's records with the witness's behind them (`keptIn_over_run`,
`keptIn_over_witness`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo)

/-! ## Keys of constant addresses -/

/-- The key of a constant address is a role or the address, never a derived key. -/
theorem keyOf_nonAux (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    Assembly.NonAuxKey (keyOf t a) := by
  intro b s h
  rcases keyOf_cases t a with ⟨hk, -⟩ | ⟨r, -, hk⟩ <;> rw [hk] at h <;> cases h

theorem soloSelf_nonAux (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    ∀ i m k, soloSelf t a i = some m → m = .ok k → Assembly.NonAuxKey k := by
  intro i m k hs hm
  cases i with
  | zero =>
    have h2 : (Except.ok (keyOf t a) : Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) = m :=
      Option.some.inj hs
    rw [hm] at h2
    rw [← Except.ok.inj h2]
    exact keyOf_nonAux t a
  | succ n =>
    have hs' : (none : Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) = some m := hs
    cases hs'

theorem blockSelf_nonAux (t : Ix.Kernel.RoleTable) (B : _root_.Address)
    (ms : Array Ixon.MutConst) :
    ∀ i m k, blockSelf t B ms i = some m → m = .ok k → Assembly.NonAuxKey k := by
  intro i m k hs hm
  have hs' : ((ms[i]?).map fun m₀ =>
      (Except.ok (keyOf t (memberAddr B i m₀)) :
        Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) = some m := hs
  obtain ⟨m₀, -, h1⟩ := Option.map_eq_some_iff.mp hs'
  rw [hm] at h1
  rw [← Except.ok.inj h1]
  exact keyOf_nonAux t _

theorem noSelf_nonAux :
    ∀ (i : Nat) (m : Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) (k : Ix.Kernel.Key .anon),
      (fun _ : Nat => (none : Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)))) i =
        some m → m = .ok k → Assembly.NonAuxKey k := by
  intro i m k hs
  have hs' : (none : Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) = some m := hs
  cases hs'

/-- An expression the reading context reads names no derived key. -/
theorem read_nonAux {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    (hself : ∀ i m k, self i = some m → m = .ok k → Assembly.NonAuxKey k) {e : Ixon.Expr}
    {v : Ix.Kernel.Expr .anon} (h : (exprReader t blob src param self).read e = .ok v) :
    v.RefsIn Assembly.NonAuxKey :=
  Assembly.memberReader_read_refsIn_nonAux (cx := readCtx t blob)
    (Ix.Cert.ReaderUnits.bindingsOf_keyed _ t) hself h

/-! ## A reading's key -/

theorem defnReads_name {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {d : Ixon.Definition} {ci₀ : ConstantInfo .anon} (h : DefnReads mr name d ci₀) :
    ci₀.name = name := by
  obtain ⟨ty, value, -, -, hshape⟩ := h
  generalize d.kind = kind at hshape
  cases kind with
  | defn =>
    obtain ⟨hint, e⟩ := hshape
    subst e
    rfl
  | thm =>
    have e : ci₀ = .thmInfo ⟨name, List.range d.lvls.toNat, ty⟩ value := hshape
    subst e
    rfl
  | opaq =>
    have e : ci₀ = .axiomInfo ⟨name, List.range d.lvls.toNat, ty⟩ := hshape
    subst e
    rfl

theorem recReads_name {t : Ix.Kernel.RoleTable} {store : Ix.Kernel.Reader.Store}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {name : Ix.Kernel.Key .anon} {rc : Ixon.Recursor} {ci₀ : ConstantInfo .anon}
    (h : RecReads t store blob src self name rc ci₀) : ci₀.name = name := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, -, -, -, -, -, -, -, -, -, e⟩ := h
  subst e
  rfl

/-- The pinned quotient constant of a kind has the name of the raw pin the kernel compares a
quotient record with (decided over the four kinds). -/
theorem quotPin_name (k : Ix.QuotKind) :
    ((Ix.Kernel.BasisKind.quotK.declsA : List (ConstantInfo .anon))[(quotSlot k).slot]?).map
        (·.name) =
      some ((Ix.Kernel.BasisKind.quotK.decls (md := .anon)).getD (quotSlot k).slot
        (.axiomInfo default)).toConstantVal.name := by
  cases k <;> first | rfl | decide

theorem quotReads_name {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {q : Ixon.Quotient} {ci₀ : ConstantInfo .anon} (h : QuotReads mr name q ci₀) :
    ci₀.name = name := by
  obtain ⟨ty, -, hpin, hget⟩ := h
  have hc : Ix.Kernel.ConstantVal.canon
        (⟨name, List.range q.lvls.toNat, ty⟩ : Ix.Kernel.ConstantVal .anon) =
      Ix.Kernel.ConstantVal.canon
        ((Ix.Kernel.BasisKind.quotK.decls (md := .anon)).getD (quotSlot q.kind).slot
          (.axiomInfo default)).toConstantVal :=
    of_decide_eq_true hpin
  have hn : name =
      ((Ix.Kernel.BasisKind.quotK.decls (md := .anon)).getD (quotSlot q.kind).slot
        (.axiomInfo default)).toConstantVal.name :=
    congrArg Ix.Kernel.ConstantVal.name hc
  have hp := quotPin_name q.kind
  rw [hget] at hp
  have hci : ci₀.name =
      ((Ix.Kernel.BasisKind.quotK.decls (md := .anon)).getD (quotSlot q.kind).slot
        (.axiomInfo default)).toConstantVal.name :=
    Option.some.inj hp
  exact hci.trans hn.symm

/-- **A reading at an address has the key of the address.** -/
theorem readsIn_name {t : Ix.Kernel.RoleTable} {store : Ix.Kernel.Reader.Store}
    {blob : _root_.Address → Option ByteArray} {a : _root_.Address} {ci₀ : ConstantInfo .anon}
    (h : ReadsIn t store blob a ci₀) : ci₀.name = keyOf t a := by
  obtain ⟨c, -, h⟩ := h
  generalize c.info = info at h
  cases info with
  | defn d =>
    obtain ⟨-, r⟩ := h
    exact defnReads_name r
  | axio ax =>
    obtain ⟨-, -, ty, -, e⟩ := h
    subst e
    rfl
  | quot q => exact quotReads_name h
  | recr rc =>
    obtain ⟨-, r⟩ := h
    exact recReads_name r
  | dPrj p =>
    obtain ⟨cb, ms, d, -, r⟩ := h
    exact defnReads_name r
  | iPrj p =>
    obtain ⟨cb, ms, ind, -, ty, caps, -, e⟩ := h
    subst e
    rfl
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, -, -, -, -, -, -, -, -, ty, -, e⟩ := h
    subst e
    rfl
  | rPrj p =>
    obtain ⟨cb, ms, rc, -, r⟩ := h
    exact recReads_name r
  | muts ms => exact False.elim h

/-- **A constant that stores what the record at `a` declares is stored at the key of `a`.** -/
theorem keptIn_name {t : Ix.Kernel.RoleTable} {store : Ix.Kernel.Reader.Store}
    {blob : _root_.Address → Option ByteArray} {a : _root_.Address} {ci : ConstantInfo .anon}
    (h : KeptIn t store blob a ci) : ci.name = keyOf t a := by
  obtain ⟨-, ci₀, hr, hst⟩ := h
  exact hst.name_eq.trans (readsIn_name hr)

/-! ## A reading names no derived key -/

section NonAux

variable {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
  {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
  {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
  {name : Ix.Kernel.Key .anon} {ci₀ : ConstantInfo .anon}

theorem defnReads_nonAux (hself : ∀ i m k, self i = some m → m = .ok k → Assembly.NonAuxKey k)
    (hname : Assembly.NonAuxKey name) {d : Ixon.Definition}
    (h : DefnReads (exprReader t blob src param self) name d ci₀) :
    Assembly.ConstantInfoNonAux ci₀ := by
  obtain ⟨ty, value, hty, hval, hshape⟩ := h
  have h1 := read_nonAux hself hty
  have h2 := read_nonAux hself hval
  generalize d.kind = kind at hshape
  cases kind with
  | defn =>
    obtain ⟨hint, e⟩ := hshape
    rw [e]
    exact ⟨hname, h1, h2⟩
  | thm =>
    have e : ci₀ = .thmInfo ⟨name, List.range d.lvls.toNat, ty⟩ value := hshape
    rw [e]
    exact ⟨hname, h1, h2⟩
  | opaq =>
    have e : ci₀ = .axiomInfo ⟨name, List.range d.lvls.toNat, ty⟩ := hshape
    rw [e]
    exact ⟨hname, h1, trivial⟩

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hm => nomatch hm
  | _, _, .cons hr htl, y, hm => by
    rcases List.mem_cons.mp hm with he | hmem
    · rw [he]
      exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hxy⟩ := forall₂_mem_right htl y hmem
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

theorem recReads_nonAux {store : Ix.Kernel.Reader.Store}
    (hself : ∀ i m k, self i = some m → m = .ok k → Assembly.NonAuxKey k)
    (hname : Assembly.NonAuxKey name) {rc : Ixon.Recursor}
    (h : RecReads t store blob src self name rc ci₀) : Assembly.ConstantInfoNonAux ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, -, -, -, -, -, -, hty, -, hrules,
    e⟩ := h
  rw [e]
  refine ⟨hname, read_nonAux hself hty, ?_⟩
  intro rl hrl
  obtain ⟨ru, -, hru⟩ := forall₂_mem_right hrules rl hrl
  obtain ⟨rhs, hr, erl⟩ := hru
  rw [erl]
  exact ⟨keyOf_nonAux t _, read_nonAux hself hr⟩

end NonAux

/-- **A reading names no derived key**: not in its own key, its type, its value or its
rules. -/
theorem readsIn_nonAux {t : Ix.Kernel.RoleTable} {store : Ix.Kernel.Reader.Store}
    {blob : _root_.Address → Option ByteArray} {a : _root_.Address} {ci₀ : ConstantInfo .anon}
    (h : ReadsIn t store blob a ci₀) : Assembly.ConstantInfoNonAux ci₀ := by
  obtain ⟨c, -, h⟩ := h
  generalize c.info = info at h
  cases info with
  | defn d =>
    obtain ⟨-, r⟩ := h
    exact defnReads_nonAux (soloSelf_nonAux t a) (keyOf_nonAux t a) r
  | axio ax =>
    obtain ⟨-, -, ty, hty, e⟩ := h
    rw [e]
    exact ⟨keyOf_nonAux t a, read_nonAux noSelf_nonAux hty, trivial⟩
  | quot q =>
    obtain ⟨ty, -, -, hget⟩ := h
    exact Assembly.basisDeclsA_nonAux .quotK ci₀ (List.mem_of_getElem? hget)
  | recr rc =>
    obtain ⟨-, r⟩ := h
    exact recReads_nonAux (soloSelf_nonAux t a) (keyOf_nonAux t a) r
  | dPrj p =>
    obtain ⟨cb, ms, d, -, r⟩ := h
    exact defnReads_nonAux (blockSelf_nonAux t p.block ms) (keyOf_nonAux t a) r
  | iPrj p =>
    obtain ⟨cb, ms, ind, -, ty, caps, hty, e⟩ := h
    rw [e]
    exact ⟨keyOf_nonAux t a, read_nonAux (blockSelf_nonAux t p.block ms) hty, trivial⟩
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, -, -, -, -, -, -, -, -, ty, hty, e⟩ := h
    rw [e]
    exact ⟨keyOf_nonAux t a, read_nonAux (blockSelf_nonAux t p.block ms) hty, trivial⟩
  | rPrj p =>
    obtain ⟨cb, ms, rc, -, r⟩ := h
    exact recReads_nonAux (blockSelf_nonAux t p.block ms) (keyOf_nonAux t a) r
  | muts ms => exact False.elim h

private theorem forall₂_mem_left' {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hm => nomatch hm
  | _, _, .cons hr htl, x, hm => by
    rcases List.mem_cons.mp hm with he | hmem
    · rw [he]
      exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hxy⟩ := forall₂_mem_left' htl x hmem
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-- **A constant that stores a declared constant naming no derived key names none.** -/
theorem storedAs_nonAux {ci ci₀ : ConstantInfo .anon} (hst : StoredAs ci ci₀)
    (hna : Assembly.ConstantInfoNonAux ci₀) : Assembly.ConstantInfoNonAux ci := by
  obtain ⟨⟨hname, -, hty⟩, hrest⟩ := hst
  obtain ⟨h1, h2, h3⟩ := hna
  have hn : Assembly.NonAuxKey ci.name := fun b s h => h1 b s (hname.symm.trans h)
  refine ⟨hn, Assembly.annotates_refsIn hty h2, ?_⟩
  cases ci with
  | defnInfo cv v hint =>
    cases ci₀ with
    | defnInfo cv₀ v₀ hint₀ => exact Assembly.annotates_refsIn hrest.1 h3
    | _ => exact hrest.elim
  | thmInfo cv v =>
    cases ci₀ with
    | thmInfo cv₀ v₀ => exact Assembly.annotates_refsIn hrest h3
    | _ => exact hrest.elim
  | recInfo cv mI rP rules =>
    cases ci₀ with
    | recInfo cv₀ mI₀ rP₀ rules₀ =>
      intro rl hrl
      obtain ⟨rl₀, hrl₀, hrs⟩ := forall₂_mem_left' hrest.2.2 rl hrl
      obtain ⟨hc, hr⟩ := h3 rl₀ hrl₀
      exact ⟨fun b s h => hc b s (hrs.1.symm.trans h), Assembly.annotates_refsIn hrs.2.2 hr⟩
    | _ => exact hrest.elim
  | axiomInfo cv => trivial
  | indInfo cv caps => trivial
  | ctorInfo cv nP nF => trivial
  | projInfo tbl => trivial

/-! ## The model -/

/-- **The claimed sub-environment has a model when no claimed constant names a derived
key**, other than the projection tables: from distinct names and the fold invariant's model
and projection-table facts. -/
theorem claimedEnv_models_of_nonAux {env : Ix.Kernel.Env .anon}
    (hnd : (env.consts.map (·.name)).Nodup)
    (hprov : ∀ c ∈ (claimedEnv env).consts,
      (∃ tbl, c = .projInfo tbl) ∨ Assembly.ConstantInfoNonAux c)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Ix.Kernel.Model.EnvModelOk V .verified env ∧ Decl.StrongEnvProps env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V (claimedEnv env)) := by
  intro V _
  obtain ⟨hok, htables, hprojCtor⟩ := hmodel V
  obtain ⟨M⟩ := model_of_envModelOk hok
  have hmono : ∀ {e : Ix.Kernel.Expr .anon},
      e.RefsIn Assembly.NonAuxKey → e.RefsIn (KeptKey env) :=
    fun hr => Assembly.refsIn_mono (fun _ hk => keptKey_of_not_aux hk) hr
  have htype : ∀ c ∈ (claimedEnv env).consts, c.toConstantVal.type.RefsIn (KeptKey env) := by
    intro c hc
    rcases hprov c hc with ⟨tbl, rfl⟩ | hna
    · trivial
    · exact hmono hna.2.1
  have hvalue : ∀ cv value hint,
      ConstantInfo.defnInfo cv value hint ∈ (claimedEnv env).consts →
      value.RefsIn (KeptKey env) := by
    intro cv value hint hc
    rcases hprov _ hc with ⟨_, heq⟩ | hna
    · cases heq
    · exact hmono hna.2.2
  have hrhs : ∀ cv mI rP rules,
      ConstantInfo.recInfo cv mI rP rules ∈ (claimedEnv env).consts →
      ∀ rl ∈ rules, rl.rhs.RefsIn (KeptKey env) := by
    intro cv mI rP rules hc rl hrl
    rcases hprov _ hc with ⟨_, heq⟩ | hna
    · cases heq
    · exact hmono (hna.2.2 rl hrl).2
  have hctor : ∀ T i entry, (claimedEnv env).findProj? T i = some entry →
      KeptKey env T → KeptKey env entry.ctor := by
    intro T i entry hfp hKT
    rw [claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, hT_eq, -, -, hctor_eq⟩ := Assembly.findProj?_some_inv hfp
    rw [hctor_eq]
    rcases hprojCtor (Ix.Kernel.projTableName T) tbl hfind_tbl with hna_ctor | hnk
    · exact keptKey_of_not_aux hna_ctor
    · rw [hT_eq] at hnk
      exact (hnk hKT).elim
  have hbody : ∀ T i entry, (claimedEnv env).findProj? T i = some entry →
      KeptKey env T → entry.body.RefsIn (KeptKey env) := by
    intro T i entry hfp hKT
    have hK_ctor := hctor T i entry hfp hKT
    rw [claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, -, hi_lt, rfl, hctor_eq⟩ := Assembly.findProj?_some_inv hfp
    rw [hctor_eq] at hK_ctor
    obtain ⟨cvC, hfind_ctor, hbodies, -⟩ := htables (Ix.Kernel.projTableName T) tbl hfind_tbl
    have hfind_claimed :
        (claimedEnv env).find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields) := by
      rwa [claimedEnv_find? hK_ctor]
    have hcty_refs : cvC.type.RefsIn (KeptKey env) :=
      htype (.ctorInfo cvC tbl.numParams tbl.numFields)
        (Ix.Kernel.Semantics.Env.find?_mem hfind_claimed)
    obtain ⟨hsz, hall⟩ :=
      Assembly.structProjBodies_spec tbl.structName tbl.numParams tbl.numFields hcty_refs hbodies
    have hi_sz : i < tbl.bodies.size := by omega
    change (tbl.bodies.getD i default).RefsIn (KeptKey env)
    have hgetD_eq : tbl.bodies.getD i default = tbl.bodies[i] := by
      unfold Array.getD
      simp only [hi_sz, ↓reduceDIte]
      rfl
    rw [hgetD_eq]
    refine hall tbl.bodies[i] ?_
    rw [← Array.getElem_toList]
    exact List.getElem_mem _
  exact ⟨claimedModel M hnd htype hvalue hrhs hctor hbody⟩

/-- **The claimed sub-environment has a model, from the provenance clause**: every claimed
constant is a projection table, a pinned basis constant, or stores what a record declares,
over any store of records and blobs. -/
theorem claimedEnv_models_of_provenance {t : Ix.Kernel.RoleTable}
    {store : Ix.Kernel.Reader.Store} {blob : _root_.Address → Option ByteArray}
    {env : Ix.Kernel.Env .anon} (hnd : (env.consts.map (·.name)).Nodup)
    (hprov : ∀ ci ∈ (claimedEnv env).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨ ∃ a, KeptIn t store blob a ci)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Ix.Kernel.Model.EnvModelOk V .verified env ∧ Decl.StrongEnvProps env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V (claimedEnv env)) := by
  refine claimedEnv_models_of_nonAux hnd (fun c hc => ?_) hmodel
  rcases hprov c hc with h | ⟨kind, hk⟩ | ⟨a, -, ci₀, hr, hst⟩
  · exact Or.inl h
  · exact Or.inr (Assembly.basisDeclsA_nonAux kind c hk)
  · exact Or.inr (storedAs_nonAux hst (readsIn_nonAux hr))

/-- **The claimed sub-environment has a model, from the provenance clause and the prefix
invariant** at any one store and limit. -/
theorem claimedEnv_models_of_prefixInv {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {lim : Option Nat} {store : Ix.Kernel.Reader.Store}
    {blob : _root_.Address → Option ByteArray} {env : Ix.Kernel.Env .anon}
    (hinv : Decl.PrefixInv.{u} E t lim env) (hnd : (env.consts.map (·.name)).Nodup)
    (hprov : ∀ ci ∈ (claimedEnv env).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨ ∃ a, KeptIn t store blob a ci) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V (claimedEnv env)) :=
  claimedEnv_models_of_provenance hnd hprov
    (fun V _ => Decl.FullDeclInv.ok V env (hinv.decl V))

/-! ## Provenance over the run's records with the witness's behind them -/

/-- **What a constant keeps of a record of the run is kept over the joint store.** -/
theorem keptIn_over_run {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {a : _root_.Address}
    {ci : ConstantInfo .anon}
    (h : KeptIn t (recordOf E₀) (fun x => E₀.blobs.get? x) a ci) :
    KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
  obtain ⟨hax, ci₀, hr, hst⟩ := h
  have hover : ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a ci₀ :=
    IxVM.Consistency.ReadsIn.over_run hr
  obtain ⟨c₀, hc₀, -⟩ := hr
  refine ⟨fun c ax hc hinfo => ?_, ci₀, hover, hst⟩
  have hs : storeOver E₀ R a = some c₀ := ReaderReads.storeOver_left hc₀
  rw [hs] at hc
  have hcc : c₀ = c := Option.some.inj hc
  rw [← hcc] at hinfo
  exact hax c₀ ax hc₀ hinfo

/-- **What a constant keeps of a record of the witness is kept over the joint store**, when
the two stores agree where both hold a record or a blob. -/
theorem keptIn_over_witness {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hrec : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    (hblob : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    {a : _root_.Address} {ci : ConstantInfo .anon}
    (h : KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci) :
    KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
  obtain ⟨hax, ci₀, hr, hst⟩ := h
  have hover : ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a ci₀ :=
    IxVM.Consistency.ReadsIn.over_witness hrec hblob hr
  obtain ⟨c₀, hc₀, -⟩ := hr
  refine ⟨fun c ax hc hinfo => ?_, ci₀, hover, hst⟩
  have hs : storeOver E₀ R a = some c₀ := ReaderReads.storeOver_right hrec hc₀
  rw [hs] at hc
  have hcc : c₀ = c := Option.some.inj hc
  rw [← hcc] at hinfo
  exact hax c₀ ax hc₀ hinfo

/-- **The provenance clause of a witness's environment holds over the joint store.** -/
theorem provenance_over_witness {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon}
    (hrec : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    (hblob : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    (hprov : ∀ ci ∈ (claimedEnv envT).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci) :
    ∀ ci ∈ (claimedEnv envT).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
  intro ci hci
  rcases hprov ci hci with h | h | ⟨a, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨a, keptIn_over_witness hrec hblob h⟩)

/-- **A constant the witness's environment stores at the key of an address is a pin, or keeps
the record at that address over the joint store.** -/
theorem stored_provenance {t : Ix.Kernel.RoleTable} (hroles : (t.bound.toList.map (·.1)).Nodup)
    {E₀ R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    (hrec : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    (hblob : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    (hprov : ∀ ci ∈ (claimedEnv envT).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci)
    {a' : _root_.Address} {ci : ConstantInfo .anon}
    (hfind : envT.find? (keyOf t a') = some ci) :
    PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) a' ci := by
  obtain ⟨hclaimed, hna⟩ := seed_claimed hfind
  rcases hprov ci hclaimed with ⟨tbl, htbl⟩ | hpin | ⟨a, hk⟩
  · rw [htbl] at hna
    exact absurd rfl (hna tbl.structName .projTable)
  · exact Or.inl hpin
  · have hname : ci.name = keyOf t a' := Ix.Kernel.Semantics.Env.find?_name hfind
    have haa : a = a' := keyOf_inj hroles ((keptIn_name hk).symm.trans hname)
    rw [haa] at hk
    exact Or.inr (keptIn_over_witness hrec hblob hk)

end IxVM.Refinement.Typing
