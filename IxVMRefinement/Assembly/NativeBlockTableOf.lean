import IxVMRefinement.Assembly.NativeBlockNewTable
import IxVMRefinement.Assembly.NativeBlockInv
import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.Decl.PointModelTele
import IxVMRefinement.Decl.Native
import IxVMRefinement.Decl.NativeEnv

/-! # The new family's projection-table facts, from the install

`blockTable_of_install`: the bundle `BlockTable` (`NativeBlockNewTable.lean`) after a native
block's install without its recursor, from the install with the family named (the telescope
constant is the stored former, the constructors are `ctorsA`), the new constants as the store
reads them (`BlockInstall`), the prefix invariant, and the freshness of the former's key. The
bundle's `fire` clause is not derived here: it is taken as the named input `BlockFire` (the
firing of the new table at every context, which the table's certificate gives with the reading
of a `proj_guard` run).

* `table`: `Decl.checkNativeTable_struct_inv` at the one constructor (no index); the stored
  constructor found among the new constants; the entries' head data from the store invariant
  after the install (`ProjOkT`); the binder zero-ness from the stored constructor's typing at the
  constructor stage (`Decl.Point.pwAll_of_infer`, `Decl.Point.sort_of_endsHead` at the stored
  former), `sumCtorRunJ_pwAll`;
* `newTable`, `ctorTele`: the shape of the new constants (`new_mem_of_checkNativeTable`) and the
  constructors' stage (`Decl.sumCtorRunJ_struct_facts`);
* `ctorAt`: a constructor the prefix stores at a constructor key of the block would make the
  prefix store the former's key (`Decl.PrefixInv.ctor_ind_stored`), which is fresh.
-/

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The firing of the new projection table**: the field `BlockTable.fire`, as a named input
(module docstring). Where the family's sort passes the zero test, the table the install stores
at the family's table name fires at every context over the role table and the store, with the
family's first constructor as the install stores it. No limit occurs. -/
def BlockFire (c : Core.Ctx) (new : List (ConstantInfo .anon)) (B : _root_.Address) : Prop :=
  ∀ tbl : Ix.Kernel.ProjTable .anon,
    (appCtx c new).env.find? (Ix.Kernel.projTableName (Core.keyOf c.t (Core.iprjAddr B 0))) =
      some (.projInfo tbl) →
    Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
    ∃ (cvC : ConstantVal .anon) (nP nF : Nat),
      (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B 0 0)) =
        some (.ctorInfo cvC nP nF) ∧
      Core.ProjTableFires c.t c.E (Core.keyOf c.t (Core.iprjAddr B 0)) tbl
        (Core.keyOf c.t (Core.cprjAddr B 0 0)) cvC

/-! ## Telescope facts -/

/-- A telescope stripped to a sort ends in that sort, at that arity. -/
theorem tbl_stripPis_sort {s : Ix.Kernel.Level} :
    ∀ (k : Nat) (e : Ix.Kernel.Expr .anon)
      (bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)),
      e.stripPis k = some (bs, .sort s) → e.resultSort = some s ∧ e.piArity = k
  | 0, e, bs, h => by
    injection h with hpair
    obtain ⟨-, rfl⟩ := Prod.mk.inj hpair
    exact ⟨rfl, rfl⟩
  | k + 1, .forallE ty b m, bs, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', body'⟩, h', hpair⟩ := h
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    obtain ⟨h1, h2⟩ := tbl_stripPis_sort k b bs' h'
    refine ⟨h1, ?_⟩
    show b.piArity + 1 = k + 1
    rw [h2]
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => nomatch h

/-- A telescope whose `stripPis k` residual ends in a head ends in that head. -/
theorem tbl_endsHead_of_stripPis {T : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level} {n : Nat} :
    ∀ (k : Nat) (e body : Ix.Kernel.Expr .anon)
      (bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)),
      e.stripPis k = some (bs, body) → Decl.Point.EndsHead T us n body →
      Decl.Point.EndsHead T us n e
  | 0, e, body, bs, h, hb => by
    injection h with hpair
    obtain ⟨-, rfl⟩ := Prod.mk.inj hpair
    exact hb
  | k + 1, .forallE ty b m, body, bs, h, hb => by
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', body'⟩, h', hpair⟩ := h
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    exact tbl_endsHead_of_stripPis k b body' bs' h' hb
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _ _, _, _, h, _ | _ + 1, .sort _, _, _, h, _
  | _ + 1, .const _ _, _, _, h, _ | _ + 1, .app _ _, _, _, h, _ | _ + 1, .lam _ _ _, _, _, h, _
  | _ + 1, .letE _ _ _ _, _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, h, _ => nomatch h

/-- A term that is no `∀` ends in its own head. -/
theorem tbl_endsHead_of_notForall {T : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level} {n : Nat}
    (e : Ix.Kernel.Expr .anon) (hnf : ∀ ty b m, e ≠ .forallE ty b m)
    (h1 : e.getAppFn = .const T us) (h2 : e.getAppArgs.length = n) :
    Decl.Point.EndsHead T us n e := by
  cases e with
  | forallE ty b m => exact absurd rfl (hnf ty b m)
  | bvar _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | fvar _ _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | sort _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | const _ _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | app _ _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | lam _ _ _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | letE _ _ _ _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | lit _ => exact (⟨h1, h2⟩ : _ ∧ _)
  | proj _ _ _ => exact (⟨h1, h2⟩ : _ ∧ _)

/-- An application spine over a head that is no `∀` is no `∀`. -/
theorem tbl_mkAppN_ne_forallE :
    ∀ (args : List (Ix.Kernel.Expr .anon)) (f : Ix.Kernel.Expr .anon),
      (∀ ty b m, f ≠ .forallE ty b m) → ∀ ty b m, Ix.Kernel.Expr.mkAppN f args ≠ .forallE ty b m
  | [], _, hf => hf
  | a :: as, f, _ => tbl_mkAppN_ne_forallE as (.app f a) (fun _ _ _ h => nomatch h)

/-- The spine arguments of an application chain extend the head's. -/
theorem tbl_getAppArgs_mkAppN :
    ∀ (args : List (Ix.Kernel.Expr .anon)) (f : Ix.Kernel.Expr .anon),
      (Ix.Kernel.Expr.mkAppN f args).getAppArgs = f.getAppArgs ++ args
  | [], f => by simp [Ix.Kernel.Expr.mkAppN]
  | a :: as, f => by
    rw [show Ix.Kernel.Expr.mkAppN f (a :: as) = Ix.Kernel.Expr.mkAppN (.app f a) as from rfl,
      tbl_getAppArgs_mkAppN as]
    simp [Ix.Kernel.Expr.getAppArgs]

/-- Every binder `stripPis` peels off a telescope whose binders all carry `P` carries `P`. -/
theorem tbl_pw_of_pwAll {P : Ix.Kernel.PropWhen} :
    ∀ (k : Nat) (e body : Ix.Kernel.Expr .anon)
      (bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)),
      Decl.Point.PwAll P e → e.stripPis k = some (bs, body) → ∀ bm ∈ bs, bm.2.pw = P
  | 0, _, _, bs, _, h, bm, hbm => by
    injection h with hpair
    rw [← (Prod.mk.inj hpair).1] at hbm
    exact nomatch hbm
  | k + 1, .forallE ty b m, body, bs, hpw, h, bm, hbm => by
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', body'⟩, h', hpair⟩ := h
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    obtain ⟨hm, hb⟩ := (hpw : m.pw = P ∧ Decl.Point.PwAll P b)
    rcases List.mem_cons.mp hbm with rfl | hbm'
    · exact hm
    · exact tbl_pw_of_pwAll k b body' bs' hb h' bm hbm'
  | _ + 1, .bvar _, _, _, _, h, _, _ | _ + 1, .fvar _ _, _, _, _, h, _, _
  | _ + 1, .sort _, _, _, _, h, _, _ | _ + 1, .const _ _, _, _, _, h, _, _
  | _ + 1, .app _ _, _, _, _, h, _, _ | _ + 1, .lam _ _ _, _, _, _, h, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, h, _, _ | _ + 1, .lit _, _, _, _, h, _, _
  | _ + 1, .proj _ _ _, _, _, _, h, _, _ => nomatch h

private theorem tbl_subst_go_self :
    ∀ (ps : List Ix.Kernel.LevelParam) (p : Ix.Kernel.LevelParam),
      Ix.Kernel.Level.subst.go ps (ps.map .param) p = .param p
  | [], _ => rfl
  | k :: ks, p => by
    show (if k = p then Ix.Kernel.Level.param k
      else Ix.Kernel.Level.subst.go ks (ks.map .param) p) = .param p
    by_cases h : k = p
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right h, tbl_subst_go_self ks p]

/-- Substituting the level parameters by themselves is the identity. -/
theorem tbl_level_subst_self (ps : List Ix.Kernel.LevelParam) :
    ∀ l : Ix.Kernel.Level, Ix.Kernel.Level.subst ps (ps.map .param) l = l
  | .zero => rfl
  | .succ l => congrArg Ix.Kernel.Level.succ (tbl_level_subst_self ps l)
  | .max a b => by
    simp only [Ix.Kernel.Level.subst, tbl_level_subst_self ps a, tbl_level_subst_self ps b]
  | .imax a b => by
    simp only [Ix.Kernel.Level.subst, tbl_level_subst_self ps a, tbl_level_subst_self ps b]
  | .param p => tbl_subst_go_self ps p

/-! ## The constructor's binder zero-ness -/

/-- A checked constant's annotated type is typed at a sort. -/
theorem tbl_typing_of_check {env : Ix.Kernel.Env .anon} {cv cv' : ConstantVal .anon}
    (h : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env cv cv') :
    ∃ st u, Ix.Kernel.Rules.Infer env .full 0 cv'.type st ∧
      Ix.Kernel.Rules.Red env 0 st (.sort u) := by
  obtain ⟨type', ⟨-, -, -, -, -, -, -, -, -, st, u, hst, hu⟩, rfl⟩ := h
  exact ⟨st, u, hst, hu⟩

/-- **Every binder of a stored constructor carries the zero-ness of the family's sort**: the
stored constructor is typed at the constructor stage (either branch of its check), its telescope
ends in the family stored there at its own level parameters, so its sort has the zero-ness of
the family's (`Decl.Point.sort_of_endsHead`) and every binder carries it
(`Decl.Point.pwAll_of_infer`). -/
theorem sumCtorRunJ_pwAll {env : Ix.Kernel.Env .anon} {cvS : ConstantVal .anon}
    {caps' : IndCaps .anon} {T : Ix.Kernel.Key .anon} {lps : List Ix.Kernel.LevelParam}
    {nP nIdx : Nat} {resSort s : Ix.Kernel.Level} {isProp large : Bool} {cvC : ConstantVal .anon}
    {nF : Nat} {cvTa cvCa : ConstantVal .anon} {sorts : List Ix.Kernel.Level}
    (hrun : Ix.Kernel.Semantics.SumCtorRunJ Ix.Kernel.Model.rulesJ
      ⟨.indInfo cvS caps' :: env.consts⟩ ⟨.indInfo cvS caps' :: env.consts⟩ T lps nP nIdx
      resSort isProp large cvC nF cvTa cvCa sorts)
    (hT : cvS.name = T) (hlps : cvS.levelParams = lps)
    (hres : cvS.type.resultSort = some s) (har : cvS.type.piArity = nP + nIdx) :
    ∃ bs body, cvCa.type.stripPis (nP + nF) = some (bs, body) ∧
      ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf s := by
  subst hT hlps
  obtain ⟨⟨cvCa₀, hchk₀, hbr⟩, ⟨cbs, es, hst, hes⟩, -⟩ := hrun
  obtain ⟨st, u, hinf, hred⟩ : ∃ st u, Ix.Kernel.Rules.Infer
      (⟨.indInfo cvS caps' :: env.consts⟩ : Ix.Kernel.Env .anon) .full 0 cvCa.type st ∧
      Ix.Kernel.Rules.Red (⟨.indInfo cvS caps' :: env.consts⟩ : Ix.Kernel.Env .anon) 0 st
        (.sort u) := by
    rcases hbr with rfl | ⟨ty', hchk₁⟩
    · exact tbl_typing_of_check hchk₀
    · exact tbl_typing_of_check hchk₁
  have hbody : Decl.Point.EndsHead cvS.name (cvS.levelParams.map .param) (nP + nIdx)
      (Ix.Kernel.Expr.mkAppN (.const cvS.name (cvS.levelParams.map .param))
        (Ix.Kernel.structPsAt nF nP ++ es)) := by
    refine tbl_endsHead_of_notForall _
      (tbl_mkAppN_ne_forallE _ _ (fun _ _ _ h => nomatch h)) ?_ ?_
    · rw [Decl.nat_getAppFn_mkAppN]
      rfl
    · rw [tbl_getAppArgs_mkAppN]
      show ([] ++ (Ix.Kernel.structPsAt nF nP ++ es)).length = nP + nIdx
      simp [Ix.Kernel.structPsAt, hes]
  have hends : Decl.Point.EndsHead cvS.name (cvS.levelParams.map .param)
      (ConstantInfo.indInfo cvS caps').toConstantVal.type.piArity cvCa.type := by
    show Decl.Point.EndsHead cvS.name (cvS.levelParams.map .param) cvS.type.piArity cvCa.type
    rw [har]
    exact tbl_endsHead_of_stripPis _ _ _ _ hst hbody
  have hf : (⟨.indInfo cvS caps' :: env.consts⟩ : Ix.Kernel.Env .anon).find? cvS.name =
      some (.indInfo cvS caps') :=
    Ix.Kernel.Env.find?_cons_self (.indInfo cvS caps') env
  have hr : (ConstantInfo.indInfo cvS caps').toConstantVal.type.resultSort = some s := hres
  obtain ⟨-, hz⟩ := Decl.Point.sort_of_endsHead (us := cvS.levelParams.map .param) hf hr _
    cvCa.type 0 st u rfl hends hinf hred
  have hz' : Ix.Kernel.Level.zeronessOf u = Ix.Kernel.Level.zeronessOf s := by
    rw [hz]
    exact congrArg Ix.Kernel.Level.zeronessOf (tbl_level_subst_self cvS.levelParams s)
  have hpw := Decl.Point.pwAll_of_infer _ cvCa.type 0 st u rfl
    (Decl.Point.EndsHead.shape _ hends) hinf hred
  refine ⟨cbs, _, hst, fun bm hbm => ?_⟩
  rw [← hz']
  exact tbl_pw_of_pwAll _ _ _ _ hpw hst bm hbm

/-! ## The new constants -/

/-- **What the native install puts in front of the prefix**: every constructor of `ctorsA`, and
at most the family's projection table. -/
theorem new_mem_of_checkNativeTable {env : Ix.Kernel.Env .anon} {new : List (ConstantInfo .anon)}
    {p : Ix.Kernel.NativeParts .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    {sortss : List (List Ix.Kernel.Level)} {cvS : ConstantVal .anon} {caps' : IndCaps .anon}
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
      (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps' :: env.consts⟩) =
        .ok ⟨new ++ env.consts⟩) :
    (∀ cA ∈ ctorsA, ConstantInfo.ctorInfo cA.1 p.nP cA.2 ∈ new) ∧
    (∀ tbl, ConstantInfo.projInfo tbl ∈ new → tbl.structName = p.cvT.name) := by
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps' :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps']) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have hmid : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps'], ∀ tbl, ci ≠ .projInfo tbl := by
    intro ci hci tbl he
    subst he
    rcases List.mem_append.mp hci with h | h
    · obtain ⟨c', -, hc'⟩ := List.mem_map.mp (List.mem_reverse.mp h)
      exact nomatch hc'
    · rw [List.mem_singleton] at h
      exact nomatch h
  have hctor : ∀ cA ∈ ctorsA, ConstantInfo.ctorInfo cA.1 p.nP cA.2 ∈
      (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps'] := fun cA hcA =>
    List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map.mpr ⟨cA, hcA, rfl⟩))
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, hsn⟩
  · have hcs : new ++ env.consts = _ := congrArg Ix.Kernel.Env.consts heq
    rw [hc] at hcs
    have hn := List.append_cancel_right hcs
    subst hn
    exact ⟨hctor, fun tbl' htbl => absurd rfl (hmid _ htbl tbl')⟩
  · have hcs : new ++ env.consts = .projInfo tbl :: _ := congrArg Ix.Kernel.Env.consts heq
    rw [hc, ← List.cons_append] at hcs
    have hn := List.append_cancel_right hcs
    subst hn
    refine ⟨fun cA hcA => List.mem_cons_of_mem _ (hctor cA hcA), fun tbl' htbl => ?_⟩
    rcases List.mem_cons.mp htbl with he | hrest
    · injection he with he
      rw [he]
      exact hsn
    · exact absurd rfl (hmid _ hrest tbl')

/-! ## The bundle -/

/-- **The new projection table's bundle, from the install** (module docstring). Inputs, at an
environment `c.env` a native block's unit step is handed: the new constants as the store reads
them (`hI`), the prefix invariant, the block's pins and keys (`hpin`, `hna`, from
`blockReads_of_member`), the install with the family named (`hfacts`, with the recognised
former `hcvT`, its counts `hnP`/`hnIdx` and the stored constructors `hlenA`/`hctorsA`: the
conclusions of `ctorOuts_of_member_named` and `nativeNoRecFacts_of_outs_named`), the freshness
of the former's key, and the firing of the new table. -/
theorem blockTable_of_install {c : Core.Ctx} {new : List (ConstantInfo .anon)}
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}
    {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {ty₀ ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    (hI : BlockInstall c new B cb ind caps)
    (hinv : Decl.PrefixInv.{u} c.E c.t c.lim c.env)
    (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk ind.params.toNat))
    (hfacts : NativeNoRecFacts c.env (appCtx c new).env blk ind.params.toNat p₀
      ⟨p, ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩)
    (hcvT : p₀.cvT = ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩)
    (hnP : p₀.nP = ind.params.toNat) (hnIdx : p₀.nIdx = ind.indices.toNat)
    (hlenA : ctorsA.length = ind.ctors.size)
    (hctorsA : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      cA.1.name = Core.keyOf c.t (Core.cprjAddr B 0 j) ∧
        cA.1.levelParams = List.range ind.lvls.toNat)
    (hfreshT : c.env.find? (Core.keyOf c.t (Core.iprjAddr B 0)) = none)
    (hfire : BlockFire c new B) :
    BlockTable c new B ind := by
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hna.1 ci (by simpa [IxVM.Consistency.installs, hpin] using hci)).1
  have hstore₂ : Decl.FoldStoreInv (appCtx c new).env :=
    hfacts.foldStoreInv hpin hnaKeys hinv.store
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, hp, hCtors, -, -, -, -, -, -, hTbl⟩ := hfacts
  injection hfam with h1 h2 h3 h4
  subst h2 h3
  rw [h4] at hlenA hctorsA
  obtain ⟨cvTa₀, s, bsT, cvS'', -, -, hstT, -, hp₁, -⟩ := hInd
  have hqcvT : q.cvT = p₀.cvT := by subst hp hp₁; rfl
  have hTname : q.cvT.name = Core.keyOf c.t (Core.iprjAddr B 0) := by rw [hqcvT, hcvT]
  have hTlps : q.cvT.levelParams = List.range ind.lvls.toNat := by rw [hqcvT, hcvT]
  have hpnP : q.nP = p₀.nP := by subst hp hp₁; rfl
  have hpnIdx : q.nIdx = p₀.nIdx := by subst hp hp₁; rfl
  have hpRes : q.resSort = s := by subst hp hp₁; rfl
  have hstT' : ty'.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort s) := hstT
  obtain ⟨hres, har⟩ := tbl_stripPis_sort _ _ _ hstT'
  have har' : ty'.piArity = q.nP + q.nIdx := by rw [har, hpnP, hpnIdx]
  obtain ⟨hlA, hlS, hall⟩ := hCtors
  obtain ⟨hnewC, hnewT⟩ := new_mem_of_checkNativeTable hTbl
  have hstoredCtor : ∀ cA ∈ ctorsB, (appCtx c new).env.find? cA.1.name =
      some (.ctorInfo cA.1 q.nP cA.2) := fun cA hcA => hI.newFind _ (hnewC cA hcA)
  refine ⟨?_, ?_, ?_, ?_, hfire⟩
  · -- table
    intro hi0 hs1
    have hlen1 : ctorsB.length = 1 := hlenA.trans hs1
    obtain ⟨cA, rfl⟩ : ∃ cA, ctorsB = [cA] := by
      rcases ctorsB with _ | ⟨cA, _ | ⟨_, _⟩⟩
      · simp at hlen1
      · exact ⟨cA, rfl⟩
      · simp at hlen1
    have hlenS1 : sortss.length = 1 := hlS.trans (hlA.symm.trans rfl)
    obtain ⟨s0, rfl⟩ : ∃ s0, sortss = [s0] := by
      rcases sortss with _ | ⟨s0, _ | ⟨_, _⟩⟩
      · simp at hlenS1
      · exact ⟨s0, rfl⟩
      · simp at hlenS1
    obtain ⟨c0, hc0⟩ : ∃ c0, q.ctors[0]? = some c0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlA]; simp)⟩
    obtain ⟨hc2, sorts, hsorts, hrun⟩ := hall 0 c0 cA hc0 rfl
    have hs : sorts = s0 := (Option.some.inj (hsorts : some s0 = some sorts)).symm
    subst hs
    have hnIdx0 : q.nIdx = 0 := hpnIdx.trans (hnIdx.trans hi0)
    obtain ⟨tbl, -, -, hfindTbl, hsn, hctor, hnPt, hnFt, hlpt, hss, -, hbodies, hguards,
      hfindProj⟩ := Decl.checkNativeTable_struct_inv hnIdx0 hTbl
    obtain ⟨hnm0, hlps0⟩ := hctorsA 0 cA rfl
    refine ⟨tbl, ?_, hsn.trans hTname, hctor.trans hnm0, ?_⟩
    · rw [← hTname]
      exact hfindTbl
    · intro cvC nP nF hf
      have hfind := hstoredCtor cA (List.mem_singleton.mpr rfl)
      rw [hnm0] at hfind
      rw [hfind] at hf
      injection hf with hf
      injection hf with h1 h2 h3
      subst h1 h2 h3
      obtain ⟨-, -, hslen, -, -, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
      obtain ⟨bs, body, hstC, hpwC⟩ := sumCtorRunJ_pwAll hrun hTname.symm hTlps.symm hres har'
      refine ⟨hnPt, hnFt, hlpt.trans (hTlps.trans hlps0.symm), hpnP.trans hnP,
        fun f hf => ⟨hfindProj f hf,
          hstore₂.store.proj_ok _ tbl hfindTbl f (by rw [hnFt]; exact hf)⟩,
        hbodies, ⟨sorts, by rw [hc2]; exact hslen, hguards⟩, bs, body, ?_, ?_⟩
      · rw [hc2]
        exact hstC
      · intro bm hbm
        rw [hss, hpRes]
        exact hpwC bm hbm
  · -- newTable
    intro tbl htbl
    exact (hnewT tbl htbl).trans hTname
  · -- ctorTele
    intro j hj cvC nP nF hf
    have hjA : j < ctorsB.length := by rw [hlenA]; exact hj
    obtain ⟨cA, hcA⟩ : ∃ cA, ctorsB[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjA⟩
    obtain ⟨hnm, -⟩ := hctorsA j cA hcA
    have hfind := hstoredCtor cA (List.mem_of_getElem? hcA)
    rw [hnm] at hfind
    rw [hfind] at hf
    injection hf with hf
    injection hf with h1 h2 h3
    subst h1 h2 h3
    obtain ⟨c0, hc0⟩ : ∃ c0, q.ctors[j]? = some c0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlA]; exact hjA)⟩
    obtain ⟨hc2, sorts, -, hrun⟩ := hall j c0 cA hc0 hcA
    obtain ⟨-, -, -, htele, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
    rw [hc2]
    exact htele
  · -- ctorAt
    intro hbh j cv nP nF hf
    rcases find?_append_cases (env := c.env) new hf with hm | hold
    · exact hm
    · exfalso
      have hne : (appCtx c new).stored.κ (Core.cprjAddr B 0 j) ≠ Core.unresolvedKey := by
        intro he
        rw [he, hinv.unresolved] at hold
        exact nomatch hold
      have hk : (appCtx c new).stored.κ (Core.cprjAddr B 0 j) =
          Core.keyOf c.t (Core.cprjAddr B 0 j) := (appCtx c new).stored.key_eq hne
      rw [hk] at hold
      obtain ⟨ci, hci⟩ := hinv.ctor_ind_stored hbh hold
      rw [hfreshT] at hci
      exact nomatch hci

end IxVM.Refinement.Typing
