module

public import IxC.Kernel.Verify.Rename.Modeled1

@[expose] public section

/-!
# The renaming walk through the modeled route: the canonical iota check (step 7.3, chunk (iii))

`checkIotaThm` at a renamed rule, recursor and constructor, over related
lookup and check environments, under a block-local renaming that commutes with
the input renaming on good keys.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem mapKeys_const_beq (hf : InjOn f P) {e : Expr md} (he : e.Good P) {k : Key md}
    (hk : k.Good P) (us : List Level) :
    (e.mapKeys f == Expr.const (k.map f) us) = (e == Expr.const k us) :=
  Expr.mapKeys_beq hf he (show Expr.Good P (Expr.const k us) from hk)

theorem map_append_mapKeys (as bs : List (Expr md)) :
    as.map (Expr.mapKeys f) ++ bs.map (Expr.mapKeys f) = (as ++ bs).map (Expr.mapKeys f) := by
  simp

/-- **The canonical rule's `iota_j` check at a renamed rule.** -/
theorem checkIotaThm_sim (mode : CheckMode) (hops : OpsSim P f ops ops')
    {env₁ envS : Env md} {env₁' envS' : Env md'} (hE₁ : EnvRel P f env₁ env₁')
    (hES : EnvRel P f envS envS') {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f))
    (hρg : ∀ k : Key md, k.Good P → (ρ k).Good P)
    {cvName : Key md} (hn : cvName.Good P) (lps : List LevelParam) {tyA : Expr md}
    (hty : tyA.Good P) (mI rP j : Nat) {r : RecRule md} (hr : r.Good P) {cvj : ConstantVal md}
    (hcvj : cvj.Good P) (cnP cnF : Nat) {rhsA : Expr md} (hrhs : rhsA.Good P) :
    SimV (checkIotaThm mode ops env₁ envS ρ cvName lps tyA mI rP j r cvj cnP cnF rhsA)
      (checkIotaThm mode ops' env₁' envS' ρ' (cvName.map f) lps (tyA.mapKeys f) mI rP j
        (r.mapKeys f) (cvj.mapKeys f) cnP cnF (rhsA.mapKeys f)) := by
  have hf := hES.inj
  unfold checkIotaThm
  have hk : (auxKey (auxKey cvName .model) (.iota j)).Good P := hn
  rw [show auxKey (auxKey (cvName.map f) .model) (.iota j) =
    (auxKey (auxKey cvName .model) (.iota j)).map f from rfl, hE₁.findCV? hk]
  refine SimE.bind (SimE.unwrapOr' (G := ConstantVal.Good P)
    (fun cv h => hE₁.findCV?_good hk h)) (fun cvt hcvt => ?_)
  simp only [ConstantVal.mapKeys_levelParams]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [ConstantVal.mapKeys_type, openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hcvt.2 hq)) (fun q hq => ?_)
  obtain ⟨fvs, tbody⟩ := q
  obtain ⟨hfvs, htbody⟩ := hq
  have htargs := htbody.getAppArgs
  have hlhs := htargs.getD 1
  have hrhsS := htargs.getD 2
  have hlargs := hlhs.getAppArgs
  simp only [Expr.mapDoms, ← Expr.mapKeys_getAppFn, isEqHead_mapKeys, Expr.getAppArgs_mapKeys,
    List.length_map, getD_mapKeys_bvar]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← hρ cvName hn, mapKeys_const_beq hf hlhs.getAppFn (hρg cvName hn)]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← List.map_take, ← List.map_take,
    list_beq_mapKeys hf (hlargs.take rP) (hfvs.take rP)]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hctor : (r.mapKeys f).ctor = r.ctor.map f := rfl
  rw [hctor, ← hρ r.ctor hr.1, getLastD_mapKeys_bvar, ← List.map_drop, ← List.map_take,
    map_append_mapKeys,
    show (Expr.const ((ρ r.ctor).map f) (cvj.levelParams.map Level.param) : Expr md') =
      (Expr.const (ρ r.ctor) (cvj.levelParams.map Level.param) : Expr md).mapKeys f from rfl,
    ← Expr.mapKeys_mkAppN]
  have hspine : (Expr.mkAppN (Expr.const (ρ r.ctor) (cvj.levelParams.map Level.param))
      (fvs.take cnP ++ fvs.drop rP) : Expr md).Good P := by
    refine Expr.Good.mkAppN (hρg r.ctor hr.1) ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hfvs.take cnP x hx
    · exact hfvs.drop rP x hx
  rw [Expr.mapKeys_beq hf (hlargs.getLastD 0) hspine]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys, Option.isSome_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hargs : Expr.GoodList P (fvs.take cnP ++ fvs.drop rP) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hfvs.take cnP x hx
    · exact hfvs.drop rP x hx
  rw [← mapKeys_renameConsts_good hρ hcvj.2, Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.instPisAt_good hargs (Expr.Good.renameConsts hρg hcvj.2) hq))
    (fun q hq => ?_)
  obtain ⟨cdoms, cres⟩ := q
  obtain ⟨hcdoms, hcres⟩ := hq
  simp only [Expr.mapDoms, Expr.getAppArgs_mapKeys, List.length_map]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← List.map_drop, ← List.map_take, ← List.map_drop]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ ((hlargs.drop rP).take (mI - rP))
    (hcres.getAppArgs.drop cnP)) (fun _ _ => ?_)
  rw [map_fvarTypeD_mapKeys, ← List.map_drop]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ (hfvs.drop rP).map_fvarTypeD
    (hcdoms.drop cnP)) (fun _ _ => ?_)
  rw [← mapKeys_renameConsts_good hρ hty, Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q hq => (Expr.instPisAt_good (hfvs.take rP) (Expr.Good.renameConsts hρg hty) hq).1))
    (fun q hq => ?_)
  obtain ⟨rdoms, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [map_fvarTypeD_mapKeys]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ (hfvs.take rP).map_fvarTypeD hq)
    (fun _ _ => ?_)
  try rw [openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q hq => (Expr.openPisAtFvars_good hty hq).1)) (fun q hq => ?_)
  obtain ⟨fvsP, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [← List.map_take]
  rw [Expr.instPisAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q h => Expr.instPisAt_good (hq.take cnP) hcvj.2 h)) (fun q hq₂ => ?_)
  obtain ⟨cdomsP, crestP⟩ := q
  obtain ⟨hcdomsP, hcrestP⟩ := hq₂
  simp only [Expr.mapDoms]
  try rw [map_fvarTypeD_mapKeys]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ (hq.take cnP).map_fvarTypeD hcdomsP)
    (fun _ _ => ?_)
  try rw [openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q h => (Expr.openPisAtFvars_good hcrestP h).1)) (fun q hq₃ => ?_)
  obtain ⟨xFvsP, _⟩ := q
  simp only [Expr.mapDoms]
  have hPX : Expr.GoodList P (fvsP ++ xFvsP) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hq x hx
    · exact hq₃ x hx
  rw [map_append_mapKeys, Expr.instLamsAt_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1)
    (fun q h => (Expr.instLamsAt_good hPX hrhs h).1)) (fun q hq₄ => ?_)
  obtain ⟨ldoms, _⟩ := q
  simp only [Expr.mapDoms]
  try rw [map_fvarTypeD_mapKeys]
  refine SimE.bind (checkDefEqList_sim hops hES _ _ _ hPX.map_fvarTypeD hq₄) (fun _ _ => ?_)
  rw [← mapKeys_renameConsts_good hρ hrhs, ← Expr.mapKeys_mkAppN]
  refine SimE.bind (hops.isDefEq hES _ _ _ hrhsS
    (Expr.Good.mkAppN (Expr.Good.renameConsts hρg hrhs) hfvs)) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  exact checkIotaSidesTy_sim mode hops hES _ (htargs.getD 0) hlhs hrhsS _ cvName

end Ix.Kernel
