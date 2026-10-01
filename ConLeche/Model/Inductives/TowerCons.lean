module

public import ConLeche.Model.IndCons

public section

/-!
# The P step at a tower-table cons (task #175 W4c, P3 module 4, part 2; S1)

`declStep_preserves_of_tower_cons`: the install kit at a head that is a
tower-backed projection **table** (task #175 S1: one constant per
structure, the fields' bodies).  The head's crossing condition is the
`NoProjEnv` of the prefix at the structure's every slot
(`BitConsCross`), the head data is `TowerHead` at every field, and
the one row the transports cannot supply — the head's own
`TowerEntryLaw` at every field — is the install's
(`towerOk_cons_tower`).  The table's leaf is `Sort 0`, a member of
its dummy type's reading `Sort 1`: a table is not a term
(`inferTypeCore` rejects a `.const` naming it), so nothing else is
owed of the leaf.  The `NoProjEnv` bookkeeping the direct install
needs is here too: the pre-block environment lacks the structure
altogether (`noProjEnv_of_fresh`), and each block constant is consed
with its own pieces' `NoProjAt` (`NoProjEnv.cons`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ProjEntry
  ProjTable natName natZeroName natSuccName eqName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## `NoProjEnv` bookkeeping -/

/-- A well-formed environment that does not store `T` has no `.proj T _`
node anywhere: every stored piece resolves in it. -/
theorem noProjEnv_of_fresh (hwf : ConLeche.EnvWF env) {T : Name}
    (hT : env.find? T = none) (i : Nat) : NoProjEnv env T i where
  type c hc := ConLeche.Expr.noProjAt_of_constsResolve hT _ (hwf c hc).2.2.1
  defn cv v hint hc :=
    ConLeche.Expr.noProjAt_of_constsResolve hT _
      ((hwf _ hc).2.2.2.2.1 cv v hint rfl).2.2.1
  rule cv mI rP rules hc r hr := by
    obtain ⟨-, -, -, -, -, hrec, -, -⟩ := hwf _ hc
    obtain ⟨-, -, hres, -, hnest⟩ := hrec cv mI rP rules rfl r hr
    refine ⟨ConLeche.Expr.noProjAt_of_constsResolve hT _ hres, ?_⟩
    intro lvls pins hn pin hp
    obtain ⟨-, -, hpins, -⟩ := hnest lvls pins hn
    exact ConLeche.Expr.noProjAt_of_constsResolve hT _ (hpins pin hp).2.2.1
  table tbl hc j hj := by
    obtain ⟨-, -, -, -, -, -, htbl, -⟩ := hwf _ hc
    obtain ⟨hsize, hb⟩ := htbl tbl rfl
    have hlt : j < tbl.bodies.size := by rw [hsize]; exact hj
    have := hb j (tbl.bodies[j]'hlt) (Array.getElem?_eq_getElem hlt)
    rw [Array.getD, dif_pos hlt]
    exact ConLeche.Expr.noProjAt_of_constsResolve hT _ this.2.2.1

/-- The head's pieces, for a cons step of `NoProjEnv`. -/
structure NoProjHead (c₀ : ConstantInfo) (T : Name) (i : Nat) : Prop where
  type : Expr.NoProjAt T i c₀.toConstantVal.type
  defn : ∀ (cv : ConstantVal) (v : Expr) (hint : ConLeche.ReducibilityHint),
    c₀ = .defnInfo cv v hint → Expr.NoProjAt T i v
  rule : ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    c₀ = .recInfo cv mI rP rules →
    ∀ r ∈ rules, Expr.NoProjAt T i (RecRule.rhs r) ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        ∀ pin ∈ pins, Expr.NoProjAt T i pin
  table : ∀ (tbl : ConLeche.ProjTable), c₀ = .projInfo tbl →
    ∀ j, j < tbl.numFields → Expr.NoProjAt T i (tbl.bodies.getD j default)

/-- A head with no value, rule or body pieces (an inductive, a
constructor, a recursor-free constant): only its type is asked. -/
theorem NoProjHead.ofType {c₀ : ConstantInfo} {T : Name} {i : Nat}
    (hty : Expr.NoProjAt T i c₀.toConstantVal.type)
    (hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint)
    (hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules)
    (hnottable : ∀ tbl, c₀ ≠ .projInfo tbl) :
    NoProjHead c₀ T i :=
  ⟨hty, fun cv v hint h => absurd h (hnotdefn cv v hint),
    fun cv mI rP rules h => absurd h (hnotrec cv mI rP rules),
    fun tbl h => absurd h (hnottable tbl)⟩

theorem NoProjEnv.cons {T : Name} {i : Nat} (h : NoProjEnv env T i)
    {c₀ : ConstantInfo} (hh : NoProjHead c₀ T i) :
    NoProjEnv ⟨c₀ :: env.consts⟩ T i where
  type c hc := by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hh.type
    · exact h.type c hc
  defn cv v hint hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.defn cv v hint heq.symm
    · exact h.defn cv v hint hc
  rule cv mI rP rules hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.rule cv mI rP rules heq.symm
    · exact h.rule cv mI rP rules hc
  table tbl hc := by
    rcases List.mem_cons.mp hc with heq | hc
    · exact hh.table tbl heq.symm
    · exact h.table tbl hc

/-! ## The kit -/

/-- **The P step at a tower-table cons.**  The head is a tower-backed
table at the structure's reserved table name; the structure's slots
are mentioned by no stored piece; the head data holds at every field
at the extension; and the fields' projection laws are supplied.  The
leaf is `Sort 0` (a member of the dummy type's reading); everything
else transports as at any fresh cons. -/
theorem declStep_preserves_of_tower_cons (mp : EnvModelM V μ env)
    {tbl : ProjTable}
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hnres : ConLeche.reservedBasisNames.contains
      (ConstantInfo.projInfo tbl).name = false)
    (hwf : ConLeche.EnvWF ⟨.projInfo tbl :: env.consts⟩)
    (hnp : ∀ i, NoProjEnv env tbl.structName i)
    (hhead : ∀ i, i < tbl.numFields →
      ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i))
    (hlaw : ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval
        (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i)) :
    ∃ mp' : EnvModelM V μ ⟨.projInfo tbl :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval
        (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) := by
  have hh : ConsHead env (.projInfo tbl) (fun _ => .sort 0) :=
    ⟨hwf, fun _ => trivial,
      fun hres => absurd hres (by rw [hnres]; exact fun h => nomatch h),
      fun t2 heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hnp,
      fun t2 heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hhead,
      fun _ _ _ _ heq => nomatch heq⟩
  have hreads : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0))
        ⟨.projInfo tbl :: env.consts⟩ ψ 0 (ConstantInfo.projInfo tbl).toConstantVal.type
        = some (.sort 1) := by
    intro ψ
    show denoteMeta _ _ ψ 0 (.sort (.succ .zero)) = _
    rw [denoteMeta_sort]
    rfl
  refine declStep_preserves_of_cons_guarded mp (c₀ := .projInfo tbl) (A := fun _ => .sort 0) hfresh hh
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by rw [WellDenoted_sort]; trivial)
    (fun _ _ => by rw [AnnotValid_sort]; trivial)
    (fun ψ => ⟨_, hreads ψ⟩)
    (fun ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      exact ⟨by rw [WellDenoted_sort]; trivial, by rw [AnnotValid_sort]; trivial⟩)
    (fun ψ ta hta ρ => by
      obtain rfl := Option.some.inj ((hreads ψ).symm.trans hta)
      exact interp_sort_mem V ρ 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hvalReads`: a table is not a definition
    intro _ψ cv2 value2 hmem
    obtain ⟨_, hdt⟩ := hmem
    exact nomatch hdt
  · -- `nat_heads`: the three guard names are reserved, this one is not
    exact fun φ => natHeads_cons_offNat mp
      (ne_of_notReserved hnres reserved_natName)
      (ne_of_notReserved hnres reserved_natZeroName)
      (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
  · exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ) hfresh
      (hntc := hh.projTower) (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact fun φ => divMod_cons_fresh (mp.div_mod φ) hfresh
      (Or.inl fun _ _ _ h => nomatch h) _ rfl
  · exact eqLaw_cons_fresh mp.eq_law
      (fun h => ne_of_notReserved hnres reserved_eqName h.symm) _ rfl
  · exact capsOk_cons_fresh mp mp.caps_ok hfresh hh.projTower
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h) _ rfl
  · exact fun φ => recRules_cons_fresh mp hfresh hh.projTower
      (fun _ _ _ _ h => nomatch h) _ rfl φ
  · exact reduceOps_cons_fresh mp.reduce_ops hfresh
      (Or.inl fun _ h => nomatch h) _ rfl
  · exact fun φ => towerOk_cons_tower mp hfresh hh.projTower _ rfl
      (hlaw _ rfl) φ

end ConLeche.Model
