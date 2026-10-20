module

public import IxC.Kernel.Verify.Rename.Core7

@[expose] public section

/-!
# Renaming and the pinned data

The pinned declarations (the basis blocks, the standard axioms'
families) name only role keys, so a renaming fixes them and they are good
at every predicate. `noIds` decides "names no input id" by computation;
each pinned datum is fixed by computation (`rfl`).

Then the checks against the pins: the canonical forms (`ConstantInfo.canon`
commutes with renaming), the pin matches (`matchesPin`, `canonEq`,
`basisPinHit`, `quotPinHit`) and the environment predicates of the
standard axioms answer alike at renamed arguments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]

/-! ## Data naming no input id -/

/-- A key naming no input id. -/
def Key.noIds : Key md → Bool
  | .id _ => false
  | .role _ => true
  | .aux k _ => k.noIds

def Expr.noIds : Expr md → Bool
  | .bvar _ | .sort _ | .lit _ => true
  | .fvar _ t => t.noIds
  | .const n _ => n.noIds
  | .app a b => a.noIds && b.noIds
  | .lam t b _ | .forallE t b _ => t.noIds && b.noIds
  | .letE t v b _ => t.noIds && v.noIds && b.noIds
  | .proj s _ e => s.noIds && e.noIds

theorem Key.good_of_noIds : ∀ {k : Key md}, k.noIds = true → k.Good P
  | .id _, h => nomatch h
  | .role _, _ => trivial
  | .aux k _, h => Key.good_of_noIds (k := k) h

theorem Expr.good_of_noIds {e : Expr md} (h : e.noIds = true) : e.Good P := by
  induction e <;> simp_all [Expr.noIds, Key.good_of_noIds]

def ConstantVal.noIds (cv : ConstantVal md) : Bool := cv.name.noIds && cv.type.noIds

def RecRule.noIds (r : RecRule md) : Bool :=
  r.ctor.noIds && r.rhs.noIds && match r.fire with
    | .nested _ pins => pins.all Expr.noIds
    | _ => true

def ConstantInfo.noIds : ConstantInfo md → Bool
  | .axiomInfo v | .ctorInfo v _ _ => v.noIds
  | .defnInfo v e _ | .thmInfo v e => v.noIds && e.noIds
  | .indInfo v caps => v.noIds && caps.etaCtor.all Key.noIds
  | .recInfo v _ _ rules => v.noIds && rules.all RecRule.noIds
  | .projInfo _ => false

theorem ConstantVal.good_of_noIds {cv : ConstantVal md} (h : cv.noIds = true) : cv.Good P := by
  simp only [ConstantVal.noIds, Bool.and_eq_true] at h
  exact ⟨Key.good_of_noIds h.1, Expr.good_of_noIds h.2⟩

theorem RecRule.good_of_noIds {r : RecRule md} (h : r.noIds = true) : r.Good P := by
  obtain ⟨c, nf, cp, fi, rhs, k, e, pb⟩ := r
  simp only [RecRule.noIds, Bool.and_eq_true] at h
  refine ⟨Key.good_of_noIds h.1.1, ?_, Expr.good_of_noIds h.1.2⟩
  cases fi with
  | nested l ps =>
    simp only [List.all_eq_true] at h
    exact fun x hx => Expr.good_of_noIds (h.2 x hx)
  | _ => trivial

theorem ConstantInfo.good_of_noIds {c : ConstantInfo md} (h : c.noIds = true) : c.Good P := by
  cases c with
  | axiomInfo v => exact ConstantVal.good_of_noIds h
  | ctorInfo v _ _ => exact ConstantVal.good_of_noIds h
  | defnInfo v e _ =>
    simp only [ConstantInfo.noIds, Bool.and_eq_true] at h
    exact ⟨ConstantVal.good_of_noIds h.1, Expr.good_of_noIds h.2⟩
  | thmInfo v e =>
    simp only [ConstantInfo.noIds, Bool.and_eq_true] at h
    exact ⟨ConstantVal.good_of_noIds h.1, Expr.good_of_noIds h.2⟩
  | indInfo v caps =>
    simp only [ConstantInfo.noIds, Bool.and_eq_true] at h
    refine ⟨ConstantVal.good_of_noIds h.1, fun k hk => Key.good_of_noIds ?_⟩
    rw [hk] at h; exact h.2
  | recInfo v _ _ rules =>
    simp only [ConstantInfo.noIds, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨ConstantVal.good_of_noIds h.1, fun r hr => RecRule.good_of_noIds (h.2 r hr)⟩
  | projInfo _ => exact nomatch h

/-! ## The pinned declarations -/

theorem eqA_mapKeys : (eqA : ConstantInfo md).mapKeys f = eqA := rfl
theorem eqA_noIds : (eqA : ConstantInfo md).noIds = true := rfl

theorem declsA_mapKeys (k : BasisKind) :
    (k.declsA (md := md)).map (ConstantInfo.mapKeys f) = k.declsA := by
  cases k <;> rfl

theorem decls_mapKeys (k : BasisKind) :
    (k.decls (md := md)).map (ConstantInfo.mapKeys f) = k.decls := by
  cases k <;> rfl

theorem declsA_noIds (k : BasisKind) : (k.declsA (md := md)).all ConstantInfo.noIds = true := by
  cases k <;> rfl

theorem decls_noIds (k : BasisKind) : (k.decls (md := md)).all ConstantInfo.noIds = true := by
  cases k <;> rfl

theorem stdPins_mapKeys :
    (iffA : ConstantInfo md).mapKeys f = iffA ∧ (iffIntroA : ConstantInfo md).mapKeys f = iffIntroA ∧
    (iffRecA : ConstantInfo md).mapKeys f = iffRecA ∧
    (nonemptyA : ConstantInfo md).mapKeys f = nonemptyA ∧
    (nonemptyIntroA : ConstantInfo md).mapKeys f = nonemptyIntroA ∧
    (nonemptyRecA : ConstantInfo md).mapKeys f = nonemptyRecA ∧
    (propextA : ConstantVal md).mapKeys f = propextA ∧
    (choiceA : ConstantVal md).mapKeys f = choiceA :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stdPins_noIds :
    (iffA : ConstantInfo md).noIds ∧ (iffIntroA : ConstantInfo md).noIds ∧
    (iffRecA : ConstantInfo md).noIds ∧ (nonemptyA : ConstantInfo md).noIds ∧
    (nonemptyIntroA : ConstantInfo md).noIds ∧ (nonemptyRecA : ConstantInfo md).noIds ∧
    (propextA : ConstantVal md).noIds ∧ (choiceA : ConstantVal md).noIds :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Canonical forms -/

@[simp] theorem canonExpr_mapKeys (m : LevelParam → LevelParam) (e : Expr md) :
    (canonExpr m e).mapKeys f = canonExpr m (e.mapKeys f) := by
  induction e <;> simp_all [canonExpr]

theorem canonExpr_good {m : LevelParam → LevelParam} {e : Expr md} (he : e.Good P) :
    (canonExpr m e).Good P := by
  induction e <;> simp_all [canonExpr]

@[simp] theorem ConstantVal.canon_mapKeys (cv : ConstantVal md) :
    (ConstantVal.canon cv).mapKeys f = ConstantVal.canon (cv.mapKeys f) := by
  simp [ConstantVal.canon, ConstantVal.mapKeys]

theorem ConstantVal.canon_good {cv : ConstantVal md} (h : cv.Good P) :
    (ConstantVal.canon cv).Good P :=
  ⟨h.1, canonExpr_good h.2⟩

@[simp] theorem ConstantInfo.canon_mapKeys (c : ConstantInfo md) :
    (ConstantInfo.canon c).mapKeys f = ConstantInfo.canon (c.mapKeys f) := by
  cases c <;> simp [ConstantInfo.canon, ConstantInfo.mapKeys, ConstantVal.canon, ConstantInfo.toConstantVal,
    ConstantVal.mapKeys, IndCaps.mapKeys, RecRule.mapKeys, List.map_map, Function.comp_def]

theorem ConstantInfo.canon_good {c : ConstantInfo md} (h : c.Good P) :
    (ConstantInfo.canon c).Good P := by
  cases c with
  | axiomInfo v => exact ConstantVal.canon_good h
  | ctorInfo v _ _ => exact ConstantVal.canon_good h
  | defnInfo v e _ => exact ⟨ConstantVal.canon_good h.1, canonExpr_good h.2⟩
  | thmInfo v e => exact ⟨ConstantVal.canon_good h.1, canonExpr_good h.2⟩
  | indInfo v caps => exact ⟨ConstantVal.canon_good h.1, fun _ hk => nomatch hk⟩
  | recInfo v _ _ rules =>
    refine ⟨ConstantVal.canon_good h.1, ?_⟩
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have := h.2 r₀ hr₀
    exact ⟨this.1, this.2.1, canonExpr_good this.2.2⟩
  | projInfo t => exact h

theorem ConstantVal.canonEq_ren (hf : InjOn f P) {a b : ConstantVal md} (ha : a.Good P)
    (hb : b.Good P) :
    ConstantVal.canonEq (a.mapKeys f) (b.mapKeys f) = ConstantVal.canonEq a b := by
  simp only [ConstantVal.canonEq, ← ConstantVal.canon_mapKeys]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨ConstantVal.mapKeys_inj hf (ConstantVal.canon_good ha) (ConstantVal.canon_good hb),
    fun h => h ▸ rfl⟩

theorem ConstantInfo.canonEq_ren (hf : InjOn f P) {a b : ConstantInfo md} (ha : a.Good P)
    (hb : b.Good P) :
    ConstantInfo.canonEq (a.mapKeys f) (b.mapKeys f) = ConstantInfo.canonEq a b := by
  simp only [ConstantInfo.canonEq, ← ConstantInfo.canon_mapKeys]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨ConstantInfo.mapKeys_inj hf (ConstantInfo.canon_good ha) (ConstantInfo.canon_good hb),
    fun h => h ▸ rfl⟩

theorem ConstantInfo.mapKeys_list_inj (hf : InjOn f P) :
    ∀ {as bs : List (ConstantInfo md)}, (∀ c ∈ as, c.Good P) → (∀ c ∈ bs, c.Good P) →
      as.map (ConstantInfo.mapKeys f) = bs.map (ConstantInfo.mapKeys f) → as = bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ha hb
    rw [ConstantInfo.mapKeys_inj hf ha.1 hb.1 h.1, ConstantInfo.mapKeys_list_inj hf ha.2 hb.2 h.2]

theorem canonEqList_ren (hf : InjOn f P) {as bs : List (ConstantInfo md)}
    (ha : ∀ c ∈ as, c.Good P) (hb : ∀ c ∈ bs, c.Good P) :
    canonEqList (as.map (ConstantInfo.mapKeys f)) (bs.map (ConstantInfo.mapKeys f)) =
      canonEqList as bs := by
  simp only [canonEqList, List.map_map]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  have hc : (ConstantInfo.canon ∘ ConstantInfo.mapKeys f) =
      (ConstantInfo.mapKeys f ∘ ConstantInfo.canon) := by
    funext c; simp
  rw [hc, ← List.map_map, ← List.map_map (g := ConstantInfo.mapKeys f)]
  constructor
  · intro h
    exact ConstantInfo.mapKeys_list_inj hf
      (fun c hc => by simp only [List.mem_map] at hc; obtain ⟨c₀, h₀, rfl⟩ := hc
                      exact ConstantInfo.canon_good (ha c₀ h₀))
      (fun c hc => by simp only [List.mem_map] at hc; obtain ⟨c₀, h₀, rfl⟩ := hc
                      exact ConstantInfo.canon_good (hb c₀ h₀)) h
  · intro h; rw [h]

/-- Names of a renamed block compare as the block's names. -/
theorem names_map_beq (hf : InjOn f P) :
    ∀ {as : List (ConstantInfo md)} {ns : List (Key md)}, (∀ c ∈ as, c.Good P) →
      (∀ n ∈ ns, n.Good P) →
      ((ns.map (Key.map f)) == (as.map (ConstantInfo.mapKeys f)).map (·.name)) =
        (ns == as.map (·.name))
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | a :: as, n :: ns, ha, hn => by
    simp only [List.mem_cons, forall_eq_or_imp] at ha hn
    simp only [List.map_cons, List.cons_beq_cons, ConstantInfo.mapKeys_name,
      names_map_beq hf ha.2 hn.2, Key.map_beq hf hn.1 ha.1.name]

theorem decls_names_good (k : BasisKind) : ∀ n ∈ (k.decls (md := md)).map (·.name), n.Good P := by
  intro n hn
  simp only [List.mem_map] at hn
  obtain ⟨c, hc, rfl⟩ := hn
  have := decls_noIds (md := md) k
  simp only [List.all_eq_true] at this
  exact (ConstantInfo.good_of_noIds (this c hc)).name

theorem basisPinHit_ren (hf : InjOn f P) {block : List (ConstantInfo md)}
    (hb : ∀ c ∈ block, c.Good P) :
    basisPinHit (block.map (ConstantInfo.mapKeys f)) = basisPinHit block := by
  unfold basisPinHit
  have hpred : (fun k : BasisKind =>
      (k.decls (md := md')).map (·.name) == (block.map (ConstantInfo.mapKeys f)).map (·.name)) =
      (fun k => (k.decls (md := md)).map (·.name) == block.map (·.name)) := by
    funext k
    rw [← decls_mapKeys (f := f) k, List.map_map]
    have h := names_map_beq hf (as := block) (ns := (k.decls (md := md)).map (·.name)) hb
      (decls_names_good k)
    rw [List.map_map] at h
    simpa [Function.comp_def] using h
  rw [hpred]
  cases (List.find? (fun k => (k.decls (md := md)).map (·.name) == block.map (·.name))
    [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK]) with
  | none => rfl
  | some k =>
    simp only [Option.filter_some]
    rw [← decls_mapKeys (f := f) k, canonEqList_ren hf hb (fun c hc => by
      have := decls_noIds (md := md) k
      simp only [List.all_eq_true] at this
      exact ConstantInfo.good_of_noIds (this c hc))]

theorem quotPinHit_ren (hf : InjOn f P) (k : QuotKind) {cv : ConstantVal md} (hcv : cv.Good P) :
    quotPinHit k (cv.mapKeys f) = quotPinHit k cv := by
  unfold quotPinHit
  have hd := decls_mapKeys (md := md) (f := f) .quotK
  have hn := decls_noIds (md := md) .quotK
  rw [← hd]
  have hpin : ((BasisKind.quotK.decls (md := md)).getD k.slot (.axiomInfo default)).Good P := by
    simp only [List.all_eq_true] at hn
    simp only [List.getD_eq_getElem?_getD]
    cases hk : (BasisKind.quotK.decls (md := md))[k.slot]? with
    | none => exact ⟨trivial, trivial⟩
    | some c => exact ConstantInfo.good_of_noIds (hn c (List.mem_of_getElem? hk))
  have hg : ((BasisKind.quotK.decls (md := md)).map (ConstantInfo.mapKeys f)).getD k.slot
      (.axiomInfo default) =
      ((BasisKind.quotK.decls (md := md)).getD k.slot (.axiomInfo default)).mapKeys f := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (BasisKind.quotK.decls (md := md))[k.slot]? <;> rfl
  rw [hg, ConstantInfo.mapKeys_toConstantVal, ConstantVal.canonEq_ren hf hcv hpin.toConstantVal]

/-! ## The standard axioms' pins -/

@[simp] theorem Expr.erasePw_mapKeys (e : Expr md) : (e.mapKeys f).erasePw = e.erasePw.mapKeys f := by
  induction e <;> simp_all [Expr.erasePw]

theorem Expr.erasePw_good {e : Expr md} (he : e.Good P) : e.erasePw.Good P := by
  induction e <;> simp_all [Expr.erasePw]

theorem ConstantVal.matchesPin_ren (hf : InjOn f P) {cv pin : ConstantVal md} (hcv : cv.Good P)
    (hpin : pin.Good P) :
    ConstantVal.matchesPin (cv.mapKeys f) (pin.mapKeys f) = ConstantVal.matchesPin cv pin := by
  simp only [ConstantVal.matchesPin, ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams,
    ConstantVal.mapKeys_type, Expr.erasePw_mapKeys,
    Expr.mapKeys_beq hf (Expr.erasePw_good hcv.2) (Expr.erasePw_good hpin.2)]
  by_cases h : cv.name = pin.name
  · have h' : Key.map f cv.name = Key.map f pin.name := by rw [h]
    simp only [h, h', decide_true, Bool.true_and]
    rfl
  · have h' : ¬Key.map f cv.name = Key.map f pin.name := fun e => h (Key.map_inj hf hcv.1 hpin.1 e)
    simp [h, h']

/-- A lookup compared with a pinned constant. -/
theorem find_eq_pin_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') {k : Key md}
    (hk : k.Good P) {pin : ConstantInfo md} (hpin : pin.noIds = true) :
    decide (env'.find? (k.map f) = some (pin.mapKeys f)) = decide (env.find? k = some pin) := by
  rw [hE.find k hk]
  simp only [decide_eq_decide]
  cases hc : env.find? k with
  | none => simp
  | some c =>
    simp only [Option.map_some, Option.some.injEq]
    exact ConstantInfo.mapKeys_eq_iff hE.inj (hE.good k c hk hc) (ConstantInfo.good_of_noIds hpin)

/-- A pin match on a renamed stored value. -/
theorem matchesPin_pin_ren (hf : InjOn f P) {cv : ConstantVal md} (hcv : cv.Good P)
    {pin : ConstantVal md} (hpin : pin.noIds = true) {pin' : ConstantVal md'}
    (he : pin.mapKeys f = pin') :
    ConstantVal.matchesPin (cv.mapKeys f) pin' = ConstantVal.matchesPin cv pin := by
  rw [← he]; exact ConstantVal.matchesPin_ren hf hcv (ConstantVal.good_of_noIds hpin)

theorem EnvRelG.good_role {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') (r : Role) :
    ∀ c, env.find? (roleKey r) = some c → c.Good P :=
  fun c hc => hE.good (roleKey r) c trivial hc

/-- Close `match env'.find? k' with … = match env.find? k with …` where the
alternatives compare the stored constant's common data with a pin. `hrw`
rewrites the renamed lookup, `hgood` gives the stored constant's goodness. -/
macro "pin_find " hrw:term ", " disc:term ", " hgood:term : tactic => `(tactic| (
  rw [$hrw:term]
  rcases hc : $disc with _ | c
  · rfl
  · have hgc := $hgood c hc
    rcases c with ⟨v⟩ | ⟨v, e, h⟩ | ⟨v, e⟩ | ⟨v, caps⟩ | ⟨v, a, b⟩ | ⟨v, a, b, rules⟩ | ⟨t⟩ <;>
      simp only [Option.map_some, ConstantInfo.mapKeys.eq_1, ConstantInfo.mapKeys.eq_2,
        ConstantInfo.mapKeys.eq_3, ConstantInfo.mapKeys.eq_4, ConstantInfo.mapKeys.eq_5,
        ConstantInfo.mapKeys.eq_6, ConstantInfo.mapKeys.eq_7] <;>
      first
      | rfl
      | exact matchesPin_pin_ren (EnvRelG.inj ‹_›) (ConstantInfo.Good.toConstantVal hgc) rfl rfl))

/-- `pin_find` where the pattern also fixes two numerals. -/
macro "pin_find " hrw:term ", " disc:term ", " hgood:term ", " p:term ", " q:term : tactic =>
  `(tactic| (
  rw [$hrw:term]
  rcases hc : $disc with _ | c
  · rfl
  · have hgc := $hgood c hc
    rcases c with ⟨v⟩ | ⟨v, e, h⟩ | ⟨v, e⟩ | ⟨v, caps⟩ | ⟨v, a, b⟩ | ⟨v, a, b, rules⟩ | ⟨t⟩ <;>
      simp only [Option.map_some, ConstantInfo.mapKeys.eq_1, ConstantInfo.mapKeys.eq_2,
        ConstantInfo.mapKeys.eq_3, ConstantInfo.mapKeys.eq_4, ConstantInfo.mapKeys.eq_5,
        ConstantInfo.mapKeys.eq_6, ConstantInfo.mapKeys.eq_7] <;>
      first
      | rfl
      | (by_cases ha : a = $p <;> by_cases hb : b = $q
         · subst ha hb
           simp only
           exact matchesPin_pin_ren (EnvRelG.inj ‹_›) (ConstantInfo.Good.toConstantVal hgc) rfl rfl
         all_goals simp [ha, hb])))

/-- Conjunctions with equal conjuncts. -/
theorem andC {a a' b b' : Bool} (h₁ : a = a') (h₂ : b = b') : (a && b) = (a' && b') := by
  rw [h₁, h₂]

theorem stdAxiomOk_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {cvA : ConstantVal md} (hcv : cvA.Good P) :
    stdAxiomOk env' (cvA.mapKeys f) = stdAxiomOk env cvA := by
  unfold stdAxiomOk
  have e1 : (cvA.mapKeys f).name = propextName ↔ cvA.name = propextName := by simp
  have e2 : (cvA.mapKeys f).name = choiceName ↔ cvA.name = choiceName := by simp
  have hq : decide (env'.find? eqName = some eqA) = decide (env.find? eqName = some eqA) :=
    find_eq_pin_ren hE (k := eqName) (pin := eqA) trivial rfl
  by_cases c1 : cvA.name = propextName
  · rw [if_pos (e1.2 c1), if_pos c1]
    refine andC (andC (andC (andC hq ?_) ?_) ?_) ?_
    · pin_find hE.find_role .iff, env.find? (roleKey .iff), hE.good_role .iff
    · pin_find hE.find_role .iffIntro, env.find? (roleKey .iffIntro), hE.good_role .iffIntro, 2, 2
    · pin_find hE.find_role .iffRec, env.find? (roleKey .iffRec), hE.good_role .iffRec, 4, 4
    · exact matchesPin_pin_ren hE.inj hcv rfl rfl
  · rw [if_neg (fun h => c1 (e1.1 h)), if_neg c1]
    by_cases c2 : cvA.name = choiceName
    · rw [if_pos (e2.2 c2), if_pos c2]
      refine andC (andC (andC ?_ ?_) ?_) ?_
      · pin_find hE.find_role .nonempty, env.find? (roleKey .nonempty), hE.good_role .nonempty
      · pin_find hE.find_role .nonemptyIntro, env.find? (roleKey .nonemptyIntro),
          hE.good_role .nonemptyIntro, 1, 1
      · pin_find hE.find_role .nonemptyRec, env.find? (roleKey .nonemptyRec),
          hE.good_role .nonemptyRec, 3, 3
      · exact matchesPin_pin_ren hE.inj hcv rfl rfl
    · rw [if_neg (fun h => c2 (e2.1 h)), if_neg c2]

end Ix.Kernel
