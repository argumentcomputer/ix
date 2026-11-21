module

public import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateExtJ
public import IxC.Kernel.Inductives.StructInstall
public import IxC.Kernel.Inductives.StructParts
import IxC.Kernel.Verify.Inductives.FixParts
import IxC.Kernel.Verify.Inductives.StructWF
import IxC.Kernel.Verify.Denote.IndFrame
import IxC.Kernel.Verify.InferLemmas

@[expose] public section

/-!
# A native install with its recursor, split at the recursor

A with-recursor native record (`DeclNativeRunJ`) and the two steps of the late route, the
install without a recursor (`DeclNativeNoRecRunJ`) followed by a recursor for the stored
family (`DeclNativeRecLateRunJ`), compared at the record's own data.

* **What decides the table** (`checkNativeTable_pure`, `checkNativeTable_cons_table`): the
  table stage conses nothing, at every environment, exactly off a structure-like block (one
  stored constructor, no index); at a structure-like block a successful stage conses the
  family's table.
* **Off a structure-like block** (`declNativeRunJ_split`): the record is the no-recursor
  install at the same parts followed by the late step for the block's recursor record, and
  the two output environments are the same environment. The record's field sorts at a large
  eliminator of a propositional family are read at the former's environment and the late
  step reads them at the constructors'; that one crossing needs the package's inference and
  sort judgements to weaken along an extension.
* **At a structure-like block** (`declNativeRunJ_struct`): the record stores its table above
  its recursor, so no late step ends at its environment. The no-recursor install conses the
  same table over the constructors and the family stays stored there. The late step over
  that table yields the same lookups as the record (a different list), and holds as soon as
  the recursor's stage and the field sorts are given above the table; the record gives both
  only below it, at an environment the table's does not extend (`EnvExt` fails at the
  family's own table).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr Key Level ConstantVal ConstantInfo IndCaps InductiveShape NativeParts
  RecRule EnvExt consSumCtors nativeCaps nativeCapsAt openPisAtFvars projTableName)

/-! ## Lists -/

theorem getLast?_cons_of_some {α : Type} {a r : α} :
    ∀ {l : List α}, l.getLast? = some r → (a :: l).getLast? = some r
  | [], h => by simp at h
  | _ :: _, h => by first | exact h | simp_all

theorem eq_singleton_of_length_eq_one {α : Type} :
    ∀ {l : List α}, l.length = 1 → ∃ a, l = [a]
  | [a], _ => ⟨a, rfl⟩
  | [], h => by simp at h
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-! ## The block's recursor record -/

/-- `sumSplit` reads the block's last member as its recursor record. -/
theorem sumSplit_getLast? :
    ∀ {l : List (ConstantInfo md)} {cs : List (ConstantVal md × Nat × Nat)} {cvR : ConstantVal md}
      {mI rP : Nat} {rules : List (RecRule md)}, Ix.Kernel.sumSplit l = some (cs, cvR, mI, rP, rules) →
      l.getLast? = some (.recInfo cvR mI rP rules)
  | [.recInfo _ _ _ _], _, _, _, _, _, h => by
    simp only [Ix.Kernel.sumSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  | .ctorInfo _ _ _ :: _, _, _, _, _, _, h => by
    simp only [Ix.Kernel.sumSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, q⟩, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact getLast?_cons_of_some (sumSplit_getLast? hq)
  | [], _, _, _, _, _, h => nomatch h
  | .recInfo _ _ _ _ :: _ :: _, _, _, _, _, _, h => nomatch h
  | .axiomInfo _ :: _, _, _, _, _, _, h => nomatch h
  | .defnInfo _ _ _ :: _, _, _, _, _, _, h => nomatch h
  | .thmInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .indInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .projInfo _ :: _, _, _, _, _, _, h => nomatch h

/-- **The recogniser's record and the block's recursor record**: the record's recursor, its
right-hand sides and its constructors are the block's, and its pin is the structural pin of
the block's recursor record. -/
theorem nativeParts?_rec {nPd : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (h : Ix.Kernel.nativeParts? nPd block = some p₀) :
    ∃ (cvT : ConstantVal md) (caps : IndCaps md) (rest : List (ConstantInfo md))
      (cs : List (ConstantVal md × Nat × Nat)) (cvR : ConstantVal md) (mI rP : Nat)
      (rules : List (RecRule md)),
      block = .indInfo cvT caps :: rest ∧ Ix.Kernel.sumSplit rest = some (cs, cvR, mI, rP, rules) ∧
      p₀.cvR = cvR ∧ p₀.rhss = rules.map (fun r : RecRule md => r.rhs) ∧
      p₀.ctors = cs.map (fun c => (c.1, c.2.2)) ∧
      p₀.recPinned = Ix.Kernel.nativeRecPinOk p₀.toInductiveShape block := by
  simp only [Ix.Kernel.nativeParts?, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  unfold Ix.Kernel.nativeShape? at hs
  split at hs
  · rename_i cvT caps rest
    split at hs
    · rename_i cs cvR mI rP rules hsplit
      have key : s.cvR = cvR ∧ s.rhss = rules.map (fun r : RecRule md => r.rhs) ∧
          s.ctors = cs.map fun c => (c.1, c.2.2) := by
        repeat' split at hs
        all_goals first
          | (simp only at hs; subst hs; exact ⟨rfl, rfl, rfl⟩)
          | (simp at hs; obtain ⟨-, rfl⟩ := hs; exact ⟨rfl, rfl, rfl⟩)
          | (simp at hs; obtain ⟨-, hs⟩ := hs
             split at hs <;> (simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩))
          | (simp at hs)
      exact ⟨cvT, caps, rest, cs, cvR, mI, rP, rules, rfl, hsplit, key.1, key.2.1, key.2.2, rfl⟩
    · exact nomatch hs
  · exact nomatch hs

/-! ## What decides the table -/

/-- **Off a structure-like block the table stage is the identity**, at every environment:
`checkNativeTable` matches one stored constructor, one sort list and no index, and returns
its input otherwise. -/
theorem checkNativeTable_pure {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} (h : ¬ (ctorsA.length = 1 ∧ p.nIdx = 0)) (X : Env md) :
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X := by
  unfold Ix.Kernel.checkNativeTable
  split
  · split
    · next hI => exact (h ⟨rfl, beq_iff_eq.mp hI⟩).elim
    · rfl
  · rfl

/-- The table stage at one constructor and no index is the structure route's table. -/
theorem checkNativeTable_one {p : NativeParts md} {cA : ConstantVal md × Nat}
    {sorts : List Level} (hI : p.nIdx = 0) (X : Env md) :
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p [cA] [sorts] X =
      Ix.Kernel.checkStructProjTable p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        (Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 X := by
  simp [Ix.Kernel.checkNativeTable, hI]

/-- **At a structure-like block a successful table stage conses the family's table.** -/
theorem checkNativeTable_cons_table {p : NativeParts md} {cA : ConstantVal md × Nat}
    {sorts : List Level} {X Y : Env md} (hI : p.nIdx = 0)
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p [cA] [sorts] X = .ok Y) :
    ∃ tbl : Ix.Kernel.ProjTable md, tbl.structName = p.cvT.name ∧
      Y = ⟨.projInfo tbl :: X.consts⟩ := by
  rw [checkNativeTable_one hI] at h
  obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
  exact ⟨_, rfl, rfl⟩

/-- The structure route's table stage runs wherever its bodies are scoped and its names free. -/
theorem checkStructProjTable_of {Y : Env md} {T C : Key md} {lps : List LevelParam}
    {nP nF : Nat} {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal md}
    {bodies : Array (Expr md)}
    (hb : Ix.Kernel.structProjBodies T nP nF cvCa.type = some bodies)
    (hsc : bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined lps && b.constsResolve Y &&
        b.looseBVarsBounded (nP + 1)) = true)
    (hfn : (List.range nF).all (fun j => (Y.find? (Ix.Kernel.projFnName T j)).isNone) = true)
    (ht : Y.find? (projTableName T) = none) :
    Ix.Kernel.checkStructProjTable (m := Ix.Kernel.CheckM md) T C lps nP nF rs guards off cvCa Y
      = .ok ⟨.projInfo ⟨T, lps, nP, C, nF, rs, bodies, guards, off⟩ :: Y.consts⟩ := by
  unfold Ix.Kernel.checkStructProjTable
  simp [hb, Ix.Kernel.unwrapOr, hfn, ht]
  split
  all_goals first
    | rfl
    | (rename_i hn; exact absurd (by simpa using hsc) hn)

/-! ## Resolution of the projection bodies -/

theorem constsResolve_liftLooseBVars {env : Env md} (n : Nat) :
    ∀ (e : Expr md) (c : Nat),
      (Ix.Kernel.Expr.liftLooseBVars n c e).constsResolve env = e.constsResolve env := by
  intro e
  induction e with
  | bvar _ =>
    intro _
    simp only [Ix.Kernel.Expr.liftLooseBVars]
    split <;> rfl
  | lit _ => intro _; rfl
  | _ => intro c; simp_all [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.constsResolve]

theorem constsResolve_instantiate1Lift {env : Env md} {v : Expr md}
    (hv : v.constsResolve env = true) :
    ∀ (e : Expr md) (d : Nat), e.constsResolve env = true →
      (e.instantiate1Lift v d).constsResolve env = true := by
  intro e
  induction e with
  | bvar _ =>
    intro _ _
    simp only [Ix.Kernel.Expr.instantiate1Lift]
    split
    · rw [constsResolve_liftLooseBVars]; exact hv
    · split <;> rfl
  | lit _ => intro _ h; exact h
  | _ => intro d h; simp_all [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.constsResolve]

theorem constsResolve_instPisAtLift {env : Env md} {as : List (Expr md)}
    (ha : ∀ a ∈ as, a.constsResolve env = true) :
    ∀ {e r : Expr md}, e.constsResolve env = true → Ix.Kernel.Expr.instPisAtLift as e = some r →
      r.constsResolve env = true := by
  induction as with
  | nil =>
    intro e r he h
    simp only [Ix.Kernel.Expr.instPisAtLift, Option.some.injEq] at h
    subst h; exact he
  | cons a as ih =>
    intro e r he h
    cases e with
    | forallE _ body _ =>
      simp only [Ix.Kernel.Expr.instPisAtLift] at h
      simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at he
      exact ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (constsResolve_instantiate1Lift (ha a List.mem_cons_self) body 0 he.2) h
    | _ => exact nomatch h

theorem constsResolve_structProjBodiesGo {env : Env md} {T : Key md}
    (hT : (env.find? T).isSome = true) :
    ∀ (k i : Nat) (r : Expr md) (bs : List (Expr md)), r.constsResolve env = true →
      Ix.Kernel.structProjBodiesGo T k i r = some bs → ∀ b ∈ bs, b.constsResolve env = true := by
  intro k
  induction k with
  | zero =>
    intro _ _ bs _ h b hb
    simp only [Ix.Kernel.structProjBodiesGo, Option.some.injEq] at h
    subst h; exact nomatch hb
  | succ k ih =>
    intro i r bs hr h b hb
    cases r with
    | forallE _ body _ =>
      simp only [Ix.Kernel.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hr
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hr.1
      · refine ih (i + 1) _ bs' (constsResolve_instantiate1Lift ?_ body 0 hr.2) hbs' b hb'
        simp [Ix.Kernel.structProjArgP, Ix.Kernel.Expr.constsResolve, hT]
    | _ => exact nomatch h

/-- **The projection bodies resolve where the constructor's type and the family do.** -/
theorem constsResolve_structProjBodies {env : Env md} {T : Key md} {nP nF : Nat}
    {cty : Expr md} {bodies : Array (Expr md)} (hT : (env.find? T).isSome = true)
    (hc : cty.constsResolve env = true)
    (h : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    ∀ b ∈ bodies, b.constsResolve env = true := by
  unfold Ix.Kernel.structProjBodies at h
  split at h
  · next r hr =>
    obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
    have hr' := constsResolve_instPisAtLift (as := Ix.Kernel.structProjPs nP) (fun a ha => by
      simp only [Ix.Kernel.structProjPs, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      rfl) hc hr
    intro b hb
    exact constsResolve_structProjBodiesGo hT nF 0 r bs hr' hbs b (by simpa using hb)
  · exact nomatch h

theorem constsResolve_ext {E E' : Env md} (hx : EnvExt E E') {e : Expr md}
    (h : e.constsResolve E = true) : e.constsResolve E' = true :=
  Ix.Kernel.Expr.constsResolve_le (fun n hn => by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    simp [hx.find hc]) h

/-! ## Lookups across a table's cons -/

/-- A stored constructor is found at the constructors' conses. -/
theorem consSumCtors_find?_ctorOf {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {env : Env md}, (ctorsA.map (·.1.name)).Nodup →
      ∀ cA ∈ ctorsA, (consSumCtors nP ctorsA env).find? cA.1.name
        = some (.ctorInfo cA.1 nP cA.2)
  | [], _, _, _, h => nomatch h
  | _ :: _, _, hnd, cA, hcA => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Ix.Kernel.consSumCtors]
    rcases List.mem_cons.mp hcA with rfl | hcA'
    · rw [consSumCtors_find?_of_not_mem hnd.1]
      exact Ix.Kernel.Env.find?_cons_self _ _
    · exact consSumCtors_find?_ctorOf hnd.2 cA hcA'

theorem find?_none_below_cons {E : Env md} {c : ConstantInfo md} {k : Key md}
    (h : Env.find? (⟨c :: E.consts⟩ : Env md) k = none) : E.find? k = none := by
  rw [Ix.Kernel.Env.find?_cons] at h
  split at h
  · exact nomatch h
  · exact h

/-- Two conses of different names commute for every lookup. -/
theorem find?_cons_comm {E : Env md} {a b : ConstantInfo md} (hne : a.name ≠ b.name)
    (k : Key md) :
    Env.find? (⟨a :: (⟨b :: E.consts⟩ : Env md).consts⟩ : Env md) k =
      Env.find? (⟨b :: (⟨a :: E.consts⟩ : Env md).consts⟩ : Env md) k := by
  rw [Ix.Kernel.Env.find?_cons (env := (⟨b :: E.consts⟩ : Env md)),
    Ix.Kernel.Env.find?_cons (env := (⟨a :: E.consts⟩ : Env md)),
    Ix.Kernel.Env.find?_cons (env := E) (c := b), Ix.Kernel.Env.find?_cons (env := E) (c := a)]
  by_cases ha : a.name = k <;> by_cases hb : b.name = k <;> simp_all

/-- A lookup that differs from another at one key only, where the one finds nothing and the
other a projection table, reads the same K bit: the bit reads constructor and inductive
records only. -/
theorem recRuleKOf_table {f g : Key md → Option (ConstantInfo md)} {k₀ : Key md}
    {t : Ix.Kernel.ProjTable md} (hfg : ∀ k, k ≠ k₀ → g k = f k) (hf : f k₀ = none)
    (hg : g k₀ = some (.projInfo t)) (c : Key md) :
    Ix.Kernel.recRuleKOf g c = Ix.Kernel.recRuleKOf f c := by
  unfold Ix.Kernel.recRuleKOf
  by_cases hc : c = k₀
  · subst hc
    rw [hf, hg] <;> rfl
  · rw [hfg c hc]
    cases f c with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cvj _ _ =>
        dsimp only
        generalize cvj.type.piResult.getAppFn = hd
        cases hd with
        | const T _ =>
          dsimp only
          by_cases hT : T = k₀
          · subst hT
            rw [hf, hg] <;> rfl
          · rw [hfg T hT]
        | _ => rfl
      | _ => rfl

/-- The same for the η bit. -/
theorem recRuleEtaOf_table {f g : Key md → Option (ConstantInfo md)} {k₀ : Key md}
    {t : Ix.Kernel.ProjTable md} (hfg : ∀ k, k ≠ k₀ → g k = f k) (hf : f k₀ = none)
    (hg : g k₀ = some (.projInfo t)) (recName c : Key md) :
    Ix.Kernel.recRuleEtaOf g recName c = Ix.Kernel.recRuleEtaOf f recName c := by
  unfold Ix.Kernel.recRuleEtaOf
  by_cases hc : c = k₀
  · subst hc
    rw [hf, hg] <;> rfl
  · rw [hfg c hc]
    cases f c with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cvj _ _ =>
        dsimp only
        generalize cvj.type.piResult.getAppFn = hd
        cases hd with
        | const T _ =>
          dsimp only
          by_cases hT : T = k₀
          · subst hT
            rw [hf, hg] <;> rfl
          · rw [hfg T hT]
        | _ => rfl
      | _ => rfl

theorem recRuleBits_table {f g : Key md → Option (ConstantInfo md)} {k₀ : Key md}
    {t : Ix.Kernel.ProjTable md} (hfg : ∀ k, k ≠ k₀ → g k = f k) (hf : f k₀ = none)
    (hg : g k₀ = some (.projInfo t)) (recName : Key md) (rl : RecRule md) :
    Ix.Kernel.recRuleBits g recName rl = Ix.Kernel.recRuleBits f recName rl := by
  unfold Ix.Kernel.recRuleBits
  rw [recRuleKOf_table hfg hf hg, recRuleEtaOf_table hfg hf hg]

/-- **The generated rules are the same across a table's cons.** -/
theorem sumRules_table {f g : Key md → Option (ConstantInfo md)} {k₀ : Key md}
    {t : Ix.Kernel.ProjTable md} (hfg : ∀ k, k ≠ k₀ → g k = f k) (hf : f k₀ = none)
    (hg : g k₀ = some (.projInfo t)) (recName : Key md) (nP mI rP : Nat) (recTy : Expr md) :
    ∀ (cs : List (ConstantVal md × Nat)) (rhss : List (Expr md)),
      Ix.Kernel.sumRules g recName nP mI rP recTy cs rhss =
        Ix.Kernel.sumRules f recName nP mI rP recTy cs rhss
  | c :: cs, rhs :: rhss => by
    simp only [Ix.Kernel.sumRules]
    rw [recRuleBits_table hfg hf hg, sumRules_table hfg hf hg recName nP mI rP recTy cs rhss]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-! ## The family's facts -/

/-- What the store holds of a family is kept by a fresh cons (a table's included). -/
theorem NativeFamStored.cons {env : Env md} {fam : NativeFam md} {c : ConstantInfo md}
    (hfresh : env.find? c.name = none) (h : NativeFamStored env fam) :
    NativeFamStored ⟨c :: env.consts⟩ fam where
  former := Ix.Kernel.Env.find?_cons_of_fresh hfresh h.former
  ctor j cA hj := ⟨Ix.Kernel.Env.find?_cons_of_fresh hfresh (h.ctor j cA hj).1, (h.ctor j cA hj).2⟩
  lenA := h.lenA
  lenK := h.lenK

/-- A record whose recursor is the declared one, whose right-hand sides are the declared ones
and whose pin is granted is the recursor record of its own summary. -/
theorem NativeFam.recParts_self {p : NativeParts md} {cvS cvTa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)} {cvR : ConstantVal md} {rhs₀ : List (Expr md)}
    (hR : p.cvR = cvR) (hrhs : p.rhss = rhs₀) (hpin : p.recPinned = true) :
    p = (⟨p, cvS, cvTa, ctorsA⟩ : NativeFam md).recParts cvR p.elim p.large rhs₀ := by
  subst hR hrhs
  obtain ⟨sh, kinds, pin⟩ := p
  obtain rfl : pin = true := hpin
  rfl

/-- The fields' sorts weaken with the package's inference and sort judgements. -/
theorem FieldSortsJ.weaken {J : Judgements md}
    (hinf : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {a t : Expr md},
      J.infer e d a t → J.infer e' d a t)
    (hsrt : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {t : Expr md} {u : Level},
      J.sort e d t u → J.sort e' d t u)
    {e e' : Env md} (hx : EnvExt e e') {isProp large : Bool} {s : Level} {nP : Nat}
    {fvs idxArgs : List (Expr md)} {n : Nat} {sorts : List Level}
    (h : FieldSortsJ J e isProp large s nP fvs idxArgs n sorts) :
    FieldSortsJ J e' isProp large s nP fvs idxArgs n sorts := by
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, h1, h2, h3, h4, h5, h6⟩ := hall i hi
  exact ⟨fv, ty, u, h1, h2, hinf hx h3, hsrt hx h4, h5, h6⟩

/-! ## The record at its own data -/

/-- The environment a late recursor step builds over `E`: the recursor consed with its
generated rules, at the family's record (`DeclNativeRecLateRunJ`'s last conjunct). -/
def lateRecEnv (E : Env md) (fam : NativeFam md) (cvRa : ConstantVal md)
    (rhss : List (Expr md)) : Env md :=
  ⟨.recInfo cvRa fam.p.majorIdx fam.p.rulePrefix
    (Ix.Kernel.sumRules E.find? cvRa.name fam.p.nP fam.p.majorIdx fam.p.rulePrefix cvRa.type
      fam.ctorsA rhss) :: E.consts⟩

/-- **What a with-recursor native record gives the late route**, at its own data: the
former's environment `envF`, the completed record `p`, the stored former `cvS`, the
telescope constant `cvTa`, the stored constructors and their sorts, the recursor stored and
its rules, and the block's recursor record `cvR mI rP rules`. -/
structure LateFront (J : Judgements md) (env : Env md) (p₀ : NativeParts md)
    (block : List (ConstantInfo md)) (envF : Env md) (p : NativeParts md)
    (cvS cvTa : ConstantVal md) (ctorsA : List (ConstantVal md × Nat))
    (sortss : List (List Level)) (cvRa : ConstantVal md) (rhss : List (Expr md))
    (cvR : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)) : Prop where
  /-- the block's recursor record is its last member -/
  last : block.getLast? = some (.recInfo cvR mI rP rules)
  /-- the install without a recursor, at the record's parts, up to its table stage -/
  noRec : ∀ X : Env md, Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
    (consSumCtors p.nP ctorsA envF) = .ok X → DeclNativeNoRecRunJ J env p₀ X
  /-- the family as stored at the constructors' environment -/
  stored : NativeFamStored (consSumCtors p.nP ctorsA envF) ⟨p, cvS, cvTa, ctorsA⟩
  /-- the record is the recursor record of its own summary at the declared recursor -/
  recParts : p = (⟨p, cvS, cvTa, ctorsA⟩ : NativeFam md).recParts cvR p.elim p.large
    (rules.map fun r : RecRule md => r.rhs)
  pinMI : mI = p.majorIdx
  pinRP : rP = p.rulePrefix
  pinLen : rules.length = ctorsA.length
  pins : ∀ (j : Nat) (r : RecRule md) (cA : ConstantVal md × Nat), rules[j]? = some r →
    ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2
  wl : p.large = true →
    (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ ctorsA.length < 2
  /-- the fields' sorts at a large eliminator of a propositional family, at `envF` -/
  sorts : p.large = true → p.isProp = true →
    ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      ∃ (fvsP : List (Expr md)) (crest : Expr md) (xFvs : List (Expr md)) (xrest : Expr md)
        (sorts : List Level),
        openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
        openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
        FieldSortsJ J envF true true p.resSort p.nP xFvs (xrest.getAppArgs.drop p.nP) cA.2 sorts
  /-- the recursor's stage and the recursor stored, at the constructors' environment -/
  recJ : NativeRecJ J (consSumCtors p.nP ctorsA envF) p cvTa ctorsA cvRa rhss
  ext : EnvExt envF (consSumCtors p.nP ctorsA envF)
  lenC : ctorsA.length = p₀.ctors.length
  lenS : sortss.length = p₀.ctors.length
  idx0 : p.nIdx = p₀.nIdx
  ctorRes : ∀ cA ∈ ctorsA, cA.1.type.constsResolve envF = true
  formerF : (envF.find? p.cvT.name).isSome = true

set_option maxHeartbeats 1600000 in
/-- **The record's stages give the late route's facts**, at the record's own data (the
former's environment written with its stored former, as `declNativeCoreJ` takes it). -/
theorem lateFront_of {J : Judgements md} {env : Env md} {nPd : Nat}
    {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    {isRec : Bool} {envF : Env md} {cvS cvTa : ConstantVal md} {caps : IndCaps md}
    {p₁ : InductiveShape md} {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {kinds : List (List RecFieldKind)}
    {cvRa : ConstantVal md} {rhss : List (Expr md)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    (henvF : envF = ⟨.indInfo cvS caps :: env.consts⟩)
    (hnd₀ : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ J env p₀.toInductiveShape (fun p₁ => nativeCapsAt p₁ isRec) envF cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ J envF envF p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hK : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams
      p.nP p.nIdx ctorsA = .ok kinds)
    (hcaps : nativeCaps p = nativeCapsAt p₁ isRec)
    (hwl : p.large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ p.ctors.length < 2)
    (hopT : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest))
    (hsorts : FieldSortsJ J envF true false p.resSort p.nP (tfvs.drop p.nP) [] p.nIdx isorts)
    (hFOk : Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true)
    (hRec : NativeRecJ J (consSumCtors p.nP ctorsA envF) p cvTa ctorsA cvRa rhss)
    (hFR : FormerReadJ envF p cvTa ctorsA) :
    ∃ (cvR : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
      LateFront J env p₀ block envF p cvS cvTa ctorsA sortss cvRa rhss cvR mI rP rules := by
  -- the recognised parts and the block's recursor record
  obtain ⟨-, hClps₀, -, -⟩ := Ix.Kernel.nativeShape?_inv (Ix.Kernel.nativeParts?_inv hdp).1
  obtain ⟨_, _, _, cs, cvR, mI, rP, rules, hblock, hsplit, hcvR, hrhs, hcs, hpin₀⟩ :=
    nativeParts?_rec hdp
  -- the completed record's projections are the recognised parts'
  obtain ⟨_, _, -, -, -, hp₁, ⟨cvS', henvF', hSt⟩, -⟩ := hInd.shape
  obtain ⟨hTn, hTl, -, -⟩ := hInd.former
  have hpT : p.cvT = p₀.cvT := by subst hp hp₁; rfl
  have hpC : p.ctors = p₀.ctors := by subst hp hp₁; rfl
  have hpP : p.nP = p₀.nP := by subst hp hp₁; rfl
  have hpI : p.nIdx = p₀.nIdx := by subst hp hp₁; rfl
  have hpR : p.cvR = p₀.cvR := by subst hp hp₁; rfl
  have hpH : p.rhss = p₀.rhss := by subst hp hp₁; rfl
  have hpPin : p.recPinned = p₀.recPinned := by subst hp hp₁; rfl
  -- the stored former
  obtain ⟨hSn, -⟩ := hSt.name_lps ⟨hTn, hTl⟩
  have hcvS := ConstantInfo.indInfo.inj
    (List.cons.inj (congrArg Env.consts (henvF'.symm.trans henvF))).1
  obtain ⟨hS1, -⟩ := hcvS
  subst cvS'
  have hfT₁ : envF.find? p.cvT.name = some (.indInfo cvS (nativeCapsAt p₁ isRec)) := by
    rw [henvF', hpT, ← hTn, ← hSn]
    exact Ix.Kernel.Env.find?_cons_self _ _
  -- the constructors
  have hlen : ctorsA.length = p.ctors.length := hCtors.1
  have hcf : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal md × Nat, p.ctors[j]? = some c ∧ cA.2 = c.2 ∧
        ∃ sorts, sortss[j]? = some sorts ∧
          SumCtorRunJ J envF envF p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
            p.large c.1 c.2 cvTa cA.1 sorts := by
    intro j cA hj
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨hnF, sorts, hs, hrun⟩ :=
      hCtors.2.2 j (p.ctors[j]) cA (List.getElem?_eq_getElem hj') hj
    exact ⟨_, List.getElem?_eq_getElem hj', hnF, sorts, hs, hrun⟩
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hCtors.2.2 j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hndA : (ctorsA.map (·.1.name)).Nodup := by rw [hnames, hpC]; exact hnd₀
  have hfreshC : ∀ c ∈ ctorsA, envF.find? c.1.name = none ∧ c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨_, -, -, _, -, hrun⟩ := hcf j c hj
    obtain ⟨hCn, -, hfC, hshC⟩ := hrun.names
    rw [hCn]; exact ⟨hfC, hshC⟩
  have hext : EnvExt envF (consSumCtors p.nP ctorsA envF) :=
    EnvExt.consSumCtors_over (Ix.Kernel.EnvExt.refl envF) (fun c hc => (hfreshC c hc).1) hndA
      (fun c hc => (hfreshC c hc).2)
  have hTnot : p.cvT.name ∉ ctorsA.map (·.1.name) := by
    intro hm
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    have h1 := (hfreshC c hc).1
    rw [he, hfT₁] at h1
    exact nomatch h1
  -- the family, as stored at the constructors' environment
  have hstored : NativeFamStored (consSumCtors p.nP ctorsA envF) ⟨p, cvS, cvTa, ctorsA⟩ := by
    refine ⟨?_, ?_, hlen, nativeFieldsOk_length hFOk⟩
    · show (consSumCtors p.nP ctorsA envF).find? p.cvT.name = some (.indInfo cvS (nativeCaps p))
      rw [consSumCtors_find?_of_not_mem hTnot, hfT₁, hcaps]
    · intro j cA hj
      obtain ⟨c, hc, hnF, _, -, hrun⟩ := hcf j cA hj
      obtain ⟨-, hClp, -, -⟩ := hrun.names
      have hmemC : c ∈ p₀.ctors := by rw [← hpC]; exact List.mem_of_getElem? hc
      refine ⟨consSumCtors_find?_ctorOf hndA cA (List.mem_of_getElem? hj), ?_, ?_⟩
      · show cA.1.levelParams = p.cvT.levelParams
        rw [hClp, (hClps₀ c hmemC).1, hpT]
      · obtain ⟨-, ⟨cbs, es, hstrip, hes⟩, -⟩ := hrun
        exact ⟨cbs, es, by rw [hnF]; exact hstrip, hes⟩
  -- the block's recursor record's pins (the record's own, granted at the recursor's stage)
  have hpinT : p.recPinned = true := by
    obtain ⟨_, _, hRR, _⟩ := id hRec
    exact hRR.2.1
  have hpinOk : Ix.Kernel.nativeRecPinOk p₀.toInductiveShape block = true := by
    rw [← hpin₀, ← hpPin]; exact hpinT
  rw [hblock] at hpinOk
  simp only [Ix.Kernel.nativeRecPinOk, hsplit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hpinOk
  obtain ⟨⟨⟨hrP, hmI⟩, hlenR⟩, hrl⟩ := hpinOk
  have hlenR' : rules.length = ctorsA.length := by rw [hlenR, hlen, hpC]
  have hpins : ∀ (j : Nat) (r : RecRule md) (cA : ConstantVal md × Nat), rules[j]? = some r →
      ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2 := by
    intro j r cA hr hcA
    obtain ⟨_, hc, hnF, _, -, hrun⟩ := hcf j cA hcA
    have hjR : j < rules.length := (List.getElem?_eq_some_iff.mp hr).1
    rw [hpC, hcs, List.getElem?_map] at hc
    obtain ⟨⟨cvC, _, nFc⟩, hc₀, rfl⟩ := Option.map_eq_some_iff.mp hc
    have h1 := hrl j (by rw [← hlenR]; exact hjR)
    rw [hr, hc₀] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨h1.1.trans hrun.names.1.symm, h1.2.trans hnF.symm⟩
  have hmI' : mI = p.majorIdx := by
    rw [hmI]
    show p₀.nP + 1 + p₀.ctors.length + p₀.nIdx = p.nP + 1 + p.ctors.length + p.nIdx
    rw [hpP, hpC, hpI]
  have hrP' : rP = p.rulePrefix := by
    rw [hrP]
    show p₀.nP + 1 + p₀.ctors.length = p.nP + 1 + p.ctors.length
    rw [hpP, hpC]
  -- the elimination restriction and the fields' sorts
  have hwl' : p.large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ ctorsA.length < 2 := by
    intro hl
    rcases hwl hl with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hlen]; exact h)
  have hsorts' : p.large = true → p.isProp = true →
      ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
        ∃ (fvsP : List (Expr md)) (crest : Expr md) (xFvs : List (Expr md)) (xrest : Expr md)
          (sorts : List Level),
          openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
          openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
          FieldSortsJ J envF true true p.resSort p.nP xFvs (xrest.getAppArgs.drop p.nP) cA.2
            sorts := by
    intro hl hpp j cA hj
    obtain ⟨_, -, hnF, sorts, -, hrun⟩ := hcf j cA hj
    obtain ⟨-, -, fvsP, crest, -, -, xFvs, idxArgs, hopP, -, -, hopF, -, -, -, hFS⟩ := hrun
    have hlenP := Ix.Kernel.Verify.openPisAtFvars_length p.nP hopP
    have hidx : (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP ++ idxArgs)).getAppArgs.drop p.nP = idxArgs := by
      rw [Ix.Kernel.Expr.getAppArgs_mkAppN]
      simp only [Ix.Kernel.Expr.getAppArgs, List.nil_append]
      simpa only [hlenP] using List.drop_left (l₁ := fvsP) (l₂ := idxArgs)
    refine ⟨fvsP, crest, xFvs,
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param)) (fvsP ++ idxArgs), sorts,
      hopP, by rw [hnF]; exact hopF, ?_⟩
    rw [hidx, hnF]
    rw [hl, hpp] at hFS
    exact hFS
  -- the constructors' types resolve at the former's environment
  have hctorRes : ∀ cA ∈ ctorsA, cA.1.type.constsResolve envF = true := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨_, -, -, _, -, hrun⟩ := hcf j cA hj
    obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, htr, -⟩, heq⟩ := hrun.check
    rw [heq]; exact htr
  have hfF : (envF.find? p.cvT.name).isSome = true := by simp [hfT₁]
  refine ⟨cvR, mI, rP, rules, ?_⟩
  exact {
    last := by rw [hblock]; exact getLast?_cons_of_some (sumSplit_getLast? hsplit)
    noRec := fun X hX => ⟨hnd₀, isRec, envF, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest,
      isorts, hInd, hp, hCtors, hK, hcaps, hopT, hsorts, hFOk, hX, hFR⟩
    stored := hstored
    recParts := NativeFam.recParts_self (hpR.trans hcvR) (hpH.trans hrhs) hpinT
    pinMI := hmI'
    pinRP := hrP'
    pinLen := hlenR'
    pins := hpins
    wl := hwl'
    sorts := hsorts'
    recJ := hRec
    ext := hext
    lenC := by rw [hlen, hpC]
    lenS := by rw [hCtors.2.1, hpC]
    idx0 := hpI
    ctorRes := hctorRes
    formerF := hfF }

/-- `lateFront_of` at a with-recursor record. -/
theorem DeclNativeRunJ.lateFront {J : Judgements md} {env env₂ : Env md} {nPd : Nat}
    {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (h : DeclNativeRunJ J env p₀ env₂) (hdp : Ix.Kernel.nativeParts? nPd block = some p₀) :
    ∃ (envF : Env md) (p : NativeParts md) (cvS cvTa : ConstantVal md)
      (ctorsA : List (ConstantVal md × Nat)) (sortss : List (List Level)) (cvRa : ConstantVal md)
      (rhss : List (Expr md)) (cvR : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
      LateFront J env p₀ block envF p cvS cvTa ctorsA sortss cvRa rhss cvR mI rP rules ∧
      Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
        ⟨.recInfo cvRa p.majorIdx p.rulePrefix
          (Ix.Kernel.sumRules (consSumCtors p.nP ctorsA envF).find? cvRa.name p.nP p.majorIdx
            p.rulePrefix cvRa.type ctorsA rhss)
          :: (consSumCtors p.nP ctorsA envF).consts⟩ = .ok env₂ := by
  obtain ⟨hnd, isRec, envF, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest, isorts,
    hInd, hp, hCtors, hK, hcaps, hwl, hopT, hsorts, hFOk, hRec, hTbl, hFR⟩ := h
  obtain ⟨_, _, -, -, -, -, ⟨cvS, henvF, -⟩, -⟩ := hInd.shape
  obtain ⟨cvR, mI, rP, rules, hF⟩ := lateFront_of hdp henvF hnd hInd hp hCtors hK hcaps hwl hopT
    hsorts hFOk hRec hFR
  exact ⟨envF, p, cvS, cvTa, ctorsA, sortss, cvRa, rhss, cvR, mI, rP, rules, hF, hTbl⟩

/-! ## Off a structure-like block -/

/-- **The two steps of the late route, off a structure-like block**: at a block whose table
stage conses nothing, the record's facts are the no-recursor install at the constructors'
environment and the late step from there, ending at the record's own environment. -/
theorem LateFront.late {J : Judgements md}
    (hinf : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {a t : Expr md},
      J.infer e d a t → J.infer e' d a t)
    (hsrt : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {t : Expr md} {u : Level},
      J.sort e d t u → J.sort e' d t u)
    {env env₂ : Env md} {p₀ : NativeParts md} {block : List (ConstantInfo md)} {envF : Env md}
    {p : NativeParts md} {cvS cvTa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {cvRa : ConstantVal md} {rhss : List (Expr md)}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hF : LateFront J env p₀ block envF p cvS cvTa ctorsA sortss cvRa rhss cvR mI rP rules)
    (hnt : ¬ (p₀.ctors.length = 1 ∧ p₀.nIdx = 0))
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (Ix.Kernel.sumRules (consSumCtors p.nP ctorsA envF).find? cvRa.name p.nP p.majorIdx
          p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA envF).consts⟩ = .ok env₂) :
    DeclNativeNoRecRunJ J env p₀ (consSumCtors p.nP ctorsA envF) ∧
      DeclNativeRecLateRunJ J (consSumCtors p.nP ctorsA envF) ⟨p, cvS, cvTa, ctorsA⟩ cvR mI rP
        rules env₂ := by
  have hnt' : ¬ (ctorsA.length = 1 ∧ p.nIdx = 0) := by rw [hF.lenC, hF.idx0]; exact hnt
  have hpure := checkNativeTable_pure (sortss := sortss) hnt'
  have henv₂ := Except.ok.inj ((hpure _).symm.trans hTbl)
  refine ⟨hF.noRec _ (hpure _), p.elim, p.large, p, cvRa, rhss, hF.recParts, hF.pinMI, hF.pinRP,
    hF.pinLen, hF.pins, hF.stored, hF.wl, ?_, hF.recJ, henv₂.symm⟩
  intro hl hpp j cA hj
  obtain ⟨fvsP, crest, xFvs, xrest, sorts, h1, h2, h3⟩ := hF.sorts hl hpp j cA hj
  exact ⟨fvsP, crest, xFvs, xrest, sorts, h1, h2, FieldSortsJ.weaken hinf hsrt hF.ext h3⟩

/-- **A with-recursor native install off a structure-like block is the no-recursor install
followed by the late recursor step**, for the block's own recursor record, with the same
output environment. The package's inference and sort judgements weaken along an extension
(the record reads a large propositional eliminator's field sorts at the former's environment,
the late step at the constructors'). -/
theorem declNativeRunJ_split {J : Judgements md}
    (hinf : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {a t : Expr md},
      J.infer e d a t → J.infer e' d a t)
    (hsrt : ∀ {e e' : Env md}, EnvExt e e' → ∀ {d : Nat} {t : Expr md} {u : Level},
      J.sort e d t u → J.sort e' d t u)
    {env env₂ : Env md} {nPd : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hnt : ¬ (p₀.ctors.length = 1 ∧ p₀.nIdx = 0))
    (h : DeclNativeRunJ J env p₀ env₂) :
    ∃ (fam : NativeFam md) (env₁ : Env md) (cvR : ConstantVal md) (mI rP : Nat)
      (rules : List (RecRule md)),
      block.getLast? = some (.recInfo cvR mI rP rules) ∧
      DeclNativeNoRecRunJ J env p₀ env₁ ∧
      NativeFamStored env₁ fam ∧
      DeclNativeRecLateRunJ J env₁ fam cvR mI rP rules env₂ := by
  obtain ⟨envF, p, cvS, cvTa, ctorsA, sortss, cvRa, rhss, cvR, mI, rP, rules, hF, hTbl⟩ :=
    h.lateFront hdp
  obtain ⟨hN, hL⟩ := hF.late hinf hsrt hnt hTbl
  exact ⟨⟨p, cvS, cvTa, ctorsA⟩, _, cvR, mI, rP, rules, hF.last, hN, hF.stored, hL⟩

/-! ## At a structure-like block -/

set_option maxHeartbeats 1600000 in
/-- **At a structure-like block the record does not split.** The record stores its table
above its recursor, so no late step ends at its environment. What does hold: the no-recursor
install conses the same table over the constructors and the family stays stored; the late
step's environment over that table has the record's lookups (a different list); and the late
step holds there given exactly two facts above the table, the recursor's stage and (at a large
eliminator of a propositional family) the field sorts. The record gives both only below the
table, at the constructors' environment, which the table's environment does not extend: the
table is the family's own (`EnvExt.tables`). -/
theorem declNativeRunJ_struct {J : Judgements md} {env env₂ : Env md} {nPd : Nat}
    {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hst : p₀.ctors.length = 1 ∧ p₀.nIdx = 0) (h : DeclNativeRunJ J env p₀ env₂) :
    ∃ (fam : NativeFam md) (envC : Env md) (tbl : Ix.Kernel.ProjTable md) (cvR : ConstantVal md)
      (mI rP : Nat) (rules : List (RecRule md)) (cvRa : ConstantVal md) (rhss : List (Expr md)),
      block.getLast? = some (.recInfo cvR mI rP rules) ∧
      tbl.structName = fam.p.cvT.name ∧
      env₂ = ⟨.projInfo tbl :: (lateRecEnv envC fam cvRa rhss).consts⟩ ∧
      (∀ (E : Env md) (fam' : NativeFam md) (cvR' : ConstantVal md) (mI' rP' : Nat)
        (rules' : List (RecRule md)), ¬ DeclNativeRecLateRunJ J E fam' cvR' mI' rP' rules' env₂) ∧
      DeclNativeNoRecRunJ J env p₀ ⟨.projInfo tbl :: envC.consts⟩ ∧
      NativeFamStored ⟨.projInfo tbl :: envC.consts⟩ fam ∧
      NativeRecJ J envC fam.p fam.cvTa fam.ctorsA cvRa rhss ∧
      ¬ EnvExt envC ⟨.projInfo tbl :: envC.consts⟩ ∧
      (∀ k, (lateRecEnv ⟨.projInfo tbl :: envC.consts⟩ fam cvRa rhss).find? k = env₂.find? k) ∧
      lateRecEnv ⟨.projInfo tbl :: envC.consts⟩ fam cvRa rhss ≠ env₂ ∧
      (NativeRecJ J ⟨.projInfo tbl :: envC.consts⟩ fam.p fam.cvTa fam.ctorsA cvRa rhss →
        (fam.p.large = true → fam.p.isProp = true →
          ∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
            ∃ (fvsP : List (Expr md)) (crest : Expr md) (xFvs : List (Expr md))
              (xrest : Expr md) (sorts : List Level),
              openPisAtFvars fam.p.nP cA.1.type 0 = some (fvsP, crest) ∧
              openPisAtFvars cA.2 crest fam.p.nP = some (xFvs, xrest) ∧
              FieldSortsJ J ⟨.projInfo tbl :: envC.consts⟩ true true fam.p.resSort fam.p.nP xFvs
                (xrest.getAppArgs.drop fam.p.nP) cA.2 sorts) →
        DeclNativeRecLateRunJ J ⟨.projInfo tbl :: envC.consts⟩ fam cvR mI rP rules
          (lateRecEnv ⟨.projInfo tbl :: envC.consts⟩ fam cvRa rhss)) := by
  obtain ⟨envF, p, cvS, cvTa, ctorsA, sortss, cvRa, rhss, cvR, mI, rP, rules, hF, hTbl⟩ :=
    h.lateFront hdp
  obtain ⟨cA, rfl⟩ := eq_singleton_of_length_eq_one (hF.lenC.trans hst.1)
  obtain ⟨sorts, rfl⟩ := eq_singleton_of_length_eq_one (hF.lenS.trans hst.1)
  have hI : p.nIdx = 0 := hF.idx0.trans hst.2
  -- the record's table, above its recursor
  rw [checkNativeTable_one hI] at hTbl
  obtain ⟨bodies, hb, hsc, hfn, htn, henv₂⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
  -- its names are free at the constructors' environment too
  have htn' : (consSumCtors p.nP [cA] envF).find? (projTableName p.cvT.name) = none :=
    find?_none_below_cons htn
  have hfn' : (List.range cA.2).all (fun j =>
      ((consSumCtors p.nP [cA] envF).find? (Ix.Kernel.projFnName p.cvT.name j)).isNone) = true :=
    List.all_eq_true.mpr fun j hj => Option.isNone_iff_eq_none.mpr
      (find?_none_below_cons (Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hfn j hj)))
  -- its bodies resolve there: they are read off the constructor's type
  have hbres : ∀ b ∈ bodies, b.constsResolve envF = true :=
    constsResolve_structProjBodies hF.formerF (hF.ctorRes cA List.mem_cons_self) hb
  have hsc' : bodies.size = cA.2 ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined p.cvT.levelParams &&
      b.constsResolve (consSumCtors p.nP [cA] envF) &&
      b.looseBVarsBounded (p.nP + 1)) = true := by
    refine ⟨hsc.1, Array.all_eq_true_iff_forall_mem.mpr fun b hbm => ?_⟩
    have h1 := (Array.all_eq_true_iff_forall_mem.mp hsc.2) b hbm
    simp only [Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨h1.1.1, constsResolve_ext hF.ext (hbres b hbm)⟩, h1.2⟩
  -- the no-recursor install conses the same table over the constructors
  have hTblC : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p [cA] [sorts]
      (consSumCtors p.nP [cA] envF) =
      .ok ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
        Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
        (consSumCtors p.nP [cA] envF).consts⟩ := by
    rw [checkNativeTable_one hI]
    exact checkStructProjTable_of hb hsc' hfn' htn'
  have hstored' := NativeFamStored.cons
    (c := .projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
      Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩) htn' hF.stored
  -- the table's environment does not extend the constructors'
  have hnotExt : ¬ EnvExt (consSumCtors p.nP [cA] envF)
      ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
        Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
        (consSumCtors p.nP [cA] envF).consts⟩ := by
    intro hx
    have h1 := hx.tables hF.stored.former
    have h2 : Env.find? (⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2,
        p.resSort, bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
        (consSumCtors p.nP [cA] envF).consts⟩ : Env md) (projTableName p.cvT.name) =
        some (.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
          Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩) :=
      Ix.Kernel.Env.find?_cons_self _ _
    rw [h2, htn'] at h1
    exact nomatch h1
  -- no late step ends at the record's environment: its head is the table
  have hnoLate : ∀ (E : Env md) (fam' : NativeFam md) (cvR' : ConstantVal md) (mI' rP' : Nat)
      (rules' : List (RecRule md)), ¬ DeclNativeRecLateRunJ J E fam' cvR' mI' rP' rules' env₂ := by
    intro _ _ _ _ _ _ hL
    obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, he⟩ := hL
    rw [henv₂] at he
    have := congrArg (fun e : Env md => e.consts.head?) he
    simp at this
  -- the late step's environment over the table: the record's lookups
  obtain ⟨hnR, -, -, hshR⟩ := hF.recJ.recursor
  have hfg : ∀ k, k ≠ projTableName p.cvT.name →
      Env.find? (⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort,
        bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
        (consSumCtors p.nP [cA] envF).consts⟩ : Env md) k
        = (consSumCtors p.nP [cA] envF).find? k := by
    intro k hk
    rw [Ix.Kernel.Env.find?_cons, if_neg (fun h => hk h.symm)]
  have hrules := sumRules_table hfg htn' (Ix.Kernel.Env.find?_cons_self _ _) cvRa.name p.nP
    p.majorIdx p.rulePrefix cvRa.type [cA] rhss
  have hL : lateRecEnv ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2,
      p.resSort, bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
      (consSumCtors p.nP [cA] envF).consts⟩ ⟨p, cvS, cvTa, [cA]⟩ cvRa rhss =
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix (Ix.Kernel.sumRules
        (consSumCtors p.nP [cA] envF).find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type [cA]
        rhss) :: (⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort,
          bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
          (consSumCtors p.nP [cA] envF).consts⟩ : Env md).consts⟩ := by
    unfold lateRecEnv
    exact congrArg (fun rs => (⟨.recInfo cvRa p.majorIdx p.rulePrefix rs ::
      (⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
        Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
        (consSumCtors p.nP [cA] envF).consts⟩ : Env md).consts⟩ : Env md)) hrules
  have hlook : ∀ k, (lateRecEnv ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name,
      cA.2, p.resSort, bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
      (consSumCtors p.nP [cA] envF).consts⟩ ⟨p, cvS, cvTa, [cA]⟩ cvRa rhss).find? k =
      env₂.find? k := by
    intro k
    rw [hL, henv₂]
    refine find?_cons_comm ?_ k
    intro he
    exact ne_projTableName_of_shape hshR p.cvT.name (hnR.symm.trans he)
  have hneq : lateRecEnv ⟨.projInfo ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2,
      p.resSort, bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩ ::
      (consSumCtors p.nP [cA] envF).consts⟩ ⟨p, cvS, cvTa, [cA]⟩ cvRa rhss ≠ env₂ := by
    rw [hL, henv₂]
    intro he
    have := congrArg (fun e : Env md => e.consts.head?) he
    simp at this
  refine ⟨⟨p, cvS, cvTa, [cA]⟩, consSumCtors p.nP [cA] envF,
    ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
      Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩,
    cvR, mI, rP, rules, cvRa, rhss, hF.last, rfl, henv₂, hnoLate, hF.noRec _ hTblC, hstored',
    hF.recJ, hnotExt, hlook, hneq, ?_⟩
  intro hRec' hfs'
  exact ⟨p.elim, p.large, p, cvRa, rhss, hF.recParts, hF.pinMI, hF.pinRP, hF.pinLen, hF.pins,
    hstored', hF.wl, hfs', hRec', rfl⟩

end Ix.Kernel.Semantics
