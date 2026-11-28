module

public import IxCK.Kernel.Model.StoreArKeep
public import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateSplitJ
public import IxCK.Kernel.Verify.Inductives.StructWF

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Arity-correct stored terms along a native block's install

The install of a native family without its recursor (`DeclNativeNoRecRunJ`) stores the former,
the constructors and, at a structure-like block, the projection table. The former's and the
constructors' types were checked at the full grade (`arRes_of_cvCheck`); the table's bodies are
generated off the constructor's type (`structProjBodies`): parameters replaced by variables, each
earlier field by the subject's projection, so they apply only the constants the constructor's
type applies (`arOk_structProjBodies`), and the install checks their resolution.
`storeArR_nativeNoRec`: the install keeps `StoreArR`.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel (Env Key Expr ConstantInfo ConstantVal RecRule ProjTable NativeParts Level
  LevelParam EnvExt)

/-! ## The projection bodies -/

theorem arOk_liftLooseBVars {env : Env md} (n : Nat) :
    ∀ (e : Expr md) (c : Nat),
      Expr.arOk env (Ix.Kernel.Expr.liftLooseBVars n c e) = Expr.arOk env e := by
  intro e
  induction e with
  | bvar _ =>
    intro _
    simp only [Ix.Kernel.Expr.liftLooseBVars]
    split <;> rfl
  | lit _ => intro _; rfl
  | _ => intro c; simp_all [Ix.Kernel.Expr.liftLooseBVars, Expr.arOk]

theorem arOk_instantiate1Lift {env : Env md} {v : Expr md} (hv : Expr.arOk env v = true) :
    ∀ (e : Expr md) (d : Nat), Expr.arOk env e = true →
      Expr.arOk env (e.instantiate1Lift v d) = true := by
  intro e
  induction e with
  | bvar _ =>
    intro _ _
    simp only [Ix.Kernel.Expr.instantiate1Lift]
    split
    · rw [arOk_liftLooseBVars]; exact hv
    · split <;> rfl
  | lit _ => intro _ h; exact h
  | _ => intro d h; simp_all [Ix.Kernel.Expr.instantiate1Lift, Expr.arOk]

theorem arOk_instPisAtLift {env : Env md} {as : List (Expr md)}
    (ha : ∀ a ∈ as, Expr.arOk env a = true) :
    ∀ {e r : Expr md}, Expr.arOk env e = true → Ix.Kernel.Expr.instPisAtLift as e = some r →
      Expr.arOk env r = true := by
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
      simp only [Expr.arOk, Bool.and_eq_true] at he
      exact ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (arOk_instantiate1Lift (ha a List.mem_cons_self) body 0 he.2) h
    | _ => exact nomatch h

theorem arOk_structProjBodiesGo {env : Env md} {T : Key md} :
    ∀ (k i : Nat) (r : Expr md) (bs : List (Expr md)), Expr.arOk env r = true →
      Ix.Kernel.structProjBodiesGo T k i r = some bs → ∀ b ∈ bs, Expr.arOk env b = true := by
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
      simp only [Expr.arOk, Bool.and_eq_true] at hr
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hr.1
      · exact ih (i + 1) _ bs'
          (arOk_instantiate1Lift (v := Ix.Kernel.structProjArgP T i) rfl body 0 hr.2) hbs' b hb'
    | _ => exact nomatch h

/-- **The projection bodies apply only the constants the constructor's type applies.** -/
theorem arOk_structProjBodies {env : Env md} {T : Key md} {nP nF : Nat}
    {cty : Expr md} {bodies : Array (Expr md)}
    (hc : Expr.arOk env cty = true)
    (h : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    ∀ b ∈ bodies, Expr.arOk env b = true := by
  unfold Ix.Kernel.structProjBodies at h
  split at h
  · next r hr =>
    obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
    have hr' := arOk_instPisAtLift (as := Ix.Kernel.structProjPs nP) (fun a ha => by
      simp only [Ix.Kernel.structProjPs, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      rfl) hc hr
    intro b hb
    exact arOk_structProjBodiesGo nF 0 r bs hr' hbs b (by simpa using hb)
  · exact nomatch h

theorem ConstArR.of_proj {env : Env md} {tbl : ProjTable md}
    (hb : ∀ (i : Nat) (b : Expr md), tbl.bodies[i]? = some b → ArRes env b) :
    ConstArR env (.projInfo tbl) where
  type := ⟨rfl, rfl⟩
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => nomatch he
  proj := fun _ he => by cases he; exact hb

/-! ## The stages -/

/-- **The constructors' conses keep `StoreArR`**, each fresh, of distinct names, at types
arity-correct where they start. -/
theorem storeArR_consSumCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {X : Env md}, StoreArR X →
      (∀ c ∈ ctorsA, X.find? c.1.name = none) → (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, ArRes X c.1.type) →
      StoreArR (Ix.Kernel.consSumCtors nP ctorsA X)
  | [], X, h, _, _, _ => h
  | c :: cs, X, h, hfresh, hnd, hty => by
    simp only [Ix.Kernel.consSumCtors]
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hfc : X.find? c.1.name = none := hfresh c List.mem_cons_self
    have h' : StoreArR ⟨.ctorInfo c.1 nP c.2 :: X.consts⟩ :=
      storeArR_cons h hfc
        (ConstArR.of_ctor ((hty c List.mem_cons_self).mono (find?_cons_fresh_ext hfc)))
        (fun ⟨_, _, _, he⟩ => nomatch he)
    refine storeArR_consSumCtors h' ?_ hnd.2 ?_
    · intro c' hc'
      rw [Ix.Kernel.Env.find?_cons]
      split
      · next heq =>
        exfalso
        apply hnd.1
        rw [List.mem_map]
        exact ⟨c', hc', heq.symm⟩
      · exact hfresh c' (List.mem_cons_of_mem _ hc')
    · intro c' hc'
      exact (hty c' (List.mem_cons_of_mem _ hc')).mono (find?_cons_fresh_ext hfc)

/-- **The table stage keeps `StoreArR`**, where the constructors' types are arity-correct. -/
theorem storeArR_nativeTable {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {X X₂ : Env md} (h : StoreArR X)
    (hty : ∀ c ∈ ctorsA, Expr.arOk X c.1.type = true)
    (hrun : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss X = .ok X₂) :
    StoreArR X₂ := by
  unfold Ix.Kernel.checkNativeTable at hrun
  split at hrun
  · split at hrun
    · obtain ⟨bodies, hb, ⟨-, hall⟩, -, hfreshT, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hrun
      refine storeArR_cons h hfreshT (ConstArR.of_proj (fun i b hbi => ?_))
        (fun ⟨_, _, _, he⟩ => nomatch he)
      have hmem : b ∈ bodies := Array.mem_of_getElem? hbi
      have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hmem
      simp only [Bool.and_eq_true] at hb'
      refine ArRes.mono (find?_cons_fresh_ext hfreshT) ⟨?_, hb'.1.2⟩
      refine arOk_structProjBodies ?_ hb b hmem
      first
        | exact hty _ (by simp)
        | exact hty _ (by simp_all)
    · obtain rfl := Except.ok.inj hrun
      exact h
  · obtain rfl := Except.ok.inj hrun
    exact h

/-! ## The install -/

/-- **A native family's install without its recursor keeps `StoreArR`.** -/
theorem storeArR_nativeNoRec {env env₂ : Env md} {p₀ : NativeParts md}
    (h : StoreArR env) (hrun : DeclNativeNoRecRunJ rulesJ env p₀ env₂) : StoreArR env₂ := by
  obtain ⟨hnd₀, isRec, envF, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp, hCtors,
    -, -, -, -, -, hTbl, -⟩ := hrun
  obtain ⟨cvTa₀, s, bs, cvS, hck₀, hck, -, hSt, hp₁, henvF⟩ := hInd
  -- the former
  have hSn : cvS.name = p₀.toInductiveShape.cvT.name := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · rcases hck with rfl | ⟨ty, hck'⟩
      · exact hck₀.name_eq
      · exact hck'.name_eq
    · exact hck₀.name_eq
  have hSa : ArRes env cvS.type := by
    rcases hSt with rfl | ⟨rfl, -, -⟩
    · rcases hck with rfl | ⟨ty, hck'⟩
      · exact arRes_of_cvCheck hck₀
      · exact arRes_of_cvCheck hck'
    · exact arRes_of_cvCheck hck₀
  have hSf : env.find? cvS.name = none := by
    rw [hSn]
    exact hck₀.fresh
  have hF : StoreArR envF := by
    subst henvF
    exact storeArR_cons h hSf (ConstArR.of_ind (hSa.mono (find?_cons_fresh_ext hSf)))
      (fun ⟨_, _, _, he⟩ => nomatch he)
  -- the constructors
  have hpC : p.ctors = p₀.ctors := by subst hp hp₁; rfl
  have hlen : ctorsA.length = p.ctors.length := hCtors.1
  have hcf : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal md × Nat, p.ctors[j]? = some c ∧
        ∃ sorts, SumCtorRunJ rulesJ envF envF p.cvT.name p.cvT.levelParams p.nP p.nIdx
          p.resSort p.isProp p.large c.1 c.2 cvTa cA.1 sorts := by
    intro j cA hj
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, sorts, -, hrun⟩ :=
      hCtors.2.2 j (p.ctors[j]) cA (List.getElem?_eq_getElem hj') hj
    exact ⟨_, List.getElem?_eq_getElem hj', sorts, hrun⟩
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
    obtain ⟨_, -, _, hrun⟩ := hcf j c hj
    obtain ⟨hCn, -, hfC, hshC⟩ := hrun.names
    rw [hCn]
    exact ⟨hfC, hshC⟩
  have hCa : ∀ cA ∈ ctorsA, ArRes envF cA.1.type := by
    intro cA hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨c, -, sorts, hrun⟩ := hcf j cA hj
    obtain ⟨⟨cvCa₀, hck0, hor⟩, -⟩ := hrun
    rcases hor with heq | ⟨ty', hck'⟩
    · rw [heq]
      exact arRes_of_cvCheck hck0
    · exact arRes_of_cvCheck hck'
  have hC : StoreArR (Ix.Kernel.consSumCtors p.nP ctorsA envF) :=
    storeArR_consSumCtors hF (fun c hc => (hfreshC c hc).1) hndA hCa
  have hextC : EnvExt envF (Ix.Kernel.consSumCtors p.nP ctorsA envF) :=
    Ix.Kernel.Semantics.EnvExt.consSumCtors_over (Ix.Kernel.EnvExt.refl envF)
      (fun c hc => (hfreshC c hc).1) hndA (fun c hc => (hfreshC c hc).2)
  -- the table
  exact storeArR_nativeTable hC (fun c hc => ((hCa c hc).mono hextC.find).ar) hTbl

end Ix.Kernel.Model
