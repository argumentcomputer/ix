module

public import IxCK.Kernel.Model.StoreArNative
public import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateJ
public import IxCK.Kernel.Semantics.Inductives.WrapRelFacts
public import IxCK.Kernel.Verify.Inductives.FixInv

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Arity-correct stored terms along a late recursor's install

A recursor installed for a stored native family (`DeclNativeRecLateRunJ`) stores the recursor
at the generated type (`structRecTyR`) with the generated rules (`checkNativeRules`, rules from
`structRecRhsR`), or at the declared type, checked, with the declared rules, which are the
generated ones up to consumed type-annotation wrappers (`WrapRel`) and carry no `let`.

* The generators apply only the family at its own level parameters, the constructors at the
  family's, the recursor at its own, and pieces of the telescope constant's type and of the
  constructors' types (`arP_structRecTyR`, `arP_structRecRhsR`, mirroring the key-scope lemmas
  `structRecTyR_good`, `structRecRhsR_good` of `Verify/Rename/Ind3.lean`). `ArP` is `Expr.arOk`
  as a proposition (`arP_iff`).
* The telescope constant is not recorded at the late step; the registry has it as the stored
  former (`htele : fam.cvTa = fam.cvS`), whose type `StoreArR` makes arity-correct.
* A declared rule is a generated one up to wrappers: `arRes_of_wrapRel`.
* The recursor is re-stored with its rules at the same level parameters: `arRes_mono_len`.

`storeArR_nativeRecLate`: the late step keeps `StoreArR`.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.LevelRen
open Ix.Kernel (Env Key Expr ConstantInfo ConstantVal RecRule ProjTable NativeParts Level
  LevelParam EnvExt BinderMeta PropWhen RecFieldKind)

/-! ## Arity as a proposition -/

/-- `Expr.arOk` as a proposition, by the term's structure. -/
@[simp] def ArP (E : Env md) : Expr md → Prop
  | .bvar _ => True
  | .fvar _ t => ArP E t
  | .sort _ => True
  | .const n us => ∀ ci, E.find? n = some ci → us.length = ci.toConstantVal.levelParams.length
  | .app a b => ArP E a ∧ ArP E b
  | .lam t b _ => ArP E t ∧ ArP E b
  | .forallE t b _ => ArP E t ∧ ArP E b
  | .letE t v b _ => ArP E t ∧ ArP E v ∧ ArP E b
  | .lit _ => True
  | .proj _ _ e => ArP E e

theorem arP_iff {E : Env md} : ∀ (e : Expr md), ArP E e ↔ Expr.arOk E e = true := by
  intro e
  induction e with
  | bvar _ => simp [ArP, Expr.arOk]
  | sort _ => simp [ArP, Expr.arOk]
  | lit _ => simp [ArP, Expr.arOk]
  | fvar _ t ih => simp only [ArP, Expr.arOk]; exact ih
  | const c us =>
    simp only [ArP, Expr.arOk]
    cases hf : E.find? c with
    | none => simp
    | some ci => simp
  | app f a ihf iha => simp only [ArP, Expr.arOk, Bool.and_eq_true, ihf, iha]
  | lam t b _ iht ihb => simp only [ArP, Expr.arOk, Bool.and_eq_true, iht, ihb]
  | forallE t b _ iht ihb => simp only [ArP, Expr.arOk, Bool.and_eq_true, iht, ihb]
  | letE t v b _ iht ihv ihb =>
    simp only [ArP, Expr.arOk, Bool.and_eq_true, iht, ihv, ihb, and_assoc]
  | proj _ _ e ih => simp only [ArP, Expr.arOk]; exact ih

section Gen

variable {E : Env md}

theorem ArP.liftLooseBVars {e : Expr md} (h : ArP E e) (n c : Nat) :
    ArP E (Ix.Kernel.Expr.liftLooseBVars n c e) := by
  rw [arP_iff, arOk_liftLooseBVars]
  exact (arP_iff e).mp h

theorem ArP.mkAppN {f : Expr md} {as : List (Expr md)} (hf : ArP E f)
    (has : ∀ a ∈ as, ArP E a) : ArP E (Expr.mkAppN f as) := by
  rw [arP_iff]
  exact arOk_mkAppN as ((arP_iff f).mp hf) (fun a ha => (arP_iff a).mp (has a ha))

theorem ArP.getAppArgs {e : Expr md} (h : ArP E e) : ∀ a ∈ e.getAppArgs, ArP E a :=
  fun a ha => (arP_iff a).mpr (arOk_getAppArgs ((arP_iff e).mp h) a ha)

/-- Every binder domain of a list is arity-correct. -/
def BindersAr (E : Env md) (bs : List (Expr md × BinderMeta)) : Prop := ∀ b ∈ bs, ArP E b.1

theorem BindersAr.getD {bs : List (Expr md × BinderMeta)} (h : BindersAr E bs) (i : Nat) :
    ArP E (bs.getD i default).1 := by
  simp only [List.getD_eq_getElem?_getD]
  cases hb : bs[i]? with
  | none => exact (show ArP E (default : Expr md) from trivial)
  | some b => exact h b (List.mem_of_getElem? hb)

theorem arP_stripPis : ∀ {k : Nat} {e : Expr md} {bs : List (Expr md × BinderMeta)}
    {b : Expr md}, ArP E e → Expr.stripPis k e = some (bs, b) → BindersAr E bs ∧ ArP E b
  | 0, e, bs, b, he, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => (nomatch h), he⟩
  | k + 1, .forallE ty body m, bs, b, he, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨bs₀, b₀⟩, h₀, rfl, rfl⟩ := h
    simp only [ArP] at he
    obtain ⟨hbs, hb⟩ := arP_stripPis he.2 h₀
    refine ⟨?_, hb⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he.1
    · exact hbs x hx
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h =>
    nomatch h

theorem arP_piBinders : ∀ {e : Expr md}, ArP E e →
    BindersAr E (Ix.Kernel.Expr.piBinders e).1 ∧ ArP E (Ix.Kernel.Expr.piBinders e).2
  | .forallE ty b m, he => by
    simp only [ArP] at he
    obtain ⟨h1, h2⟩ := arP_piBinders he.2
    refine ⟨?_, h2⟩
    intro x hx
    simp only [Ix.Kernel.Expr.piBinders, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he.1
    · exact h1 x hx
  | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he
  | .lam _ _ _, he | .letE _ _ _ _, he | .lit _, he | .proj _ _ _, he =>
    ⟨fun _ h => (nomatch h), he⟩

theorem arP_replacePisPw (pw : PropWhen) :
    ∀ {k : Nat} {e b r : Expr md}, ArP E e → ArP E b → Ix.Kernel.Expr.replacePisPw pw k e b = some r →
      ArP E r
  | 0, _, _, _, _, hb, h => by
    simp only [Ix.Kernel.Expr.replacePisPw, Option.some.injEq] at h; exact h ▸ hb
  | k + 1, .forallE ty rest m, b, r, he, hb, h => by
    simp only [Ix.Kernel.Expr.replacePisPw, Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨he.1, arP_replacePisPw pw he.2 hb h₀⟩
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

theorem arP_pisToLamsPw (pw : PropWhen) :
    ∀ {k : Nat} {e b r : Expr md}, ArP E e → ArP E b → Ix.Kernel.Expr.pisToLamsPw pw k e b = some r →
      ArP E r
  | 0, _, _, _, _, hb, h => by
    simp only [Ix.Kernel.Expr.pisToLamsPw, Option.some.injEq] at h; exact h ▸ hb
  | k + 1, .forallE ty rest m, b, r, he, hb, h => by
    simp only [Ix.Kernel.Expr.pisToLamsPw, Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨he.1, arP_pisToLamsPw pw he.2 hb h₀⟩
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

theorem arP_mkPisOf : ∀ {bs : List (Expr md × BinderMeta)} {b : Expr md},
    BindersAr E bs → ArP E b → ArP E (Ix.Kernel.Expr.mkPisOf bs b)
  | [], _, _, hb => hb
  | (t, m) :: bs, b, hbs, hb => by
    simp only [Ix.Kernel.Expr.mkPisOf, ArP]
    exact ⟨hbs (t, m) (List.mem_cons_self ..),
      arP_mkPisOf (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hb⟩

theorem arP_mkLamsOf : ∀ {bs : List (Expr md × BinderMeta)} {b : Expr md},
    BindersAr E bs → ArP E b → ArP E (Ix.Kernel.Expr.mkLamsOf bs b)
  | [], _, _, hb => hb
  | (t, m) :: bs, b, hbs, hb => by
    simp only [Ix.Kernel.Expr.mkLamsOf, ArP]
    exact ⟨hbs (t, m) (List.mem_cons_self ..),
      arP_mkLamsOf (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hb⟩

/-! ## The generators -/

theorem arP_structFamI {T : Key md} {lps : List LevelParam}
    (hT : ArP E (.const T (lps.map .param))) (nP nIdx e o : Nat) :
    ArP E (Ix.Kernel.structFamI T lps nP nIdx e o) := by
  refine ArP.mkAppN hT ?_
  intro x hx
  simp only [Ix.Kernel.structPsAt, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

theorem arP_structCtorSpineAt {C : Key md} {lps : List LevelParam}
    (hC : ArP E (.const C (lps.map .param))) (o nP nF : Nat) :
    ArP E (Ix.Kernel.structCtorSpineAt C lps o nP nF) := by
  refine ArP.mkAppN hC ?_
  intro e he
  simp only [Ix.Kernel.structPsAt, List.mem_append, List.mem_map] at he
  rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

theorem arP_structMotiveTyI {T : Key md} {lps : List LevelParam}
    (hT : ArP E (.const T (lps.map .param))) {nP nIdx : Nat} {ℓ : Level} {itele r : Expr md}
    (hi : ArP E itele) (h : Ix.Kernel.structMotiveTyI T lps nP nIdx ℓ itele = some r) :
    ArP E r :=
  arP_replacePisPw _ hi (show ArP E (Expr.forallE _ (.sort ℓ) _) from
    ⟨arP_structFamI hT _ _ _ _, trivial⟩) h

theorem arP_structIdxAt {e : Expr md} (he : ArP E e) (nF o i l m : Nat) :
    ArP E (Ix.Kernel.structIdxAt nF o i l m e) :=
  (he.liftLooseBVars _ _).liftLooseBVars _ _

theorem arP_structTeleAt {tele : List (Expr md × BinderMeta)} (h : BindersAr E tele)
    (nF o i l : Nat) (pw : PropWhen) : BindersAr E (Ix.Kernel.structTeleAt nF o i l pw tele) := by
  intro x hx
  simp only [Ix.Kernel.structTeleAt, List.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact arP_structIdxAt (h.getD k) _ _ _ _ _

theorem arP_structTeleVars (m : Nat) :
    ∀ x ∈ (Ix.Kernel.structTeleVars m : List (Expr md)), ArP E x := by
  intro x hx
  simp only [Ix.Kernel.structTeleVars, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  trivial

theorem arP_structRecPrefixAt (nP n nF e : Nat) :
    ∀ x ∈ (Ix.Kernel.structRecPrefixAt nP n nF e : List (Expr md)), ArP E x := by
  intro x hx
  simp only [Ix.Kernel.structRecPrefixAt, Ix.Kernel.structPsAt, List.mem_append, List.mem_map,
    List.mem_singleton] at hx
  rcases hx with (⟨_, _, rfl⟩ | rfl) | ⟨_, _, rfl⟩ <;> trivial

theorem arP_structFieldTeleOf {cty : Expr md} (hc : ArP E cty) (nP nF i : Nat) :
    BindersAr E (Ix.Kernel.structFieldTeleOf cty nP nF i) := by
  unfold Ix.Kernel.structFieldTeleOf
  cases h : Ix.Kernel.Expr.stripPis (nP + nF) cty with
  | none => exact fun _ h => nomatch h
  | some r =>
    obtain ⟨hbs, _⟩ := arP_stripPis hc h
    exact (arP_piBinders (hbs.getD (nP + i))).1

theorem arP_structFieldIdxOf {cty : Expr md} (hc : ArP E cty) (nP nF i : Nat) :
    ∀ x ∈ Ix.Kernel.structFieldIdxOf cty nP nF i, ArP E x := by
  unfold Ix.Kernel.structFieldIdxOf
  cases h : Ix.Kernel.Expr.stripPis (nP + nF) cty with
  | none => exact fun _ h => nomatch h
  | some r =>
    obtain ⟨hbs, _⟩ := arP_stripPis hc h
    intro x hx
    exact (arP_piBinders (hbs.getD (nP + i))).2.getAppArgs x (List.mem_of_mem_drop hx)

theorem arP_structIhApp {recC : Key md} {rlvls : List Level} (hr : ArP E (.const recC rlvls))
    {tele : List (Expr md × BinderMeta)} (ht : BindersAr E tele) {idx : List (Expr md)}
    (hi : ∀ x ∈ idx, ArP E x) (pw : PropWhen) (nP n nF i : Nat) :
    ArP E (Ix.Kernel.structIhApp recC rlvls pw nP n nF i tele idx) := by
  refine arP_mkLamsOf (arP_structTeleAt ht _ _ _ _ _) (ArP.mkAppN hr ?_)
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with (hx | ⟨y, hy, rfl⟩) | rfl
  · exact arP_structRecPrefixAt _ _ _ _ x hx
  · exact arP_structIdxAt (hi y hy) _ _ _ _ _
  · exact ArP.mkAppN trivial (arP_structTeleVars _)

theorem arP_structRuleBodyR {recC : Key md} {rlvls : List Level} (hr : ArP E (.const recC rlvls))
    {teleOf : Nat → List (Expr md × BinderMeta)} (ht : ∀ i, BindersAr E (teleOf i))
    {idxOf : Nat → List (Expr md)} (hi : ∀ i, ∀ x ∈ idxOf i, ArP E x)
    (pw : PropWhen) (nP n nF j : Nat) (recIdx : List Nat) :
    ArP E (Ix.Kernel.structRuleBodyR recC rlvls pw nP n nF j recIdx teleOf idxOf) := by
  refine ArP.mkAppN trivial ?_
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩ | ⟨i, _, rfl⟩
  · trivial
  · exact arP_structIhApp hr (ht i) (hi i) _ _ _ _ _

theorem arP_structIhPis {teleOf : Nat → List (Expr md × BinderMeta)}
    (ht : ∀ i, BindersAr E (teleOf i)) {idxOf : Nat → List (Expr md)}
    (hi : ∀ i, ∀ x ∈ idxOf i, ArP E x) (nF o : Nat) (pw : PropWhen) :
    ∀ (is : List Nat) (l : Nat) {body : Expr md}, ArP E body →
      ArP E (Ix.Kernel.structIhPis nF o pw teleOf idxOf is l body)
  | [], _, _, hb => hb
  | i :: is, l, body, hb => by
    simp only [Ix.Kernel.structIhPis, ArP]
    refine ⟨arP_mkPisOf (arP_structTeleAt (ht i) _ _ _ _ _) (ArP.mkAppN trivial ?_),
      arP_structIhPis ht hi nF o pw is (l + 1) hb⟩
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl
    · exact arP_structIdxAt (hi i y hy) _ _ _ _ _
    · exact ArP.mkAppN trivial (arP_structTeleVars _)

theorem arP_structMinorTyR {C : Key md} {lps : List LevelParam}
    (hC : ArP E (.const C (lps.map .param))) {cty : Expr md} (hc : ArP E cty)
    {nP nF o : Nat} {pw : PropWhen} {recIdx : List Nat} {r : Expr md}
    (h : Ix.Kernel.structMinorTyR C lps nP nF o pw cty recIdx = some r) : ArP E r := by
  unfold Ix.Kernel.structMinorTyR at h
  cases h₁ : Ix.Kernel.Expr.stripPis nP cty with
  | none => rw [h₁] at h; exact nomatch h
  | some q =>
    rw [h₁] at h
    obtain ⟨_, hq⟩ := arP_stripPis hc h₁
    simp only [Option.bind_some] at h
    cases h₂ : Ix.Kernel.Expr.stripPis nF q.2 with
    | none => rw [h₂] at h; exact nomatch h
    | some s =>
      rw [h₂] at h
      obtain ⟨_, hs⟩ := arP_stripPis hq h₂
      simp only [Option.bind_some] at h
      refine arP_replacePisPw _ (hq.liftLooseBVars _ _) ?_ h
      refine arP_structIhPis (arP_structFieldTeleOf hc nP nF) (arP_structFieldIdxOf hc nP nF)
        _ _ _ _ _ (ArP.liftLooseBVars (ArP.mkAppN (f := Expr.bvar (nF + o - 1)) trivial ?_) _ _)
      intro x hx
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨y, hy, rfl⟩ | rfl
      · exact (hs.getAppArgs y (List.mem_of_mem_drop hy)).liftLooseBVars _ _
      · exact arP_structCtorSpineAt hC _ _ _

/-- The constructors the generators take are arity-correct: each at the family's level
parameters, each type. -/
def Ctors4Ar (E : Env md) (lps : List LevelParam)
    (cs : List (Key md × Nat × Expr md × List Nat)) : Prop :=
  ∀ c ∈ cs, ArP E (.const c.1 (lps.map .param)) ∧ ArP E c.2.2.1

theorem arP_structMinorsPisR {lps : List LevelParam} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List (Key md × Nat × Expr md × List Nat)} {o : Nat} {body r : Expr md},
      Ctors4Ar E lps cs → ArP E body → Ix.Kernel.structMinorsPisR lps nP pw cs o body = some r →
        ArP E r
  | [], _, _, _, _, hb, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.some.injEq] at h; exact h ▸ hb
  | (C, nF, cty, recIdx) :: cs, o, body, r, hcs, hb, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, hm, rest, hr, rfl⟩ := h
    have hc := hcs _ (List.mem_cons_self ..)
    exact ⟨arP_structMinorTyR hc.1 hc.2 hm,
      arP_structMinorsPisR (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hb hr⟩

theorem arP_structMinorsLamsR {lps : List LevelParam} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List (Key md × Nat × Expr md × List Nat)} {o : Nat} {body r : Expr md},
      Ctors4Ar E lps cs → ArP E body → Ix.Kernel.structMinorsLamsR lps nP pw cs o body = some r →
        ArP E r
  | [], _, _, _, _, hb, h => by
    simp only [Ix.Kernel.structMinorsLamsR, Option.some.injEq] at h; exact h ▸ hb
  | (C, nF, cty, recIdx) :: cs, o, body, r, hcs, hb, h => by
    simp only [Ix.Kernel.structMinorsLamsR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, hm, rest, hr, rfl⟩ := h
    have hc := hcs _ (List.mem_cons_self ..)
    exact ⟨arP_structMinorTyR hc.1 hc.2 hm,
      arP_structMinorsLamsR (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hb hr⟩

/-- **The generated recursor type is arity-correct.** -/
theorem arP_structRecTyR {T : Key md} {lps : List LevelParam} (hT : ArP E (.const T (lps.map .param)))
    {elim : LevelParam} {large : Bool} {nP nIdx : Nat} {tty : Expr md} (ht : ArP E tty)
    {ctors : List (Key md × Nat × Expr md × List Nat)} (hcs : Ctors4Ar E lps ctors) {r : Expr md}
    (h : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some r) : ArP E r := by
  unfold Ix.Kernel.structRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, mt, hmt, major, hmaj, minors, hmin, hr⟩ := h
  obtain ⟨_, hq2⟩ := arP_stripPis ht hq
  have hmtg := arP_structMotiveTyI hT hq2 hmt
  have hmajg : ArP E major := by
    refine arP_replacePisPw _ (hq2.liftLooseBVars _ _) ?_ hmaj
    simp only [ArP]
    refine ⟨arP_structFamI hT _ _ _ _, ArP.mkAppN trivial ?_⟩
    intro x hx
    simp only [Ix.Kernel.structPsAt, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨_, _, rfl⟩ | rfl <;> trivial
  have hming := arP_structMinorsPisR hcs hmajg hmin
  exact arP_replacePisPw _ ht (show ArP E (Expr.forallE _ _ _) from ⟨hmtg, hming⟩) hr

/-- **The generated rules are arity-correct.** -/
theorem arP_structRecRhsR {T : Key md} {lps : List LevelParam}
    (hT : ArP E (.const T (lps.map .param))) {elim : LevelParam} {large : Bool} {nP nIdx : Nat}
    {tty : Expr md} (ht : ArP E tty)
    {ctors : List (Key md × Nat × Expr md × List Nat)} (hcs : Ctors4Ar E lps ctors)
    {recC : Key md} {rlvls : List Level} (hr : ArP E (.const recC rlvls)) {j : Nat} {r : Expr md}
    (h : Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some r) :
    ArP E r := by
  unfold Ix.Kernel.structRecRhsR at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    rw [hj] at h
    obtain ⟨C, nF, cty, recIdx⟩ := c
    have hc := hcs _ (List.mem_of_getElem? hj)
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tq, htq, mt, hmt, q, hq, inner, hin, minors, hmin, hr'⟩ := h
    obtain ⟨_, htq2⟩ := arP_stripPis ht htq
    obtain ⟨_, hq2⟩ := arP_stripPis hc.2 hq
    have hmtg := arP_structMotiveTyI hT htq2 hmt
    have hing : ArP E inner :=
      arP_pisToLamsPw _ (hq2.liftLooseBVars _ _)
        (arP_structRuleBodyR hr (arP_structFieldTeleOf hc.2 nP nF)
          (arP_structFieldIdxOf hc.2 nP nF) _ _ _ _ _ _) hin
    have hming := arP_structMinorsLamsR hcs hing hmin
    exact arP_pisToLamsPw _ ht (show ArP E (Expr.lam _ _ _) from ⟨hmtg, hming⟩) hr'

/-- The generators' constructors are the stored constructors' names and types. -/
theorem mem_nativeCtors4 {ctorsA : List (ConstantVal md × Nat)} :
    ∀ {kinds : List (List RecFieldKind)} {c : Key md × Nat × Expr md × List Nat},
      c ∈ Ix.Kernel.nativeCtors4 ctorsA kinds → ∃ cA ∈ ctorsA, c.1 = cA.1.name ∧ c.2.2.1 = cA.1.type := by
  unfold Ix.Kernel.nativeCtors4
  induction ctorsA with
  | nil => intro kinds c hc; simp at hc
  | cons a as ih =>
    intro kinds c hc
    cases kinds with
    | nil => simp at hc
    | cons k ks =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨a, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨cA, hcA, h1, h2⟩ := ih hc
        exact ⟨cA, List.mem_cons_of_mem _ hcA, h1, h2⟩

end Gen

/-! ## Monotonicity at the same level parameters -/

theorem arOk_mono_len {env env₂ : Env md}
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci →
      ∃ ci', env₂.find? n = some ci' ∧
        ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length) :
    ∀ {e : Expr md}, e.constsResolve env = true → Expr.arOk env e = true →
      Expr.arOk env₂ e = true := by
  intro e
  induction e with
  | bvar _ => intro _ _; rfl
  | sort _ => intro _ _; rfl
  | lit _ => intro _ _; rfl
  | const c us =>
    intro hr ha
    simp only [Expr.constsResolve, Option.isSome_iff_exists] at hr
    obtain ⟨ci, hci⟩ := hr
    obtain ⟨ci', h2, hlen⟩ := hf hci
    simp only [Expr.arOk, hci, h2, beq_iff_eq] at ha ⊢
    rw [hlen]
    exact ha
  | fvar i ty ih =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk] at hr ha ⊢
    exact ih hr ha
  | app f a ihf iha =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨ihf hr.1 ha.1, iha hr.2 ha.2⟩
  | lam ty b m iht ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨iht hr.1 ha.1, ihb hr.2 ha.2⟩
  | forallE ty b m iht ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨iht hr.1 ha.1, ihb hr.2 ha.2⟩
  | letE ty v b l iht ihv ihb =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ⟨⟨iht hr.1.1 ha.1.1, ihv hr.1.2 ha.1.2⟩, ihb hr.2 ha.2⟩
  | proj s i e ih =>
    intro hr ha
    simp only [Expr.constsResolve, Expr.arOk, Bool.and_eq_true] at hr ha ⊢
    exact ih hr.2 ha

/-- **Arity and resolution survive a step that keeps every stored name at its level count.** -/
theorem arRes_mono_len {env env₂ : Env md}
    (hf : ∀ {n : Key md} {ci : ConstantInfo md}, env.find? n = some ci →
      ∃ ci', env₂.find? n = some ci' ∧
        ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length)
    {e : Expr md} (h : ArRes env e) : ArRes env₂ e :=
  ⟨arOk_mono_len hf h.res h.ar, Ix.Kernel.Expr.constsResolve_of_find (fun n hn => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', h2, -⟩ := hf hci
    rw [h2]
    rfl) h.res⟩

/-- Two conses over one environment whose heads share their name and level parameters. -/
theorem find?_cons_same_len {env : Env md} {a b : ConstantInfo md} (hn : a.name = b.name)
    (hl : a.toConstantVal.levelParams = b.toConstantVal.levelParams) :
    ∀ {n : Key md} {ci : ConstantInfo md}, Env.find? ⟨a :: env.consts⟩ n = some ci →
      ∃ ci', Env.find? ⟨b :: env.consts⟩ n = some ci' ∧
        ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length := by
  intro n ci h
  rw [Ix.Kernel.Env.find?_cons] at h
  rw [Ix.Kernel.Env.find?_cons]
  by_cases ha : a.name = n
  · rw [if_pos ha] at h
    obtain rfl := Option.some.inj h
    rw [if_pos (hn ▸ ha)]
    exact ⟨b, rfl, by rw [hl]⟩
  · rw [if_neg ha] at h
    rw [if_neg (by rw [← hn]; exact ha)]
    exact ⟨ci, h, rfl⟩

/-! ## Declared rules up to wrappers -/

/-- `Forall₂`'s lengths. -/
theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_length h]

/-- Every right element of a `Forall₂` has a related left one. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => nomatch hb
  | _, _, .cons hr h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- **A declared term without `let` related to a generated closed one by `WrapRel` is
arity-correct and resolves where the generated one is.** -/
theorem arRes_of_wrapRel {E : Env md} {find? : Key md → Option (ConstantInfo md)}
    {g d : Expr md} (h : WrapRel find? g d) (hfv : g.hasFvar = false) (hd : letFree d = true)
    (hg : ArRes E g) : ArRes E d := by
  have key : ArP E g ∧ g.constsResolve E = true → ArP E d ∧ d.constsResolve E = true :=
    WrapRel.rec
      (motive_1 := fun g d _ => g.hasFvar = false → letFree d = true →
        ArP E g ∧ g.constsResolve E = true → ArP E d ∧ d.constsResolve E = true)
      (motive_2 := fun t t' _ => t.hasFvar = false → letFree t' = true →
        ArP E t ∧ t.constsResolve E = true → ArP E t' ∧ t'.constsResolve E = true)
      (bvar := fun i _ _ hg => hg)
      (fvar := fun _ _ hfv _ _ => by simp [Ix.Kernel.Expr.hasFvar] at hfv)
      (sort := fun _ _ _ _ => ⟨trivial, rfl⟩)
      (const := fun hus _ _ hg => by
        refine ⟨fun ci hci => ?_, hg.2⟩
        rw [← forall₂_length hus]
        exact hg.1 ci hci)
      (lit := fun _ _ _ hg => hg)
      (app := fun _ _ ihf iha hfv hd hg => by
        simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
        simp only [letFree, Bool.and_eq_true] at hd
        simp only [ArP, Expr.constsResolve, Bool.and_eq_true] at hg ⊢
        have h1 := ihf hfv.1 hd.1 ⟨hg.1.1, hg.2.1⟩
        have h2 := iha hfv.2 hd.2 ⟨hg.1.2, hg.2.2⟩
        exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩)
      (lam := fun _ _ _ ihd ihb hfv hd hg => by
        simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
        simp only [letFree, Bool.and_eq_true] at hd
        simp only [ArP, Expr.constsResolve, Bool.and_eq_true] at hg ⊢
        have h1 := ihd hfv.1 hd.1 ⟨hg.1.1, hg.2.1⟩
        have h2 := ihb hfv.2 hd.2 ⟨hg.1.2, hg.2.2⟩
        exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩)
      (forallE := fun _ _ _ ihd ihb hfv hd hg => by
        simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hfv
        simp only [letFree, Bool.and_eq_true] at hd
        simp only [ArP, Expr.constsResolve, Bool.and_eq_true] at hg ⊢
        have h1 := ihd hfv.1 hd.1 ⟨hg.1.1, hg.2.1⟩
        have h2 := ihb hfv.2 hd.2 ⟨hg.1.2, hg.2.2⟩
        exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩)
      (letE := fun _ _ _ _ _ _ _ hd _ => by simp [letFree] at hd)
      (proj := fun _ ih hfv hd hg => by
        simp only [Ix.Kernel.Expr.hasFvar] at hfv
        simp only [letFree] at hd
        simp only [ArP, Expr.constsResolve, Bool.and_eq_true] at hg ⊢
        have h1 := ih hfv hd ⟨hg.1, hg.2.2⟩
        exact ⟨h1.1, hg.2.1, h1.2⟩)
      (zeta := fun _ _ _ hd _ => by simp [letFree] at hd)
      (keep := fun _ ih hfv hd hg => ih hfv hd hg)
      (consume := fun hc _ ih hfv hd hg => by
        have hP := consumeWrapper_of
          (P := fun e : Expr md => e.hasFvar = false ∧ ArP E e ∧ e.constsResolve E = true)
          (fun f x hfx => by
            obtain ⟨h1, h2, h3⟩ := hfx
            simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h1
            simp only [ArP, Expr.constsResolve, Bool.and_eq_true] at h2 h3
            exact ⟨⟨h1.1, h2.1, h3.1⟩, ⟨h1.2, h2.2, h3.2⟩⟩)
          hc ⟨hfv, hg.1, hg.2⟩
        exact ih hP.1 hd ⟨hP.2.1, hP.2.2⟩)
      h hfv hd
  have r := key ⟨(arP_iff g).mpr hg.ar, hg.res⟩
  exact ⟨(arP_iff d).mp r.1, r.2⟩

/-! ## The stored rules -/

/-- **The stored rules carry the given right-hand sides and are not nested.** -/
theorem sumRules_mem {f : Key md → Option (ConstantInfo md)} {recName : Key md}
    {nP mI rP : Nat} {ty : Expr md} :
    ∀ {cs : List (ConstantVal md × Nat)} {rhss : List (Expr md)} {rl : RecRule md},
      rl ∈ Ix.Kernel.sumRules f recName nP mI rP ty cs rhss →
        rl.rhs ∈ rhss ∧ ∀ lvls pins, rl.fire ≠ .nested lvls pins
  | [], _, _, h => by simp [Ix.Kernel.sumRules] at h
  | _ :: _, [], _, h => by simp [Ix.Kernel.sumRules] at h
  | c :: cs, rhs :: rhss, rl, h => by
    simp only [Ix.Kernel.sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨List.mem_cons_self .., fun lvls pins hf => ?_⟩
      simp only [Ix.Kernel.recRuleBits] at hf
      split at hf <;> exact nomatch hf
    · obtain ⟨h1, h2⟩ := sumRules_mem h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem ConstArR.of_rec {env : Env md} {cv : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (ht : ArRes env cv.type)
    (hr : ∀ rl ∈ rules, ArRes env rl.rhs ∧
      ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, ArRes env p) :
    ConstArR env (.recInfo cv mI rP rules) where
  type := ht
  defn := fun _ _ _ he => nomatch he
  thm := fun _ _ he => nomatch he
  rhs := fun _ _ _ _ he => by cases he; exact hr
  proj := fun _ he => nomatch he

/-! ## The late step -/

/-- **A late recursor's install keeps `StoreArR`**, where the family's telescope constant is
its stored former and the former carries the family's level parameters (the registry's
`LateFamAt.tele`, `LateFamAt.lps`). -/
theorem storeArR_nativeRecLate {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)} (h : StoreArR env)
    (htele : fam.cvTa = fam.cvS) (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂) : StoreArR env₂ := by
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hFS, -, -, hRec, rfl⟩ := hrun
  obtain ⟨cvRg, rhsG, ⟨-, -, cvRi, recTy, hck, hty, -, hres, -, -, -, hrules, hcvRg⟩, hst⟩ := hRec
  -- the family's parts at `env`
  have hFormer := hFS.former
  have hT : ArRes env (.const fam.p.cvT.name (fam.p.cvT.levelParams.map .param)) := by
    refine ⟨arOk_const_of (fun ci hci => ?_), by simp [Expr.constsResolve, hFormer]⟩
    rw [hFormer] at hci
    obtain rfl := Option.some.inj hci
    simp [hlps, Ix.Kernel.ConstantInfo.toConstantVal]
  have htty : ArRes env fam.cvTa.type := by
    rw [htele]
    exact (h.const hFormer).type
  have hcs : ∀ c ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
      ArRes env (.const c.1 (fam.p.cvT.levelParams.map .param)) ∧ ArRes env c.2.2.1 := by
    intro c hc
    obtain ⟨cA, hcA, h1, h2⟩ := mem_nativeCtors4 hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨hfC, hlC, -⟩ := hFS.ctor j cA hj
    have har : Expr.arOk env (.const cA.1.name (fam.p.cvT.levelParams.map .param)) = true :=
      arOk_const_of (fun ci hci => by
        rw [hfC] at hci
        obtain rfl := Option.some.inj hci
        simp [hlC, Ix.Kernel.ConstantInfo.toConstantVal])
    have hres' : (Expr.const cA.1.name (fam.p.cvT.levelParams.map .param)).constsResolve env =
        true := by
      simp [Expr.constsResolve, hfC]
    rw [h1, h2]
    exact ⟨⟨har, hres'⟩, (h.const hfC).type⟩
  -- the recursor's name is fresh
  have hfresh : env.find? pR.cvR.name = none := hck.fresh
  -- the generated rules at the environment holding the recursor
  have hpT : pR.cvT = fam.p.cvT := by rw [hpR]; rfl
  have hpK : pR.kinds = fam.p.kinds := by rw [hpR]; rfl
  let cvG : ConstantVal md := ⟨pR.cvR.name, pR.cvR.levelParams, recTy⟩
  let envR : Env md := ⟨.recInfo cvG pR.majorIdx pR.rulePrefix [] :: env.consts⟩
  have hR : ∀ {e : Expr md}, ArRes env e → ArRes envR e := fun he =>
    he.mono (find?_cons_fresh_ext (c := .recInfo cvG pR.majorIdx pR.rulePrefix []) hfresh)
  have hTR : ArP envR (.const pR.cvT.name (pR.cvT.levelParams.map .param)) := by
    rw [hpT]; exact (arP_iff _).mpr (hR hT).ar
  have httyR : ArP envR fam.cvTa.type := (arP_iff _).mpr (hR htty).ar
  have hcsR : Ctors4Ar envR pR.cvT.levelParams (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds) := by
    intro c hc
    rw [hpK] at hc
    rw [hpT]
    exact ⟨(arP_iff _).mpr (hR (hcs c hc).1).ar, (arP_iff _).mpr (hR (hcs c hc).2).ar⟩
  have hrecR : ArP envR (.const pR.cvR.name (pR.cvR.levelParams.map .param)) := by
    intro ci hci
    have hs : envR.find? pR.cvR.name = some (.recInfo cvG pR.majorIdx pR.rulePrefix []) :=
      Ix.Kernel.Env.find?_cons_self (ConstantInfo.recInfo cvG pR.majorIdx pR.rulePrefix []) env
    rw [hs] at hci
    obtain rfl := Option.some.inj hci
    simp [cvG, Ix.Kernel.ConstantInfo.toConstantVal]
  have hG : ∀ r ∈ rhsG, ArRes envR r ∧ r.hasFvar = false := by
    intro r hr
    obtain ⟨hlen, hall⟩ := Ix.Kernel.checkNativeRules_inv hrules
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
    have hi' : i < (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
    obtain ⟨rhs, hrhs, hgen, -, hres', -, hfv⟩ := hall i hi'
    rw [hi] at hrhs
    obtain rfl := Option.some.inj hrhs
    exact ⟨⟨(arP_iff _).mp (arP_structRecRhsR hTR httyR hcsR hrecR hgen), hres'⟩, hfv⟩
  -- both ways of storing the recursor
  have hstore : ArRes envR cvRa.type ∧ (∀ r ∈ rhss, ArRes envR r) ∧
      cvRa.name = pR.cvR.name ∧ cvRa.levelParams = pR.cvR.levelParams := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨cvRi', hck', rfl, -, hW, hlet, -, -, -, -⟩
    · subst hcvRg
      refine ⟨⟨(arP_iff _).mp (arP_structRecTyR hTR httyR hcsR hty), ?_⟩,
        fun r hr => (hG r hr).1, rfl, rfl⟩
      exact Ix.Kernel.Expr.constsResolve_mono hres
    · refine ⟨hR (show ArRes env cvRi'.type from arRes_of_cvCheck hck'), fun r hr => ?_, rfl, rfl⟩
      obtain ⟨g, hg, hgr⟩ := forall₂_mem_right hW r hr
      exact arRes_of_wrapRel hgr (hG g hg).2 (hlet r hr) (hG g hg).1
  obtain ⟨hTy, hRh, hname, hlp⟩ := hstore
  -- the cons
  have hfreshA : env.find? (ConstantInfo.recInfo cvRa pR.majorIdx pR.rulePrefix
      (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
        fam.ctorsA rhss)).name = none := by
    show env.find? cvRa.name = none
    rw [hname]
    exact hfresh
  have hlen : ∀ {n : Key md} {ci : ConstantInfo md}, envR.find? n = some ci →
      ∃ ci', Env.find? ⟨.recInfo cvRa pR.majorIdx pR.rulePrefix
          (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
            fam.ctorsA rhss) :: env.consts⟩ n = some ci' ∧
        ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length :=
    find?_cons_same_len (by show pR.cvR.name = cvRa.name; rw [hname])
      (by show pR.cvR.levelParams = cvRa.levelParams; rw [hlp])
  refine storeArR_cons h hfreshA (ConstArR.of_rec (arRes_mono_len hlen hTy) ?_)
    (fun ⟨_, _, _, he⟩ => nomatch he)
  intro rl hrl
  obtain ⟨hmem, hnn⟩ := sumRules_mem hrl
  exact ⟨arRes_mono_len hlen (hRh _ hmem), fun lvls pins hf => absurd hf (hnn lvls pins)⟩

end Ix.Kernel.Model
