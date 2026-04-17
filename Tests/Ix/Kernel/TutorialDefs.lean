/-
  Tutorial definitions for kernel testing.
  Adapted from lean-kernel-arena tutorial/Tutorial.lean.
  Uses macros from TutorialMeta.lean.
-/
import Tests.Ix.Kernel.TutorialMeta

set_option linter.unusedVariables false

open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.TutorialDefs

/-! ## Axioms used by tutorial tests -/
axiom aDepProp : Type → Prop
axiom mkADepProp : ∀ t, aDepProp t
axiom aType : Type
axiom aProp : Prop

/-! ## Basic definitions (Tutorial.lean 16–60) -/

good_def basicDef : Type := Prop
bad_def badDef : Prop := unchecked Type
good_def arrowType : Type := Prop → Prop
good_def dependentType : Prop := ∀ (p: Prop), p
good_def constType : Type → Type → Type := fun x y => x
good_def betaReduction : constType Prop (Prop → Prop) := ∀ p : Prop, p
good_def betaReduction2 : ∀ (p : Prop), constType Prop (Prop → Prop) := fun p => p
good_def forallSortWhnf : Prop := ∀ (p : id Prop) (x : p), p
bad_def nonTypeType : constType := unchecked Prop

/-! ## Level computation (Tutorial.lean 62–118) -/

good_decl (.defnDecl {
    name := `levelComp1, levelParams := [],
    type := .sort 1, value := .sort (.imax 1 0),
    hints := .opaque, safety := .safe })

good_decl (.defnDecl {
    name := `levelComp2, levelParams := [],
    type := .sort 2, value := .sort (.imax 0 1),
    hints := .opaque, safety := .safe })

good_decl (.defnDecl {
    name := `levelComp3, levelParams := [],
    type := .sort 3, value := .sort (.imax 2 1),
    hints := .opaque, safety := .safe })

def levelParamF.{u} : Sort u → Sort u → Sort u := fun α β => α

good_def levelParams : levelParamF Prop (Prop → Prop) := ∀ p : Prop, p

bad_decl .defnDecl {
  name := `tut06_bad01,
  levelParams := [`u, `u],
  type := .sort 1, value := .sort 0,
  hints := .opaque, safety := .safe }

good_def levelComp4.{u} : Type 0 := Sort (imax u 0)
good_def levelComp5.{u} : Type u := Sort (imax u u)
good_def imax1 : (p : Prop) → Prop := fun p => Type → p
good_def imax2 : (α : Type) → Type 1 := fun α => Type → α

/-! ## Variable inference and def-eq (Tutorial.lean 119–125) -/

good_def inferVar : ∀ (f : Prop) (g : f), f := fun f g => g
good_def defEqLambda : ∀ (f : (Prop → Prop) → Prop) (g : (a : Prop → Prop) → f a), f (fun p => p → p) :=
  fun f g => g (fun p => p → p)

/-! ## Peano arithmetic (Tutorial.lean 127–153) -/

def PN := ∀ α, (α → α) → (α → α)
def PN.zero : PN := fun α s z => z
def PN.succ : PN → PN := fun n α s z => s (n α s z)
def PN.lit0 := PN.zero
def PN.lit1 := PN.succ PN.lit0
def PN.lit2 := PN.succ PN.lit1
def PN.lit3 := PN.succ PN.lit2
def PN.lit4 := PN.succ PN.lit3
def PN.add : PN → PN → PN := fun n m α s z => n α s (m α s z)
def PN.mul : PN → PN → PN := fun n m α s z => n α (m α s) z

good_thm peano1.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2.{u} :=
  fun t v => v PN.lit2.{u}

good_thm peano2.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2.{u} :=
  fun t v => v (PN.lit1.add PN.lit1)

good_thm peano3.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit4.{u} :=
  fun t v => v (PN.lit2.mul PN.lit2)

/-! ## Let declarations (Tutorial.lean 159–196) -/

good_decl (.defnDecl {
    name := `letType, levelParams := [],
    type := .sort 1,
    value := .letE (nondep := false) `x (.sort 1) (.sort 0) (.bvar 0),
    hints := .opaque, safety := .safe })

good_decl (.defnDecl {
    name := `letTypeDep, levelParams := [],
    type := (Lean.mkConst ``aDepProp).app (.sort 0),
    value := .letE (nondep := false) `x (.sort 1) (.sort 0) <|
             (Lean.mkConst ``mkADepProp).app (.bvar 0),
    hints := .opaque, safety := .safe })

good_decl (.defnDecl {
    name := `letRed, levelParams := [],
    type := .letE (nondep := false) `x (.sort 1) (.sort 0) <| .bvar 0,
    value := Lean.mkConst ``aProp,
    hints := .opaque, safety := .safe })

/-! ## Proof irrelevance and eta (Tutorial.lean 953–985) -/

good_def proofIrrelevance : ∀ (p : Prop) (h1 h2 : p), h1 = h2 := fun _ _ _ => rfl
good_def unitEta1 : ∀ (x y : Unit), x = y := fun _ _ => rfl
good_def unitEta2.{u} : ∀ (x y : PUnit.{u}), x = y := fun _ _ => rfl
good_def unitEta3 : ∀ (x y : PUnit.{0}), x = y := fun _ _ => rfl
good_def structEta.{u} : ∀ (α β : Type u) (x : α × β), x = ⟨x.1, x.2⟩ ∧ ⟨x.1, x.2⟩ = x := fun _ _ _ => ⟨rfl, rfl⟩

good_thm funEta :
  ∀ (α : Type) (β : Type) (f : α → β), (fun x => f x) = f :=
  fun _ _ f => rfl

good_thm funEtaDep :
  ∀ (α : Type) (β : α → Type) (f : ∀ a, β a), (fun a => f a) = f :=
  fun _ _ f => rfl

bad_thm funEtaBad :
  ∀ (α : Type) (β : Type) (g : α → α) (f : α → β), (fun x => f (g x)) = f :=
  fun _ _ _ f => unchecked Eq.refl f

/-! ## Custom Nat with rec reduction -/

inductive TN : Type where | zero : TN | succ : TN → TN

noncomputable def TN.add : TN → TN → TN :=
  TN.rec (fun m => m) (fun _ ih m => (ih m).succ)

theorem tnAddZero : ∀ m, TN.add TN.zero m = m := fun _ => rfl
theorem tnAddSucc : ∀ n m, TN.add (TN.succ n) m = TN.succ (TN.add n m) := fun _ _ => rfl

/-! ## Reflexive inductive (Tutorial.lean 1145–1159) -/

inductive TRTree : Type where
  | leaf : TRTree
  | node (children : Bool → TRTree) : TRTree

noncomputable def TRTree.left (t : TRTree) : TRTree :=
  TRTree.rec (motive := fun _ => TRTree) .leaf (fun children _ih => children true) t

theorem trtreeRecReduction (t1 t2 : TRTree) :
    (TRTree.node (Bool.rec t2 t1)).left = t1 := rfl

/-! ## Acc reduction (Tutorial.lean 1168–1181) -/

good_thm accRecReduction :
  ∀ {α : Type} (r : α → α → Prop) (a : α)
    (h : ∀ b, r b a → Acc r b) (p : Bool),
    Acc.rec (motive := fun _ _ => Bool) (fun _ _ _ => p) (Acc.intro (x := a) h) = p := by
  intro α r a h p; rfl

-- Acc.rec does NOT have structure eta (bad theorem)
bad_thm accRecNoEta.{u} :
  ∀ (α : Sort u) (p : α → α → Prop) (x : α) (h : Acc p x) (a : Bool),
    Acc.rec (motive := fun _ _ => Bool) (fun _ _ _ => a) h = a :=
  @fun α p x h a => unchecked Eq.refl a

/-! ## Quotient reduction (Tutorial.lean 1185–1224) -/

good_thm quotLiftReduction.{u,v} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) (a : α),
    Quot.lift f h (Quot.mk r a) = f a := by
  intros; rfl

good_thm quotIndReduction.{u} :
  ∀ {α : Sort u} (r : α → α → Prop) {β : Quot r → Prop}
    (mk : ∀ a : α, β (Quot.mk r a)) (a : α),
    Quot.ind (r := r) (β := β) mk (Quot.mk r a) = mk a := by
  intros; rfl

/-! ## Prod.rec reduction (Tutorial.lean 701–705) -/

good_thm prodRecEqns.{u} :
  ∀ {α β : Type} {motive : α × β → Sort u} (f : (a : α) → (b : β) → motive (a, b)) (a : α) (b : β),
    Prod.rec f (a, b) = f a b := by
  intros; rfl

/-! ## Rule K (Tutorial.lean 906–928) -/

good_thm ruleK :
  ∀ (h : true = true) (a : Bool),
    Eq.rec (motive := fun _ _ => Bool) a h = a :=
  fun _ a => Eq.refl a

bad_thm ruleKbad :
  ∀ (h : true = false) (a : Bool),
    Eq.rec (motive := fun _ _ => Bool) a h = a :=
  fun _ a => unchecked Eq.refl a

/-! ## forallSortBad (Tutorial.lean 42–50) -/

bad_decl (.defnDecl {
  name := `forallSortBad
  levelParams := []
  type := .sort 0
  value := arrow (Lean.mkApp2 (Lean.mkConst ``id [2]) (.sort 1) (.sort 0)) <|
    arrow (.bvar 0) <| arrow (.bvar 0) <| .bvar 1
  hints := .opaque
  safety := .safe
})

/-! ## nonPropThm (Tutorial.lean 55–61) -/

bad_decl (.thmDecl {
  name := `nonPropThm
  levelParams := []
  type := .sort 0
  value := arrow (.sort 0) (.bvar 0)
})

/-! ## Good inductives: type assertions (Tutorial.lean 204–243) -/

good_def empty : Type := Empty
good_def boolType : Type := Bool

structure TTwoBool where
  b1 : Bool
  b2 : Bool

good_def twoBool : Type := TTwoBool
good_def andType : Prop → Prop → Prop := And
good_def prodType : Type → Type → Type := Prod
good_def pprodType : Type → Type → Type := PProd
good_def pUnitType : Type := PUnit
good_def eqType.{u_1} : {α : Sort u_1} → α → α → Prop := @Eq

inductive TN2 : Type where | zero : TN2 | succ : TN2 → TN2
good_def natDef : Type := TN2

inductive TColor where | r | b

inductive TRBTree (α : Type u) : TColor → TN2 → Type u where
  | leaf : TRBTree α .b .zero
  | red {n} : TRBTree α .b n → α → TRBTree α .b n → TRBTree α .r n
  | black {c1 c2 n} : TRBTree α c1 n → α → TRBTree α c2 n → TRBTree α .b n.succ

good_def rbTreeDef.{u} : Type u → TColor → TN2 → Type u := TRBTree

inductive TBoolProp : Prop where | a | b

inductive TSortElimProp (b : Bool) : Bool → Bool → Prop
  | mk (b1 b2 : Bool) : TSortElimProp b b2 b1

inductive TSortElimProp2 (b : Bool) : Bool → Bool → Prop
  | mk (b1 b2 : Bool) : TSortElimProp2 b b2 (id b1)

/-! ## Universe level tests for inductive fields (Tutorial.lean 558–579) -/

inductive PredWithTypeField : Prop where
  | mk (α : Type) : PredWithTypeField

good_def predWithTypeField : Prop := PredWithTypeField

inductive TypeWithTypeField : Type 1 where
  | mk (α : Type) : TypeWithTypeField

good_def typeWithTypeField : Type 1 := TypeWithTypeField

inductive TypeWithTypeFieldPoly : Type (u + 1) where
  | mk (α : Type u) : TypeWithTypeFieldPoly

good_def typeWithTypeFieldPoly.{u} : Type (u + 1) := TypeWithTypeFieldPoly

/-! ## Good recursor type assertions (Tutorial.lean 615–640) -/

good_def emptyRec.{u} : ∀ (motive : Empty → Sort u) (x : Empty), motive x := @Empty.rec
good_def boolRec.{u} : ∀ {motive : Bool → Sort u} (false : motive false) (true : motive true) (t : Bool), motive t := Bool.rec
good_def andRec.{u} : ∀ (p q : Prop) {motive : And p q → Sort u} (mk : ∀ p q, motive (And.intro p q)) (x : And p q), motive x := @And.rec
good_def nRec.{u} : ∀ {motive : TN2 → Sort u} (zero : motive TN2.zero) (succ : (a : TN2) → motive a → motive a.succ) (t : TN2), motive t := @TN2.rec

good_def twoBoolRec.{u} : ∀ {motive : TTwoBool → Sort u} (mk : ∀ b1 b2, motive ⟨b1, b2⟩) (x : TTwoBool), motive x := TTwoBool.rec

good_def prodRec.{u,v,w} : ∀ (α : Type u) (β : Type v) {motive : Prod α β → Sort u} (mk : ∀ p q, motive (.mk p q)) (x : Prod α β), motive x := @Prod.rec

good_def pprodRec.{u,v,w} : ∀ (α : Sort u) (β : Sort v) {motive : PProd α β → Sort u} (mk : ∀ p q, motive (.mk p q)) (x : PProd α β), motive x := @PProd.rec

good_def punitRec.{u,w} : ∀ {motive : PUnit.{u} → Sort w} (mk : motive ⟨⟩) (x : PUnit), motive x := @PUnit.rec

good_def eqRec.{u, u_1} : ∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → Sort u}
  (refl : motive a (.refl a)) {a' : α} (t : a = a'), motive a' t := @Eq.rec

good_def rbTreeRef.{u} : ∀ {α : Type u}
  {motive : (a : TColor) → (a_1 : TN2) → TRBTree α a a_1 → Sort u},
   motive TColor.b TN2.zero TRBTree.leaf →
      ({n : TN2} →
          (a : TRBTree α TColor.b n) →
            (a_1 : α) →
              (a_2 : TRBTree α TColor.b n) →
                motive TColor.b n a → motive TColor.b n a_2 → motive TColor.r n (a.red a_1 a_2)) →
        ({c1 c2 : TColor} →
            {n : TN2} →
              (a : TRBTree α c1 n) →
                (a_1 : α) →
                  (a_2 : TRBTree α c2 n) → motive c1 n a → motive c2 n a_2 → motive TColor.b n.succ (a.black a_1 a_2)) →
          {a : TColor} → {a_1 : TN2} → (t : TRBTree α a a_1) → motive a a_1 t := @TRBTree.rec

good_def boolPropRec : ∀ {motive : TBoolProp → Prop} (a : motive TBoolProp.a) (b : motive TBoolProp.b) (x : TBoolProp), motive x := @TBoolProp.rec

good_def existsRec.{u} : ∀ {α : Sort u} {p : α → Prop} {motive : Exists p → Prop}
  (intro : ∀ (w : α) (h : p w), motive ⟨w, h⟩) (t : Exists p), motive t := @Exists.rec

good_def sortElimPropRec.{u} : ∀ {b : Bool} {motive : ∀ b1 b2, TSortElimProp b b1 b2 → Sort u}
  (mk : ∀ b1 b2, motive b2 b1 (.mk b1 b2)) (b1 b2 : Bool) (x : TSortElimProp b b1 b2), motive b1 b2 x := @TSortElimProp.rec

good_def sortElimProp2Rec : ∀ {b : Bool} {motive : ∀ b1 b2, TSortElimProp2 b b1 b2 → Prop}
  (mk : ∀ b1 b2, motive b2 b1 (.mk b1 b2)) (b1 b2 : Bool) (x : TSortElimProp2 b b1 b2), motive b1 b2 x := @TSortElimProp2.rec

/-! ## Bool.rec reduction (Tutorial.lean 694–699) -/

good_thm boolRecEqns.{u} :
  (∀ {motive : Bool → Sort u} (falseVal : motive false) (trueVal : motive true),
    Bool.rec falseVal trueVal false = falseVal) ∧
  (∀ {motive : Bool → Sort u} (falseVal : motive false) (trueVal : motive true),
    Bool.rec falseVal trueVal true = trueVal) := by
  constructor <;> intros <;> rfl

/-! ## Projection functions (Tutorial.lean 748–758) -/

good_consts #[``And.left, ``And.right]
good_consts #[``Prod.fst, ``Prod.snd]
good_consts #[``PProd.fst, ``PProd.snd]
good_consts #[``PSigma.fst, ``PSigma.snd]

/-! ## Projection reduction (Tutorial.lean 902–903) -/

good_def projRed : (Prod.mk true false).2 = false := rfl

/-! ## Structure eta (Tutorial.lean 967–968) -/

good_def structEtaDef.{u} : ∀ (α β : Type u) (x : α × β), x = ⟨x.1, x.2⟩ ∧ ⟨x.1, x.2⟩ = x := fun _ _ _ => ⟨rfl, rfl⟩

/-! ## Nat literals (Tutorial.lean 930–951) -/

good_decl (.defnDecl {
  name := `aNatLit
  levelParams := {}
  type := Lean.mkConst ``Nat
  value := .lit (.natVal 0)
  hints := .opaque
  safety := .safe
})

good_decl (.thmDecl {
  name := `natLitEq
  levelParams := {}
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat) (.lit (.natVal 3))
    (Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkConst ``Nat.zero
    )
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (.lit (.natVal 3))
})

/-! ## Eta corner cases (Tutorial.lean 987–1013) -/

bad_def etaRuleK : ∀ (a : true = true → Bool),
  @Eq (true = true → Bool)
    (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _)
    a :=
  fun a => unchecked Eq.refl a

structure T where
  val : Bool
  proof : True

bad_def etaCtor :
  ∀ (x : True → T) , (T.mk (x True.intro).val) = x := fun x => unchecked Eq.refl x

/-! ## Constructor parameter reduction — good tests (Tutorial.lean 468–486) -/

good_decl
  let n := `reduceCtorParam
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 0)) ((Lean.mkConst n []).app (.bvar 0))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

/-! ## Reflexive inductive constructor param reduction — good tests (Tutorial.lean 1089–1138) -/

good_decl
  let n := `reduceCtorParamRefl
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (arrow (.bvar 0) (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 1)) ((Lean.mkConst n []).app (.bvar 1)))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

good_decl
  let n := `reduceCtorParamRefl2
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (arrow (.bvar 0) (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 1)) (.bvar 1))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

/-! ## More recursor reduction tests (Tutorial.lean 701–744) -/

noncomputable def TN2.add : TN2 → TN2 → TN2 :=
  TN2.rec (fun m => m) (fun _ ih m => (ih m).succ)

good_thm nRecReduction :
  (∀ m, TN2.add TN2.zero m = m) ∧
  (∀ n m, TN2.add (TN2.succ n) m = TN2.succ (TN2.add n m)) := by
  unfold TN2.add; constructor <;> intros <;> rfl

noncomputable def myListAppended {α : Type} (xs ys : List α) : List α :=
  List.recOn xs ys (fun x _xs ih => x :: ih)

good_thm listRecReduction : ∀ {α : Type} (xs ys : List α),
  (myListAppended [] ys = ys) ∧
  (∀ x xs, myListAppended (x :: xs) ys = x :: myListAppended xs ys) := by
  intros; unfold myListAppended; constructor <;> intros <;> rfl

noncomputable def TRBTree.id {α : Type} {c : TColor} {n : TN2} (t : TRBTree α c n) : TRBTree α c n :=
  TRBTree.rec .leaf
    (fun _t1 a _t2 ih1 ih2 => TRBTree.red ih1 a ih2)
    (fun _t1 a _t2 ih1 ih2 => TRBTree.black ih1 a ih2)
    t

good_thm TRBTree.id_spec : ∀ {α : Type} {c : TColor} {n : TN2} (t : TRBTree α c n), t.id = t := by
  intro α c n t; induction t
  · rfl
  · dsimp [TRBTree.id]; congr
  · dsimp [TRBTree.id]; congr

/-! ## Quotient type assertions (Tutorial.lean 1185–1208) -/

good_def quotMkType.{u} :
  ∀ {α : Sort u} (r : α → α → Prop) (a : α), Quot r :=
  @Quot.mk

good_def quotIndType.{u} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}
    (mk : ∀ a : α, β (Quot.mk r a)) (q : Quot r),
      β q :=
  @Quot.ind

good_def quotLiftType.{u,v} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ (a b : α), r a b → f a = f b),
      Quot r → β :=
  @Quot.lift

good_def quotSoundType.{u} :
  ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b :=
  @Quot.sound

/-! ## Acc type assertion (Tutorial.lean 1161–1164) -/

noncomputable def accRecType := @Acc.rec

good_consts #[``accRecType]

/-! ## Rule K for Acc (Tutorial.lean 926–928) -/

bad_thm ruleKAcc.{u} :
  ∀ (α : Sort u) (p : α → α → Prop) (x : α) (h : Acc p x) (a : Bool),
    Acc.rec (motive := fun _ _ => Bool) (fun _ _ _ => a) h = a :=
  fun α p x h a => unchecked Eq.refl a

/-! ## Ill-formed inductive types (Tutorial.lean 247–466) -/

bad_raw_consts
  let n := `inductBadNonSort
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .const ``constType []
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

bad_raw_consts
  let n := `inductBadNonSort2
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .const ``aType []
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

bad_raw_consts
  let n := `inductLevelParam
  #[ .inductInfo {
      name := n
      levelParams := [`u, `u]
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

bad_raw_consts
  let n := `inductTooFewParams
  #[ .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 0)
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

bad_raw_consts
  let n := `inductWrongCtorParams
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (.sort 1) ((Lean.mkConst n).app (.const ``aProp []))
      numParams := 1
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 1)
      numParams := 1
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `inductWrongCtorResParams
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| Lean.mkApp2 (Lean.mkConst n) (.bvar 0) (.bvar 1)
      numParams := 2
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| .sort 1
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `inductWrongCtorResLevel
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := [`u1, `u2]
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <|
        Lean.mkApp2 (Lean.mkConst n [.param `u2,.param `u1]) (.bvar 1) (.bvar 0)
      numParams := 2
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := [`u1,`u2]
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| .sort 1
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `inductInIndex
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := Lean.mkApp (Lean.mkConst n) (Lean.mkApp (Lean.mkConst n) (Lean.mkConst ``aProp))
      numParams := 0
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 0)
      numParams := 0
      numIndices := 1
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `indNeg
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (.const n []) (.const n [])) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-! ## Constructor param reduction — bad tests (Tutorial.lean 491–610) -/

bad_raw_consts
  let n := `reduceCtorType
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  },
  dummyRecInfo n,
  .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := Lean.mkApp2 (.const ``id [2]) (.sort 1) (Lean.mkConst n)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  }
  ]

bad_raw_consts
  let n := `indNegReducible
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (Lean.mkApp2 (.const ``constType []) (.const ``aType []) (.const n [])) (.const n [])) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `typeWithTooHighTypeField
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  },
  dummyRecInfo n,
  .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (.sort 1) (Lean.mkConst n)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  }
  ]

/-! ## Projection — bad tests (Tutorial.lean 760–900) -/

bad_raw_consts #[
  .defnInfo {
    name := `projOutOfRange
    levelParams := []
    type := arrow (.sort 0) <| arrow (.sort 0) <|
      arrow (Lean.mkApp2 (Lean.mkConst `And []) (.bvar 1) (.bvar 0)) <| .bvar 2
    value :=
      .lam `x (binderInfo := .default) (.sort 0) <|
      .lam `y (binderInfo := .default) (.sort 0) <|
      .lam `z (binderInfo := .default) (Lean.mkApp2 (Lean.mkConst `And []) (.bvar 1) (.bvar 0)) <|
      .proj `And 2 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
]

bad_raw_consts #[
  .defnInfo {
    name := `projNotStruct
    levelParams := []
    type := arrow (Lean.mkConst ``TN2) <| (Lean.mkConst ``TN2)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``TN2) <|
      .proj ``TN2 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
]

inductive PropStructure.{u,v} : Prop where
  | mk (aProof : PUnit.{u}) (someData : PUnit.{v}) (aSecondProof : PUnit.{u})
    (someMoreData : PUnit.{v}) (aProofAboutData : someMoreData = someMoreData)
    (aFinalProof : PUnit.{u})

good_raw_consts #[
  .defnInfo {
    name := `projProp1
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) (Lean.mkConst ``PUnit [0])
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

bad_raw_consts #[
  .defnInfo {
    name := `projProp2
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) (Lean.mkConst ``PUnit [1])
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 1 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

good_raw_consts #[
  .defnInfo {
    name := `projProp3
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) (Lean.mkConst ``PUnit [0])
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 2 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

bad_raw_consts #[
  .defnInfo {
    name := `projProp4
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) (Lean.mkConst ``PUnit [1])
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 3 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

bad_raw_consts #[
  .defnInfo {
    name := `projProp5
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) <|
      (Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``PUnit [1]) (.proj ``PropStructure 3 (.bvar 0)) (.proj ``PropStructure 3 (.bvar 0)))
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 4 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

bad_raw_consts #[
  .defnInfo {
    name := `projProp6
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) (Lean.mkConst ``PUnit [0])
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure 5 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

inductive ProjDataIndex : TN2 → Prop
  | mk (n : TN2) (p : True) : ProjDataIndex n

noncomputable def projDataIndexRec := @ProjDataIndex.rec

good_consts #[``projDataIndexRec]

bad_raw_consts
  #[ .defnInfo {
    name := `projIndexData
    levelParams := []
    type :=
      arrow (Lean.mkConst ``TN2) <|
      arrow ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      (Lean.mkConst ``TN2)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``TN2) <|
      .lam `x (binderInfo := .default) ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      .proj ``PropStructure 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

bad_raw_consts
  #[ .defnInfo {
    name := `projIndexData2
    levelParams := []
    type :=
      arrow (Lean.mkConst ``TN2) <|
      arrow ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      (Lean.mkConst ``True)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``TN2) <|
      .lam `x (binderInfo := .default) ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      .proj ``PropStructure 1 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

/-! ## Reflexive inductive — bad tests (Tutorial.lean 1017–1087) -/

bad_raw_consts
  let n := `reflOccLeft
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (Lean.mkConst ``Nat) (arrow (.const n []) (Lean.mkConst ``Nat))) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

bad_raw_consts
  let n := `reflOccInIndex
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type :=
        arrow (n := `α) (.sort 1) <|
        arrow (arrow (Lean.mkConst ``Nat) <|
          Lean.mkApp (Lean.mkConst n) (Lean.mkApp (Lean.mkConst n) (.bvar 0))) <|
        Lean.mkApp (Lean.mkConst n) (.bvar 1)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (n := `α) (.sort 1) (.sort 1)
      numParams := 0
      numIndices := 1
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-! ## Name collisions (Tutorial.lean 1233–1269) -/

def dupDef : Type := Prop
def dupDef2 : Type := Prop
inductive DupInd where | mk
inductive DupInd2 where | mk1 | mk2

bad_consts #[``dupDef2, ``dupDef]
  renaming #[(``dupDef, `dup_defs), (``dupDef2, `dup_defs)]

bad_consts #[``dupDef, ``DupInd]
  renaming #[(``DupInd, `dup_ind_def), (``DupInd.mk, `dup_ind_def.mk), (``DupInd.rec, `dup_ind_def.rec), (``dupDef, `dup_ind_def)]

bad_consts #[``dupDef, ``DupInd]
  renaming #[(``DupInd, `dup_ctor_def), (``DupInd.mk, `dup_ctor_def.mk), (``DupInd.rec, `dup_ctor_def.rec), (``dupDef, `dup_ctor_def.mk)]

bad_consts #[``dupDef, ``DupInd]
  renaming #[(``DupInd, `dup_rec_def), (``DupInd.mk, `dup_rec_def.mk), (``DupInd.rec, `dup_rec_def.rec), (``dupDef, `dup_rec_def.rec)]

bad_consts #[``dupDef, ``DupInd]
  renaming #[(``DupInd, `dup_rec_def2), (``DupInd.mk, `dup_rec_def2.mk), (``DupInd.rec, `dup_rec_def2.original_rec), (``dupDef, `dup_rec_def2.rec)]

bad_consts #[``DupInd]
  renaming #[(``DupInd, `dup_ctor_rec), (``DupInd.mk, `dup_ctor_rec.rec), (``DupInd.rec, `dup_ctor_rec.rec)]

bad_consts #[``DupInd2]
  renaming #[(``DupInd2, `DupConCon), (``DupInd2.mk1, `dup_ind_con_con.mk), (``DupInd2.mk2, `dup_ind_con_con.mk)]

/-! ## Adversarial: bogus proof (lean-kernel-arena bogus1) -/

-- Theorem 0 = 1 with proof True.intro — must be rejected.
bad_thm bogus_0_eq_1 :
  @Eq Nat (Nat.zero) (Nat.succ Nat.zero) :=
  unchecked True.intro

/-! ## Adversarial: level-imax-leq (lean-kernel-arena)
  Exploits incorrect `leq(imax(u,v)+1, imax(u,v))` in universe level comparison.
  At u=0, v=0 this becomes leq(1, 0) which is false.
  A buggy kernel accepts this, enabling a universe-collapsing identity `down`
  that coerces Type to Prop, breaking proof irrelevance and proving False. -/

-- down.{u,v} : Sort(succ(imax u v)) → Sort(imax u v) := fun x => x
-- Value type is Sort(succ(imax u v)) but declared return is Sort(imax u v) — mismatch.
bad_decl (.defnDecl {
  name := `adv_imax_leq_down
  levelParams := [`u, `v]
  type := .forallE `x
    (.sort (.succ (.imax (.param `u) (.param `v))))
    (.sort (.imax (.param `u) (.param `v)))
    .default
  value := .lam `x
    (.sort (.succ (.imax (.param `u) (.param `v))))
    (.bvar 0)
    .default
  hints := .abbrev
  safety := .safe
})

/-! ## Adversarial: level-imax-normalization (lean-kernel-arena)
  Exploits `imax 0 v` being conflated with `succ(imax 0 v)` during normalization.
  At v=0 these are 0 and 1 — distinct. A buggy normalizer drops the successor
  offset when decomposing `imax`, accepting down.{0} : Type → Prop. -/

-- down.{v} : Sort(succ(imax 0 v)) → Sort(imax 0 v) := fun x => x
bad_decl (.defnDecl {
  name := `adv_imax_norm_down
  levelParams := [`v]
  type := .forallE `x
    (.sort (.succ (.imax (.zero) (.param `v))))
    (.sort (.imax (.zero) (.param `v)))
    .default
  value := .lam `x
    (.sort (.succ (.imax (.zero) (.param `v))))
    (.bvar 0)
    .default
  hints := .abbrev
  safety := .safe
})

/-! ## Adversarial: nat-rec-rules (lean-kernel-arena)
  Exploits a checker that compares imported recursor rules against themselves
  instead of freshly generated ones. The succ rule of Nat.rec is replaced with
  one that always returns h_zero (ignoring the induction hypothesis), making
  Nat.rec n = Nat.rec 0 for all n. This breaks Nat.beq and proves False.

  We test just the wrong recursor: a .recInfo with a succ rule rhs that
  returns h_zero instead of h_succ n ih. The kernel should reject it because
  the generated recursor rules don't match the provided ones. -/

-- Custom Nat for the adversarial test (so we don't conflict with stdlib Nat)
inductive AdvNat : Type where | zero : AdvNat | succ : AdvNat → AdvNat

-- The CORRECT recursor would have succ rule:
--   λ motive h_zero h_succ n => h_succ n (AdvNat.rec motive h_zero h_succ n)
-- The WRONG succ rule returns h_zero:
--   λ motive h_zero h_succ n => h_zero
bad_raw_consts
  let n := ``AdvNat
  let recName := ``AdvNat.rec
  let zeroName := ``AdvNat.zero
  let succName := ``AdvNat.succ
  let nat := Lean.mkConst n
  let app := Lean.mkApp
  let lam := Lean.mkLambda
  let pi := Lean.mkForall
  -- Motive type: AdvNat → Sort u
  let motiveType := pi `t .default nat (.sort (.param `u))
  -- h_zero type: motive AdvNat.zero
  let hzeroType := app (.bvar 0) (Lean.mkConst zeroName)
  -- ih type: motive n (under ∀ n, used in h_succ)
  let ihType := app (.bvar 2) (.bvar 0)
  -- h_succ type: ∀ (n : AdvNat) (ih : motive n), motive (AdvNat.succ n)
  let hsuccType := pi `n .default nat <|
    pi `ih .default ihType <|
    app (.bvar 2) (app (Lean.mkConst succName) (.bvar 1))
  -- Full recursor type: ∀ {motive} (h_zero) (h_succ) (t), motive t
  let recType := pi `motive .implicit motiveType <|
    pi `h_zero .default hzeroType <|
    pi `h_succ .default hsuccType <|
    pi `t .default nat (app (.bvar 1) (.bvar 0))
  -- CORRECT zero rule rhs: λ motive h_zero h_succ => h_zero
  let zeroRhs := lam `motive .default motiveType <|
    lam `h_zero .default hzeroType <|
    lam `h_succ .default hsuccType <|
    .bvar 1  -- h_zero
  -- WRONG succ rule rhs: λ motive h_zero h_succ n => h_zero (should be h_succ n ih)
  let wrongSuccRhs := lam `motive .default motiveType <|
    lam `h_zero .default hzeroType <|
    lam `h_succ .default hsuccType <|
    lam `n .default nat <|
    .bvar 2  -- h_zero (WRONG! should involve h_succ)
  #[.recInfo {
    name := recName
    levelParams := [`u]
    type := recType
    all := [n]
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 2
    rules := [
      { ctor := zeroName, nfields := 0, rhs := zeroRhs },
      { ctor := succName, nfields := 1, rhs := wrongSuccRhs }
    ]
    k := false
    isUnsafe := false
  }]

/-! ## Adversarial: constlevels (lean-kernel-arena)
  Exploits a kernel that doesn't check level parameter arity on constant references.
  When a constant has 2 level params but is referenced with 0, `unfold_definition`
  fails, causing UB in the official Lean kernel (issue #10577).

  We test two variants: too few and too many level args. -/

-- Reference Eq.casesOn (2 level params: u, u_1) with 0 level args
bad_decl (.thmDecl {
  name := `adv_constlevels_too_few
  levelParams := []
  type := Lean.mkConst ``True
  -- Value: Eq.casesOn with ZERO level args (should have 2)
  value := Lean.mkConst ``Eq.casesOn (us := [])
})

-- Reference Eq (1 level param: u_1) with 0 level args
bad_decl (.defnDecl {
  name := `adv_constlevels_eq_zero
  levelParams := []
  type := .sort 1
  -- Type is fine, but value references @Eq with 0 level args instead of 1
  value := Lean.mkConst ``Eq (us := [])
  hints := .opaque
  safety := .safe
})

-- Reference Eq (1 level param: u_1) with 3 level args (too many)
bad_decl (.defnDecl {
  name := `adv_constlevels_eq_extra
  levelParams := [`u, `v, `w]
  type := .sort 1
  value := Lean.mkConst ``Eq (us := [.param `u, .param `v, .param `w])
  hints := .opaque
  safety := .safe
})

/-! ## Struct eta in def-eq (B1 fix: no Prop guard)
  Struct eta should work even for Prop-valued structures.
  Previously the zero kernel had a spurious Prop guard that
  rejected valid struct eta comparisons on Prop types. -/

structure PropPair (p q : Prop) : Prop where
  fst : p
  snd : q

-- Struct eta: mk (x.1) (x.2) ≡ x for a Prop structure
good_thm structEtaProp :
  ∀ (p q : Prop) (x : PropPair p q),
    PropPair.mk x.fst x.snd = x := by
  intros; rfl

-- Struct eta for non-Prop too (sanity check)
good_thm structEtaNonProp :
  ∀ (x : TTwoBool),
    TTwoBool.mk x.b1 x.b2 = x := by
  intros; rfl

/-! ## Proof irrelevance
  Two distinct proofs of the same Prop are definitionally equal. -/

good_thm proofIrrel :
  ∀ (p : Prop) (h1 h2 : p), h1 = h2 := by
  intros; rfl

good_thm proofIrrelAnd :
  ∀ (a b : Prop) (h1 h2 : a ∧ b), h1 = h2 := by
  intros; rfl

/-! ## String literal def-eq
  String literals must be def-eq to their constructor form. -/

good_thm stringEmptyMk : ("" : String) = String.mk [] := by rfl

good_thm stringEmptyOfList : ("" : String) = String.ofList [] := by rfl

good_thm natOfNatLit : (97 : Nat) = @OfNat.ofNat Nat 97 (instOfNatNat 97) := by rfl

good_thm charOfNatLit : Char.ofNat 97 = Char.ofNat (@OfNat.ofNat Nat 97 (instOfNatNat 97)) := by rfl

good_thm charListLit : [Char.ofNat 97] = [@Char.ofNat (@OfNat.ofNat Nat 97 (instOfNatNat 97))] := by rfl

good_thm stringOfListBoth : String.ofList [Char.ofNat 97] = String.ofList [@Char.ofNat (@OfNat.ofNat Nat 97 (instOfNatNat 97))] := by rfl

good_thm stringAMk : ("a" : String) = String.mk [Char.ofNat 97] := by rfl

good_thm stringAOfList : ("a" : String) = String.ofList [Char.ofNat 97] := by rfl

/-! ## Nat primitive reduction
  Nat.ble/beq on literals should reduce via try_reduce_nat. -/

good_thm natBleTrue : Nat.ble 3 5 = true := by native_decide

good_thm natBleFalse : Nat.ble 5 3 = false := by native_decide

good_thm natBeqTrue : Nat.beq 42 42 = true := by native_decide

good_thm natBeqFalse : Nat.beq 42 43 = false := by native_decide

end Tests.Ix.Kernel.TutorialDefs
