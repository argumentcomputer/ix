/-
  Kernel2 Nat debug suite: synthetic MyNat environment with real names,
  side-by-side with real Lean Nat, for step-by-step tracing.
-/
import Tests.Ix.Kernel.Helpers
import Ix.Kernel.Convert
import Ix.CompileM
import Ix.Common
import Ix.Meta
import LSpec

open LSpec
open Ix.Kernel (buildPrimitives)
open Tests.Ix.Kernel.Helpers (mkAddr parseIxName)
open Tests.Ix.Kernel.Helpers

namespace Tests.Ix.Kernel.Nat

/-! ## Named Expr constructors for .meta mode -/

private def bv (n : Nat) (name : Ix.Name := default) : E := .bvar n name
private def srt (n : Nat) : E := Ix.Kernel.Expr.mkSort (levelOfNat n)
  where levelOfNat : Nat → Ix.Kernel.Level .meta
    | 0 => .zero
    | n + 1 => .succ (levelOfNat n)
private def ty : E := srt 1
private def lam (dom body : E) (name : Ix.Name := default)
    (bi : Lean.BinderInfo := .default) : E :=
  .lam dom body name bi
private def pi (dom body : E) (name : Ix.Name := default)
    (bi : Lean.BinderInfo := .default) : E :=
  .forallE dom body name bi
private def app (f a : E) : E := Ix.Kernel.Expr.mkApp f a
private def cst (addr : Address) (name : Ix.Name := default) : E :=
  .const addr #[] name
private def cstL (addr : Address) (lvls : Array (Ix.Kernel.Level .meta))
    (name : Ix.Name := default) : E :=
  .const addr lvls name
private def proj (typeAddr : Address) (idx : Nat) (struct : E)
    (name : Ix.Name := default) : E :=
  .proj typeAddr idx struct name

private def n (s : String) : Ix.Name := parseIxName s

/-! ## Level helpers -/

private abbrev L' := Ix.Kernel.Level .meta
private def lZero : L' := .zero
private def lSucc (l : L') : L' := .succ l
private def lMax (a b : L') : L' := .max a b
private def lParam (i : Nat) (name : Ix.Name := default) : L' := .param i name

/-! ## Synthetic Nat environment with real names -/

/-- Build a Nat environment mirroring the real Lean kernel names.
    Returns (env, natAddr, zeroAddr, succAddr, recAddr). -/
def buildNatEnv (baseEnv : Env := default) : Env × Address × Address × Address × Address :=
  let natAddr   := mkAddr 50
  let zeroAddr  := mkAddr 51
  let succAddr  := mkAddr 52
  let recAddr   := mkAddr 53

  let natName   := n "Nat"
  let zeroName  := n "Nat.zero"
  let succName  := n "Nat.succ"
  let recName   := n "Nat.rec"

  let natType : E := srt 1
  let natConst : E := cst natAddr natName

  let env := baseEnv.insert natAddr (.inductInfo {
    toConstantVal := { numLevels := 0, type := natType, name := natName, levelParams := default },
    numParams := 0, numIndices := 0, all := #[natAddr], ctors := #[zeroAddr, succAddr],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  })

  let env := env.insert zeroAddr (.ctorInfo {
    toConstantVal := { numLevels := 0, type := natConst, name := zeroName, levelParams := default },
    induct := natAddr, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  })

  let succType : E := pi natConst natConst (n "n")
  let env := env.insert succAddr (.ctorInfo {
    toConstantVal := { numLevels := 0, type := succType, name := succName, levelParams := default },
    induct := natAddr, cidx := 1, numParams := 0, numFields := 1, isUnsafe := false
  })

  -- Nat.rec.{u} : (motive : Nat → Sort u) → motive Nat.zero →
  --   ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
  let u : L' := .param 0 (n "u")
  let motiveType := pi natConst (.sort u) (n "a")
  let recType : E :=
    pi motiveType                                              -- [0] motive
      (pi (app (bv 0 (n "motive")) (cst zeroAddr zeroName))   -- [1] zero
        (pi (pi natConst                                        -- [2] succ: ∀ (n : Nat),
              (pi (app (bv 2 (n "motive")) (bv 0 (n "n")))    --   motive n →
                (app (bv 3 (n "motive")) (app (cst succAddr succName) (bv 1 (n "n")))))
              (n "n"))
          (pi natConst                                          -- [3] (t : Nat) →
            (app (bv 3 (n "motive")) (bv 0 (n "t")))          --   motive t
            (n "t"))
          (n "succ"))
        (n "zero"))
      (n "motive")

  let zeroRhs : E :=
    lam motiveType
      (lam (app (bv 0) (cst zeroAddr zeroName))
        (lam (pi natConst (pi (app (bv 2) (bv 0)) (app (bv 3) (app (cst succAddr succName) (bv 1)))))
          (bv 1)
          (n "succ"))
        (n "zero"))
      (n "motive")

  let succRhs : E :=
    lam motiveType
      (lam (app (bv 0) (cst zeroAddr zeroName))
        (lam (pi natConst (pi (app (bv 2) (bv 0)) (app (bv 3) (app (cst succAddr succName) (bv 1)))))
          (lam natConst
            (app (app (bv 1) (bv 0))
              (app (app (app (app (cstL recAddr #[u] recName) (bv 3)) (bv 2)) (bv 1)) (bv 0)))
            (n "n"))
          (n "succ"))
        (n "zero"))
      (n "motive")

  let env := env.insert recAddr (.recInfo {
    toConstantVal := { numLevels := 1, type := recType, name := recName, levelParams := default },
    all := #[natAddr], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
    rules := #[
      { ctor := zeroAddr, nfields := 0, rhs := zeroRhs },
      { ctor := succAddr, nfields := 1, rhs := succRhs }
    ],
    k := false, isUnsafe := false
  })

  (env, natAddr, zeroAddr, succAddr, recAddr)

/-! ## Full brecOn-based Nat.add environment -/

structure NatAddrs where
  nat       : Address := mkAddr 50
  zero      : Address := mkAddr 51
  succ      : Address := mkAddr 52
  natRec    : Address := mkAddr 53
  punit     : Address := mkAddr 60
  punitUnit : Address := mkAddr 61
  pprod     : Address := mkAddr 70
  pprodMk   : Address := mkAddr 71
  below     : Address := mkAddr 80
  natCasesOn : Address := mkAddr 81
  brecOnGo  : Address := mkAddr 82
  brecOn    : Address := mkAddr 83
  addMatch1 : Address := mkAddr 84
  natAdd    : Address := mkAddr 85

/-- Build the full brecOn-based Nat.add environment matching real Lean. -/
def buildBrecOnNatAddEnv : Env × NatAddrs :=
  let a : NatAddrs := {}
  let (env, _, _, _, _) := buildNatEnv

  let natConst := cst a.nat (n "Nat")
  let zeroConst := cst a.zero (n "Nat.zero")
  let succConst := cst a.succ (n "Nat.succ")

  -- Level params for polymorphic defs (param 0 = u, param 1 = v for PProd)
  let u := lParam 0 (n "u")
  let v := lParam 1 (n "v")
  let max1u := lMax (lSucc lZero) u
  let succMax1u := lSucc max1u
  -- Concrete levels for use in Nat.add body (which has 0 level params)
  let l1 := lSucc lZero             -- 1

  -- Nat → Sort u (the motive type)
  let motiveT := pi natConst (.sort u) (n "a")

  /- PUnit.{u} : Sort u -/
  let env := env.insert a.punit (.inductInfo {
    toConstantVal := { numLevels := 1, type := .sort u, name := n "PUnit", levelParams := default },
    numParams := 0, numIndices := 0, all := #[a.punit], ctors := #[a.punitUnit],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  })
  let env := env.insert a.punitUnit (.ctorInfo {
    toConstantVal := { numLevels := 1, type := cstL a.punit #[u] (n "PUnit"),
                        name := n "PUnit.unit", levelParams := default },
    induct := a.punit, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  })

  /- PProd.{u,v} : Sort u → Sort v → Sort (max (max 1 u) v) -/
  let pprodSort := .sort (lMax (lMax (lSucc lZero) u) v)
  let pprodType := pi (.sort u) (pi (.sort v) pprodSort (n "β")) (n "α")
  let env := env.insert a.pprod (.inductInfo {
    toConstantVal := { numLevels := 2, type := pprodType, name := n "PProd", levelParams := default },
    numParams := 2, numIndices := 0, all := #[a.pprod], ctors := #[a.pprodMk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  })

  /- PProd.mk.{u,v} : (α : Sort u) → (β : Sort v) → α → β → PProd α β
      [0] α [1] β [2] fst: bv1=α [3] snd: bv1=β  body: PProd bv3 bv2 -/
  let pprodMkType :=
    pi (.sort u)
      (pi (.sort v)
        (pi (bv 1 (n "α"))
          (pi (bv 1 (n "β"))
            (app (app (cstL a.pprod #[u, v] (n "PProd")) (bv 3 (n "α"))) (bv 2 (n "β")))
            (n "snd"))
          (n "fst"))
        (n "β"))
      (n "α")
  let env := env.insert a.pprodMk (.ctorInfo {
    toConstantVal := { numLevels := 2, type := pprodMkType, name := n "PProd.mk", levelParams := default },
    induct := a.pprod, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false
  })

  /- Nat.below.{u} : (motive : Nat → Sort u) → Nat → Sort (max 1 u)
     λ[0]motive λ[1]t: bv0=t bv1=motive
     step λ[2]n λ[3]n_ih: domain bv0=n bv2=motive; body bv0=n_ih bv1=n bv3=motive -/
  let belowType := pi motiveT (pi natConst (.sort max1u) (n "t")) (n "motive")
  let belowBody :=
    lam motiveT
      (lam natConst
        (app (app (app (app
          (cstL a.natRec #[succMax1u] (n "Nat.rec"))
          (lam natConst (.sort max1u) (n "_")))
          (cstL a.punit #[max1u] (n "PUnit")))
          (lam natConst
            (lam (.sort max1u)  -- n_ih domain: the rec motive applied to n = Sort(max 1 u)
              (app (app (cstL a.pprod #[u, max1u] (n "PProd"))
                (app (bv 3 (n "motive")) (bv 1 (n "n"))))
                (bv 0 (n "n_ih")))
              (n "n_ih"))
            (n "n")))
          (bv 0 (n "t")))
        (n "t"))
      (n "motive")
  let env := env.insert a.below (.defnInfo {
    toConstantVal := { numLevels := 1, type := belowType, name := n "Nat.below", levelParams := default },
    value := belowBody, hints := .abbrev, safety := .safe, all := #[a.below]
  })

  /- Nat.casesOn.{u} -/
  let casesOnType :=
    pi motiveT
      (pi natConst
        (pi (app (bv 1 (n "motive")) zeroConst)
          (pi (pi natConst (app (bv 3 (n "motive")) (app succConst (bv 0 (n "n")))) (n "n"))
            (app (bv 3 (n "motive")) (bv 2 (n "t")))
            (n "succ"))
          (n "zero"))
        (n "t"))
      (n "motive")
  let casesOnBody :=
    lam motiveT
      (lam natConst
        (lam (app (bv 1 (n "motive")) zeroConst)
          (lam (pi natConst (app (bv 3 (n "motive")) (app succConst (bv 0))) (n "n"))
            (app (app (app (app
              (cstL a.natRec #[u] (n "Nat.rec"))
              (bv 3 (n "motive")))
              (bv 1 (n "zero")))
              (lam natConst
                (lam (app (bv 4 (n "motive")) (bv 0 (n "n")))
                  (app (bv 2 (n "succ")) (bv 1 (n "n")))
                  (n "_"))
                (n "n")))
              (bv 2 (n "t")))
            (n "succ"))
          (n "zero"))
        (n "t"))
      (n "motive")
  let env := env.insert a.natCasesOn (.defnInfo {
    toConstantVal := { numLevels := 1, type := casesOnType, name := n "Nat.casesOn", levelParams := default },
    value := casesOnBody, hints := .abbrev, safety := .safe, all := #[a.natCasesOn]
  })

  /- Nat.brecOn.go.{u} -/
  -- Helper: PProd.{u, max1u} applied to two type args
  let pprodU := fun (aE bE : E) => app (app (cstL a.pprod #[u, max1u] (n "PProd")) aE) bE
  -- Helper: PProd.mk.{u, max1u} applied to 4 args
  let pprodMkU := fun (aE bE fE sE : E) =>
    app (app (app (app (cstL a.pprodMk #[u, max1u] (n "PProd.mk")) aE) bE) fE) sE
  -- Helper: Nat.below.{u} motive t
  let belowU := fun (motE tE : E) => app (app (cstL a.below #[u] (n "Nat.below")) motE) tE

  -- F_1 type: under [0]motive [1]t: bv0=t bv1=motive
  -- Domain is at depth 2: bv0=t bv1=motive → so inner pi refs shift
  -- (t' : Nat) → Nat.below.{u} bv2(motive) bv0(t') → bv3(motive) bv1(t')
  let f1TypeInGo :=
    pi natConst
      (pi (belowU (bv 2 (n "motive")) (bv 0 (n "t'")))
        (app (bv 3 (n "motive")) (bv 1 (n "t'")))
        (n "x"))
      (n "t'")

  -- Result type: under [0]motive [1]t [2]F_1: bv0=F_1 bv1=t bv2=motive
  let goResult := pprodU (app (bv 2 (n "motive")) (bv 1 (n "t")))
                         (belowU (bv 2 (n "motive")) (bv 1 (n "t")))

  let goType := pi motiveT (pi natConst (pi f1TypeInGo goResult (n "F_1")) (n "t")) (n "motive")

  -- Body: under λ[0]motive λ[1]t λ[2]F_1: bv0=F_1 bv1=t bv2=motive
  -- Rec motive (+ λ[3]t'): bv0=t' bv1=F_1 bv2=t bv3=motive
  let goRecMotive :=
    lam natConst
      (pprodU (app (bv 3 (n "motive")) (bv 0 (n "t'")))
              (belowU (bv 3 (n "motive")) (bv 0 (n "t'"))))
      (n "t'")

  -- Base case (at depth 3): bv0=F_1 bv1=t bv2=motive
  let goBase :=
    pprodMkU
      (app (bv 2 (n "motive")) zeroConst)
      (cstL a.punit #[max1u] (n "PUnit"))
      (app (app (bv 0 (n "F_1")) zeroConst) (cstL a.punitUnit #[max1u] (n "PUnit.unit")))
      (cstL a.punitUnit #[max1u] (n "PUnit.unit"))

  -- Step (at depth 3 + λ[3]n λ[4]n_ih):
  --   n_ih domain (depth 4): bv0=n bv1=F_1 bv2=t bv3=motive
  --   body (depth 5): bv0=n_ih bv1=n bv2=F_1 bv3=t bv4=motive
  let goStep :=
    lam natConst
      (lam (pprodU (app (bv 3 (n "motive")) (bv 0 (n "n")))
                   (belowU (bv 3 (n "motive")) (bv 0 (n "n"))))
        (pprodMkU
          (app (bv 4 (n "motive")) (app succConst (bv 1 (n "n"))))
          (pprodU (app (bv 4 (n "motive")) (bv 1 (n "n")))
                  (belowU (bv 4 (n "motive")) (bv 1 (n "n"))))
          (app (app (bv 2 (n "F_1")) (app succConst (bv 1 (n "n")))) (bv 0 (n "n_ih")))
          (bv 0 (n "n_ih")))
        (n "n_ih"))
      (n "n")

  let goBody :=
    lam motiveT
      (lam natConst
        (lam f1TypeInGo
          (app (app (app (app
            (cstL a.natRec #[max1u] (n "Nat.rec"))
            goRecMotive) goBase) goStep)
            (bv 1 (n "t")))
          (n "F_1"))
        (n "t"))
      (n "motive")

  let env := env.insert a.brecOnGo (.defnInfo {
    toConstantVal := { numLevels := 1, type := goType, name := n "Nat.brecOn.go", levelParams := default },
    value := goBody, hints := .abbrev, safety := .safe, all := #[a.brecOnGo]
  })

  /- Nat.brecOn.{u} -/
  let brecOnType :=
    pi motiveT (pi natConst (pi f1TypeInGo
      (app (bv 2 (n "motive")) (bv 1 (n "t")))
      (n "F_1")) (n "t")) (n "motive")
  let brecOnBody :=
    lam motiveT
      (lam natConst
        (lam f1TypeInGo
          (proj a.pprod 0
            (app (app (app (cstL a.brecOnGo #[u] (n "Nat.brecOn.go"))
              (bv 2 (n "motive"))) (bv 1 (n "t"))) (bv 0 (n "F_1")))
            (n "PProd"))
          (n "F_1"))
        (n "t"))
      (n "motive")
  let env := env.insert a.brecOn (.defnInfo {
    toConstantVal := { numLevels := 1, type := brecOnType, name := n "Nat.brecOn", levelParams := default },
    value := brecOnBody, hints := .abbrev, safety := .safe, all := #[a.brecOn]
  })

  /- Nat.add.match_1.{u_1} -/
  let u1 := lParam 0 (n "u_1")
  let matchMotT := pi natConst (pi natConst (.sort u1) (n "b")) (n "a")

  let match1Type :=
    pi matchMotT
      (pi natConst                                                         -- a
        (pi natConst                                                       -- b
          (pi (pi natConst (app (app (bv 3 (n "motive")) (bv 0 (n "a"))) zeroConst) (n "a"))  -- h_1
            (pi (pi natConst (pi natConst
                  (app (app (bv 5 (n "motive")) (bv 1 (n "a"))) (app succConst (bv 0 (n "b"))))
                  (n "b")) (n "a"))                                        -- h_2
              (app (app (bv 4 (n "motive")) (bv 3 (n "a"))) (bv 2 (n "b")))  -- motive a b
              (n "h_2"))
            (n "h_1"))
          (n "b"))
        (n "a"))
      (n "motive")

  let match1Body :=
    lam matchMotT
      (lam natConst
        (lam natConst
          (lam (pi natConst (app (app (bv 3 (n "motive")) (bv 0 (n "a"))) zeroConst) (n "a"))
            (lam (pi natConst (pi natConst
                    (app (app (bv 5 (n "motive")) (bv 1 (n "a"))) (app succConst (bv 0 (n "b"))))
                    (n "b")) (n "a"))
              (app (app (app (app
                (cstL a.natCasesOn #[u1] (n "Nat.casesOn"))
                (lam natConst (app (app (bv 5 (n "motive")) (bv 4 (n "a"))) (bv 0 (n "x"))) (n "x")))
                (bv 2 (n "b")))
                (app (bv 1 (n "h_1")) (bv 3 (n "a"))))
                (lam natConst (app (app (bv 1 (n "h_2")) (bv 4 (n "a"))) (bv 0 (n "n"))) (n "n")))
              (n "h_2"))
            (n "h_1"))
          (n "b"))
        (n "a"))
      (n "motive")

  let env := env.insert a.addMatch1 (.defnInfo {
    toConstantVal := { numLevels := 1, type := match1Type, name := n "Nat.add.match_1", levelParams := default },
    value := match1Body, hints := .abbrev, safety := .safe, all := #[a.addMatch1]
  })

  /- Nat.add : Nat → Nat → Nat (uses concrete level 1, 0 level params) -/
  -- Helpers with concrete level 1 for Nat.add body
  let below1 := fun (motE tE : E) => app (app (cstL a.below #[l1] (n "Nat.below")) motE) tE
  let addMotive := lam natConst (pi natConst natConst (n "x")) (n "_")

  -- match_1 motive: λ x y => (Nat.below.{1} (λ _ => Nat→Nat) y) → Nat
  let matchMotive :=
    lam natConst
      (lam natConst
        (pi (below1 (lam natConst (pi natConst natConst (n "x")) (n "_"))
                     (bv 0 (n "y")))
          natConst (n "below"))
        (n "y"))
      (n "x")

  -- h_1: λ a _. a
  let h1 :=
    lam natConst
      (lam (below1 (lam natConst (pi natConst natConst (n "x")) (n "_")) zeroConst)
        (bv 1 (n "a"))
        (n "_"))
      (n "a")

  -- h_2: λ a b below. succ (below.0 a)
  -- below.0 = proj PProd 0 below : Nat → Nat (the recursive result)
  -- (below.0 a) : Nat
  let h2 :=
    lam natConst
      (lam natConst
        (lam (below1 (lam natConst (pi natConst natConst (n "x")) (n "_"))
                      (app succConst (bv 0 (n "b"))))
          (app succConst
            (app (proj a.pprod 0 (bv 0 (n "below")) (n "PProd"))
                 (bv 2 (n "a"))))
          (n "below"))
        (n "b"))
      (n "a")

  -- F_1 domain for f: under [2]y': bv0=y'
  let fDom := below1 (lam natConst (pi natConst natConst (n "x")) (n "_")) (bv 0 (n "y'"))

  -- F_1 = λ y' f x' => match_1.{1} matchMotive x' y' h_1 h_2 f
  let f1 :=
    lam natConst
      (lam fDom
        (lam natConst
          (app
            (app (app (app (app (app
              (cstL a.addMatch1 #[l1] (n "Nat.add.match_1"))
              matchMotive)
              (bv 0 (n "x'")))
              (bv 2 (n "y'")))
              h1)
              h2)
            (bv 1 (n "f")))
          (n "x'"))
        (n "f"))
      (n "y'")

  let addType := pi natConst (pi natConst natConst (n "y")) (n "x")
  let addBody :=
    lam natConst
      (lam natConst
        (app
          (app (app (app
            (cstL a.brecOn #[l1] (n "Nat.brecOn"))
            addMotive)
            (bv 0 (n "y")))
            f1)
          (bv 1 (n "x")))
        (n "y"))
      (n "x")

  let env := env.insert a.natAdd (.defnInfo {
    toConstantVal := { numLevels := 0, type := addType, name := n "Nat.add", levelParams := default },
    value := addBody, hints := .abbrev, safety := .safe, all := #[a.natAdd]
  })

  (env, a)

/-! ## Tests -/

def testSyntheticNatAdd : TestSeq :=
  let (env, natAddr, _zeroAddr, succAddr, recAddr) := buildNatEnv
  let natConst := cst natAddr (n "Nat")
  let addAddr := mkAddr 55
  let addName := n "Nat.add"
  let addType : E := pi natConst (pi natConst natConst (n "m")) (n "a")
  let motive := lam natConst natConst (n "_")
  let base := bv 1 (n "a")
  let step := lam natConst (lam natConst (app (cst succAddr (n "Nat.succ")) (bv 0 (n "ih"))) (n "ih")) (n "n✝")
  let target := bv 0 (n "m")
  let recApp := app (app (app (app (cstL recAddr #[.succ .zero] (n "Nat.rec")) motive) base) step) target
  let addBody := lam natConst (lam natConst recApp (n "m")) (n "a")
  let env := env.insert addAddr (.defnInfo {
    toConstantVal := { numLevels := 0, type := addType, name := addName, levelParams := default },
    value := addBody, hints := .abbrev, safety := .safe, all := #[addAddr]
  })
  let twoE := app (cst succAddr) (app (cst succAddr) (cst _zeroAddr))
  let threeE := app (cst succAddr) (app (cst succAddr) (app (cst succAddr) (cst _zeroAddr)))
  let addApp := app (app (cst addAddr) twoE) threeE
  test "synth Nat.add 2 3 whnf" (whnfK2 env addApp |>.isOk) $
  let result := Ix.Kernel.typecheckConst env (buildPrimitives) addAddr
  test "synth Nat.add typechecks" (result.isOk) $
  match result with
  | .ok () => test "synth Nat.add succeeded" true
  | .error e => test s!"synth Nat.add error: {e}" false

def testBrecOnDeps : List TestSeq :=
  let (env, a) := buildBrecOnNatAddEnv
  let checkAddr (label : String) (addr : Address) : TestSeq :=
    let result := Ix.Kernel.typecheckConst env (buildPrimitives) addr
    test s!"{label} typechecks" (result.isOk) $
    match result with
    | .ok () => test s!"{label} ok" true
    | .error e => test s!"{label} error: {e}" false
  [checkAddr "Nat.below" a.below,
   checkAddr "Nat.casesOn" a.natCasesOn,
   checkAddr "Nat.brecOn.go" a.brecOnGo,
   checkAddr "Nat.brecOn" a.brecOn,
   checkAddr "Nat.add.match_1" a.addMatch1,
   checkAddr "Nat.add" a.natAdd]

def testBrecOnNatAdd : TestSeq :=
  let (env, a) := buildBrecOnNatAddEnv
  let succConst := cst a.succ (n "Nat.succ")
  let zeroConst := cst a.zero (n "Nat.zero")
  let twoE := app succConst (app succConst zeroConst)
  let threeE := app succConst (app succConst (app succConst zeroConst))
  let addApp := app (app (cst a.natAdd (n "Nat.add")) twoE) threeE
  let whnfResult := whnfK2 env addApp
  test "brecOn Nat.add 2+3 whnf" (whnfResult.isOk) $
  match whnfResult with
  | .ok _ => test "brecOn Nat.add whnf ok" true
  | .error e => test s!"brecOn Nat.add whnf: {e}" false $
  let result := Ix.Kernel.typecheckConst env (buildPrimitives) a.natAdd
  test "brecOn Nat.add typechecks" (result.isOk) $
  match result with
  | .ok () => test "brecOn Nat.add typecheck ok" true
  | .error e => test s!"brecOn Nat.add typecheck: {e}" false

/-! ## Real Nat.add test -/

def testRealNatAdd : TestSeq :=
  .individualIO "real Nat.add typecheck" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let dumpConst (name : String) : IO Unit := do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | IO.println s!"  {name}: NOT FOUND"
        let addr := cNamed.addr
        match kenv.find? addr with
        | some ci =>
          IO.println s!"  {name} [{ci.kindName}] addr={addr}"
          IO.println s!"    type: {ci.type.pp}"
          match ci with
          | .defnInfo dv => IO.println s!"    body: {dv.value.pp}"
          | .thmInfo tv => IO.println s!"    body: {tv.value.pp}"
          | .recInfo rv =>
            IO.println s!"    params={rv.numParams} motives={rv.numMotives} minors={rv.numMinors} indices={rv.numIndices} k={rv.k}"
            for r in rv.rules do
              IO.println s!"    rule: ctor={r.ctor} nfields={r.nfields} rhs={r.rhs.pp}"
          | .inductInfo iv =>
            IO.println s!"    params={iv.numParams} indices={iv.numIndices} ctors={iv.ctors} isRec={iv.isRec}"
          | .ctorInfo cv =>
            IO.println s!"    cidx={cv.cidx} params={cv.numParams} fields={cv.numFields} induct={cv.induct}"
          | _ => pure ()
        | none => IO.println s!"  {name}: not in kenv"

      IO.println "=== Nat.add dependency dump ==="
      for name in #["Nat", "Nat.zero", "Nat.succ", "Nat.rec",
                     "Nat.below", "Nat.brecOn.go", "Nat.brecOn", "Nat.casesOn",
                     "Nat.add.match_1", "Nat.add",
                     "PProd", "PProd.mk", "PUnit", "PUnit.unit"] do
        dumpConst name

      let ixName := parseIxName "Nat.add"
      let some cNamed := ixonEnv.named.get? ixName
        | return (false, some "Nat.add not found")
      match Ix.Kernel.typecheckConst kenv prims cNamed.addr quotInit with
      | .ok () =>
        IO.println "  ✓ real Nat.add typechecks"
        return (true, none)
      | .error e =>
        IO.println s!"  ✗ real Nat.add: {e}"
        return (false, some e)
  ) .done

/-! ## Suite -/

def suite : List LSpec.TestSeq :=
  [group "synthetic Nat.add" testSyntheticNatAdd,
   group "brecOn Nat.add" testBrecOnNatAdd] ++
  testBrecOnDeps.map (group "brecOn deps")

def realSuite : List LSpec.TestSeq := [
  testRealNatAdd,
]

end Tests.Ix.Kernel.Nat
