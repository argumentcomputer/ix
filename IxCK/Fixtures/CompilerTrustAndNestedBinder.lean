import IxCK.Kernel.Frontend.InModel
import IxCK.Kernel.Cached.Installed
import IxCK.Kernel.Cached.Policy
import IxCK.Kernel.Admission
import IxCK.Kernel.Tier.Check
import IxCK.Kernel.Basis.Eq
import IxCK.Kernel.Basis.Nat
import IxCK.Kernel.Basis.PUnit
import IxCK.Kernel.Basis.Empty
import IxCK.Kernel.Basis.False
import IxCK.Kernel.Basis.Quot

/-! # Certified-kernel fixtures for `§7.10` and `h-nested-binder` (`M8`)

Two self-contained checks run at elaboration time through `Ix.Kernel.Cached.checkDecls`
and `Ix.Kernel.Frontend.InModel.generate`:

1. **`§7.10` (inert compiler-trust constants):** the five compiler-trust roles
   (`Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool`,
   `Lean.ofReduceNat`) are tolerated when declared at their pinned specifications,
   install nothing into the environment, decline on specification mismatch, and
   decline (`.notImplemented`, not `.invalid`) whenever any declaration uses one.
2. **`h-nested-binder` (`M8`, nested inductive under a binder):** `InModel.generate`
   constructs a full model (including `Quot`-based function extensionality, iota
   theorems, and structure projections) for `inductive NB | mk (f : Nat → List NB)`
   and `structure NBStruct where f : Nat → List NBStruct`, and `checkDecls` accepts
   the generated model plus the modeled inductive block. -/

open Ix.Kernel Ix.Kernel.BasisDSL Ix.Kernel.Frontend.InModel

namespace Tests.Ix.Kernel.CompilerTrustAndNestedBinder

abbrev E := Expr .source
abbrev K := Key .source

private def key (s : String) : K := .id (.str .anonymous s)
private def key2 (a b : String) : K := .id (.str (.str .anonymous a) b)

private def isDeclined : Except (CheckError .source × Nat) (Env .source) → Bool
  | .error (.notImplemented _, _) => true
  | _ => false

private def isInvalid : Except (CheckError .source × Nat) (Env .source) → Bool
  | .error (.invalid _, _) => true
  | _ => false

/-! ## Minimal prelude (valid under `checkUnits`: raw `indDecl` / `quotDecl` / `axiomDecl`) -/

private def boolBlock : List (ConstantInfo .source) :=
  let b := cnst boolName
  let mTy := piA b (srt u)
  let recTy := piI "motive" mTy <| pi "false" (.app (bv 0) (cnst boolFalseName)) <|
    pi "true" (.app (bv 1) (cnst boolTrueName)) <| pi "t" b (.app (bv 3) (bv 0))
  let lams (body : E) := lm "motive" mTy <| lm "false" (.app (bv 0) (cnst boolFalseName)) <|
    lm "true" (.app (bv 1) (cnst boolTrueName)) body
  [.indInfo ⟨boolName, [], type1⟩ {},
   .ctorInfo ⟨boolFalseName, [], b⟩ 0 0,
   .ctorInfo ⟨boolTrueName, [], b⟩ 0 0,
   .recInfo ⟨.role .boolRec, [uN], recTy⟩ 3 3
     [rule boolFalseName 0 (lams (bv 1)), rule boolTrueName 0 (lams (bv 0))]]

private def trueBlock : List (ConstantInfo .source) :=
  let t := cnst trueName
  let mTy := piA t (srt u)
  let recTy := piI "motive" mTy <| pi "intro" (.app (bv 0) (cnst trueIntroName)) <|
    pi "t" t (.app (bv 2) (bv 0))
  let lams (body : E) := lm "motive" mTy <| lm "intro" (.app (bv 0) (cnst trueIntroName)) body
  [.indInfo ⟨trueName, [], prop⟩ {},
   .ctorInfo ⟨trueIntroName, [], t⟩ 0 0,
   .recInfo ⟨key2 "True" "rec", [uN], recTy⟩ 2 2 [rule trueIntroName 0 (lams (bv 0))]]

private def listRecKey : K := key2 "List" "rec"

private def listBlock : List (ConstantInfo .source) :=
  let uP : LevelParam := 1
  let mP : LevelParam := 0
  let lu : Level := .param uP
  let lm_ : Level := .param mP
  let listA (a : E) := .app (cnst listName [lu]) a
  let nilA (a : E) := .app (cnst listNilName [lu]) a
  let consA (a h t : E) := ap3 (cnst listConsName [lu]) a h t
  let tyList := pi "α" (srt (.succ lu)) (srt (.succ lu))
  let tyNil := piI "α" (srt (.succ lu)) (listA (bv 0))
  let tyCons := piI "α" (srt (.succ lu)) <| pi "head" (bv 0) <| pi "tail" (listA (bv 1)) (listA (bv 2))
  let mTy := piA (listA (bv 0)) (srt lm_)
  let nilTy := .app (bv 0) (nilA (bv 1))
  let consTy := pi "head" (bv 2) <| pi "tail" (listA (bv 3)) <|
    pi "tail_ih" (.app (bv 3) (bv 0)) (.app (bv 4) (consA (bv 5) (bv 2) (bv 1)))
  let recTy := piI "α" (srt (.succ lu)) <| piI "motive" mTy <| pi "nil" nilTy <|
    pi "cons" consTy <| pi "t" (listA (bv 3)) (.app (bv 3) (bv 0))
  let rLams (body : E) := lm "α" (srt (.succ lu)) <| lm "motive" mTy <|
    lm "nil" nilTy <| lm "cons" consTy body
  let nilRhs := rLams (bv 1)
  let consRhs := rLams <| lm "head" (bv 3) <| lm "tail" (listA (bv 4)) <|
    ap3 (bv 2) (bv 1) (bv 0) (Expr.mkAppN (cnst listRecKey [lm_, lu]) [bv 5, bv 4, bv 3, bv 2, bv 0])
  [.indInfo ⟨listName, [uP], tyList⟩ {},
   .ctorInfo ⟨listNilName, [uP], tyNil⟩ 1 0,
   .ctorInfo ⟨listConsName, [uP], tyCons⟩ 1 2,
   .recInfo ⟨listRecKey, [mP, uP], recTy⟩ 4 4 [rule listNilName 0 nilRhs, rule listConsName 2 consRhs]]

private def listBlockRec : BlockRec .source :=
  match listBlock with
  | [.indInfo cvI _, .ctorInfo cvN _ _, .ctorInfo cvC _ _, .recInfo cvR _ _ rules] =>
    ⟨[{ cv := cvI, nP := 1, nIdx := 0, ctors := [listNilName, listConsName],
        isRec := true, isReflexive := false, numNested := 0 }],
     [{ cv := cvN, nP := 1, nF := 0 }, { cv := cvC, nP := 1, nF := 2 }],
     [{ cv := cvR, nP := 1, nM := 1, nm := 2, nI := 0, rules }]⟩
  | _ => default

private def quotDecls : List (Declaration .source) :=
  match quotBasis (md := .source) with
  | [.indInfo cvQ _, .ctorInfo cvM _ _, .recInfo cvL _ _ _, .recInfo cvI _ _ _, .axiomInfo cvS] =>
    [.quotDecl .type cvQ, .quotDecl .ctor cvM, .quotDecl .lift cvL, .quotDecl .ind cvI, .axiomDecl cvS]
  | _ => []

private def preludeStream : Array (Declaration .source) :=
  (#[Declaration.indDecl eqBasis 2, Declaration.indDecl natBasis 0, Declaration.indDecl punitBasis 0,
     Declaration.indDecl emptyBasis 0, Declaration.indDecl falseBasis 0,
     Declaration.indDecl boolBlock 0, Declaration.indDecl trueBlock 0] ++
   quotDecls.toArray).push (Declaration.indDecl listBlock 1)

/-! ## Task 1 (`§7.10`): Inert compiler-trust constants -/

private def trustDecl : Declaration .source :=
  .axiomDecl ⟨.role .trustCompiler, [], cnst trueName⟩

private def reduceBoolDecl : Declaration .source :=
  let ty := piA (cnst boolName) (cnst boolName)
  let v := lm "b" (cnst boolName)
    (.letE (cnst trueName) (cnst (.role .trustCompiler)) (bv 1) {})
  .opaqueDecl ⟨.role .reduceBool, [], ty⟩ v

private def reduceNatDecl : Declaration .source :=
  let ty := piA (cnst natName) (cnst natName)
  let v := lm "n" (cnst natName)
    (.letE (cnst trueName) (cnst (.role .trustCompiler)) (bv 1) {})
  .opaqueDecl ⟨.role .reduceNat, [], ty⟩ v

private def ofReduceBoolDecl : Declaration .source :=
  let b := cnst boolName
  let ty := pi "a" b <| pi "b" b <|
    piA (ap3 (cnst eqName [.succ .zero]) b (.app (cnst (.role .reduceBool)) (bv 1)) (bv 0))
      (ap3 (cnst eqName [.succ .zero]) b (bv 2) (bv 1))
  .axiomDecl ⟨.role .ofReduceBool, [], ty⟩

private def ofReduceNatDecl : Declaration .source :=
  let n := cnst natName
  let ty := pi "a" n <| pi "b" n <|
    piA (ap3 (cnst eqName [.succ .zero]) n (.app (cnst (.role .reduceNat)) (bv 1)) (bv 0))
      (ap3 (cnst eqName [.succ .zero]) n (bv 2) (bv 1))
  .axiomDecl ⟨.role .ofReduceNat, [], ty⟩

private def ctDecls : Array (Declaration .source) :=
  #[trustDecl, reduceBoolDecl, reduceNatDecl, ofReduceBoolDecl, ofReduceNatDecl]

private def cleanThmDecl : Declaration .source :=
  .thmDecl ⟨key "cleanThm", [], cnst trueName⟩ (cnst trueIntroName)

-- 1a. All 5 compiler-trust declarations + clean theorem are accepted, and NONE of the 5 is installed.
#guard match Cached.checkDecls .verified [] (preludeStream ++ ctDecls.push cleanThmDecl) with
  | .ok env =>
    (env.find? (key "cleanThm")).isSome &&
    compilerTrustKeys.all fun k => (env.find? k).isNone
  | .error _ => false

-- 1b. Every spoofed specification declines with `.notImplemented`.
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨.role .trustCompiler, [], cnst falseName⟩))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.opaqueDecl ⟨.role .reduceBool, [], piA (cnst natName) (cnst natName)⟩ (lm "n" (cnst natName) (bv 0))))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.opaqueDecl ⟨.role .reduceNat, [], piA (cnst boolName) (cnst boolName)⟩ (lm "b" (cnst boolName) (bv 0))))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨.role .ofReduceBool, [], cnst falseName⟩))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨.role .ofReduceNat, [], cnst falseName⟩))

-- 1c. Every use of any of the 5 declines with `.notImplemented` (never `.invalid`, never `.ok`).
#guard isDeclined <| Cached.checkDecls .verified []
  ((preludeStream ++ ctDecls).push (.thmDecl ⟨key "useTrust", [], cnst trueName⟩ (cnst (.role .trustCompiler))))
#guard isDeclined <| Cached.checkDecls .verified []
  ((preludeStream ++ ctDecls).push (.defnDecl ⟨key "useRB", [], cnst boolName⟩ (.app (cnst (.role .reduceBool)) (cnst boolTrueName)) .opaque))
#guard isDeclined <| Cached.checkDecls .verified []
  ((preludeStream ++ ctDecls).push (.defnDecl ⟨key "useRN", [], cnst natName⟩ (.app (cnst (.role .reduceNat)) (cnst natZeroName)) .opaque))
#guard isDeclined <| Cached.checkDecls .verified []
  ((preludeStream ++ ctDecls).push (.thmDecl ⟨key "useORB", [], cnst trueName⟩
    (.letE (cnst trueName) (cnst (.role .ofReduceBool)) (cnst trueIntroName) {})))
#guard isDeclined <| Cached.checkDecls .verified []
  ((preludeStream ++ ctDecls).push (.thmDecl ⟨key "useORN", [], cnst trueName⟩
    (.letE (cnst trueName) (cnst (.role .ofReduceNat)) (cnst trueIntroName) {})))

-- 1d (`HIGH-5`): Auto-derived axiom-role lists cover compiler-trust axioms under `--allow-user-axioms`.
#guard [Role.propext, .choice, .sorryAx, .trustCompiler, .ofReduceBool, .ofReduceNat].all
  Ix.Kernel.Admission.userAxiomRoles.contains

private def dummyAddr (b : UInt8) : Address := ⟨ByteArray.mk (Array.replicate 32 b)⟩

private def tableWithRoles (rs : List Role) : RoleTable :=
  { version := 1
    bound := rs.toArray.map fun r => (r, dummyAddr r.idx.toUInt8)
    evidence := #[] }

-- Admission accepts a table binding all `userAxiomRoles`, and refuses any table omitting
-- `trustCompiler`, `ofReduceBool`, or `ofReduceNat` under `.allowUser`.
#guard match Ix.Kernel.Admission.admitAxiomPolicy .allowUser
    (tableWithRoles Ix.Kernel.Admission.userAxiomRoles) with
  | .ok () => true
  | .error _ => false
#guard match Ix.Kernel.Admission.admitAxiomPolicy .allowUser
    (tableWithRoles (Ix.Kernel.Admission.userAxiomRoles.filter (· != .trustCompiler))) with
  | .error (.axiomRoleUnbound .trustCompiler) => true
  | _ => false
#guard match Ix.Kernel.Admission.admitAxiomPolicy .allowUser
    (tableWithRoles (Ix.Kernel.Admission.userAxiomRoles.filter (· != .ofReduceBool))) with
  | .error (.axiomRoleUnbound .ofReduceBool) => true
  | _ => false
#guard match Ix.Kernel.Admission.admitAxiomPolicy .allowUser
    (tableWithRoles (Ix.Kernel.Admission.userAxiomRoles.filter (· != .ofReduceNat))) with
  | .error (.axiomRoleUnbound .ofReduceNat) => true
  | _ => false

-- `axiomRoleSpecHit?` detects unbound `.id` axioms restating compiler-trust specs.
#guard Cached.axiomRoleSpecHit? (md := .source) ⟨key "unboundTrust", [], cnst trueName⟩ == some .trustCompiler
#guard match ofReduceBoolDecl with
  | .axiomDecl cv =>
    Cached.axiomRoleSpecHit? (md := .source) { cv with name := key "unboundORB" } == some .ofReduceBool
  | _ => false
#guard match ofReduceNatDecl with
  | .axiomDecl cv =>
    Cached.axiomRoleSpecHit? (md := .source) { cv with name := key "unboundORN" } == some .ofReduceNat
  | _ => false

-- Under `checkDeclsWithUserAxioms`, an unbound `.id` restating `trustCompiler` is declined,
-- while a genuine user axiom (`customAx : False`) is accepted (and declined under strict `checkDecls`).
#guard isDeclined <| Cached.checkDeclsWithUserAxioms .verified []
  (preludeStream.push (.axiomDecl ⟨key "unboundTrust", [], cnst trueName⟩))
#guard match Cached.checkDeclsWithUserAxioms .verified []
    (preludeStream.push (.axiomDecl ⟨key "customAx", [], cnst falseName⟩)) with
  | .ok env => (env.find? (key "customAx")).isSome
  | .error _ => false
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨key "customAx", [], cnst falseName⟩))

-- 1e (`MED-3`): Kind exclusivity and value closedness for `§7.10` declarations.
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.defnDecl ⟨.role .trustCompiler, [], cnst trueName⟩ (cnst trueIntroName) .opaque))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.thmDecl ⟨.role .trustCompiler, [], cnst trueName⟩ (cnst trueIntroName)))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.opaqueDecl ⟨.role .trustCompiler, [], cnst trueName⟩ (cnst trueIntroName)))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.defnDecl ⟨.role .reduceBool, [], piA (cnst boolName) (cnst boolName)⟩ (lm "b" (cnst boolName) (bv 0)) .opaque))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.thmDecl ⟨.role .reduceBool, [], cnst trueName⟩ (cnst trueIntroName)))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨.role .reduceBool, [], piA (cnst boolName) (cnst boolName)⟩))
#guard isDeclined <| Cached.checkDecls .verified []
  (preludeStream.push (.axiomDecl ⟨.role .reduceNat, [], piA (cnst natName) (cnst natName)⟩))
#guard isInvalid <| Cached.checkDecls .verified []
  (preludeStream.push (.opaqueDecl ⟨.role .reduceBool, [], piA (cnst boolName) (cnst boolName)⟩ (bv 0)))
#guard isInvalid <| Cached.checkDecls .verified []
  (preludeStream.push (.opaqueDecl ⟨.role .reduceBool, [], piA (cnst boolName) (cnst boolName)⟩ (.fvar 0 (cnst trueName))))

-- 1f (`MED-8`): Typing-tier `opaqueC` and `axiomC` decline `.role _` and `.aux _` keys.
private def tierIsDeclined {α : Type} : Except (CheckError .source) α → Bool
  | .error (.notImplemented _) => true
  | _ => false

#guard match Cached.checkDecls .verified [] preludeStream with
  | .ok env =>
    let fe := mkFEnv env
    tierIsDeclined (Tier.opaqueC fe fe ⟨.role .trustCompiler, [], cnst trueName⟩ (cnst trueIntroName)) &&
    tierIsDeclined (Tier.opaqueC fe fe ⟨.aux (key "x") .recursor, [], cnst trueName⟩ (cnst trueIntroName)) &&
    tierIsDeclined (Tier.axiomC fe ⟨.role .propext, [], cnst trueName⟩) &&
    tierIsDeclined (Tier.axiomC fe ⟨.role .trustCompiler, [], cnst trueName⟩) &&
    tierIsDeclined (Tier.axiomC fe ⟨.aux (key "x") .recursor, [], cnst trueName⟩)
  | .error _ => false

/-! ## Task 2 (`h-nested-binder` / `M8`): `inductive NB | mk (f : Nat → List NB)` -/

private def mkNestedBinderBlock (base : String) : BlockRec .source × Declaration .source :=
  let kT := key base
  let kMk := key2 base "mk"
  let kRec := key2 base "rec"
  let kRec1 := key2 base "rec_1"
  let nat := cnst natName
  let listT := .app (cnst listName [.zero]) (cnst kT)
  let nilT := .app (cnst listNilName [.zero]) (cnst kT)
  let consT (h t : E) := ap3 (cnst listConsName [.zero]) (cnst kT) h t
  let fnTy := piA nat listT
  let m1Ty := piA (cnst kT) (srt u)
  let m2Ty := piA listT (srt u)
  -- `mk` minor: `∀ (f : Nat → List T), (∀ n : Nat, motive_2 (f n)) → motive_1 (T.mk f)`
  let mkMinorTy := pi "f" fnTy <|
    pi "f_ih" (pi "a" nat (.app (bv 2) (.app (bv 1) (bv 0)))) <|
    .app (bv 3) (.app (cnst kMk) (bv 1))
  -- `nil` minor: `motive_2 (List.nil T)`
  let nilMinorTy := .app (bv 1) nilT
  -- `cons` minor: `∀ (hd : T) (tl : List T), motive_1 hd → motive_2 tl → motive_2 (List.cons T hd tl)`
  let consMinorTy := pi "head" (cnst kT) <| pi "tail" listT <|
    pi "head_ih" (.app (bv 5) (bv 1)) <|
    pi "tail_ih" (.app (bv 5) (bv 1)) <|
    .app (bv 6) (consT (bv 3) (bv 2))
  let recTy := piI "motive_1" m1Ty <| piI "motive_2" m2Ty <|
    pi "mk" mkMinorTy <| pi "nil" nilMinorTy <| pi "cons" consMinorTy <|
    pi "t" (cnst kT) (.app (bv 5) (bv 0))
  let rec1Ty := piI "motive_1" m1Ty <| piI "motive_2" m2Ty <|
    pi "mk" mkMinorTy <| pi "nil" nilMinorTy <| pi "cons" consMinorTy <|
    pi "t" listT (.app (bv 4) (bv 0))
  let pLams (body : E) := lm "motive_1" m1Ty <| lm "motive_2" m2Ty <|
    lm "mk" mkMinorTy <| lm "nil" nilMinorTy <| lm "cons" consMinorTy body
  let mkRhs := pLams <| lm "f" fnTy <|
    ap2 (bv 3) (bv 0)
      (lm "a" nat (Expr.mkAppN (cnst kRec1 [u]) [bv 6, bv 5, bv 4, bv 3, bv 2, .app (bv 1) (bv 0)]))
  let nilRhs := pLams (bv 1)
  let consRhs := pLams <| lm "head" (cnst kT) <| lm "tail" listT <|
    Expr.mkAppN (bv 2) [bv 1, bv 0,
      Expr.mkAppN (cnst kRec [u]) [bv 6, bv 5, bv 4, bv 3, bv 2, bv 1],
      Expr.mkAppN (cnst kRec1 [u]) [bv 6, bv 5, bv 4, bv 3, bv 2, bv 0]]
  let cvT : ConstantVal .source := ⟨kT, [], type1⟩
  let cvMk : ConstantVal .source := ⟨kMk, [], pi "f" fnTy (cnst kT)⟩
  let cvR : ConstantVal .source := ⟨kRec, [uN], recTy⟩
  let cvR1 : ConstantVal .source := ⟨kRec1, [uN], rec1Ty⟩
  let rules0 := [rule kMk 1 mkRhs]
  let rules1 := [rule listNilName 0 nilRhs, rule listConsName 2 consRhs]
  let b : BlockRec .source :=
    ⟨[{ cv := cvT, nP := 0, nIdx := 0, ctors := [kMk], isRec := true, isReflexive := true, numNested := 1 }],
     [{ cv := cvMk, nP := 0, nF := 1 }],
     [{ cv := cvR, nP := 0, nM := 2, nm := 3, nI := 0, rules := rules0 },
      { cv := cvR1, nP := 0, nM := 2, nm := 3, nI := 0, rules := rules1 }]⟩
  let d : Declaration .source :=
    .indDecl [.indInfo cvT {}, .ctorInfo cvMk 0 1,
              .recInfo cvR 5 5 rules0, .recInfo cvR1 5 5 rules1] 0
  (b, d)

private def allBaseInfos : List (ConstantInfo .source) :=
  eqBasis ++ natBasis ++ punitBasis ++ emptyBasis ++ falseBasis ++ boolBlock ++ trueBlock ++ quotBasis ++ listBlock

private def inModelCtx (b : BlockRec .source) : Ctx .source :=
  let memberNames := b.types.map (·.cv.name)
  ⟨fun n => (allBaseInfos.find? (·.toConstantVal.name == n)).map fun ci =>
      (ci.toConstantVal.levelParams, ci.toConstantVal.type),
   fun _ => 0,
   fun n =>
     if memberNames.contains n then some b
     else if n == listName then some listBlockRec
     else none,
   fun _ => none⟩

-- `NB`: single-constructor nested-under-binder (`mk (f : Nat → List NB)`) exercises
-- both the reflexive-mimic isomorphism + iota proof AND Step 10 (`proj_0` + `proj_0.iota`).
#guard
  let (b, d) := mkNestedBinderBlock "NB"
  match generate (inModelCtx b) b with
  | .error _ => false
  | .ok gen =>
    let hasProj := gen.any fun dec => dec.names.contains (projModelName (key "NB") 0)
    match Cached.checkDecls .verified [] (preludeStream ++ gen.toArray.push d) with
    | .ok env => hasProj && (env.find? (key "NB")).isSome && (env.find? (key2 "NB" "rec")).isSome
    | .error _ => false

end Tests.Ix.Kernel.CompilerTrustAndNestedBinder
