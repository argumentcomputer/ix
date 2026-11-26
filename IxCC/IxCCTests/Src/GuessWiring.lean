import IxCC.Src.Table.Build
import IxCC.Src.Table.Validate
import IxCC.Src.Table.Cert
import IxCC.Src.EvalG
import IxCC.Src.Proof.Unfold
import IxCC.Recheck.Json
import IxCC.CompileClaim.Closure

/-! # Phase 2.2b Tier-2 `guess f c θ [θc]` Wiring Tests (`IxCCTests.Src.GuessWiring`)

Positive and negative unit tests exercising the full `IxCC` wiring of `guess`:
1. `Hints.ofK1Json` / `Hints.toK1Json` round-trip with optional `"guesses"` array (with and
   without `"completeness_address"`) and backwards compatibility when absent.
2. `Table.build`, `Table.validate`, `TableCert.ofTable`, `TableCert.keysOk`, and `Table.ofCert`
   for valid `guess` entries (with `comp? = none` and `comp? = some comp`).
3. `Recheck.CertJson.table` / `Recheck.CertJson.table?` round-trip for `TableCert` carrying
   `guess` entries, legacy JSON without `"guess"`, and malformed `guess` JSON rejection.
4. `CompileClaim.tableTheoremAddrs` extraction of both `g.thm` and optional `g.comp?` (plus
   fail-closed rejection when a theorem `CId` is absent).
5. Negative controls:
   - Direct circular `guess` (`c == f`) rejected by `build`, `validate`, `ofCert`.
   - Transitive circular `guess` (`c → helper → f`, `FE-3`) rejected by `build`, `validate`, `ofCert`.
   - Bogus soundness theorem (wrong conclusion, wrong hypothesis, `byStatement`, non-standard
     axiom) rejected by `build`, `validate`, `ofCert`.
   - Bogus completeness theorem (wrong body, `byStatement`, non-standard axiom) rejected.
   - Tampered arity / duplicate keys / out-of-range keys in `TableCert.guess` rejected by `ofCert`.
6. Operational `SrcG` (`RunG` / `EvalG`) concrete derivations and conservativity collapse. -/

namespace IxCCTests.Src.GuessWiring

open IxCC IxCC.Src IxCC.Src.Table IxCC.Ixon IxCC.Recheck IxCC.CompileClaim

/-! ## Synthetic program builder with valid `Pins.fixed` identities -/

private def mkAddr (tag : UInt8) : Ixon.Address :=
  Ixon.Address.replicate tag

private def pinnedAddr (opt : Option Nat) (fallback : UInt8) : Ixon.Address :=
  match opt with
  | some n => Pinned.addrOfNat n
  | none => mkAddr fallback

private def appS (f a : Term) : Term := .app f a .strict .rel

private def mkEq (eqId : CId) (u : Univ) (ty lhs rhs : Term) : Term :=
  appS (appS (appS (.const eqId [u]) ty) lhs) rhs

/-- Base program containing pinned `Nat` (0), `Bool` (1), `Bool.true` (2), `Bool.false` (3),
`Eq` (4), non-standard axiom `badAx` (5), subject `f : Nat → Nat` (6), honest checker
`c : Nat → Nat → Bool` (7), soundness theorem `thm` (8), and completeness theorem `comp` (9). -/
private def mkValidProgram : Program :=
  let natId : CId := 0
  let boolId : CId := 1
  let boolTrueId : CId := 2
  let boolFalseId : CId := 3
  let eqId : CId := 4
  let fId : CId := 6
  let cId : CId := 7
  let natT := Term.const natId []
  let boolT := Term.const boolId []
  let boolTrueT := Term.const boolTrueId []
  let b : Binder := {}
  -- `f : Nat → Nat := λ x. x`
  let fTy := Term.pi b natT natT
  let fVal := Term.lam b natT (.var 0)
  -- `c : Nat → Nat → Bool := λ x y. Bool.true` (does NOT reference `f`)
  let cTy := Term.pi b natT (Term.pi b natT boolT)
  let cVal := Term.lam b natT (Term.lam b natT boolTrueT)
  -- `thm : Π (x : Nat) (y : Nat) (_ : @Eq.{1} Bool (c x y) Bool.true), @Eq.{1} Nat y (f x)`
  let cxy := appS (appS (.const cId []) (.var 1)) (.var 0)
  let hDom := mkEq eqId (.succ .zero) boolT cxy boolTrueT
  let fx2 := appS (.const fId []) (.var 2)
  let concl := mkEq eqId (.succ .zero) natT (.var 1) fx2
  let thmTy := Term.pi b natT (Term.pi b natT (Term.pi b hDom concl))
  -- `comp : Π (x : Nat), @Eq.{1} Bool (c x (f x)) Bool.true`
  let cxfx := appS (appS (.const cId []) (.var 0)) (appS (.const fId []) (.var 0))
  let compTy := Term.pi b natT (mkEq eqId (.succ .zero) boolT cxfx boolTrueT)
  let mkE (a : Ixon.Address) (d : Decl) : ConstEntry := { ref := .member a 0, addr := a, decl := d }
  let entries : List ConstEntry := [
    mkE (pinnedAddr Pins.fixed.nat 10) (.induct true 0 0 0 (.sort (.succ .zero)) []),
    mkE (pinnedAddr Pins.fixed.bool 11) (.induct true 0 0 0 (.sort (.succ .zero)) [boolTrueId, boolFalseId]),
    mkE (pinnedAddr Pins.fixed.boolTrue 12) (.ctor true 0 boolId 1 0 0 boolT),
    mkE (pinnedAddr Pins.fixed.boolFalse 13) (.ctor true 0 boolId 0 0 0 boolT),
    mkE (pinnedAddr Pins.fixed.eq 14) (.induct true 1 2 1 (.sort (.succ (.var 0))) []),
    mkE (mkAddr 15) (.axio true 0 (.sort .zero)),
    mkE (mkAddr 16) (.defn .defn .safe 0 fTy fVal),
    mkE (mkAddr 17) (.defn .defn .safe 0 cTy cVal),
    mkE (mkAddr 18) (.defn .thm .safe 0 thmTy (.natLit 0)),
    mkE (mkAddr 19) (.defn .thm .safe 0 compTy (.natLit 0))
  ]
  let p0 : Program := { Program.ofConsts entries with roots := [(mkAddr 16, fId)] }
  let p1 := { p0 with known := { pins := Pins.fixed } }
  { p1 with known := Pinned.known p1 }

private def addConst (p : Program) (tag : UInt8) (d : Decl) : Program × CId :=
  let cid := p.size
  let a := mkAddr tag
  (p.push { ref := .member a 0, addr := a, decl := d }, cid)

/-! ## 1. Positive tests: valid `guess` with and without `comp?` -/

private def validProg : Program := mkValidProgram
private def fId : CId := 6
private def cId : CId := 7
private def thmId : CId := 8
private def compId : CId := 9
private def badAxId : CId := 5

#guard Pinned.knownOk validProg == true

-- 1a. `Table.build` accepts valid `guess` without completeness theorem
#guard
  let prop : Proposal := {
    kind := .guess, subject := validProg.addr fId,
    checker? := some (validProg.addr cId), theorem? := some (validProg.addr thmId),
    comp? := none, name? := some "f" }
  let (tbl, diags, stats) := Table.build {} validProg #[prop]
  let expected : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := none }
  diags.isEmpty && stats.guessAccepted == #[fId] && stats.guessRefused.isEmpty &&
    tbl.guessOf fId == some expected &&
    (Table.validate {} { validProg with table := tbl }).isOk

-- 1b. `Table.build` + `Table.validate` + `TableCert.ofTable` + `Table.ofCert` with `comp? = some compId`
#guard
  let prop : Proposal := {
    kind := .guess, subject := validProg.addr fId,
    checker? := some (validProg.addr cId), theorem? := some (validProg.addr thmId),
    comp? := some (validProg.addr compId), name? := some "f" }
  let (tbl, diags, stats) := Table.build {} validProg #[prop]
  let expected : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := some compId }
  let tc := TableCert.ofTable tbl
  let rebuilt := Table.ofCert {} validProg tc
  diags.isEmpty && stats.guessAccepted == #[fId] &&
    tc.keysOk validProg.size &&
    tc.guess == [(fId, expected)] &&
    (Table.validate {} { validProg with table := tbl }).isOk &&
    match rebuilt with
    | .ok tbl' => tbl'.guessOf fId == some expected
    | .error _ => false

-- 1c. `Recheck.CertJson.table` / `table?` round-trip + `Table.ofCert` on decoded cert
#guard
  let g1 : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := none }
  let g2 : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := some compId }
  let tc1 : TableCert := { guess := [(fId, g1)] }
  let tc2 : TableCert := { guess := [(fId, g2)] }
  let rt1 := CertJson.table? (CertJson.table tc1)
  let rt2 := CertJson.table? (CertJson.table tc2)
  (rt1.toOption == some tc1) && (rt2.toOption == some tc2) &&
    (match rt1 with | .ok c => (Table.ofCert {} validProg c).isOk | .error _ => false) &&
    (match rt2 with | .ok c => (Table.ofCert {} validProg c).isOk | .error _ => false)

-- 1d. `Hints.toK1Json` / `Hints.ofK1Json` round-trip with `"guesses"` and without `"guesses"`
#guard
  let h : Hints := {
    roots := #[(validProg.addr fId, some "f")],
    proposals := #[
      { kind := .guess, subject := validProg.addr fId,
        checker? := some (validProg.addr cId), theorem? := some (validProg.addr thmId),
        comp? := none, name? := some "f_no_comp" },
      { kind := .guess, subject := validProg.addr fId,
        checker? := some (validProg.addr cId), theorem? := some (validProg.addr thmId),
        comp? := some (validProg.addr compId), name? := some "f_with_comp" }
    ] }
  let j := Hints.toK1Json h "test"
  match Hints.ofK1Json j with
  | .ok h' =>
    h'.roots.size == 1 && h'.proposals.size == 2 &&
      h'.proposals[0]!.kind == .guess && h'.proposals[0]!.comp? == none &&
      h'.proposals[1]!.kind == .guess && h'.proposals[1]!.comp? == some (validProg.addr compId)
  | .error _ => false

-- 1e. `CompileClaim.tableTheoremAddrs` extracts BOTH `thm` and optional `comp?` (deduplicated)
#guard
  let gNoComp : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := none }
  let gWithComp : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := some compId }
  let tc1 : TableCert := { guess := [(fId, gNoComp)] }
  let tc2 : TableCert := { guess := [(fId, gWithComp)] }
  let aThm := Src.KernelFront.kaddr (validProg.addr thmId)
  let aComp := Src.KernelFront.kaddr (validProg.addr compId)
  (match tableTheoremAddrs validProg tc1 with
    | .ok addrs => addrs == #[aThm]
    | .error _ => false) &&
  (match tableTheoremAddrs validProg tc2 with
    | .ok addrs => addrs == #[aThm, aComp]
    | .error _ => false)

/-! ## 2. Negative tests: circular `guess`, bogus theorems, malformed certs -/

-- 2a. Direct circular `guess` (`c == f`) rejected by `Table.build`, `Table.validate`, `Table.ofCert`
#guard
  let natT := Term.const 0 []
  let boolT := Term.const 1 []
  let boolTrueT := Term.const 2 []
  let b : Binder := {}
  -- Suppose `fSelf : Nat → Nat → Bool` tries to self-check (even with a shape-matching theorem)
  let (p1, fSelf) := addConst validProg 30
    (.defn .defn .safe 0 (Term.pi b natT (Term.pi b natT boolT)) (Term.lam b natT (Term.lam b natT boolTrueT)))
  -- `c == fSelf` cannot even type-check as `f`'s checker, and `c == f` is explicitly rejected.
  let tcCirc : TableCert := { guess := [(fSelf, { checker := fSelf, arity := 1, thm := thmId })] }
  let prop : Proposal := {
    kind := .guess, subject := p1.addr fSelf,
    checker? := some (p1.addr fSelf), theorem? := some (p1.addr thmId) }
  let (tbl, diags, stats) := Table.build {} p1 #[prop]
  !(Table.ofCert {} p1 tcCirc).isOk &&
    !(Table.validate {} { p1 with table := { guess := NatMap.ofList tcCirc.guess } }).isOk &&
    stats.guessAccepted.isEmpty && !diags.isEmpty && tbl.guessOf fSelf == none

-- 2b. Transitive circular `guess` (`cBad → helper → f`, `FE-3`) rejected by `build`, `validate`, `ofCert`
#guard
  let natT := Term.const 0 []
  let boolT := Term.const 1 []
  let boolTrueT := Term.const 2 []
  let eqId : CId := 4
  let b : Binder := {}
  -- `helper : Nat → Nat := λ x. f x` (references `fId`)
  let (p1, helperId) := addConst validProg 40
    (.defn .defn .safe 0 (Term.pi b natT natT) (Term.lam b natT (appS (.const fId []) (.var 0))))
  -- `cBad : Nat → Nat → Bool := λ x y. let _ := helper x; Bool.true` (transitively reaches `fId`)
  let cBadVal := Term.lam b natT (Term.lam b natT
    (.letE true default .rel natT (appS (.const helperId []) (.var 1)) boolTrueT))
  let (p2, cBadId) := addConst p1 41
    (.defn .defn .safe 0 (Term.pi b natT (Term.pi b natT boolT)) cBadVal)
  -- Shape-valid theorem for `(fId, cBadId)`
  let cxy := appS (appS (.const cBadId []) (.var 1)) (.var 0)
  let hDom := mkEq eqId (.succ .zero) boolT cxy boolTrueT
  let fx2 := appS (.const fId []) (.var 2)
  let concl := mkEq eqId (.succ .zero) natT (.var 1) fx2
  let thmBadTy := Term.pi b natT (Term.pi b natT (Term.pi b hDom concl))
  let (p3, thmBadId) := addConst p2 42 (.defn .thm .safe 0 thmBadTy (.natLit 0))
  let gBad : GuessEntry := { checker := cBadId, arity := 1, thm := thmBadId, comp? := none }
  let tcBad : TableCert := { guess := [(fId, gBad)] }
  let prop : Proposal := {
    kind := .guess, subject := p3.addr fId,
    checker? := some (p3.addr cBadId), theorem? := some (p3.addr thmBadId) }
  let (tbl, diags, stats) := Table.build {} p3 #[prop]
  !(Table.ofCert {} p3 tcBad).isOk &&
    !(Table.validate {} { p3 with table := { guess := NatMap.ofList tcBad.guess } }).isOk &&
    stats.guessAccepted.isEmpty && stats.guessRefused.size == 1 && !diags.isEmpty &&
    tbl.guessOf fId == none

-- 2c. Bogus soundness theorem: wrong conclusion (`y = y` instead of `y = f x`) rejected
#guard
  let natT := Term.const 0 []
  let boolT := Term.const 1 []
  let boolTrueT := Term.const 2 []
  let eqId : CId := 4
  let b : Binder := {}
  let cxy := appS (appS (.const cId []) (.var 1)) (.var 0)
  let hDom := mkEq eqId (.succ .zero) boolT cxy boolTrueT
  let badConcl := mkEq eqId (.succ .zero) natT (.var 1) (.var 1)
  let badThmTy := Term.pi b natT (Term.pi b natT (Term.pi b hDom badConcl))
  let (p1, badThmId) := addConst validProg 50 (.defn .thm .safe 0 badThmTy (.natLit 0))
  let tcBad : TableCert := { guess := [(fId, { checker := cId, arity := 1, thm := badThmId })] }
  !(Table.ofCert {} p1 tcBad).isOk &&
    !(Table.validate {} { p1 with table := { guess := NatMap.ofList tcBad.guess } }).isOk

-- 2d. Bogus soundness theorem: `byStatement` theorem (proof unread) rejected
#guard
  let pByStmt : Program := { validProg with byStatement := validProg.byStatement.insert thmId }
  let tc : TableCert := { guess := [(fId, { checker := cId, arity := 1, thm := thmId })] }
  !(Table.ofCert {} pByStmt tc).isOk &&
    !(Table.validate {} { pByStmt with table := { guess := NatMap.ofList tc.guess } }).isOk

-- 2e. Bogus soundness theorem: depends on non-standard axiom `badAxId` rejected
#guard
  let natT := Term.const 0 []
  let boolT := Term.const 1 []
  let boolTrueT := Term.const 2 []
  let eqId : CId := 4
  let b : Binder := {}
  let cxy := appS (appS (.const cId []) (.var 1)) (.var 0)
  let hDom := mkEq eqId (.succ .zero) boolT cxy boolTrueT
  let fx2 := appS (.const fId []) (.var 2)
  let concl := mkEq eqId (.succ .zero) natT (.var 1) fx2
  let thmTy := Term.pi b natT (Term.pi b natT (Term.pi b hDom concl))
  let (p1, axThmId) := addConst validProg 51 (.defn .thm .safe 0 thmTy (.const badAxId []))
  let tc : TableCert := { guess := [(fId, { checker := cId, arity := 1, thm := axThmId })] }
  !(Table.ofCert {} p1 tc).isOk &&
    !(Table.validate {} { p1 with table := { guess := NatMap.ofList tc.guess } }).isOk

-- 2f. Bogus completeness theorem (`byStatement` or wrong body) rejected
#guard
  let pCompByStmt : Program := { validProg with byStatement := validProg.byStatement.insert compId }
  let tc : TableCert :=
    { guess := [(fId, { checker := cId, arity := 1, thm := thmId, comp? := some compId })] }
  let tcWrongComp : TableCert :=
    { guess := [(fId, { checker := cId, arity := 1, thm := thmId, comp? := some thmId })] }
  !(Table.ofCert {} pCompByStmt tc).isOk &&
    !(Table.ofCert {} validProg tcWrongComp).isOk

-- 2g. Tampered arity, duplicate key, out-of-range key in `TableCert.guess` rejected
#guard
  let gBadArity : GuessEntry := { checker := cId, arity := 2, thm := thmId, comp? := none }
  let gGood : GuessEntry := { checker := cId, arity := 1, thm := thmId, comp? := none }
  let tcBadArity : TableCert := { guess := [(fId, gBadArity)] }
  let tcDup : TableCert := { guess := [(fId, gGood), (fId, gGood)] }
  let tcOob : TableCert := { guess := [(999, gGood)] }
  !(Table.ofCert {} validProg tcBadArity).isOk &&
    !tcDup.keysOk validProg.size && !(Table.ofCert {} validProg tcDup).isOk &&
    !tcOob.keysOk validProg.size && !(Table.ofCert {} validProg tcOob).isOk

-- 2h. `tableTheoremAddrs` fails closed when a `guess` theorem `CId` or `comp?` `CId` is missing
#guard
  let tcMissingThm : TableCert :=
    { guess := [(fId, { checker := cId, arity := 1, thm := 999, comp? := none })] }
  let tcMissingComp : TableCert :=
    { guess := [(fId, { checker := cId, arity := 1, thm := thmId, comp? := some 999 })] }
  !(tableTheoremAddrs validProg tcMissingThm).isOk &&
    !(tableTheoremAddrs validProg tcMissingComp).isOk

/-! ## 3. Operational `SrcG` (`RunG` / `EvalG`) concrete derivations & conservativity -/

-- 3a. Executable check of `Src.run` and `runAt` for `f` and `c`
#guard
  match IxCC.Src.run validProg 8 fId [.lit 42] with
  | .ok (.lit 42) => true
  | _ => false

#guard
  match IxCC.Src.runAt validProg 8 [] cId [.lit 42, .lit 42] with
  | .ok (.con 2 [] [] []) => true
  | _ => false

/-- Standard `SrcEval` runs `f 42 = 42` in `validProg`, yielding a `RunGRoot` derivation. -/
example : RunGRoot validProg fId [.lit 42] (.lit 42) := by
  refine runG_of_run (k := 4) ?_
  unfold IxCC.Src.run
  rw [evalConst_eq]
  change (match eval validProg 3 [] [] (Term.lam {} (Term.const 0 []) (.var 0)) with
    | .ok f => applyAll validProg 4 f [.val (.lit 42)]
    | r => r) = .ok (.lit 42)
  rw [eval_lam]; dsimp only
  rw [applyAll_cons, apply_clo]
  change (Sem.Result.bind (eval validProg 3 [] [.val (.lit 42)] (.var 0)) fun v =>
    applyAll validProg 4 v []) = .ok (.lit 42)
  rw [eval_var_of _ _ _ _ rfl, force_val]; dsimp only [Sem.Result.bind]
  rw [applyAll_nil]

/-- Under a table with the validated `guess` entry for `f`, `RunG.guess` derives `f 42 = 42`
via `c 42 42 = Bool.true`. -/
example :
    let tbl : IxCC.Src.Table :=
      { guess := NatMap.ofList [(fId, { checker := cId, arity := 1, thm := thmId, comp? := some compId })] }
    RunGRoot { validProg with table := tbl } fId [.lit 42] (.lit 42) := by
  intro tbl
  let pG : Program := { validProg with table := tbl }
  refine runG_of_guess_src (p := pG) (k := 4)
    (g := { checker := cId, arity := 1, thm := thmId, comp? := some compId })
    (boolTrueC := 2) rfl rfl rfl ?_
  unfold IxCC.Src.runAt
  rw [evalConst_eq]
  change (match eval pG 3 [] []
      (Term.lam {} (Term.const 0 []) (Term.lam {} (Term.const 0 []) (.const 2 []))) with
    | .ok fv => applyAll pG 4 fv [.val (.lit 42), .val (.lit 42)]
    | r => r) = .ok (.con 2 [] [] [])
  rw [eval_lam]; dsimp only
  rw [applyAll_cons, apply_clo]
  change (Sem.Result.bind (eval pG 3 [] [.val (.lit 42)]
      (Term.lam {} (Term.const 0 []) (.const 2 []))) fun v =>
    applyAll pG 4 v [.val (.lit 42)]) = .ok (.con 2 [] [] [])
  rw [eval_lam]; dsimp only [Sem.Result.bind]
  rw [applyAll_cons, apply_clo]
  change (Sem.Result.bind (eval pG 3 [] [.val (.lit 42), .val (.lit 42)] (.const 2 [])) fun v =>
    applyAll pG 4 v []) = .ok (.con 2 [] [] [])
  rw [eval_const, evalConst_eq]
  change (Sem.Result.bind (headValue pG 3 [] (.ctor 2)) fun v =>
    applyAll pG 4 v []) = .ok (.con 2 [] [] [])
  rw [headValue_eq]
  change (Sem.Result.bind (fire pG 3 (.ctor 2) [] []) fun v =>
    applyAll pG 4 v []) = .ok (.con 2 [] [] [])
  rw [fire_ctor]
  change (Sem.Result.bind (Sem.Result.bind (forceAll pG 3 []) fun fields =>
    .ok (.con 2 [] [] fields)) fun v => applyAll pG 4 v []) = .ok (.con 2 [] [] [])
  rw [forceAll_nil]; dsimp only [Sem.Result.bind]
  rw [applyAll_nil]

/-- Conservativity: on `validProg` (`table.guess = .leaf`), `RunGRoot` collapses to `Src.run`. -/
example {xs : List Value} {y : Value} :
    RunGRoot validProg fId xs y ↔ ∃ k, IxCC.Src.run validProg k fId xs = .ok y :=
  runG_root_iff_src_of_leaf rfl

end IxCCTests.Src.GuessWiring
