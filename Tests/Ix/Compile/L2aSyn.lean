/-
  l2a-syn (M7 L2a-syn): the domain of the image construction on the `pass3` fixtures, the
  restated construction at X1's core against the executable, and the fuel of the call-site
  development on a family where it is not linear in the height (finding D-L2S-1).

  Per compile unit (the `pass3` suite's units, compiled in-process under Pass 3), for every Lean
  recursor of every changed block's view:

  * `Dom` (`Ix.CompileCert.Img.Dom`: the construction with the checking development succeeds);
  * the closedness hypotheses of the totality theorem on the constants the image reads (the
    recursor's type and rules, its constructors' types);
  * `imageOfP` (the restatement at X1's table-free core, what the theorems are about) against
    `imageOf` (the executable): value, type and every rule statement, by hash.

  Then the D-L2S-1 family `instantiate (λ x₁ x₂. x₁ (λ y. h (gᴺ y) x₂)) [λ w. wᴺ c, c₂]`: the least
  fuel the core needs, against the input's height, for growing `N`.

  Run with: `lake test -- --ignored l2a-syn` (`L2A_SYN_ONLY` restricts the units:
  comma-separated stems).
-/
import Tests.Ix.Compile.Pass3
import Ix.CompileCert.Image.Total

open Lean (Environment)

namespace Tests.Ix.Compile.L2aSyn

open _root_.Ix (Name Level Expr ConstantInfo)
open _root_.Ix.Compile.Image

/-! ## Per recursor -/

structure Row where
  rec_ : Name
  dom : Bool
  closed : Bool
  exec : Bool
  core : Bool
  same : Bool

def closedE (e : Expr) : Bool :=
  match e with
  | .fvar .. => false
  | .app f a _ => closedE f && closedE a
  | .lam _ t b _ _ | .forallE _ t b _ _ => closedE t && closedE b
  | .letE _ t v b _ _ => closedE t && closedE v && closedE b
  | .mdata _ x _ | .proj _ _ x _ => closedE x
  | _ => true

def sameImage (a b : Image) : Bool :=
  a.value == b.value && a.type == b.type && a.rules.size == b.rules.size &&
    (a.rules.zip b.rules).all fun (x, y) => x.type == y.type && x.proof == y.proof && x.name == y.name

def row (const? : Name → Option ConstantInfo) (spec : ImageSpec) (r : Name) : Row := Id.run do
  let dom := (_root_.Ix.CompileCert.Img.imageOfW _root_.Ix.CompileCert.Img.domDev {} const? spec r).isOk
  let closed := match const? r with
    | some (.recInfo rv) =>
      closedE rv.cnst.type && rv.rules.all (fun rl => closedE rl.rhs) &&
        rv.rules.all fun rl => match const? rl.ctor with
          | some ci => closedE ci.getCnst.type
          | none => true
    | _ => false
  let e := imageOf {} const? spec r
  let p := _root_.Ix.CompileCert.Img.imageOfP {} const? spec r
  let same := match e, p with
    | .ok a, .ok b => sameImage a b
    | _, _ => false
  return { rec_ := r, dom, closed, exec := e.isOk, core := p.isOk, same }

structure UnitResult where
  rows : Array Row := #[]
  problems : Array String := #[]

def runCompiled (cenv : _root_.Ix.CompileM.CompileEnv) : UnitResult := Id.run do
  let mut res : UnitResult := {}
  let inp := _root_.Ix.Compile.Pass.viewInput cenv
  for (key, all) in cenv.p3Blocks do
    match _root_.Ix.Compile.Pass.buildView inp all with
    | .error e => res := { res with problems := res.problems.push s!"view {key.pretty}: {e}" }
    | .ok v =>
      for r in (_root_.Ix.Compile.Pass.imageKinds inp.const? all).filter
          (fun r => match inp.const? r with | some (.recInfo _) => true | _ => false) do
        if cenv.ungrounded.contains r then continue
        res := { res with rows := res.rows.push (row (v.const? inp) v.spec r) }
  return res

def summary (name : String) (r : UnitResult) : Array String := Id.run do
  let n := r.rows.size
  let dom := (r.rows.filter (·.dom)).size
  let closed := (r.rows.filter (·.closed)).size
  let exec := (r.rows.filter (·.exec)).size
  let core := (r.rows.filter (·.core)).size
  let same := (r.rows.filter (·.same)).size
  let mut out := #[s!"{name}: recursors={n} Dom={dom} closed={closed} executable-ok={exec} core-ok={core} core=executable={same}"]
  for row in r.rows do
    if !row.dom || !row.closed || !row.same then
      out := out.push s!"{name}:   {row.rec_.pretty}: Dom={row.dom} closed={row.closed} exec={row.exec} core={row.core} same={row.same}"
  for p in r.problems do out := out.push s!"{name}: PROBLEM {p}"
  return out

/-! ## D-L2S-1: the call-site development's fuel against the height -/

def nm (s : String) : Name := _root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon s
def ty : Expr := Expr.mkSort lvlZero
def iter (n : Nat) (f : Expr → Expr) (x : Expr) : Expr := (List.range n).foldl (fun t _ => f t) x

/-- `(λ x₁ x₂. x₁ (λ y. h (gᴺ y) x₂), [λ w. wᴺ c, c₂])`. -/
def family (n : Nat) : Expr × Array Expr :=
  let h := Expr.mkConst (nm "h") #[]
  let g := Expr.mkConst (nm "g") #[]
  let w := Expr.mkLam (nm "y") ty
    (Expr.mkApp (Expr.mkApp h (iter n (Expr.mkApp g) (Expr.mkBVar 0))) (Expr.mkBVar 1)) .default
  let f := Expr.mkLam (nm "x1") ty (Expr.mkLam (nm "x2") ty (Expr.mkApp (Expr.mkBVar 1) w) .default) .default
  let a1 := Expr.mkLam (nm "w") ty (iter n (Expr.mkApp (Expr.mkBVar 0)) (Expr.mkConst (nm "c") #[])) .default
  (f, #[a1, Expr.mkConst (nm "c2") #[]])

/-- The least fuel with which the core's call-site development succeeds (it is monotone in the
fuel, X1's `fuel_mono`). -/
def leastFuel (f : Expr) (args : Array Expr) : Nat := Id.run do
  let ok := fun (m : Nat) => (_root_.Ix.CompileCert.Conv.happP m f args.toList).isOk
  let mut hi := 1
  while !ok hi && hi < (1 <<< 24) do hi := hi * 2
  let mut lo := 0
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ok mid then hi := mid else lo := mid
  return hi

def run (env : Environment) : IO UInt32 := do
  let _ := env
  let only := ((← IO.getEnv "L2A_SYN_ONLY").map (·.splitOn ",")).getD []
  let want := fun (s : String) => only.isEmpty || only.contains s
  let files := Tests.Ix.Compile.Pass3.auxCertFiles ++ Tests.Ix.Compile.Pass3.protoFiles ++
    Tests.Ix.Compile.Pass3.passFiles ++ Tests.Ix.Compile.Pass3.pjPassFiles
  let mut all : UnitResult := {}
  let mut units := 0
  for p in files do
    let stem := (System.FilePath.mk p).fileStem.getD p
    if !want stem || Tests.Ix.Compile.Pass3.leanRejects.contains stem then continue
    try
      let u ← Tests.Ix.Compile.Pass3.unitOfFile p
      let on ← Tests.Ix.Compile.Pass3.compileUnit u
      let r := runCompiled on.cenv
      units := units + 1
      for l in summary stem r do IO.println s!"[l2a-syn] {l}"
      all := { rows := all.rows ++ r.rows, problems := all.problems ++ r.problems.map (s!"{stem}: " ++ ·) }
    catch e =>
      IO.println s!"[l2a-syn] {stem}: compile refused ({(toString e).take 160})"
  for l in summary "TOTAL" all do IO.println s!"[l2a-syn] {l}"
  -- D-L2S-1
  for n in [2, 4, 8, 16, 32, 64] do
    let (f, args) := family n
    let h := args.foldl (fun m a => max m (_root_.Ix.CompileCert.Img.hgt a)) (_root_.Ix.CompileCert.Img.hgt f)
    let fuel := leastFuel f args
    IO.println s!"[l2a-syn] D-L2S-1 N={n}: input height={h} least fuel={fuel} fuel/height={fuel / h}"
  IO.println s!"[l2a-syn] {units} units, {all.rows.size} recursors, {all.problems.size} problem(s)"
  let bad := all.rows.filter fun r => !r.dom || !r.closed || !r.same
  return if bad.isEmpty && all.problems.isEmpty then 0 else 1

end Tests.Ix.Compile.L2aSyn
