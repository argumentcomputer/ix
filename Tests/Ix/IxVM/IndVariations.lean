import Ix.Meta
import Ix.CompileCertified
import Ix.IxVM.ClaimHarness
import Tests.Ix.IxVM.Harness
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.IxVM.IndVariationsDefs

/-!
# The inductive variations through three checkers

`ixvm-ind-variations` (manual) runs every fixture through Lean's kernel, the
certified kernel (IxC, `ixonVerdicts`, as `ix check-lean` checks a record) and
IxVM (a `CheckEnv` claim owning the fixture's records, everything else assumed,
in circuit-verdict mode), and prints one row per fixture.

Fixtures are of three kinds:
- **honest**: the declarations of `IndVariationsDefs`, elaborated and checked by
  Lean, with theorems that exercise iota, eta, projections and K; also each
  base block's records copied under a fresh name (`ctl-*`), which validates the
  renaming and Lean's replay oracle;
- **must-reject**: a base block's records, mutated (rules, flags, counts, types,
  safety), copied under a fresh name. Lean's verdict is its replay: the
  mutated block's declaration is added with `Kernel.Environment.addDecl`, and
  every record must equal the one Lean generates, as lean4checker's replay
  requires;
- **addDecl**: declarations Lean's elaborator does not produce, decided by
  `addDecl` alone (a recursive occurrence under a redex or behind a definition,
  a nested occurrence behind a definition or in an index position, `.proj` on
  shapes the elaborator never projects at). Where Lean refuses the inductive,
  the recursor is a hand-built `casesOn`-shaped record.

IxVM's case is submitted with the verdict the program in force is expected to
give (`expectedVerdict`): Lean's, except where the program refuses by design what
Lean accepts (`refusedByDesign`; a fixture that owns a recursor of a mutual or
nested family, while `modeledRecursorsRefused`) and where a mutation Lean refuses
never reaches the claim (`outsideTheClaim`). A `FAILED` line from the host is a
disagreement with that expectation; the `IV` rows carry Lean's and IxC's
verdicts and the expectation. -/

namespace Tests.Ix.IxVM.IndVariations

open Lean

/-- Fixtures Lean accepts and the program refuses by design, with the reason. -/
def refusedByDesign : List (String × String) := [
  ("h-mutual-nonrec-eta", "no structure eta at a mutual block"),
  ("h-mutual-nonrec-unit", "no unit-like conversion at a mutual block"),
  ("h-nested-struct-proj", "no projection at a member of a mutual or nested block"),
  ("p-mutual-nonrec-fn", "no projection at a member of a mutual or nested block"),
  ("p-nested-struct-thm", "no projection at a member of a mutual or nested block"),
  ("p-mutual-nonrec-thm", "no projection at a member of a mutual or nested block"),
  ("h-nested-binder", "a nested occurrence under a binder has no model"),
  ("a-redex-rec", "a field that mentions the block only where reduction erases it"),
  ("a-phantom-def", "a field that mentions the block only where reduction erases it"),
  -- positivity on the native route reads the field as stored: an occurrence of the block
  -- under a definition's head is refused, though it is the block itself after unfolding
  ("a-rec-behind-def", "a recursive occurrence behind a definition")]

/-- Mutations Lean's replay refuses whose forged record does not reach the claim: the
compiler does not write it, or the claim builder leaves it out as unsafe. The claim then
owns the honest records alone, and is accepted. -/
def outsideTheClaim : List String := ["small-type", "unsafe-rec"]

/-- Whether the records hold a recursor of a mutual or nested family. -/
def ownsFamilyRecursor (records : List ConstantInfo) : Bool :=
  records.any fun
    | .recInfo r => r.numMotives > 1
    | _ => false

/-- The verdict expected of the program in force, and the refusal's message where one
refusal is expected before any other. -/
def expectedVerdict (id : String) (leanOk : Bool) (records : List ConstantInfo) :
    Bool × Option String :=
  if outsideTheClaim.contains id then (true, none)
  else if !leanOk then (false, none)
  else if (refusedByDesign.lookup id).isSome then (false, none)
  else if Tests.Ix.IxVM.modeledRecursorsRefused && ownsFamilyRecursor records then
    (false, some Tests.Ix.IxVM.modeledRecursorRefusal)
  else (true, none)

/-! ## Records -/

/-- The records of the block declaring `seed`: types, constructors, recursors
(with the nested auxiliaries). -/
def blockOf (env : Environment) (seed : Name) : List ConstantInfo := Id.run do
  let some (.inductInfo v) := env.find? seed | return []
  let mut out : List ConstantInfo := []
  for t in v.all do
    if let some (.inductInfo w) := env.find? t then
      out := out ++ [.inductInfo w]
      for c in w.ctors do
        if let some ci := env.find? c then out := out ++ [ci]
  for t in v.all do
    if let some ci := env.find? (mkRecName t) then out := out ++ [ci]
  if let some first := v.all.head? then
    for i in [0:v.numNested] do
      if let some ci := env.find? (first.str s!"rec_{i + 1}") then out := out ++ [ci]
  return out

def renameCI (rn : Name → Name) (re : Expr → Expr) : ConstantInfo → ConstantInfo
  | .inductInfo v => .inductInfo { v with
      name := rn v.name, type := re v.type, all := v.all.map rn, ctors := v.ctors.map rn }
  | .ctorInfo v => .ctorInfo { v with name := rn v.name, type := re v.type, induct := rn v.induct }
  | .recInfo v => .recInfo { v with
      name := rn v.name, type := re v.type, all := v.all.map rn,
      rules := v.rules.map fun r => { r with ctor := rn r.ctor, rhs := re r.rhs } }
  | .defnInfo v => .defnInfo { v with
      name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | .thmInfo v => .thmInfo { v with
      name := rn v.name, type := re v.type, value := re v.value, all := v.all.map rn }
  | ci => ci

/-- Copy records under `IxIV.M.<tag>`, renaming every reference to them. -/
def renameAll (tag : String) (cis : List ConstantInfo) : List ConstantInfo :=
  let names := cis.map (·.name)
  let pre : Name := `IxIV.M ++ Name.mkSimple tag
  let rn (n : Name) : Name := if names.contains n then n.replacePrefix `IxIV pre else n
  let re (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => if names.contains n then some (.const (rn n) ls) else none
    | _ => none
  cis.map (renameCI rn re)

def mapRec (n : Name) (f : RecursorVal → RecursorVal) : List ConstantInfo → List ConstantInfo :=
  List.map fun ci => match ci with
    | .recInfo v => if v.name == n then .recInfo (f v) else ci
    | _ => ci

def mapCtor (n : Name) (f : ConstructorVal → ConstructorVal) : List ConstantInfo → List ConstantInfo :=
  List.map fun ci => match ci with
    | .ctorInfo v => if v.name == n then .ctorInfo (f v) else ci
    | _ => ci

def mapInd (n : Name) (f : InductiveVal → InductiveVal) : List ConstantInfo → List ConstantInfo :=
  List.map fun ci => match ci with
    | .inductInfo v => if v.name == n then .inductInfo (f v) else ci
    | _ => ci

def dropRec (n : Name) (cis : List ConstantInfo) : List ConstantInfo := cis.filter (·.name != n)

def swap01 (rs : List RecursorRule) : List RecursorRule :=
  match rs with
  | r0 :: r1 :: rest => { r0 with rhs := r1.rhs } :: { r1 with rhs := r0.rhs } :: rest
  | _ => rs

/-- The inductive declaration the records' types and constructors make. -/
def toInductDecl (cis : List ConstantInfo) : Option Declaration := do
  let inds := cis.filterMap fun ci => match ci with | .inductInfo v => some v | _ => none
  let v0 ← inds.head?
  let ctorTy (n : Name) : Option Expr := cis.findSome? fun ci => match ci with
    | .ctorInfo c => if c.name == n then some c.type else none
    | _ => none
  let types ← v0.all.mapM fun t => do
    let v ← inds.find? (·.name == t)
    let cs ← v.ctors.mapM fun cn => do
      let ty ← ctorTy cn
      pure ({ name := cn, type := ty } : Constructor)
    pure ({ name := t, type := v.type, ctors := cs } : InductiveType)
  return .inductDecl v0.levelParams v0.numParams types v0.isUnsafe

def sameRecord : ConstantInfo → ConstantInfo → Bool
  | .inductInfo a, .inductInfo b =>
    a.type == b.type && a.levelParams == b.levelParams && a.numParams == b.numParams &&
    a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors && a.isRec == b.isRec &&
    a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive && a.numNested == b.numNested
  | .ctorInfo a, .ctorInfo b =>
    a.type == b.type && a.levelParams == b.levelParams && a.induct == b.induct && a.cidx == b.cidx &&
    a.numParams == b.numParams && a.numFields == b.numFields && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    a.type == b.type && a.levelParams == b.levelParams && a.all == b.all &&
    a.numParams == b.numParams && a.numIndices == b.numIndices && a.numMotives == b.numMotives &&
    a.numMinors == b.numMinors && a.k == b.k && a.isUnsafe == b.isUnsafe &&
    a.rules.length == b.rules.length &&
    (a.rules.zip b.rules).all fun (x, y) => x.ctor == y.ctor && x.nfields == y.nfields && x.rhs == y.rhs
  | _, _ => false

/-! ## Lean's verdict -/

/-- Add `decls` in order, then require every record of `replay` to be the one
Lean generated. -/
def leanVerdict (leanEnv : Environment) (decls : List Declaration) (replay : List ConstantInfo) :
    IO (Bool × String × Kernel.Environment) := do
  let mut kenv := leanEnv.toKernelEnv
  for d in decls do
    match kenv.addDecl {} d with
    | .ok k => kenv := k
    | .error e =>
      let msg ← (e.toMessageData {}).toString
      return (false, s!"kernel: {(msg.replace "\n" " ").take 200}", kenv)
  for ci in replay do
    match kenv.find? ci.name with
    | none => return (false, s!"replay: {ci.name} is not a record Lean generates", kenv)
    | some g =>
      unless sameRecord g ci do
        return (false, s!"replay: {ci.name} differs from the record Lean generates", kenv)
  return (true, "accepted", kenv)

/-! ## Builders for hand-made declarations -/

def u1 : Level := .succ .zero

/-- `a → b`. -/
def arr (a b : Expr) : Expr := .forallE `x a b .default

/-- `List.{l} a`. -/
def listOf (l : Level) (a : Expr) : Expr := mkApp (mkConst ``List [l]) a

/-- `∀ x : T, x = C x.0 … x.(n-1)`, proved by `Eq.refl x`. -/
def etaThm (name T C : Name) (n : Nat) : Declaration :=
  let tT := mkConst T
  let rhs := mkAppN (mkConst C) ((Array.range n).map fun i => Expr.proj T i (.bvar 0))
  let ty := Expr.forallE `x tT (mkAppN (mkConst ``Eq [u1]) #[tT, .bvar 0, rhs]) .default
  let val := Expr.lam `x tT (mkAppN (mkConst ``Eq.refl [u1]) #[tT, .bvar 0]) .default
  .thmDecl { name, levelParams := [], type := ty, value := val }

/-- `def name : dom → cod := fun x => x.i` at the struct type `S`. -/
def projDef (name S : Name) (dom cod : Expr) (i : Nat) : Declaration :=
  .defnDecl {
    name, levelParams := [], type := .forallE `x dom cod .default,
    value := .lam `x dom (.proj S i (.bvar 0)) .default, hints := .opaque, safety := .safe }

/-- `theorem name : ∀ x : dom, x.i = x.i := fun x => Eq.refl x.i`, with `x.i : cod : Sort l`. -/
def projThm (name S : Name) (dom cod : Expr) (l : Level) (i : Nat) : Declaration :=
  let p := Expr.proj S i (.bvar 0)
  .thmDecl {
    name, levelParams := [],
    type := .forallE `x dom (mkAppN (mkConst ``Eq [l]) #[cod, p, p]) .default,
    value := .lam `x dom (mkAppN (mkConst ``Eq.refl [l]) #[cod, p]) .default }

/-- A one-constructor, one-field inductive `T : Type`, `T.mk : D → T` (`D` closed,
may mention `T`), with a hand-built `casesOn`-shaped recursor (no hypotheses). -/
def oneField (T : Name) (D : Expr) (nested : Nat := 0) : Declaration × List ConstantInfo :=
  let tT := mkConst T
  let mk := T.str "mk"
  let ctorTy := Expr.forallE `a D tT .default
  let ity : InductiveType := { name := T, type := .sort u1, ctors := [{ name := mk, type := ctorTy }] }
  let decl := Declaration.inductDecl [] 0 [ity] false
  let motiveTy := Expr.forallE `t tT (.sort (.param `u)) .default
  let minorTy := Expr.forallE `a D (.app (.bvar 1) (.app (mkConst mk) (.bvar 0))) .default
  let recTy := Expr.forallE `motive motiveTy (.forallE `mk minorTy
    (.forallE `t tT (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit
  let rhs := Expr.lam `motive motiveTy (.lam `mk minorTy (.lam `a D (.app (.bvar 1) (.bvar 0)) .default)
    .default) .default
  let ind : InductiveVal := {
    name := T, levelParams := [], type := .sort u1, numParams := 0,
    numIndices := 0, all := [T], ctors := [mk], numNested := nested, isRec := true, isUnsafe := false,
    isReflexive := false }
  let ctor : ConstructorVal := {
    name := mk, levelParams := [], type := ctorTy, induct := T, cidx := 0,
    numParams := 0, numFields := 1, isUnsafe := false }
  let r : RecursorVal := {
    name := T.str "rec", levelParams := [`u], type := recTy, all := [T],
    numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := mk, nfields := 1, rhs }], k := false, isUnsafe := false }
  (decl, [.inductInfo ind, .ctorInfo ctor, .recInfo r])

/-- The end of a telescope, a sort, replaced by `Sort (param u)`. -/
def endSort (u : Name) : Expr → Expr
  | .forallE n d b bi => .forallE n d (endSort u b) bi
  | .sort _ => .sort (.param u)
  | e => e

/-- Replace the sort at the end of the motive binders' types (the binders
`np … np + nm - 1` of a recursor type) by `Sort (param u)`. -/
def largeMotives (u : Name) (np nm : Nat) (e : Expr) (i : Nat := 0) : Expr :=
  match e with
  | .forallE n d b bi =>
    let d' := if np ≤ i && i < np + nm then endSort u d else d
    .forallE n d' (largeMotives u np nm b (i + 1)) bi
  | e => e

/-- The large eliminator a small one would be: a fresh level parameter and the
motives into `Sort u`. -/
def mkLarge (r : RecursorVal) : RecursorVal :=
  { r with
    levelParams := `uL :: r.levelParams,
    type := largeMotives `uL r.numParams r.numMotives r.type }

/-- The small eliminator a large one would be: the elimination level dropped,
the motives into `Prop`. -/
def mkSmall (r : RecursorVal) : RecursorVal :=
  match r.levelParams with
  | u :: rest =>
    let ty := (largeMotives `uDrop r.numParams r.numMotives r.type).replaceLevel fun l =>
      match l with
      | .param p => if p == `uDrop || p == u then some .zero else none
      | _ => none
    { r with levelParams := rest, type := ty }
  | [] => r

/-! ## Fixtures -/

structure Fx where
  id : String
  dim : String
  /-- `honest`, `must-reject`, `addDecl` -/
  kind : String
  intent : String
  records : List ConstantInfo
  /-- `none`: the records are Lean's own, accepted when `IndVariationsDefs` was
  checked; otherwise the declarations Lean decides and the records it must have
  generated. -/
  lean : Option (List Declaration × List ConstantInfo) := none

def ixiv (s : String) : Name := `IxIV ++ (s.splitOn ".").foldl (fun n c => n.str c) .anonymous

/-- The honest fixtures: each base block with the theorems about it. -/
def honest (env : Environment) : List Fx :=
  let thm (s : String) : List ConstantInfo := (env.find? (ixiv s)).toList
  let blk (s : String) : List ConstantInfo := blockOf env (ixiv s)
  let mk (id dim : String) (b : String) (thms : List String) : Fx :=
    { id, dim, kind := "honest", intent := s!"{b} as Lean elaborates it",
      records := blk b ++ thms.flatMap thm }
  [ mk "h-enum" "enum (native)" "Color" ["Color.rec'"],
    mk "h-struct" "structure: eta, projection (native)" "Pt" ["Pt.eta'", "Pt.proj'"],
    mk "h-unitlike" "unit-like eta (native)" "U0" ["U0.uniq"],
    mk "h-prop-struct" "Prop structure: eta" "PA" ["PA.eta'"],
    mk "h-class" "class (structure)" "Cls" ["Cls.app'"],
    mk "h-univpoly" "universe-polymorphic structure: eta" "Box" ["Box.eta'"],
    mk "h-rec" "recursive (native)" "Tr" ["Tr.rec'"],
    mk "h-rec-structlike" "recursive one-constructor (native, no eta)" "RS" [],
    mk "h-reflexive" "reflexive (native)" "W" ["W.rec'"],
    mk "h-indexed" "indexed family (native)" "Vec" [],
    mk "h-indexed-onector" "one-constructor indexed family" "IV1" [],
    mk "h-prop-K" "Prop, large elim, K: K-reduction" "Eq'" ["Eq'.k"],
    mk "h-prop-acc" "Prop, large elim, reflexive (Acc)" "Acc'" [],
    mk "h-prop-small" "Prop, small elim (Or)" "Or'" [],
    mk "h-prop-small-data" "Prop, small elim, data field (Exists)" "Ex'" [],
    mk "h-prop-empty" "empty Prop" "F0" [],
    mk "h-type-empty" "empty Type" "E0" [],
    mk "h-sortpoly-unit" "Sort u, unit (PUnit)" "PU" [],
    mk "h-sortpoly-sum" "Sort (max 1 u v) (PSum)" "PS" [],
    mk "h-mutual-prop" "mutual, indexed, Prop" "Ev" [],
    mk "h-mutual" "mutual recursive" "TA" ["TA.rec'"],
    mk "h-mutual-nonrec-eta" "mutual non-recursive: structure eta" "MA" ["MA.eta'"],
    mk "h-mutual-nonrec-unit" "mutual non-recursive: unit-like eta" "MA" ["MB.uniq"],
    mk "h-mutual-nonrec-block" "mutual non-recursive block alone" "MA" [],
    mk "h-nested" "nested (List)" "Rose" ["Rose.rec'"],
    mk "h-nested-array-option" "nested (Array, Option): nested-nested via Array" "J" [],
    mk "h-nested-nested" "nested-nested (List (Array _))" "NN" [],
    mk "h-nested-mutual" "nested and mutual" "A1" [],
    mk "h-nested-struct" "nested structure, block alone" "NS" [],
    mk "h-nested-struct-proj" "projection at a nested structure" "NS" ["NS.kids'", "NS.kids"],
    mk "h-nested-binder" "nested under a binder" "NB" [],
    mk "h-quot" "quotient: lift reduces on mk" "" ["QT.f'", "QT.f", "QT", "QR"],
    mk "h-nested-index-param" "nested, index domain over a parameter" "NB4" [],
    mk "h-nested-reflexive" "nested, reflexive field into a member" "RA1" [],
    mk "h-nested-pin-fun" "nested, container pinned at a function into the block" "RA3" [],
    mk "h-former-def" "a former declared at a definition (Mathlib: 31 blocks)" "RT" [],
    mk "h-unsafe" "unsafe, non-positive (Lean skips positivity)" "UB" [] ]

/-- Control copies and must-reject mutations of the base blocks. -/
def mutations (env : Environment) : List Fx := Id.run do
  let mut out : List Fx := []
  let n := ixiv
  let rec1 (s : String) : Name := (n s).str "rec_1"
  let recOf (s : String) : Name := mkRecName (n s)
  let roseType : Expr := mkApp2 (mkConst ``Prod [.zero, u1]) (mkConst (n "Rose")) (.sort u1)
  -- (base, tag, dim, intent, mutation)
  let cases : List (String × String × String × String × (List ConstantInfo → List ConstantInfo)) := [
    -- controls
    ("Color", "ctl-enum", "control copy", "an honest copy", id),
    ("Tr", "ctl-rec", "control copy", "an honest copy", id),
    ("Vec", "ctl-indexed", "control copy", "an honest copy", id),
    ("W", "ctl-reflexive", "control copy", "an honest copy", id),
    ("Eq'", "ctl-prop-K", "control copy", "an honest copy", id),
    ("Or'", "ctl-prop-small", "control copy", "an honest copy", id),
    ("PA", "ctl-prop-struct", "control copy", "an honest copy", id),
    ("Pt", "ctl-struct", "control copy", "an honest copy", id),
    ("Box", "ctl-univpoly", "control copy", "an honest copy", id),
    ("TA", "ctl-mutual", "control copy", "an honest copy", id),
    ("Ev", "ctl-mutual-prop", "control copy", "an honest copy", id),
    ("MA", "ctl-mutual-nonrec", "control copy", "an honest copy", id),
    ("Rose", "ctl-nested", "control copy", "an honest copy", id),
    ("A1", "ctl-nested-mutual", "control copy", "an honest copy", id),
    ("NN", "ctl-nested-nested", "control copy", "an honest copy", id),
    -- recursor rules
    ("Color", "rule-swap-enum", "wrong recursor rules", "Color.rec r ↦ the minor for g",
      mapRec (recOf "Color") fun r => { r with rules := swap01 r.rules }),
    ("Tr", "rule-swap-rec", "wrong recursor rules", "Tr.rec's two rules swapped",
      mapRec (recOf "Tr") fun r => { r with rules := swap01 r.rules }),
    ("Vec", "rule-swap-indexed", "wrong recursor rules", "Vec.rec's two rules swapped",
      mapRec (recOf "Vec") fun r => { r with rules := swap01 r.rules }),
    ("TA", "rule-swap-mutual", "wrong recursor rules", "TA.rec's rules swapped",
      mapRec (recOf "TA") fun r => { r with rules := swap01 r.rules }),
    ("Ev", "rule-swap-mutual-prop", "wrong recursor rules", "Ev.rec's rules swapped",
      mapRec (recOf "Ev") fun r => { r with rules := swap01 r.rules }),
    ("Rose", "rule-swap-aux", "forged auxiliary nested recursor", "Rose.rec_1's nil/cons rules swapped",
      mapRec (rec1 "Rose") fun r => { r with rules := swap01 r.rules }),
    ("A1", "rule-swap-aux-mutual", "forged auxiliary nested recursor", "A1.rec_1's rules swapped",
      mapRec (rec1 "A1") fun r => { r with rules := swap01 r.rules }),
    -- forged records at NB4 (`modeled-nested-parameter-index-forged-*` of `kernel-entry-cases`)
    ("NB4", "nested-forged-rule", "forged nested recursor", "NB4.rec's rules swapped",
      mapRec (recOf "NB4") fun r => { r with rules := swap01 r.rules }),
    ("NB4", "nested-forged-motives", "forged nested recursor", "NB4.rec numMotives + 1",
      mapRec (recOf "NB4") fun r => { r with numMotives := r.numMotives + 1 }),
    ("NB4", "nested-forged-fields", "forged nested recursor", "NB4.rec's second rule with one more field",
      mapRec (recOf "NB4") fun r => { r with rules := r.rules.mapIdx fun i x => if i == 1 then { x with nfields := x.nfields + 1 } else x }),
    ("NB4", "nested-forged-k", "forged nested recursor", "K on NB4.rec",
      mapRec (recOf "NB4") fun r => { r with k := true }),
    ("RA1", "nested-forged-rule-reflexive", "forged nested recursor", "RA1.rec's rules swapped",
      mapRec (recOf "RA1") fun r => { r with rules := swap01 r.rules }),
    ("NB4", "ctl-nested-index-param", "control copy", "an honest copy", id),
    ("Color", "rule-fields", "wrong recursor rules", "Color.rec's first rule claims a field",
      mapRec (recOf "Color") fun r => { r with rules := r.rules.map fun x =>
        if x.ctor == (n "Color.r") then { x with nfields := 1 } else x }),
    ("Rose", "rule-fields-aux", "forged auxiliary nested recursor", "Rose.rec_1's cons rule with 3 fields",
      mapRec (rec1 "Rose") fun r => { r with rules := r.rules.map fun x =>
        if x.nfields == 2 then { x with nfields := 3 } else x }),
    ("Tr", "rule-drop", "wrong recursor rules", "Tr.rec without its node rule",
      mapRec (recOf "Tr") fun r => { r with rules := r.rules.take 1 }),
    ("Rose", "rule-drop-aux", "forged auxiliary nested recursor", "Rose.rec_1 without its cons rule",
      mapRec (rec1 "Rose") fun r => { r with rules := r.rules.take 1 }),
    ("Rose", "aux-dropped", "forged auxiliary nested recursor", "Rose's family without Rose.rec_1",
      dropRec (rec1 "Rose")),
    ("Rose", "aux-numNested0", "wrong flags (absent from Ixon)", "Rose with numNested := 0",
      mapInd (n "Rose") fun v => { v with numNested := 0 }),
    -- K
    ("Or'", "k-or", "wrong K flag", "K on Or (two constructors)", mapRec (recOf "Or'") fun r => { r with k := true }),
    ("PA", "k-and", "wrong K flag", "K on a Prop structure with fields", mapRec (recOf "PA") fun r => { r with k := true }),
    ("Acc'", "k-acc", "wrong K flag", "K on Acc", mapRec (recOf "Acc'") fun r => { r with k := true }),
    ("Vec", "k-type", "wrong K flag", "K on a Type family", mapRec (recOf "Vec") fun r => { r with k := true }),
    ("Ev", "k-mutual", "wrong K flag", "K on a mutual Prop", mapRec (recOf "Ev") fun r => { r with k := true }),
    ("Rose", "k-nested", "wrong K flag", "K on a nested block", mapRec (recOf "Rose") fun r => { r with k := true }),
    ("Eq'", "k-off", "wrong K flag", "K dropped from Eq (incomplete, not Lean's)",
      mapRec (recOf "Eq'") fun r => { r with k := false }),
    -- counts
    ("Tr", "rec-params", "mismatched counts", "Tr.rec numParams + 1",
      mapRec (recOf "Tr") fun r => { r with numParams := r.numParams + 1 }),
    ("Tr", "rec-indices", "mismatched counts", "Tr.rec numIndices + 1",
      mapRec (recOf "Tr") fun r => { r with numIndices := r.numIndices + 1 }),
    ("Tr", "rec-motives", "mismatched counts", "Tr.rec numMotives + 1",
      mapRec (recOf "Tr") fun r => { r with numMotives := r.numMotives + 1 }),
    ("Tr", "rec-minors", "mismatched counts", "Tr.rec numMinors - 1",
      mapRec (recOf "Tr") fun r => { r with numMinors := r.numMinors - 1 }),
    ("Vec", "rec-indices-0", "mismatched counts", "Vec.rec numIndices 0",
      mapRec (recOf "Vec") fun r => { r with numIndices := 0 }),
    ("TA", "rec-motives-mutual", "mismatched counts", "TA.rec numMotives 1",
      mapRec (recOf "TA") fun r => { r with numMotives := 1 }),
    ("Rose", "rec-motives-aux", "mismatched counts", "Rose.rec_1 numMotives 1",
      mapRec (rec1 "Rose") fun r => { r with numMotives := 1 }),
    ("Vec", "ind-params", "mismatched counts", "Vec numParams 2",
      mapInd (n "Vec") fun v => { v with numParams := 2 }),
    ("Vec", "ind-indices", "mismatched counts", "Vec numIndices 0",
      mapInd (n "Vec") fun v => { v with numIndices := 0 }),
    ("Pt", "ctor-fields", "mismatched counts", "Pt.mk numFields 3",
      mapCtor (n "Pt.mk") fun c => { c with numFields := 3 }),
    ("Vec", "ctor-params", "mismatched counts", "Vec.cons numParams 2",
      mapCtor (n "Vec.cons") fun c => { c with numParams := 2 }),
    ("Color", "ctor-cidx", "mismatched counts", "Color.r and Color.g with swapped cidx",
      fun cis => cis.map fun ci => match ci with
        | .ctorInfo c => if c.name == n "Color.r" then .ctorInfo { c with cidx := 1 }
          else if c.name == n "Color.g" then .ctorInfo { c with cidx := 0 } else ci
        | _ => ci),
    ("Box", "ctor-lps", "universe violation", "Box.mk with a second level parameter",
      mapCtor (n "Box.mk") fun c => { c with levelParams := c.levelParams ++ [`w] }),
    -- elimination level
    ("Or'", "large-or", "large elimination", "Or.rec into any Sort",
      mapRec (recOf "Or'") mkLarge),
    ("Ex'", "large-exists", "large elimination", "Exists.rec into any Sort (a choice operator)",
      mapRec (recOf "Ex'") mkLarge),
    ("Ev", "large-mutual-prop", "large elimination", "a mutual Prop block into any Sort",
      mapRec (recOf "Ev") mkLarge),
    ("Tr", "small-type", "large elimination", "Tr.rec into Prop only (not Lean's)",
      mapRec (recOf "Tr") mkSmall),
    -- safety
    ("Tr", "unsafe-rec", "wrong flags (unsafe)", "Tr.rec unsafe, Tr safe",
      mapRec (recOf "Tr") fun r => { r with isUnsafe := true }),
    ("Rose", "unsafe-aux", "wrong flags (unsafe)", "Rose.rec_1 unsafe with swapped rules, Rose.rec safe",
      mapRec (rec1 "Rose") fun r => { r with isUnsafe := true, rules := swap01 r.rules }),
    ("TA", "unsafe-peer-rec", "wrong flags (unsafe)", "TB.rec unsafe with swapped rules, TA.rec safe",
      mapRec (recOf "TB") fun r => { r with isUnsafe := true, rules := swap01 r.rules }),
    ("Rose", "unsafe-recblock", "wrong flags (unsafe)", "both Rose recursors unsafe, Rose.rec_1 rules swapped, Rose safe",
      fun cis => mapRec (rec1 "Rose") (fun r => { r with isUnsafe := true, rules := swap01 r.rules }) (mapRec (recOf "Rose") (fun r => { r with isUnsafe := true }) cis)),
    ("Color", "unsafe-ctor", "wrong flags (unsafe)", "Color.g unsafe",
      mapCtor (n "Color.g") fun c => { c with isUnsafe := true }),
    ("Tr", "unsafe-ind", "wrong flags (unsafe)", "Tr unsafe, its constructors and recursor safe",
      mapInd (n "Tr") fun v => { v with isUnsafe := true }),
    ("Tr", "isrec-flag", "wrong flags (absent from Ixon)", "Tr with isRec := false",
      mapInd (n "Tr") fun v => { v with isRec := false }),
    -- positivity and universes in mutual and nested blocks
    ("TA", "nonpos-mutual", "non-positive occurrence", "TB.c : (TA → Nat) → TB",
      fun cis => (mapCtor (n "TB.c") fun c => { c with type := arr (arr (mkConst (n "TA")) (mkConst ``Nat)) (mkConst (n "TB")) })
        (mapInd (n "TA") (fun v => { v with isReflexive := true }) (mapInd (n "TB") (fun v => { v with isReflexive := true }) cis))),
    ("Rose", "nonpos-nested", "non-positive occurrence", "Rose.node : List (Rose → Nat) → Rose",
      fun cis => (mapCtor (n "Rose.node") fun c => { c with type := arr (listOf .zero (arr (mkConst (n "Rose")) (mkConst ``Nat))) (mkConst (n "Rose")) })
        (mapInd (n "Rose") (fun v => { v with isReflexive := true }) cis)),
    ("TA", "univ-mutual", "universe violation", "TB.c : Type → TB with TB : Type",
      mapCtor (n "TB.c") fun c => { c with type := arr (.sort u1) (mkConst (n "TB")) }),
    ("Rose", "univ-nested", "universe violation", "Rose.node : List (Rose × Type) → Rose",
      fun cis => (mapCtor (n "Rose.node") fun c => { c with type := arr (listOf u1 roseType) (mkConst (n "Rose")) })
        (mapInd (n "Rose") (fun v => { v with numNested := 2 }) cis)) ]
  for (base, tag, dim, intent, f) in cases do
    let recs := renameAll tag (f (blockOf env (n base)))
    let kind := if tag.startsWith "ctl-" then "honest" else "must-reject"
    let lean := match toInductDecl recs with
      | some d => some ([d], recs)
      | none => some ([], recs)
    out := out ++ [{ id := tag, dim, kind, intent := s!"{base}: {intent}", records := recs, lean }]
  return out

/-- A fixture decided by Lean through `decls` alone. -/
def adFx (id dim intent : String) (records : List ConstantInfo) (decls : List Declaration)
    (replay : List ConstantInfo := []) : Fx :=
  { id, dim, kind := "addDecl", intent, records, lean := some (decls, replay) }

def thmCI : Declaration → List ConstantInfo
  | .thmDecl t => [.thmInfo t]
  | .defnDecl d => [.defnInfo d]
  | _ => []

/-- Declarations only `addDecl` produces. An accepted inductive's records are
the ones Lean generated. -/
def addDeclFixtures (env : Environment) : IO (List Fx) := do
  let n := ixiv
  let nat := mkConst ``Nat
  let bool := mkConst ``Bool
  let mut out : List Fx := []
  -- a recursive occurrence under a beta redex: Lean's `is_rec` is syntactic (no eta)
  let hr := n "D.HR"
  let hrCtor : Constructor := {
    name := hr.str "mk",
    type := .forallE `x (.app (.lam `t (.sort u1) nat .default) (mkConst hr)) (mkConst hr) .default }
  let hrDecl := Declaration.inductDecl [] 0 [{ name := hr, type := .sort u1, ctors := [hrCtor] }] false
  let (ok, _, kenv) ← leanVerdict env [hrDecl] []
  let hrRecs := if ok then [hr, hr.str "mk", hr.str "rec"].filterMap kenv.find? else []
  let hrEta := etaThm (hr.str "eta") hr (hr.str "mk") 1
  out := out ++ [
    adFx "a-redex-rec" "is_rec under a redex" "HR.mk : (fun _ => Nat) HR → HR" hrRecs [hrDecl] hrRecs,
    adFx "a-redex-rec-eta" "is_rec under a redex: structure eta"
      "∀ x : HR, x = HR.mk x.0 (Lean: no eta, its is_rec is syntactic)"
      (hrRecs ++ thmCI hrEta) [hrDecl, hrEta] hrRecs ]
  -- a recursive occurrence behind a definition
  let b1 := n "D.B1"
  let b1Ctor : Constructor := {
    name := b1.str "mk",
    type := .forallE `x (.app (mkConst (n "Id'")) (mkConst b1)) (mkConst b1) .default }
  let b1Decl := Declaration.inductDecl [] 0 [{ name := b1, type := .sort u1, ctors := [b1Ctor] }] false
  let (ok, _, kenv) ← leanVerdict env [b1Decl] []
  let b1Recs := if ok then [b1, b1.str "mk", b1.str "rec"].filterMap kenv.find? else []
  out := out ++ [adFx "a-rec-behind-def" "recursive occurrence behind a definition"
    "B1.mk : Id' B1 → B1 (Lean: positivity and the hypothesis after whnf)" b1Recs [b1Decl] b1Recs]
  -- a mention whnf erases (a phantom definition): Lean's positivity reads the field after whnf
  let ph := n "D.PH"
  let phCtor : Constructor := {
    name := ph.str "mk",
    type := .forallE `x (.app (mkConst (n "Tagged")) (mkConst ph)) (mkConst ph) .default }
  let phDecl := Declaration.inductDecl [] 0 [{ name := ph, type := .sort u1, ctors := [phCtor] }] false
  let (ok, _, kenv) ← leanVerdict env [phDecl] []
  let phRecs := if ok then [ph, ph.str "mk", ph.str "rec"].filterMap kenv.find? else []
  out := out ++ [adFx "a-phantom-def" "a mention whnf erases"
    "PH.mk : Tagged PH → PH, Tagged _ := Nat (Lean: no occurrence after whnf)" phRecs [phDecl] phRecs]
  -- nested occurrences Lean's syntactic detection does not see, and a dropped auxiliary
  let oneFields : List (String × String × Name × Expr) := [
    ("a-nested-behind-def", "NL.mk : LA NL → NL, LA := List (Lean: invalid occurrence)",
      n "D.NL", mkApp (mkConst (n "LA")) (mkConst (n "D.NL"))),
    ("a-nested-behind-def-neg", "NN.mk : NA NN → NN, NA := NegC, negative (Lean: invalid occurrence)",
      n "D.NNg", mkApp (mkConst (n "NA")) (mkConst (n "D.NNg"))),
    ("a-nested-index", "IX.mk : @Eq Type Nat IX → IX, the block in an index argument (Lean: invalid occurrence)",
      n "D.IX", mkAppN (mkConst ``Eq [.succ (.succ .zero)]) #[.sort u1, nat, mkConst (n "D.IX")]),
    ("a-nested-casesOn", "PL.mk : List PL → PL with a casesOn-shaped recursor and no auxiliary (not Lean's)",
      n "D.PL", mkApp (mkConst ``List [.zero]) (mkConst (n "D.PL"))) ]
  for (tag, intent, T, D) in oneFields do
    let (decl, recs) := oneField T D (if tag == "a-nested-casesOn" then 1 else 0)
    out := out ++ [adFx tag "nested occurrence Lean does not detect" intent recs [decl] recs]
  -- projections and eta at shapes the elaborator never produces them at
  let projs : List (String × String × Declaration) := [
    ("p-indexed-onector", "`.proj` at a one-constructor indexed family (Lean's infer_proj allows it)",
      projDef (n "D.p1") (n "IV1") (mkApp (mkConst (n "IV1")) (mkRawNatLit 3)) bool 1),
    ("p-rec-structlike", "`.proj` at a recursive one-constructor type",
      projDef (n "D.p2") (n "RS") (mkConst (n "RS")) nat 0),
    ("p-enum", "`.proj` at an enumeration", projDef (n "D.p3") (n "Color") (mkConst (n "Color")) nat 0),
    ("p-or", "`.proj` at Or (two constructors)",
      projDef (n "D.p4") (n "Or'") (mkApp2 (mkConst (n "Or'")) (mkConst ``True) (mkConst ``True))
        (mkConst ``True) 0),
    ("p-exists-data", "`.proj` of data out of an Exists proof",
      projDef (n "D.p5") (n "Ex'") (mkApp2 (mkConst (n "Ex'") [u1]) nat (.lam `x nat (mkConst ``True) .default))
        nat 0),
    ("p-nested-struct-thm", "`.proj` at a nested structure inside a theorem (not a projection function)",
      projThm (n "D.p6") (n "NS") (mkConst (n "NS")) (mkApp (mkConst ``List [.zero]) (mkConst (n "NS"))) u1 0),
    ("p-mutual-nonrec-thm", "`.proj` at a mutual non-recursive structure inside a theorem",
      projThm (n "D.p7") (n "MA") (mkConst (n "MA")) nat u1 0),
    ("p-mutual-nonrec-fn", "a projection function at a mutual non-recursive structure",
      projDef (n "D.p8") (n "MA") (mkConst (n "MA")) nat 0),
    ("e-rec-structlike", "structure eta at a recursive one-constructor type (Lean: none)",
      etaThm (n "D.e1") (n "RS") (n "RS.mk") 2),
    ("e-nested-struct", "structure eta at a nested structure (Lean: none, is_rec)",
      etaThm (n "D.e2") (n "NS") (n "NS.mk") 1) ]
  for (tag, intent, d) in projs do
    let dim := if tag.startsWith "e-" then "structure eta" else "projections"
    out := out ++ [adFx tag dim intent (thmCI d) [d]]
  return out

/-! ## The three checkers -/

def groupOf (a : Address) (ci : Ixon.ConstantInfo) : Address :=
  match ci with
  | .iPrj p => p.block
  | .cPrj p => p.block
  | .rPrj p => p.block
  | .dPrj p => p.block
  | _ => a

/-- Names a record refers to. -/
def refsOf (ci : ConstantInfo) : List Name :=
  let es : List Expr := match ci with
    | .defnInfo v => [v.type, v.value]
    | .thmInfo v => [v.type, v.value]
    | .recInfo v => v.type :: v.rules.map (·.rhs)
    | ci => [ci.type]
  es.flatMap fun e => e.getUsedConstants.toList

def outcomeOf (rows : List (Name × String × String)) : String :=
  let bad := rows.filter fun (_, o, _) => o != "accept" && o != "typed"
  let pick (o : String) := bad.find? (·.2.1 == o)
  match pick "reject" <|> pick "decline" <|> pick "blocked" <|> bad.head? with
  | some (nm, o, r) => s!"{o} ({nm}: {(r.replace "\n" " ").take 160})"
  | none => "accept"

/-- `env` with the records whose binder data the compiler left undecided given the data IxC's
pass computes for them (`never` where it computes none), re-addressed with every record that
names them; and the number of such records. Binder data are the prover's to choose: with
undecided ones the program refuses a record at its first binder, before the check a fixture
is about. -/
def decideBinders (env : Ixon.Env) : Except String (Ixon.Env × Nat) := do
  let mut consts := env.consts
  let mut redone := 0
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      if c.binders.any (·.nodes.any (·.isUndecided)) then
        let stripped : Ixon.Constant := { c with binders := #[] }
        let bytes := Ixon.serConstant stripped
        consts := consts.insert a { buf := bytes, len := bytes.size, cache := some stripped }
        redone := redone + 1
  if redone == 0 then return (env, 0)
  let ctx ← Ix.ClaimContext.ofDefaultTable
  let (env', _, _) ← Tests.Ix.IxVM.withRecordSections { env with consts }
    (.check ctx default none) {}
  return (env', redone)

def run (leanEnv : Environment) : IO UInt32 := do
  let only? := (← IO.getEnv "IX_IV_ONLY").map (·.splitOn ",")
  let all := honest leanEnv ++ mutations leanEnv ++ (← addDeclFixtures leanEnv)
  let fixtures := match only? with
    | some ids => all.filter fun (x : Fx) => ids.contains x.id
    | none => all
  IO.println s!"[ixvm-ind-variations] {fixtures.length} fixtures"
  let mut builders : Array Tests.Ix.IxVM.Builder := #[]
  for f in fixtures do
    try
      -- Lean
      let (leanOk, leanMsg) ← match f.lean with
        | none => pure (true, "accepted (elaborated and checked)")
        | some (decls, replay) => do
          let (ok, msg, _) ← leanVerdict leanEnv decls replay
          pure (ok, msg)
      if f.records.isEmpty then
        IO.println s!"IV\t{f.id}\t{f.kind}\t{f.dim}\tLean={leanMsg}\tIxC=n/a (no records)\tIxVM=n/a\t{f.intent}"
      else
        -- the compile input: the records and the closure of what they use
        let names := f.records.map (·.name)
        let seeds := (f.records.flatMap refsOf).eraseDups.filter fun x => !names.contains x
        let (_, closed) := Tests.Ix.Kernel.TutorialMeta.collectDepsWithExtras leanEnv {} seeds
        let input := (closed.filter fun (x, _) => !names.contains x) ++ f.records.map fun ci => (ci.name, ci)
        -- the compile writes each record's binder data with the kernel annotator, as
        -- `ix compile` does; where IxC's environment does not install for a mutated input,
        -- it leaves every binder undecided
        let canon := Ix.CompileM.canonInput input.toArray 32
        let (annotated, data) ← try
            pure (← IxVM.ClaimHarness.withKernelAnnotator canon, "annotated")
          catch _ => pure (canon, "not annotated")
        let (rawEnv, _, _) ← IO.ofExcept <| Ix.Cert.compileUnchecked annotated
        let missing := names.filter fun x => (rawEnv.getAddr? (Ix.Name.fromLeanName x)).isNone
        -- IxC
        let rows ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts rawEnv
        let ixcRows := names.filterMap fun x =>
          (rows[Ix.LeanIngress.ingressKey (Ix.Name.fromLeanName x)]?).map fun (o, r) => (x, o, r)
        let ixc := if ixcRows.isEmpty then "no rows" else outcomeOf ixcRows
        -- IxVM: a CheckEnv claim owning the fixture's records and their blocks
        let tabled ← if rawEnv.roleBinding.isSome then pure rawEnv else
          IO.ofExcept (IxVM.ClaimHarness.withRoleTable rawEnv (← IO.ofExcept Ix.Kernel.Reader.defaultTableBytes))
        let (decidedEnv, redone) ← IO.ofExcept (decideBinders tabled)
        let data := if redone == 0 then data else s!"{data}, {redone} records' data recomputed"
        let ixonEnv ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding decidedEnv)
        let mut groups : Std.HashMap Address (Array Address) := {}
        for (a, lc) in ixonEnv.consts do
          if let some c := lc.get? then
            let g := groupOf a c.info
            groups := groups.insert g ((groups.getD g #[]).push a)
        let mut owned : Std.HashSet Address := {}
        for x in names do
          if let some a := ixonEnv.getAddr? (Ix.Name.fromLeanName x) then
            if let some c := ixonEnv.getConst? a then
              for m in groups.getD (groupOf a c.info) #[a] do owned := owned.insert m
        let label := s!"IV {f.id}"
        let (accept, rejectsWith) := expectedVerdict f.id leanOk f.records
        let mut ixvm := s!"submitted, expecting {if accept then "accept" else "reject"}"
        match IxVM.ClaimHarness.buildShardCheckEnvWitness ixonEnv owned.toArray (assumeBinding := true) with
        | .ok (_, witness) =>
          builders := builders.push fun _ => pure { label, accept, rejectsWith, witness }
        | .error e => ixvm := s!"claim not built: {(e.replace "\n" " ").take 160}"
        let miss := if missing.isEmpty then "" else s!"\tnot compiled: {missing}"
        IO.println s!"IV\t{f.id}\t{f.kind}\t{f.dim}\tLean={leanMsg}\tIxC={ixc}\tIxVM={ixvm}\tbinder data: {data}\t{f.intent}{miss}"
    catch e =>
      IO.println s!"IV\t{f.id}\t{f.kind}\t{f.dim}\tERROR\t{e}"
  Tests.Ix.IxVM.runCases "ixvm-ind-variations" builders (jobs := 8)

end Tests.Ix.IxVM.IndVariations
