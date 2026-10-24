/- # Pass 3a: images of a changed block in the compiler (Def 3.3-3.5)

## Contract
Input: a changed Lean block `all`, read through
* `source`: the input environment (Lean's block, its recursors and
  auxiliaries, and every external inductive), by lookup only;
* `addr?`: the compiled address of a name (Pass 1's comparator needs the
  addresses of external references);
* `groupOf`: how an external occurrence opens its group in the canonical
  expansion (the compiler's compiled classes, `Canon.groupOfBlocks`; Lean's
  `I.all` by default);
* `canonRec?`: the canonical recursors Pass 2 generated for the block's
  components (aux-gen's names: `rep.rec`, and `all₀.rec_j` by Lean's source
  index `j`).

Output, per image-kind auxiliary `a` of the block (`Ix.Compile.Pass.imageKinds`),
its expansion `img(a)` (`Ix.Compile.Pass.Expansion`) and the type of its image
constant:
* a Lean recursor `r`: the generated image (`Ix.Compile.Image.imageOf`) over
  Pass 1's canonical form (the compiler's rules) and Pass 2's recursors;
* `casesOn`, `recOn`, `below*`, `brecOn*`, `.go`, `.eq`: Lean's value
  (Def 3.5), rewritten by `Ix.Compile.Pass.Translate` when used.

**The view.** The generator reads the canonical blocks under placeholder
names (`viewNaming`: the canonical inductive of a class is `rep._ix`, its
constructors `rep._ix.c`, its recursor `rep._ix.rec`, the component's nested
recursors `rep₀._ix.rec_i` by canonical position). The canonical inductives
and constructors are Lean's representatives renamed (`ImageSpec.ofBlock`);
the recursors are Pass 2's, renamed. After generation the inductives and
constructors are mapped back to the names that resolve to the same constants
(`back`): `rep._ix ↦ rep` and `rep._ix.c ↦ rep.c`. The recursors are not
mapped back: `rep._ix.rec` and `rep₀._ix.rec_i` are exactly the `_ix`
display names under which a changed block's Pass 2 recursors are registered
(`Ix.Compile.Pass.ixAuxName`), so the image terms reference Pass 2's
recursors by their `_ix` display names, never by Lean's recursor names (which
denote the images themselves).

## Shape (for the statements)
Pure and total: every function here is a fold over arrays with an explicit
error on every missing piece, and the generator underneath
(`Ix.Compile.Image`) is total with an explicit development bound. One view
construction (`buildViewWith`), over a given canonical form; `buildView`
supplies Pass 1's. The view's own constant table is keyed exactly
(`ExactName`); `back` is the renaming map `Canon.canonicalizeConstNames`
takes.

## Faithfulness
`img(r)` has Lean's type `tr_N(type r)` and its computation rules hold by
`rfl` (the generator's contract; re-checked by the `pass3` suite in the
compiler setting).

## Side condition and fallback
A missing canonical recursor, an empty slot class or an exhausted bound is
an error naming the block (no fallback: the call site cannot be compiled
faithfully without the image).
-/
module
public import Ix.Environment
public import Ix.Compile.ExactKey
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Block
public import Ix.Compile.Image.Spec
public import Ix.Compile.Image.Build
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Translate
public section

namespace Ix.Compile.Pass

open Ix (Name Level Expr ConstantInfo InductiveVal ConstructorVal RecursorVal)
open Ix.Compile.Canon (BlockCanon ComponentCanon canonicalizeConstNames)
open Ix.Compile.Image (ImageSpec Naming Image)
open Ix.Compile.ExactKey (ExactName)

/-- Placeholder names of the view (`rep._ix` for the canonical inductives,
as `Naming.default`; an image keeps the Lean name of its auxiliary, which
denotes it). -/
def viewNaming : Naming where
  ind _ _ rep := Name.mkStr rep ixComponent
  img r := r

/-- What the view reads of the compiler. -/
structure ViewInput where
  source : Ix.Environment
  addr? : Name → Option Address
  /-- External groups of the canonical expansion (`Canon.Env.groupOf`). -/
  groupOf : Ix.Compile.Canon.GroupOf := Ix.Compile.Canon.leanGroup
  canonRec? : Name → Option RecursorVal

def ViewInput.const? (inp : ViewInput) : Name → Option ConstantInfo := inp.source.get?

/-- Pass 1's environment over the view's input. -/
def ViewInput.env (inp : ViewInput) : Ix.Compile.Canon.Env :=
  { const? := inp.const?, addr? := inp.addr?, groupOf := inp.groupOf }

/-! ### Equality of views

The check mode of the driver's view table compares a stored view with one
built again. Every record a view holds compares by its derived `BEq`, so a
field added later is compared without notice (expressions and names by
`Ix.Expr`'s and `Ix.Name`'s `BEq`; hash maps by their sets of entries). The
one field left out is the spec's `naming`: it is functions, and every view
is built with the one constant `viewNaming` (`buildView`). -/

deriving instance BEq for Ix.Compile.Canon.SortStats, Ix.Compile.Canon.Sig,
  Ix.Compile.Canon.NestedCanon, Ix.Compile.Canon.ComponentCanon, Ix.Compile.Canon.BlockCanon,
  Ix.Compile.Image.CanonCtor, Ix.Compile.Image.CanonType, Ix.Compile.Image.CanonDecl

/-- `naming` compares equal: it is not data (see above). -/
local instance : BEq Naming := ⟨fun _ _ => true⟩

deriving instance BEq for ImageSpec

/-- The view of one changed Lean block. -/
structure BlockView where
  all : Array Name
  canon : BlockCanon
  spec : ImageSpec
  /-- The canonical inductives, constructors and recursors under view names. -/
  canonConsts : Std.HashMap ExactName ConstantInfo
  /-- View name ↦ input name, for the inductives and constructors only
  (`rep._ix ↦ rep`, `rep._ix.c ↦ rep.c`); recursor view names are the `_ix`
  display names and stay. -/
  back : Std.HashMap Name Name
  deriving BEq

def BlockView.const? (inp : ViewInput) (v : BlockView) (n : Name) : Option ConstantInfo :=
  match v.canonConsts.get? n with
  | some c => some c
  | none => inp.const? n

/-- Pass 1's canonical form of `all` (`canonBlock` under the compiler's
rules), computed only for the components whose members are all compiled
(`compiled? n`): an uncompiled component cannot be sorted (the comparator
reads compiled addresses), and no image a compiled constant needs can use it
(a component an image relocates into is a dependency of the major's
component, hence compiled first). Uncompiled components get one class per
member, in `all` order, and no nested data. With every member compiled it
computes what `Canon.canonBlock Rules.compiler` computes. -/
def canonBlockCompiled (env : Ix.Compile.Canon.Env) (compiled? : Name → Bool)
    (all : Array Name) : Except String BlockCanon := do
  let rules := Ix.Compile.Canon.Rules.compiler
  let comps ← Ix.Compile.Canon.blockComponents env all
  let mut out : Array ComponentCanon := #[]
  for members in comps do
    if members.all compiled? then
      let cs ← members.toList.mapM (Ix.Compile.Canon.mutConstOf env)
      let (classes, stats) ← (Ix.Compile.Canon.sortClasses rules env.addr? cs).mapError toString
      out := out.push { members, classes := Ix.Compile.Canon.classNames classes, stats,
                        nested := none }
    else
      out := out.push { members, classes := members.map (#[·]), stats := default,
                        nested := none }
  let classesAll := out.map (·.classes)
  let mut out' : Array ComponentCanon := #[]
  for (c, i) in out.zipIdx do
    if c.members.all compiled? then
      let nested ← Ix.Compile.Canon.componentNested env all c.classes
      let nested ← nested.mapM (Ix.Compile.Canon.evaporate env all classesAll i)
      out' := out'.push { c with nested }
    else out' := out'.push c
  return { all, components := out' }

/-- The view of `all` over the canonical form `canon` of `all`. Missing
canonical recursors (a component not compiled yet) are left out: an image
that needs one fails naming it. -/
def buildViewWith (inp : ViewInput) (canon : BlockCanon) (all : Array Name) :
    Except String BlockView := do
  let spec ← ImageSpec.ofBlock viewNaming inp.const? canon
  let some all0 := all[0]? | throw "Pass 3 view: empty block"
  let mut consts : Std.HashMap ExactName ConstantInfo := {}
  let mut back : Std.HashMap Name Name := {}
  -- component index ↦ its canonical `all` (view names)
  let mut compAll : Std.HashMap Nat (Array Name) := {}
  for d in spec.decls do
    compAll := compAll.insert d.comp (d.types.map (·.name))
  for d in spec.decls do
    let some comp := canon.components[d.comp]?
      | throw s!"Pass 3 view: component {d.comp} is absent from the canonical block"
    let some canonAll := compAll[d.comp]?
      | throw s!"Pass 3 view: component {d.comp} has no canonical member list"
    let numNested := match comp.nested with
      | some n => n.canonClasses.size
      | none => 0
    for (ty, k) in d.types.zipIdx do
      let some rep := (comp.classes[k]?).bind (·[0]?)
        | throw s!"Pass 3 view: class {k} of component {d.comp}"
      let some (.inductInfo iv) := inp.const? rep
        | throw s!"Pass 3 view: {rep.pretty} is not an inductive"
      back := back.insert ty.name rep
      consts := consts.insert ty.name (.inductInfo { iv with
        cnst := { iv.cnst with name := ty.name, type := ty.type }
        all := canonAll
        ctors := ty.ctors.map (·.name)
        numNested })
      for (cc, j) in ty.ctors.zipIdx do
        let some lc := iv.ctors[j]? | throw s!"Pass 3 view: constructor {j} of {rep.pretty}"
        let some (.ctorInfo cv) := inp.const? lc
          | throw s!"Pass 3 view: {lc.pretty} is not a constructor"
        back := back.insert cc.name lc
        consts := consts.insert cc.name (.ctorInfo { cv with
          cnst := { cv.cnst with name := cc.name, type := cc.type }
          induct := ty.name })
      -- the class's canonical recursor (Pass 2), renamed into the view
      let viewRec := Name.mkStr ty.name "rec"
      if let some rv := inp.canonRec? (Name.mkStr rep "rec") then
        consts := consts.insert viewRec (.recInfo { rv with
          cnst := { rv.cnst with name := viewRec, type := spec.tr rv.cnst.type }
          all := canonAll })
    -- the component's canonical nested recursors, by canonical position
    if let some n := comp.nested then
      let some rep0 := canonAll[0]? | continue
      let mut done : Std.HashSet Nat := {}
      for (p, j) in n.perm.zipIdx do
        let some i := p | continue
        if done.contains i then continue
        done := done.insert i
        if let some rv := inp.canonRec? (Name.mkStr all0 s!"rec_{j + 1}") then
          let viewRec := Name.mkStr rep0 s!"rec_{i + 1}"
          consts := consts.insert viewRec (.recInfo { rv with
            cnst := { rv.cnst with name := viewRec, type := spec.tr rv.cnst.type }
            all := canonAll })
  return { all, canon, spec, canonConsts := consts, back }

/-- The view of `all` over Pass 1's canonical form of its compiled
components (`canonBlockCompiled`). -/
def buildView (inp : ViewInput) (all : Array Name) : Except String BlockView := do
  buildViewWith inp (← canonBlockCompiled inp.env (fun n => (inp.addr? n).isSome) all) all

/-- The generated image of the Lean recursor `r`, with view names mapped
back to input names. -/
def BlockView.image (inp : ViewInput) (v : BlockView) (r : Name) : Except String Image := do
  let img ← Ix.Compile.Image.imageOf {} (v.const? inp) v.spec r
  return { img with
    value := canonicalizeConstNames v.back img.value
    type := canonicalizeConstNames v.back img.type
    rules := img.rules.map fun s => { s with
      type := canonicalizeConstNames v.back s.type
      proof := canonicalizeConstNames v.back s.proof } }

/-- The expansion of an image-kind auxiliary `a` of the block of `v`, and the
type of its image constant. -/
def BlockView.expansion (inp : ViewInput) (v : BlockView) (a : Name) :
    Except String (Expansion × Expr) := do
  match inp.const? a with
  | some (.recInfo _) =>
    let img ← v.image inp a
    return ({ levelParams := img.levelParams, value := img.value, arity := img.arity
              needsRewrite := false }, img.type)
  | some (.defnInfo d) =>
    return ({ levelParams := d.cnst.levelParams, value := d.value, arity := lamArity d.value
              needsRewrite := true }, d.cnst.type)
  | some (.thmInfo d) =>
    return ({ levelParams := d.cnst.levelParams, value := d.value, arity := lamArity d.value
              needsRewrite := true }, d.cnst.type)
  | _ => throw s!"Pass 3: {a.pretty} has no image (not a recursor or definition)"

end Ix.Compile.Pass

end
