import Lean.Elab.Command
import IxC.Kernel.Admission
import IxC.Kernel.Audit.Runtime

/-! # The display-use audit (IXC-PLAN §11, step 6)

`.meta` carries display data that the checker never reads: a field of type
`Mode.D α` holds a value in `.meta` and `()` in the certified modes. Today
the one display field is the reader's output (`Reader.Read.display`, what the
`.ixe`'s metadata says of the keys a record declares); the checker's own
types (keys, terms, constants, declarations) carry none, so its structural
equality stays α-equivalence at `.meta` too. A checker that read display
could decide differently at `.meta` than at `.anon` on the erasure; the
erasure test (`kernel-check-ixe --meta`) measures that on the corpus, and
this audit rules it out in the code. It finds

* every **display field**: a structure field of the kernel whose type is
  `Mode.D …`;
* every **reader** of one: a definition of the kernel's modules whose value
  uses a display field's projection, or a primitive projection at its index,
  other than copying the field into the same field of a value of the same
  structure it rebuilds (`{ r with decls := … }` copies `r.display`). The
  structure's own declarations are not readers; its derived instances
  (equality, `Repr`) are listed apart;
* every derived instance of a structure with display fields that the fold
  (`Ix.Kernel.Cached.checkDecls`) reaches in its compiled code: an equality
  there would compare display at `.meta`;
* every definition that destructures a structure with display fields by
  cases (a match could bind a display field).

All four lists are frozen. Readers must stay empty: the renderers that spell
a key with its names (`.meta`'s messages) live outside the kernel. -/

open Lean Meta Elab Command

namespace Ix.Kernel.Audit.Display

/-- A display field: its structure, its index among the structure's fields,
and its projection. -/
structure Field where
  struct : Lean.Name
  idx : Nat
  proj : Lean.Name
  deriving Inhabited

/-- Is `n` declared in a module of the kernel (`IxC.Kernel.*`)? -/
def inKernel (env : Environment) (n : Lean.Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`IxC.Kernel).isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => false

/-- The kernel's display fields, by their projections' result types. -/
def displayFields : MetaM (Array Field) := do
  let env ← getEnv
  let mut out : Array Field := #[]
  for (n, ci) in env.constants.toList do
    unless inKernel env n do continue
    let some info := env.getProjectionFnInfo? n | continue
    if info.fromClass then continue
    let isDisplay ← forallTelescopeReducing ci.type fun _ body => do
      let body ← instantiateMVars body
      pure (body.getAppFn.isConstOf ``Ix.Kernel.Mode.D)
    -- the reducing telescope stops at `Mode.D`, whose match does not reduce
    -- on a free mode
    let isDisplay := isDisplay ||
      (ci.type.getForallBody.getAppFn.isConstOf ``Ix.Kernel.Mode.D)
    if isDisplay then
      let some ctor := env.find? info.ctorName | continue
      out := out.push { struct := ctor.name.getPrefix, idx := info.i, proj := n }
  return out.qsort (fun a b => a.proj.toString < b.proj.toString)

/-- The projection a constructor application copies at its last argument:
`e`'s head is a display structure's constructor, its last argument `a` sits at
a display field's position, and `a` is that field's projection of some value
(`{ r with decls := … }` passes `r.display` there). -/
def copied (fields : Array Field) (ctors : NameMap (Nat × Lean.Name)) (e a : Lean.Expr) :
    Option Lean.Name := do
  let .const c _ := e.getAppFn | none
  let (nparams, struct) ← ctors.find? c
  let i := e.getAppNumArgs - 1
  guard (i ≥ nparams)
  let f ← fields.find? fun f => f.struct == struct && f.idx == i - nparams && a.getAppFn.isConstOf f.proj
  pure f.proj

/-- The display fields' projections used in `e` other than as a copy (`copied`):
`allow` is the projection the application spine being walked copies, if any.
Primitive projections at a display index count as uses. -/
def uses (fields : Array Field) (ctors : NameMap (Nat × Lean.Name)) (allow : Option Lean.Name) :
    Lean.Expr → Array Lean.Name
  | .const c _ => if fields.any (·.proj == c) && allow != some c then #[c] else #[]
  | e@(.app f a) =>
    uses fields ctors allow f ++ uses fields ctors (copied fields ctors e a) a
  | .proj s i b =>
    (if fields.any (fun f => f.struct == s && f.idx == i) then #[s ++ `proj] else #[]) ++
      uses fields ctors none b
  | .lam _ t b _ | .forallE _ t b _ => uses fields ctors none t ++ uses fields ctors none b
  | .letE _ t v b _ => uses fields ctors none t ++ uses fields ctors none v ++ uses fields ctors none b
  | .mdata _ b => uses fields ctors allow b
  | _ => #[]

/-- The structures with display fields, and their constructors' parameter
counts. -/
def displayCtors (fields : Array Field) : MetaM (NameMap (Nat × Lean.Name)) := do
  let env ← getEnv
  let mut out : NameMap (Nat × Lean.Name) := {}
  for f in fields do
    if let some info := getStructureInfo? env f.struct then
      let ctor := (getStructureCtor env f.struct)
      out := out.insert ctor.name (ctor.numParams, info.structName)
  return out

/-- Is `n` one of the structure's own declarations, or a derived instance of
it (listed apart)? -/
def ownOf (structs : Array Lean.Name) (n : Lean.Name) : Bool :=
  structs.any fun s => s.isPrefixOf n

/-- Derived instances of a structure with display fields: `inst<Class><S>`
and their auxiliaries. -/
def isDerivedInstance (structs : Array Lean.Name) (n : Lean.Name) : Bool :=
  structs.any fun s =>
    let base := s.getString!
    let p := s.getPrefix
    (p.isPrefixOf n) && (n.components.any fun c =>
      let t := c.toString
      t.startsWith "inst" && t.endsWith base)

end Ix.Kernel.Audit.Display

open Ix.Kernel.Audit.Display in
/-- info: display field Ix.Kernel.Reader.Read.display (Ix.Kernel.Reader.Read, field 5) -/
#guard_msgs in
run_cmd liftTermElabM do
  for f in ← displayFields do
    logInfo m!"display field {f.proj} ({f.struct}, field {f.idx})"

open Ix.Kernel.Audit.Display in
/-- info: readers of display fields in the kernel's definitions: [] -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let fields ← displayFields
  let ctors ← displayCtors fields
  let structs := (fields.map (·.struct)).toList.eraseDups.toArray
  let mut readers : Array Lean.Name := #[]
  for (n, ci) in env.constants.toList do
    unless inKernel env n do continue
    if ownOf structs n || isDerivedInstance structs n then continue
    let some v := ci.value? (allowOpaque := true) | continue
    if ci matches .thmInfo _ then continue
    unless (uses fields ctors none v).isEmpty do readers := readers.push n
  logInfo m!"readers of display fields in the kernel's definitions: \
    {readers.qsort (·.toString < ·.toString)}"

open Ix.Kernel.Audit.Display in
/-- info: derived instances of display structures in the fold's runtime closure: [] -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let fields ← displayFields
  let structs := (fields.map (·.struct)).toList.eraseDups.toArray
  let r := Ix.Kernel.Audit.runtimeClosure env #[``Ix.Kernel.Cached.checkDecls]
  -- equality, ordering, hashing and printing read every field; `Inhabited`
  -- builds a default and reads none
  let readsAll (n : Lean.Name) : Bool := n.components.any fun c =>
    let t := c.toString
    ["DecidableEq", "BEq", "Ord", "Hashable", "Repr", "ToString"].any (t.startsWith s!"inst{·}")
  let hits := r.visited.filter fun n => isDerivedInstance structs n && readsAll n
  logInfo m!"derived instances of display structures in the fold's runtime closure: \
    {hits.qsort (·.toString < ·.toString)}"
open Ix.Kernel.Audit.Display in
/-- info: definitions destructuring a display structure by cases: [] -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let fields ← displayFields
  let structs := (fields.map (·.struct)).toList.eraseDups.toArray
  let elims := structs.flatMap fun s => #[s ++ `casesOn, s ++ `rec, s ++ `recOn]
  let mut found : Array Lean.Name := #[]
  for (n, ci) in env.constants.toList do
    unless inKernel env n do continue
    if ownOf structs n || isDerivedInstance structs n then continue
    if ci matches .thmInfo _ then continue
    let some v := ci.value? (allowOpaque := true) | continue
    if (v.find? fun e => elims.any e.isConstOf).isSome then found := found.push n
  logInfo m!"definitions destructuring a display structure by cases: \
    {found.qsort (·.toString < ·.toString)}"
