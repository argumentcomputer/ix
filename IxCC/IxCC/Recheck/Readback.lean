import IxCC.Cfg.Syntax
import IxCC.Rt.Readback

/-! Bounded readback-signature discovery for ground first-order inductives.
Source CIds and instantiated constructor telescopes determine types; emitted
constructor rows determine the retained layout. Unsupported dependent,
erased/unboxed, polymorphic or incomplete shapes decline. No source-typing
or SrcEval adequacy theorem is inferred from this structural check. -/

namespace IxCC.Recheck.Readback

open IxCC

inductive Shape where
  | nat
  | ind (c : Src.CId) (levels : List Nat) (args : List Shape)
  deriving BEq, Repr, Inhabited

def level? (ls : List Nat) : IxCC.Ixon.Univ → Option Nat
  | .zero => some 0
  | .succ u => (level? ls u).map (· + 1)
  | .max a b => do return max (← level? ls a) (← level? ls b)
  | .imax a b => do
    let x ← level? ls a
    let y ← level? ls b
    return if y == 0 then 0 else max x y
  | .var i => ls[i.toNat]?

/-- Resolve only ground, value-independent first-order type applications. -/
def shape? (p : Src.Program) : Nat → List Nat → List (Option Shape) → Src.Term → Option Shape
  | 0, _, _, _ => none
  | fuel + 1, ls, ctx, t => do
    let (h, args) := t.spine
    match h with
    | .var i =>
      if !args.isEmpty then none else (ctx[i]?).join
    | .const c us =>
      let levels ← us.mapM (level? ls)
      if some c == p.known.nat then
        if args.isEmpty && levels.isEmpty then some .nat else none
      else
        let .induct true nl np 0 ty _ ← p.decl? c | none
        unless levels.length == nl && args.length == np do none
        let params := ty.pis.1.take np
        unless params.length == np && params.all (fun (_, d) => match d with | .sort _ => true | _ => false) do none
        let actuals ← args.mapM fun (a, _, _) => shape? p fuel ls ctx a
        return .ind c levels actuals
    | _ => none

structure Row where
  shape : Shape
  fields : Option (List (List Rt.FoTy)) := none
  deriving Inhabited

abbrev M := StateT (List Row) (Except String)

def fail {α : Type} (msg : String) : M α := throw msg

def fieldShapes (p : Src.Program) (shape : Shape) (c : Src.CId) : Except String (Nat × List Shape) := do
  let .ind ind ls args := shape | throw "constructor owner is not inductive"
  let some (.ctor true nl parent tag np nf ty) := p.decl? c | throw "missing safe source constructor"
  unless parent == ind && nl == ls.length && np == args.length do throw "constructor owner/parameters mismatch"
  let (binders, result) := ty.pis
  unless binders.length == np + nf do throw "constructor field telescope mismatch"
  unless (binders.take np).all (fun (_, d) => match d with | .sort _ => true | _ => false) do
    throw "constructor has a non-type parameter"
  let mut ctx := args.reverse.map some
  let mut fields := []
  for (_, dom) in binders.drop np do
    let some field := shape? p 128 ls ctx dom | throw "dependent or unsupported field type"
    fields := fields ++ [field]
    ctx := none :: ctx
  let some ret := shape? p 128 ls ctx result | throw "unsupported constructor result"
  unless ret == shape do throw "constructor result differs from instance"
  return (tag, fields)

def lower (p : Src.Program) (ctors : List Lam.CtorInfo) : Nat → Shape → M Rt.FoTy
  | 0, _ => fail "signature discovery budget"
  | fuel + 1, shape => do
    match shape with
    | .nat => return .nat
    | .ind ind _ _ =>
      let rows ← get
      if let some (_, index) := rows.zipIdx.find? (fun (r, _) => r.shape == shape) then
        return .ind index
      unless rows.length < 128 do fail "signature instance budget"
      let some (.induct true _ _ 0 _ keys) := p.decl? ind | fail "unsupported inductive"
      unless !keys.isEmpty && keys.eraseDups.length == keys.length do fail "empty/duplicate constructor family"
      let index := rows.length
      set (rows ++ [{ shape }])
      let mut out := []
      for (key, expectedTag) in keys.zipIdx do
        let (tag, fields) ← match fieldShapes p shape key with
          | .ok x => pure x
          | .error e => fail e
        unless tag == expectedTag do fail "constructor index disagrees with family order"
        let [row] := ctors.filter (fun row => row.key == .src key) | fail "missing/duplicate emitted constructor"
        unless row.tag == tag && row.arity == fields.length do fail "erased/unboxed/mismatched constructor layout"
        let types ← fields.mapM (lower p ctors fuel)
        out := out ++ [types]
      modify fun rs => rs.zipIdx.map fun (r, i) => if i == index then { r with fields := some out } else r
      return .ind index

def inBounds (n : Nat) : Rt.FoTy → Bool
  | .nat => true
  | .ind i => i < n

def closed (sig : Rt.Sig) (ty : Rt.FoTy) : Bool :=
  inBounds sig.inds.length ty && sig.inds.all (fun row => row.all (fun fields => fields.all (inBounds sig.inds.length)))

structure Candidate where
  root : Shape
  shapes : List Shape
  sig : Rt.Sig
  ty : Rt.FoTy
  deriving Inhabited

def discoverRaw (p : Src.Program) (C : Cfg.Program) (c : Src.CId) : Except String Candidate := do
  let some d := p.decl? c | throw "root absent"
  unless d.lvls == 0 do throw "polymorphic root"
  let some shape := shape? p 128 [] [] d.type.pis.2 | throw "unsupported root result"
  let (ty, rows) ← (lower p C.ctors 128 shape).run []
  let inds ← rows.mapM fun r => match r.fields with
    | some fields => pure fields
    | none => throw "incomplete signature row"
  let sig : Rt.Sig := { inds }
  return { root := shape, shapes := rows.map (·.shape), sig, ty }

def shapeRef (shapes : List Shape) : Shape → Option Rt.FoTy
  | .nat => some .nat
  | shape => ((shapes.zipIdx.find? fun (s, _) => s == shape).map fun (_, i) => .ind i)

/-- An independent final pass recomputes the source field shapes and compares
their instance indices with the emitted signature. No recursive discovery or
in-progress row is consumed by this check. -/
def rowMatches (p : Src.Program) (C : Cfg.Program) (shapes : List Shape)
    (shape : Shape) (row : List (List Rt.FoTy)) : Bool := Id.run do
  let .ind ind ls args := shape | return false
  let some (.induct true nl np 0 _ keys) := p.decl? ind | return false
  unless nl == ls.length && np == args.length && !keys.isEmpty &&
      keys.eraseDups.length == keys.length && keys.length == row.length do return false
  for (key, tag) in keys.zipIdx do
    let .ok (sourceTag, fields) := fieldShapes p shape key | return false
    let [emitted] := C.ctors.filter (fun r => r.key == .src key) | return false
    unless sourceTag == tag && emitted.tag == tag && emitted.arity == fields.length do return false
    let some fieldTypes := fields.mapM (shapeRef shapes) | return false
    unless row[tag]? == some fieldTypes do return false
  return true

def layoutsMatch (p : Src.Program) (C : Cfg.Program) (c : Src.CId) (q : Candidate) : Bool :=
  let rootMatches := match p.decl? c with
    | some d => d.lvls == 0 && shape? p 128 [] [] d.type.pis.2 == some q.root
    | none => false
  rootMatches && shapeRef q.shapes q.root == some q.ty &&
    q.shapes.eraseDups.length == q.shapes.length && q.shapes.length == q.sig.inds.length &&
    (q.shapes.zip q.sig.inds).all (fun (shape, row) => rowMatches p C q.shapes shape row)

def valid (p : Src.Program) (C : Cfg.Program) (c : Src.CId) (q : Candidate) : Bool :=
  closed q.sig q.ty && layoutsMatch p C c q

/-- Discovery's completed signature must have no dangling inductive index. -/
def discover (p : Src.Program) (C : Cfg.Program) (c : Src.CId) :
    Except String (Rt.Sig × Rt.FoTy) :=
  match discoverRaw p C c with
  | .error e => .error e
  | .ok result =>
    if valid p C c result then .ok (result.sig, result.ty)
    else .error "signature layout/provenance validation failed"

/-- Every accepted signature has an independently checked source-instance and
constructor-layout witness. This is structural evidence, not source adequacy. -/
theorem discover_valid {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (h : discover p C c = .ok (sig, ty)) :
    ∃ q, discoverRaw p C c = .ok q ∧ valid p C c q = true ∧ q.sig = sig ∧ q.ty = ty := by
  cases hr : discoverRaw p C c with
  | error e => simp [discover, hr] at h
  | ok q =>
    by_cases hv : valid p C c q = true
    · have he : (q.sig, q.ty) = (sig, ty) := by simpa [discover, hr, hv] using h
      exact ⟨q, by simp [hr], hv, congrArg Prod.fst he, congrArg Prod.snd he⟩
    · simp [discover, hr, hv] at h

/-- Structural closure, not a source typing or evaluator adequacy claim. -/
theorem discover_closed {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (h : discover p C c = .ok (sig, ty)) :
    closed sig ty = true := by
  obtain ⟨q, _, hv, hs, ht⟩ := discover_valid h
  have hc : closed q.sig q.ty = true := (Bool.and_eq_true_iff.mp hv).1
  simpa [hs, ht] using hc

theorem discover_layouts {p : Src.Program} {C : Cfg.Program} {c : Src.CId}
    {sig : Rt.Sig} {ty : Rt.FoTy} (h : discover p C c = .ok (sig, ty)) :
    ∃ q, q.sig = sig ∧ q.ty = ty ∧ layoutsMatch p C c q = true := by
  obtain ⟨q, _, hv, hs, ht⟩ := discover_valid h
  exact ⟨q, hs, ht, (Bool.and_eq_true_iff.mp hv).2⟩

end IxCC.Recheck.Readback
