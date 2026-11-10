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
  deriving Repr, Inhabited

mutual

/-- Structural equality of shapes, written out (a derived `BEq` on this nested
inductive is an opaque function, about which nothing can be proved). -/
def Shape.beq : Shape → Shape → Bool
  | .nat, .nat => true
  | .ind c ls as, .ind c' ls' as' => c == c' && ls == ls' && Shape.beqList as as'
  | _, _ => false

def Shape.beqList : List Shape → List Shape → Bool
  | [], [] => true
  | a :: as, b :: bs => Shape.beq a b && Shape.beqList as bs
  | _, _ => false

end

instance : BEq Shape := ⟨Shape.beq⟩

mutual

theorem Shape.eq_of_beq : ∀ {s t : Shape}, Shape.beq s t = true → s = t
  | .nat, .nat, _ => rfl
  | .ind c ls as, .ind c' ls' as', h => by
    simp only [Shape.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [Shape.eq_of_beqList h]
  | .nat, .ind .., h => by simp [Shape.beq] at h
  | .ind .., .nat, h => by simp [Shape.beq] at h

theorem Shape.eq_of_beqList : ∀ {as bs : List Shape}, Shape.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Shape.beqList, Bool.and_eq_true] at h
    rw [Shape.eq_of_beq h.1, Shape.eq_of_beqList h.2]
  | [], _ :: _, h => by simp [Shape.beqList] at h
  | _ :: _, [], h => by simp [Shape.beqList] at h

end

mutual

theorem Shape.beq_refl : ∀ s : Shape, Shape.beq s s = true
  | .nat => rfl
  | .ind c ls as => by simp [Shape.beq, Shape.beqList_refl as]

theorem Shape.beqList_refl : ∀ as : List Shape, Shape.beqList as as = true
  | [] => rfl
  | a :: as => by simp [Shape.beqList, Shape.beq_refl a, Shape.beqList_refl as]

end

instance : LawfulBEq Shape where
  eq_of_beq h := Shape.eq_of_beq h
  rfl := Shape.beq_refl _

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
      exact ⟨q, by simp, hv, congrArg Prod.fst he, congrArg Prod.snd he⟩
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

/-! ## What discovery checks, as facts -/

/-- A `for` loop in `Id` whose body, from the initial state, continues with it
or stops with `some false`: it ends with `none` or `some false`, and if with
`none`, the body continued on every element. -/
theorem forIn_none_all {α : Type} (body : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit)))
    (P : α → Prop)
    (hb : ∀ x, body x (none, ()) = ForInStep.yield (none, ()) → P x)
    (hb' : ∀ x, body x (none, ()) = ForInStep.yield (none, ()) ∨
      body x (none, ()) = ForInStep.done (some false, ())) :
    ∀ l : List α, ((forIn (m := Id) l ((none : Option Bool), ()) body).1 = none ∧ ∀ x ∈ l, P x) ∨
      (forIn (m := Id) l ((none : Option Bool), ()) body).1 = some false
  | [] => .inl ⟨rfl, fun _ hx => by cases hx⟩
  | y :: l => by
    rw [List.forIn_cons]
    rcases hb' y with hy | hy
    · rw [hy]
      rcases forIn_none_all body P hb hb' l with ⟨h1, h2⟩ | h1
      · refine .inl ⟨h1, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hb x hy
        · exact h2 x hx
      · exact .inr h1
    · rw [hy]
      exact .inr rfl

/-- A shape `shape?` resolves in the empty context is `Nat` (the pinned `Nat`
at the head) or an instance of a safe inductive with no indices at the head. -/
theorem shape?_head {p : Src.Program} {fuel : Nat} {ls : List Nat} {t : Src.Term} {s : Shape}
    (h : shape? p fuel ls [] t = some s) :
    ∃ c us, t.spine.1 = .const c us ∧
      ((s = .nat ∧ some c = p.known.nat) ∨
        ∃ lv ac nl np ty keys, s = .ind c lv ac ∧ some c ≠ p.known.nat ∧
          p.decl? c = some (.induct true nl np 0 ty keys)) := by
  cases fuel with
  | zero => simp [shape?] at h
  | succ fuel =>
    unfold shape? at h
    generalize hsp : t.spine = sp at h
    obtain ⟨hd, args⟩ := sp
    simp only at h
    split at h
    · simp at h
    · next c us =>
      refine ⟨c, us, rfl, ?_⟩
      simp only [Option.bind_eq_bind] at h
      cases hl : List.mapM (level? ls) us with
      | none => simp [hl] at h
      | some levels =>
        simp only [hl, Option.bind_some] at h
        cases hn : (some c == p.known.nat) with
        | true =>
          simp only [hn, ↓reduceIte] at h
          split at h
          · cases h; exact .inl ⟨rfl, eq_of_beq hn⟩
          · cases h
        | false =>
          simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
          have hne : some c ≠ p.known.nat := fun e => by simp [e] at hn
          cases hd : p.decl? c with
          | none => simp [hd] at h
          | some d =>
            simp only [hd, Option.bind_some] at h
            split at h
            · next nl np ty keys =>
              split at h
              · split at h
                · cases ha : List.mapM (fun x => shape? p fuel ls [] x.fst) args with
                  | none => simp [ha] at h
                  | some ac =>
                    simp only [ha, Option.bind_some] at h
                    cases h
                    exact .inr ⟨levels, ac, nl, np, ty, keys, rfl, hne, rfl⟩
                · simp at h
              · simp at h
            · simp at h
    · simp at h

theorem forIn_all_of_none {α : Type} {l : List α}
    {body : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit))} (P : α → Prop)
    (hn : (forIn (m := Id) l ((none : Option Bool), ()) body).1 = none)
    (hb : ∀ x, body x (none, ()) = ForInStep.yield (none, ()) → P x)
    (hb' : ∀ x, body x (none, ()) = ForInStep.yield (none, ()) ∨
      body x (none, ()) = ForInStep.done (some false, ())) : ∀ x ∈ l, P x := by
  rcases forIn_none_all body P hb hb' l with ⟨_, hall⟩ | hfalse
  · exact hall
  · rw [hfalse] at hn; cases hn

theorem forIn_some_false {α : Type} {l : List α}
    {body : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit))} {r : Bool}
    (hs : (forIn (m := Id) l ((none : Option Bool), ()) body).1 = some r)
    (hb' : ∀ x, body x (none, ()) = ForInStep.yield (none, ()) ∨
      body x (none, ()) = ForInStep.done (some false, ())) : r = false := by
  rcases forIn_none_all body (fun _ => True) (fun _ _ => trivial) hb' l with ⟨h1, _⟩ | h1
  · rw [h1] at hs; cases hs
  · rw [h1] at hs; cases hs; rfl

/-- What `rowMatches` checks of each constructor of the row's inductive: it
has exactly one row in the constructor table, with its tag, and the
signature row has an entry at that tag. -/
theorem rowMatches_spec {p : Src.Program} {C : Cfg.Program} {shapes : List Shape} {shape : Shape}
    {row : List (List Rt.FoTy)} (h : rowMatches p C shapes shape row = true) :
    ∃ ind ls args nl np ty keys, shape = .ind ind ls args ∧
      p.decl? ind = some (.induct true nl np 0 ty keys) ∧
      ∀ key tag, (key, tag) ∈ keys.zipIdx →
        ∃ emitted fts, C.ctors.filter (fun r => r.key == .src key) = [emitted] ∧
          emitted.tag = tag ∧ row[tag]? = some fts := by
  unfold rowMatches at h
  simp only [Id.run, bind, pure] at h
  split at h
  · next ind ls args =>
    split at h
    · next nl np ty keys hd =>
      split at h
      · refine ⟨ind, ls, args, nl, np, ty, keys, rfl, hd, ?_⟩
        split at h
        · next r hr =>
          have := forIn_some_false hr ?_
          · subst this; cases h
          · intro x
            obtain ⟨key, tag⟩ := x
            simp only
            split
            · split
              · split
                · split
                  · split
                    · exact .inl rfl
                    · exact .inr rfl
                  · exact .inr rfl
                · exact .inr rfl
              · exact .inr rfl
            · exact .inr rfl
        · next hn =>
          intro key tag hk
          refine forIn_all_of_none (fun x => ∃ emitted fts,
            C.ctors.filter (fun r => r.key == .src x.1) = [emitted] ∧ emitted.tag = x.2 ∧
              row[x.2]? = some fts) hn ?_ ?_ (key, tag) hk
          · intro x hx
            obtain ⟨key, tag⟩ := x
            simp only at hx
            split at hx
            · split at hx
              · next emitted _ =>
                split at hx
                · next hc =>
                  split at hx
                  · next fts _ =>
                    split at hx
                    · next hr =>
                      simp only [Bool.and_eq_true, beq_iff_eq] at hc
                      exact ⟨emitted, fts, by assumption, hc.1.2, by simpa using hr⟩
                    · cases hx
                  · cases hx
                · cases hx
              · cases hx
            · cases hx
          · intro x
            obtain ⟨key, tag⟩ := x
            simp only
            split
            · split
              · split
                · split
                  · split
                    · exact .inl rfl
                    · exact .inr rfl
                  · exact .inr rfl
                · exact .inr rfl
              · exact .inr rfl
            · exact .inr rfl
      · cases h
    · cases h
  · cases h

theorem discoverRaw_root {p : Src.Program} {C : Cfg.Program} {c : Src.CId} {q : Candidate}
    (h : discoverRaw p C c = .ok q) :
    ∃ d, p.decl? c = some d ∧ shape? p 128 [] [] d.type.pis.2 = some q.root := by
  unfold discoverRaw at h
  cases hd : p.decl? c with
  | none => rw [hd] at h; cases h
  | some d =>
    refine ⟨d, rfl, ?_⟩
    rw [hd] at h
    simp only [bind, Except.bind] at h
    cases hl : (d.lvls == 0) with
    | false =>
      simp [hl] at h
    | true =>
      simp only [hl, ↓reduceIte, pure, Except.pure] at h
      cases hs : shape? p 128 [] [] d.type.pis.2 with
      | none => simp [hs] at h
      | some s =>
        simp only [hs] at h
        cases hlow : StateT.run (lower p C.ctors 128 s) [] with
        | error e => simp only [hlow] at h; cases h
        | ok v =>
          simp only [hlow] at h
          split at h
          · cases h
          · simp only [Except.ok.injEq] at h
            subst h
            rfl

end IxCC.Recheck.Readback
