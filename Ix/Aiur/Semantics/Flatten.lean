module
public import Ix.Aiur.Stages.Source
public import Ix.Aiur.Stages.Concrete
public import Ix.Aiur.Semantics.BytecodeFfi
public import Std.Data.HashSet

/-!
Total flattening utilities: convert between structured `Value`s and flat `Array G`.

Total by threading a `visited : HashSet Global` through `typFlatSize` /
`dataTypeFlatSize` to guard against direct datatype recursion without
`.pointer` indirection.
-/

public section
@[expose] section

namespace Aiur

/-- Runtime values produced by the source-level reference evaluators.
See `Ix/Aiur/Source/Eval.lean` and `Ix/Aiur/Concrete/Eval.lean`. -/
inductive Value : Type where
  | unit    : Value
  | field   : G → Value
  | tuple   : Array Value → Value
  | array   : Array Value → Value
  | ctor    : Global → Array Value → Value
  | fn      : Global → Value
  /-- `width, index` — width is the flat size of the stored element's type. In the
  Source-form evaluator only `index` is meaningful; in the Concrete-form
  evaluator `width` selects the per-width memory bucket to match Rust's
  `memory_queries`. -/
  | pointer : (width : Nat) → (index : Nat) → Value
  deriving Repr, Hashable, Inhabited

deriving instance DecidableEq for Global

mutual

def Value.decEq : (a b : Value) → Decidable (a = b)
  | .unit, .unit => isTrue rfl
  | .field g₁, .field g₂ =>
    if h : g₁ = g₂ then isTrue (h ▸ rfl) else isFalse fun h' => h (Value.field.inj h')
  | .tuple vs₁, .tuple vs₂ =>
    match Value.arrayDecEq vs₁ vs₂ with
    | isTrue h  => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun h' => h (Value.tuple.inj h')
  | .array vs₁, .array vs₂ =>
    match Value.arrayDecEq vs₁ vs₂ with
    | isTrue h  => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun h' => h (Value.array.inj h')
  | .ctor g₁ vs₁, .ctor g₂ vs₂ =>
    if hg : g₁ = g₂ then
      match Value.arrayDecEq vs₁ vs₂ with
      | isTrue hvs => isTrue (hg ▸ hvs ▸ rfl)
      | isFalse hvs => isFalse fun h' => hvs (Value.ctor.inj h').2
    else isFalse fun h' => hg (Value.ctor.inj h').1
  | .fn g₁, .fn g₂ =>
    if h : g₁ = g₂ then isTrue (h ▸ rfl) else isFalse fun h' => h (Value.fn.inj h')
  | .pointer w₁ n₁, .pointer w₂ n₂ =>
    if hw : w₁ = w₂ then
      if hn : n₁ = n₂ then isTrue (hw ▸ hn ▸ rfl)
      else isFalse fun h' => hn (Value.pointer.inj h').2
    else isFalse fun h' => hw (Value.pointer.inj h').1
  | .unit, .field _     | .unit, .tuple _     | .unit, .array _
  | .unit, .ctor _ _    | .unit, .fn _        | .unit, .pointer _ _
  | .field _, .unit      | .field _, .tuple _   | .field _, .array _
  | .field _, .ctor _ _  | .field _, .fn _      | .field _, .pointer _ _
  | .tuple _, .unit      | .tuple _, .field _   | .tuple _, .array _
  | .tuple _, .ctor _ _  | .tuple _, .fn _      | .tuple _, .pointer _ _
  | .array _, .unit      | .array _, .field _   | .array _, .tuple _
  | .array _, .ctor _ _  | .array _, .fn _      | .array _, .pointer _ _
  | .ctor _ _, .unit     | .ctor _ _, .field _  | .ctor _ _, .tuple _
  | .ctor _ _, .array _  | .ctor _ _, .fn _     | .ctor _ _, .pointer _ _
  | .fn _, .unit         | .fn _, .field _      | .fn _, .tuple _
  | .fn _, .array _      | .fn _, .ctor _ _     | .fn _, .pointer _ _
  | .pointer _ _, .unit    | .pointer _ _, .field _  | .pointer _ _, .tuple _
  | .pointer _ _, .array _ | .pointer _ _, .ctor _ _ | .pointer _ _, .fn _ =>
    isFalse Value.noConfusion

def Value.arrayDecEq : (a b : Array Value) → Decidable (a = b)
  | ⟨as⟩, ⟨bs⟩ =>
    match Value.listDecEq as bs with
    | isTrue h  => isTrue (congrArg Array.mk h)
    | isFalse h => isFalse fun h' => h (Array.mk.inj h')

def Value.listDecEq : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _::_ => isFalse (fun h => nomatch h)
  | _::_, [] => isFalse (fun h => nomatch h)
  | a::as, b::bs =>
    match Value.decEq a b, Value.listDecEq as bs with
    | isTrue ha, isTrue ht  => isTrue (ha ▸ ht ▸ rfl)
    | isFalse h, _          => isFalse fun h' => h (List.cons.inj h').1
    | _, isFalse h          => isFalse fun h' => h (List.cons.inj h').2

end

instance : DecidableEq Value := Value.decEq

/-- `OfNat Value n` produces `Value.field (G.ofNat n)` so numeric literals
write directly as `Value`s in test inputs and other contexts. -/
instance : OfNat Value n := ⟨.field (G.ofNat n)⟩

/-! ## Flat size computation — total via `visited` set

If a datatype is recursively referenced without a `.pointer` indirection, the
fixed-width flattening is ill-defined. The `visited` set makes the functions
total by detecting the cycle and returning `0` (a benign default that cannot
actually occur once the recursion-through-pointer-only invariant is established
by the checker). Mirrors `Layout.DataType.size:49-57`.

**On the `Nat` parameter that looks like fuel.** It's a *bound* on the remaining
recursion depth, not user-facing fuel. The outer interfaces
`typFlatSize` / `dataTypeFlatSize` set the bound to `decls.size + 1`; the visited
set's monotonic growth (capped at `decls.size`) guarantees the bound is never
exhausted on well-formed inputs. To eliminate this Nat parameter entirely we'd
need to refine `visited` to a subtype enforcing `visited.size ≤ decls.size` —
that's a multi-hour refactor that produces equivalent provability with more
ceremony, so we keep the bound parameter.

(This is *not* the same as the fuel in the reference evaluators, which is
genuine semantic call-counting and cannot be removed.)
-/

open Std (HashSet)

mutual

/-- See `typFlatSize` for the outer interface. -/
def typFlatSizeBound (decls : Source.Decls) : Nat → HashSet Global → Typ → Nat
  | 0, _, _ => 0
  | _+1, _, .unit => 0
  | _+1, _, .field => 1
  | _+1, _, .pointer _ => 1
  | _+1, _, .function _ _ => 1
  | bound+1, visited, .tuple ts =>
      ts.attach.foldl (init := 0)
        (fun acc ⟨t, _⟩ => acc + typFlatSizeBound decls bound visited t)
  | bound+1, visited, .array t n =>
      n * typFlatSizeBound decls bound visited t
  | bound+1, visited, .ref g
  | bound+1, visited, .app g _ =>
      if visited.contains g then 0
      else match decls.getByKey g with
        | some (.dataType dt) =>
            dataTypeFlatSizeBound decls bound (visited.insert g) dt
        | _ => 0
  | _+1, _, .mvar _ => 0

/-- Flat size of a datatype (max constructor size + 1 for the tag). -/
def dataTypeFlatSizeBound (decls : Source.Decls) : Nat → HashSet Global → DataType → Nat
  | 0, _, _ => 1
  | bound+1, visited, dt =>
      let ctorSizes := dt.constructors.map fun ctor =>
        ctor.argTypes.foldl (init := 0)
          (fun acc t => acc + typFlatSizeBound decls bound visited t)
      ctorSizes.foldl max 0 + 1

end

/-- Outer interface. The bound `decls.size + 1` cannot be exhausted given the
visited-set monotonicity (each step adds one fresh datatype name to `visited`,
which is bounded by `decls.size`), but the function is sound regardless: if the
bound were exhausted it returns `0`/`1`, which only matters on ill-formed inputs. -/
def typFlatSize (decls : Source.Decls) (visited : HashSet Global) (t : Typ) : Nat :=
  typFlatSizeBound decls (decls.size + 1) visited t

def dataTypeFlatSize (decls : Source.Decls) (visited : HashSet Global) (dt : DataType) : Nat :=
  dataTypeFlatSizeBound decls (decls.size + 1) visited dt

/-! ## Flattening: `Value → Array G` -/

open Source in
/-- Flatten a `Value` to a flat `Array G`. Structural recursion on `Value`.
Total: `sizeOf` on the `Value` inductive sees through `Array.attach`.

NOTE: post-concretize values carry mangled ctor names (`concretizeName g args`)
not present in source `decls`. The `.ctor` arm falls to the `| _ =>` branch
for such values, dropping tag+padding. `concretize_preserves_runFunction`
must bridge this via a ctor-rename relation (`ValueRelByConcretize`) or use
a concDecls-aware flatten variant. -/
def flattenValue (decls : Decls) (funcIdx : Global → Option Nat) :
    Value → Array G
  | .unit        => #[]
  | .field g     => #[g]
  | .pointer _ n => #[.ofNat n]
  | .fn g        => #[.ofNat (funcIdx g |>.getD 0)]
  | .tuple vs    =>
      vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v)
  | .array vs    =>
      vs.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v)
  | .ctor g args =>
      match decls.getByKey g with
      | some (.constructor dt ctor) =>
          let ctorIndex := dt.constructors.findIdx? (· == ctor) |>.getD 0
          let dtSize := dataTypeFlatSize decls {} dt
          let argsFlat := args.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v)
          let flat := #[.ofNat ctorIndex] ++ argsFlat
          let padding := dtSize - flat.size
          flat ++ Array.replicate padding 0
      | _ => args.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v)
termination_by v => sizeOf v

/-! ## Flat-size on `Concrete.Decls`.

Post-concretize declarations use `Concrete.Typ` (no `.app`/`.mvar`), so flat-
size collapses to a simpler recursion. Mirrors `typFlatSize` structurally. -/

open Source in
mutual

def Concrete.typFlatSizeBound (decls : Concrete.Decls) :
    Nat → HashSet Global → Concrete.Typ → Nat
  | 0, _, _ => 0
  | _+1, _, .unit => 0
  | _+1, _, .field => 1
  | _+1, _, .pointer _ => 1
  | _+1, _, .function _ _ => 1
  | bound+1, visited, .tuple ts =>
      ts.attach.foldl (init := 0)
        (fun acc ⟨t, _⟩ => acc + Concrete.typFlatSizeBound decls bound visited t)
  | bound+1, visited, .array t n =>
      n * Concrete.typFlatSizeBound decls bound visited t
  | bound+1, visited, .ref g =>
      if visited.contains g then 0
      else match decls.getByKey g with
        | some (.dataType dt) =>
            Concrete.dataTypeFlatSizeBound decls bound (visited.insert g) dt
        | _ => 0

def Concrete.dataTypeFlatSizeBound (decls : Concrete.Decls) :
    Nat → HashSet Global → Concrete.DataType → Nat
  | 0, _, _ => 1
  | bound+1, visited, dt =>
      let ctorSizes := dt.constructors.map fun ctor =>
        ctor.argTypes.foldl (init := 0)
          (fun acc t => acc + Concrete.typFlatSizeBound decls bound visited t)
      ctorSizes.foldl max 0 + 1

end

def Concrete.dataTypeFlatSize (decls : Concrete.Decls)
    (visited : HashSet Global) (dt : Concrete.DataType) : Nat :=
  Concrete.dataTypeFlatSizeBound decls (decls.size + 1) visited dt

/-! ## Flattening over `Concrete.Decls`.

Mirror of `flattenValue` but resolves ctor names in `Concrete.Decls` instead
of `Source.Decls`. Used in `concretize_preserves_runFunction` to flatten
post-concretize values where ctor names are concretized (not in source decls). -/

def Concrete.flattenValue (decls : Concrete.Decls) (funcIdx : Global → Option Nat) :
    Value → Array G
  | .unit        => #[]
  | .field g     => #[g]
  | .pointer _ n => #[.ofNat n]
  | .fn g        => #[.ofNat (funcIdx g |>.getD 0)]
  | .tuple vs    =>
      vs.attach.flatMap (fun ⟨v, _⟩ => Concrete.flattenValue decls funcIdx v)
  | .array vs    =>
      vs.attach.flatMap (fun ⟨v, _⟩ => Concrete.flattenValue decls funcIdx v)
  | .ctor g args =>
      match decls.getByKey g with
      | some (.constructor dt ctor) =>
          let ctorIndex := dt.constructors.findIdx? (· == ctor) |>.getD 0
          let dtSize := Concrete.dataTypeFlatSize decls {} dt
          let argsFlat := args.attach.flatMap
            (fun ⟨v, _⟩ => Concrete.flattenValue decls funcIdx v)
          let flat := #[.ofNat ctorIndex] ++ argsFlat
          let padding := dtSize - flat.size
          flat ++ Array.replicate padding 0
      | _ => args.attach.flatMap
          (fun ⟨v, _⟩ => Concrete.flattenValue decls funcIdx v)
termination_by v => sizeOf v

/-- Read a structured `Value` from a flat `Array G`, guided by the type.
Fuel-bounded like `typFlatSize`; the outer `unflattenValue` uses the same
`decls.size + 1` bound. -/
def unflattenValueBound (decls : Source.Decls) (gs : Array G) :
    Nat → Nat → Typ → Value × Nat
  | 0, _, _ => (.unit, 0)
  | _+1, _, .unit => (.unit, 0)
  | _+1, offset, .field => (.field (gs.getD offset 0), 1)
  | _+1, offset, .pointer t =>
      let w := typFlatSize decls {} t
      (.pointer w (gs.getD offset 0).val.toNat, 1)
  | _+1, _, .function _ _ => (.fn ⟨.anonymous⟩, 1)
  | bound+1, offset, .tuple ts =>
      let (vs, consumed) := ts.attach.foldl (init := (#[], 0))
        fun (acc, off) ⟨t, _⟩ =>
          let (v, n) := unflattenValueBound decls gs bound (offset + off) t
          (acc.push v, off + n)
      (.tuple vs, consumed)
  | bound+1, offset, .array t n =>
      let eltSize := typFlatSize decls {} t
      let vs := Array.ofFn fun (i : Fin n) =>
        (unflattenValueBound decls gs bound (offset + i.val * eltSize) t).1
      (.array vs, n * eltSize)
  | bound+1, offset, .ref g
  | bound+1, offset, .app g _ =>
      match decls.getByKey g with
      | some (.dataType dt) =>
          let dtSize := dataTypeFlatSize decls {} dt
          let tag := (gs.getD offset 0).val.toNat
          let ctors := dt.constructors.toArray
          if h : tag < ctors.size then
            let ctor := ctors[tag]
            let ctorName := dt.name.pushNamespace ctor.nameHead
            let (args, _) := ctor.argTypes.foldl (init := (#[], 1)) fun (acc, off) t =>
              let (v, n) := unflattenValueBound decls gs bound (offset + off) t
              (acc.push v, off + n)
            (.ctor ctorName args, dtSize)
          else (.field (gs.getD offset 0), dtSize)
      | _ => (.field (gs.getD offset 0), 1)
  | _+1, _, .mvar _ => (.unit, 0)
termination_by bound _ _ => bound

/-- Outer interface; the recursion bound is `decls.size + 1` (see note above). -/
def unflattenValue (decls : Source.Decls) (gs : Array G) (offset : Nat) (t : Typ) :
    Value × Nat :=
  unflattenValueBound decls gs (decls.size + 1) offset t

open Source in
/-- Reconstruct structured input `Value`s from a flat `Array G`. -/
def unflattenInputs (decls : Decls) (gs : Array G) (inputTypes : List Typ) :
    List Value :=
  let (vals, _) := inputTypes.foldl (init := (#[], 0)) fun (acc, off) t =>
    let (v, n) := unflattenValue decls gs off t
    (acc.push v, off + n)
  vals.toList

/-! ## Naturally-list coercion for args, used in the compile_correct statement -/

open Source in
/-- The natural list-to-flat coercion used in the statement of `compile_correct`. -/
def Flatten.args (decls : Decls) (funcIdx : Global → Option Nat)
    (args : List Value) : Array G :=
  args.foldl (fun acc v => acc ++ flattenValue decls funcIdx v) #[]

end Aiur

end -- @[expose] section
end
