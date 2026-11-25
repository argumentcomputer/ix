import IxCCTests.Fir.Support
import IxCC.Own.Immortal
import IxCC.Own.Plain.Owned
import IxCC.Fir.ShapeInfer

/-! The array primitives at Fir and Own (`plans/ONE-PIPELINE.md`, lane prims-core, stage B).
`Fir.lower` still refuses them (`fir.arrays`, `IxCCTests.Anf.ArrayPrims`), so the program here is
hand-written Fir: one function `fun n => …` per root, its bindings numbered from 1.

* At Fir, every root on every argument gives what the list model says (computed here with `List`
  functions): a number, an array (`ctor (arrInfo n) elems`), or a trap for an out-of-range `get`
  or `set`, a dead one included.
* Own (the immortal embedding), under both allocation policies, has the same outcome and a value
  denoting Fir's (`sameFirOwn`: an array is a cell under `arrInfo n`, the empty one the immediate
  `ctor0 (arrInfo 0)`).
* The shape certificate (`Fir.Shape.check`) accepts a hand-written certificate with typed array
  shapes (`ArrOk`: element shapes kept, static lengths tracked, `size` of a known length bounded),
  refuses two wrong ones, and accepts what the producer proposes for both programs; the typed
  function returns a value of its result shape at every argument, at Fir and at Own.
* The ownership checker declines an array primitive (`own.arrays`). -/

namespace IxCCTests.Fir.ArrayPrims

open IxCC IxCCTests.Src
open IxCC.Fir (Arg Rhs Code)

def arr (op : Src.ArrOp) (args : List Arg) : Rhs := .prim (.arr op) args
def v (x : Nat) : Arg := .var x
def lit (n : Nat) : Arg := .lit (.nat n)

/-- Bind `rs` to the variables `1, 2, …` in order (`0` is the parameter) and return the last. -/
def seq (rs : List Rhs) : Code :=
  rs.zipIdx.foldr (fun (r, i) k => .bind (i + 1) r k) (.ret (.var rs.length))

def natV (n : Nat) : FVal := .lit (.nat n)
def arrV (xs : List FVal) : FVal := .ctor (IxCC.Fir.arrInfo xs.length) xs
def nats (xs : List Nat) : FVal := arrV (xs.map natV)

/-- The roots with their list-model meaning (`none`: a trap). -/
def roots : List (String × Code × (Nat → Option FVal)) :=
  [("size (replicate n 3 ++ [n])",
      seq [arr .replicate [v 0, lit 3], arr .empty [lit 0], arr .push [v 2, v 0],
        arr .append [v 1, v 3], arr .size [v 4]],
      fun n => some (natV (List.replicate n 3 ++ [n]).length)),
   ("get (replicate n 5 ++ [n, 9]) n",
      seq [arr .replicate [v 0, lit 5], arr .push [v 1, v 0], arr .push [v 2, lit 9],
        arr .get [v 3, v 0]],
      fun n => ((List.replicate n 5 ++ [n, 9])[n]?).map natV),
   ("push (replicate 2 n) 7",
      seq [arr .replicate [lit 2, v 0], arr .push [v 1, lit 7]],
      fun n => some (nats [n, n, 7])),
   ("empty n",
      seq [arr .empty [v 0]],
      fun _ => some (nats [])),
   ("set (replicate 3 0) 1 n",
      seq [arr .replicate [lit 3, lit 0], arr .set [v 1, lit 1, v 0]],
      fun n => some (nats ((List.replicate 3 0).set 1 n))),
   ("set (replicate 2 0) n 1 (out of range from 2)",
      seq [arr .replicate [lit 2, lit 0], arr .set [v 1, v 0, lit 1]],
      fun n => if n < 2 then some (nats ((List.replicate 2 0).set n 1)) else none),
   ("get (replicate n 7) n (out of range)",
      seq [arr .replicate [v 0, lit 7], arr .get [v 1, v 0]],
      fun _ => none),
   ("a dead get out of range",
      .bind 1 (arr .empty [lit 0]) (.bind 2 (arr .get [v 1, v 0]) (.ret (lit 42))),
      fun _ => none),
   ("a dead push",
      .bind 1 (arr .empty [lit 0]) (.bind 2 (arr .push [v 1, v 0]) (.ret (lit 42))),
      fun _ => some (natV 42)),
   ("pop (replicate n 4)",
      seq [arr .replicate [v 0, lit 4], arr .pop [v 1]],
      fun n => some (nats (List.replicate n 4).dropLast)),
   ("extract (replicate 10 1) n 7",
      seq [arr .replicate [lit 10, lit 1], arr .extract [v 1, v 0, lit 7]],
      fun n => some (nats (Src.ArraySpec.extractList (List.replicate 10 1) n 7))),
   ("copySlice [9, 8, 7, 6] 1 (replicate n 0) 0 2",
      seq [arr .empty [lit 0], arr .push [v 1, lit 9], arr .push [v 2, lit 8],
        arr .push [v 3, lit 7], arr .push [v 4, lit 6], arr .replicate [v 0, lit 0],
        arr .copySlice [v 5, lit 1, v 6, lit 0, lit 2]],
      fun n => some (nats (Src.ArraySpec.copySliceList [9, 8, 7, 6] 1 (List.replicate n 0) 0 2))),
   ("push (empty 0) (replicate n 1): an array of arrays",
      seq [arr .replicate [v 0, lit 1], arr .empty [lit 0], arr .push [v 2, v 1]],
      fun n => some (arrV [nats (List.replicate n 1)]))]

def program : FProgram :=
  let fs : List IxCC.Fir.Fun := roots.zipIdx.map fun ((_, body, _), i) =>
    { key := .const i [], params := [(0, .tobj)], body, vars := 16 }
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (f, i) => (i, f)), size := fs.length
    exports := List.range fs.length, ctors := [], known := {} }

/-- A function whose certificate types its arrays: `fun n =>` (shapes on the right). -/
def typedBody : Code :=
  seq [arr .empty [lit 0],            -- 1 : arr nat (some 0)
    arr .push [v 1, v 0],             -- 2 : arr nat (some 1)
    arr .push [v 2, lit 7],           -- 3 : arr nat (some 2)
    arr .replicate [lit 3, v 0],      -- 4 : arr nat none
    arr .append [v 3, v 4],           -- 5 : arr nat none
    arr .size [v 3],                  -- 6 : natLt 3
    arr .get [v 5, v 6],              -- 7 : nat
    arr .set [v 3, lit 0, v 7],       -- 8 : arr nat (some 2)
    arr .size [v 8]]                  -- 9 : natLt 3

def typedFun : IxCC.Fir.Fun :=
  { key := .const 0 [], params := [(0, .tobj)], body := typedBody, vars := 16 }

def typed : FProgram :=
  { funs := Src.NatMap.ofList [(0, typedFun)], size := 1, exports := [0], ctors := [], known := {} }

def typedShapes (size6 arr2 : IxCC.Shape.Shape) : IxCC.Fir.Shape.ShapeCert :=
  let ns : IxCC.Shape.Shape := .nat
  let fs : IxCC.Fir.Shape.FunShapes :=
    { params := [ns], ret := .natLt 3,
      vars := Src.NatMap.ofList [(0, ns), (1, .arr ns (some 0)), (2, arr2), (3, .arr ns (some 2)),
        (4, .arr ns none), (5, .arr ns none), (6, size6), (7, ns), (8, .arr ns (some 2)),
        (9, .natLt 3)] }
  { funs := Src.NatMap.ofList [(0, fs)] }

def args : List Nat := [0, 1, 2, 5, 9]

def clock : Nat := 20

def run (a : Assert) : IO (Array String) := do
  let F := program
  let O := IxCC.Own.immortal F
  let mut runs := 0
  let mut traps := 0
  for ((label, _, meaning), r) in roots.zipIdx do
    for n in args do
      let rf ← runFir F clock r [n]
      let ok := match meaning n, rf with
        | some w, .ok w' => w' == w
        | none, .trap => true
        | _, _ => false
      expect a ok s!"Fir: {label} at {n}: {firOutcome rf}"
      if rf matches .trap then traps := traps + 1
      for pol in [IxCC.Own.AllocPol.immortal, .rc] do
        let ro ← runOwn pol O clock r [n]
        expect a (sameFirOwn rf ro) s!"Own: {label} at {n}: {ownOutcome ro}, Fir {firOutcome rf}"
      runs := runs + 1
  -- the shape certificate
  let good := typedShapes (.natLt 3) (.arr .nat (some 1))
  expect a (IxCC.Fir.Shape.check typed good) "the typed array certificate is refused"
  expect a (!IxCC.Fir.Shape.check typed (typedShapes (.natLt 2) (.arr .nat (some 1))))
    "a certificate bounding the size of a length-2 array by 2 is accepted"
  expect a (!IxCC.Fir.Shape.check typed (typedShapes (.natLt 3) (.arr .nat (some 5))))
    "a certificate giving a push the wrong length is accepted"
  expect a (IxCC.Fir.ShapeInfer.run typed).2
    "the producer's certificate for the typed function is refused"
  expect a (IxCC.Fir.ShapeInfer.run F).2 "the producer's certificate for the array roots is refused"
  let To := IxCC.Own.immortal typed
  for n in args do
    let rf ← runFir typed clock 0 [n]
    expect a (match rf with | .ok (.lit (.nat m)) => m < 3 | _ => false)
      s!"typed at {n}: {firOutcome rf} is not below 3"
    let ro ← runOwn .immortal To clock 0 [n]
    expect a (sameFirOwn rf ro) s!"typed at {n}: Own {ownOutcome ro}, Fir {firOutcome rf}"
  let declined := match IxCC.Own.Plain.bindStep {} 1 (arr .size [v 0]) with
    | .error e => e.startsWith "own.arrays"
    | .ok _ => false
  expect a declined "the ownership checker accepts an array primitive"
  return #[s!"arrays at Fir: {roots.length} roots × {args.length} arguments agree with the list model ({runs} runs, {traps} traps)",
    s!"arrays at Own: the same outcomes and denoting values under both policies ({2 * runs} runs)",
    "arrays: the shape certificate accepts typed array shapes and refuses two wrong ones",
    "arrays: the ownership checker declines with own.arrays"]

end IxCCTests.Fir.ArrayPrims
