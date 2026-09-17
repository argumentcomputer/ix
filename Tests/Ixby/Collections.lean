module
import Tests.Ixby.Common
import Ix.Ixby

namespace Tests.Ixby.Collections
open Ix.Ixby

private def n (x : Nat) : Value := .scalar (.nat x)
private def w (x : UInt32) : Value := .scalar (.word32 x)
private def f (x : Nat) : Value := .scalar (.field (Goldilocks.reduce x))
private def bytes (x : Array UInt8) : Value := .scalar (.bytes x)
private def accepts (op : Primitive) (args : List Value) (value : Value)
    (limits : Limits := {}) : Bool :=
  match op.eval limits args with | .ok actual => actual == value | _ => false
private def rejects (op : Primitive) (args : List Value) (error : Error)
    (limits : Limits := {}) : Bool :=
  match op.eval limits args with | .error actual => actual == error | _ => false

example : Primitive.eval {} .arraySet
    [.array #[.erased, .scalar (.nat 9)], .scalar (.nat 0), .scalar (.nat 7)] =
    .ok (.array #[.scalar (.nat 7), .scalar (.nat 9)]) := rfl

example : Primitive.eval {} .byteBuilderAppend
    [.byteBuilder #[1, 2], .scalar (.bytes #[3, 4])] = .ok (.byteBuilder #[1, 2, 3, 4]) := rfl

example : Primitive.eval {} .arrayGet [.array #[], .scalar (.nat 0)] =
    .error (.primitiveValue .arrayGet) := rfl

private def pipeline : Program := { functions := #[{
  arity := 0
  blocks := #[
    ⟨0, .letOp (.primitive .arrayEmpty []) 1⟩,
    ⟨1, .letOp (.primitive .arrayPush [.local 0, .literal (.nat 7)]) 2⟩,
    ⟨2, .letOp (.primitive .arraySet [.local 1, .literal (.nat 0), .literal (.nat 9)]) 3⟩,
    ⟨3, .letOp (.primitive .arrayGet [.local 1, .literal (.nat 0)]) 4⟩,
    ⟨4, .letOp (.primitive .arrayGet [.local 2, .literal (.nat 0)]) 5⟩,
    ⟨5, .letOp (.primitive .natAdd [.local 3, .local 4]) 6⟩,
    ⟨6, .ret (.local 5)⟩] }] }

private def checks : IO (List Check) := do
  let original := (Array.range 33).map n
  let chunks : Array (Array UInt8) := #[#[], #[1], #[2, 3], #[], (Array.range 65).map Nat.toUInt8]
  let builderCheck := Id.run do
    let mut builder := Value.byteBuilder #[]
    let mut expected := #[]
    for chunk in chunks do
      let old := builder
      let oldBytes := expected
      match Primitive.eval {} .byteBuilderAppend [builder, bytes chunk] with
      | .error _ => return false
      | .ok next => builder := next
      expected := expected ++ chunk
      if !accepts .byteBuilderFreeze [old] (bytes oldBytes) then return false
      if !accepts .byteBuilderFreeze [builder] (bytes expected) then return false
      if !accepts .byteBuilderLength [builder] (n expected.size) then return false
    return true
  return [
    ("empty array", accepts .arrayEmpty [] (.array #[])),
    ("array length", accepts .arrayLength [.array original] (n 33)),
    ("array length obeys Nat capacity", rejects .arrayLength [.array original]
      (.limit .natBits) { natBits := 5 }),
    ("checked get at every index", (List.range 33).all fun i =>
      accepts .arrayGet [.array original, n i] (n i)),
    ("persistent set preserves every old alias", (List.range 33).all fun i =>
      let next := original.set! i (n 100)
      accepts .arraySet [.array original, n i, n 100] (.array next) &&
        (List.range 33).all (fun j => accepts .arrayGet [.array original, n j] (n j) &&
          accepts .arrayGet [.array next, n j] (n (if i == j then 100 else j)))),
    ("push preserves old array", accepts .arrayPush [.array original, .erased]
      (.array (original.push .erased)) && accepts .arrayLength [.array original] (n 33)),
    ("empty get rejects", rejects .arrayGet [.array #[], n 0] (.primitiveValue .arrayGet)),
    ("end get rejects", rejects .arrayGet [.array original, n 33] (.primitiveValue .arrayGet)),
    ("huge index rejects without narrowing", rejects .arrayGet [.array original, n (2 ^ 80)]
      (.primitiveValue .arrayGet)),
    ("end set rejects", rejects .arraySet [.array original, n 33, .erased]
      (.primitiveValue .arraySet)),
    ("index input capacity checked first", rejects .arrayGet [.array original, n 32]
      (.limit .natBits) { natBits := 5 }),
    ("index must be Nat", rejects .arrayGet [.array original, w 0] (.primitiveType .arrayGet)),
    ("array tag required", rejects .arrayLength [bytes #[]] (.primitiveType .arrayLength)),
    ("nested values preserved", accepts .arrayPush [.array #[], .array original]
      (.array #[.array original])),
    ("zero arity enforced", rejects .arrayEmpty [.erased] (.arityMismatch 0 1)),
    ("set arity enforced", rejects .arraySet [.array original, n 0] (.arityMismatch 3 2)),
    ("empty builder", accepts .byteBuilderEmpty [] (.byteBuilder #[])),
    ("builder append and freeze preserve all aliases", builderCheck),
    ("builder input bound", rejects .byteBuilderFreeze [.byteBuilder #[1, 2]]
      (.limit .byteArrayBytes) { byteArrayBytes := 1 }),
    ("builder append result bound", rejects .byteBuilderAppend [.byteBuilder #[1], bytes #[2]]
      (.limit .byteArrayBytes) { byteArrayBytes := 1 }),
    ("builder exact bound", accepts .byteBuilderAppend [.byteBuilder #[1], bytes #[2]]
      (.byteBuilder #[1, 2]) { byteArrayBytes := 2 }),
    ("builder must be frozen before bytes operations", rejects .bytesLength [.byteBuilder #[]]
      (.primitiveType .bytesLength)),
    ("builder length obeys Nat capacity", rejects .byteBuilderLength [.byteBuilder #[1, 2]]
      (.limit .natBits) { natBits := 1 }),
    ("slice retains exact range", accepts .bytesSlice [bytes #[1, 2, 3, 4], w 1, w 2] (bytes #[2, 3])),
    ("empty slice at end", accepts .bytesSlice [bytes #[1], w 1, w 0] (bytes #[])),
    ("slice past end rejects", rejects .bytesSlice [bytes #[1], w 1, w 1] (.primitiveValue .bytesSlice)),
    ("slice addition cannot wrap", rejects .bytesSlice [bytes #[1], w 0xffffffff, w 2]
      (.primitiveValue .bytesSlice)),
    ("field canonical representative", [0, 1, 2 ^ 32, goldilocksModulus - 1].all fun x =>
      accepts .fieldToNat [f x] (n x)),
    ("Nat to field is explicit modular reduction", [0, goldilocksModulus - 1, goldilocksModulus,
      goldilocksModulus + 1, 2 ^ 128 - 1, 2 ^ 256 + 37].all fun x => accepts .natToField [n x] (f x)),
    ("field to Nat result capacity", rejects .fieldToNat [f 32] (.limit .natBits) { natBits := 5 }),
    ("Nat to field source capacity", rejects .natToField [n 32] (.limit .natBits) { natBits := 5 }),
    ("field conversion preserves tag checks", rejects .fieldToNat [n 0] (.primitiveType .fieldToNat) &&
      rejects .natToField [w 0] (.primitiveType .natToField)),
    ("old and updated arrays coexist through execution", match execute {} pipeline #[] 8 with
      | .ok value => value == n 16 | _ => false),
    ("array operations consume exact logical fuel", match execute {} pipeline #[] 7 with
      | .error .outOfFuel => true | _ => false)
  ]

public def suite : IO UInt32 := runChecks "ixby-collections" checks
end Tests.Ixby.Collections
