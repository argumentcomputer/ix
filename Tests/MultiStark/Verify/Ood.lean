module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Ood

namespace Tests.MultiStark.Verify.Ood

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def e (n : Nat) : Ext := Arithmetic.fromNat n
private def zero : Ext := Arithmetic.zero
private def one : Ext := Arithmetic.one
private def x : Ext := Arithmetic.basis
private def coord (n : Nat) : Arithmetic.Coordinates := .embed (e n)
private def okEquals {ε α : Type} [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with | .ok actual => actual == expected | .error _ => false

private def circuit : Circuit := ⟨1, 0, 0, 3, 1, #[], #[], #[]⟩
private def values : Shape.CircuitValues := {
  index := 0, circuit, logDegree := 3, stage1 := (#[], #[]), stage2 := (#[], #[])
  preprocessed := (#[], #[]), quotient := #[⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩, ⟨7, 8⟩] }

private def checks : IO (List Check) := do
  let point : Ext := ⟨3, 2⟩
  let collision : Arithmetic.Coordinates := ⟨x, Arithmetic.neg one⟩
  let computed := #[e 2, e 3, e 5, e 7]
  let beta := coord 11
  let gamma := coord 13
  let two : Array Lookup := #[⟨0, #[2]⟩, ⟨1, #[3]⟩]
  let challenges : Transcript.Challenges := ⟨zero, e 3, e 5, point⟩
  return [
    ("quadratic basis squares to seven", x.mul x == e 7),
    ("protocol base inverse rejects zero", !(Arithmetic.inverseBase 0).isOk),
    ("protocol extension inverse rejects zero", !(Arithmetic.inverse zero).isOk),
    ("protocol division rejects zero", !(Arithmetic.divide one zero).isOk),
    ("extension inverse agrees with multiplication", (#[⟨1, 0⟩, ⟨0, 1⟩, point] : Array Ext).all
      (fun value => match Arithmetic.inverse value with
        | .ok inv => value.mul inv == one | .error _ => false)),
    ("logarithmic exponentiation agrees with repeated multiplication",
      #[0, 1, 2, 3, 7, 17, 64].all fun n => Arithmetic.pow point n ==
        (List.range n).foldl (fun value _ => value.mul point) one),
    ("repeated squaring exponent convention", (List.range 8).all fun n =>
      Arithmetic.pow2 point n == Arithmetic.pow point (2 ^ n)),
    ("native generator ladder squares to the previous entry", (List.range 32).all fun n =>
      match Arithmetic.twoAdicGenerator n, Arithmetic.twoAdicGenerator (n + 1) with
      | .ok previous, .ok next => next.mul next == previous
      | _, _ => false),
    ("all supported native generators have exact two-adic order", (List.range 33).all fun n =>
      match Arithmetic.twoAdicGenerator n with
      | .ok g => g.pow (2 ^ n) == 1 && (n == 0 || g.pow (2 ^ (n - 1)) != 1)
      | .error _ => false),
    ("unsupported subgroup degree rejected", !(Arithmetic.twoAdicGenerator 33).isOk),
    ("singular first-row OOD point rejected", !(Ood.selectors 3 one).isOk),
    ("oversized selector domain rejected", !(Ood.selectors 33 point).isOk),
    ("raw selector and normalization equations", match Ood.selectors 3 point,
        Arithmetic.twoAdicGenerator 3 with
      | .ok selectors, .ok generator =>
        let vanishing := (Arithmetic.pow2 point 3).sub one
        selectors.first.mul (point.sub one) == vanishing &&
        selectors.last.mul selectors.transition == vanishing &&
        selectors.invVanishing.mul vanishing == one &&
        selectors.injectionNorm.mul (Arithmetic.embed (generator.mul 8)) == one
      | _, _ => false),
    ("distinct lookup coordinates must not be collapsed",
      collision != Arithmetic.Coordinates.zero && collision.c0.add (collision.c1.mul x) == zero),
    ("lookup-free group preserves two independent constraints",
      okEquals (Ood.groupEquation #[] #[] beta gamma collision) collision),
    ("single lookup equation golden value",
      okEquals (Ood.groupEquation computed #[⟨0, #[2]⟩] beta gamma (coord 4)) (coord 62)),
    ("grouped product-minus-multiplicity equation golden value",
      okEquals (Ood.groupEquation computed two beta gamma (coord 4)) (coord 1068)),
    ("lookup fingerprint coefficient order and both coordinates",
      okEquals (Ood.lookupMessage computed ⟨e 11, e 13⟩ ⟨e 5, e 7⟩ ⟨0, #[0, 1]⟩) ⟨e 28, e 34⟩),
    ("invalid lookup reference rejected", !(Ood.lookupMessage computed beta gamma ⟨0, #[9]⟩).isOk),
    ("quotient recombination preserves OOD-valued coefficient coordinates",
      okEquals (Ood.recombineQuotient values (e 5)) ⟨334, 70⟩),
    ("odd quotient width rejected", !(Ood.recombineQuotient
      { values with quotient := values.quotient.pop } (e 5)).isOk),
    ("empty accumulator list never balances", !Ood.balanced #[]),
    ("nonzero final accumulator rejected", !Ood.balanced #[one]),
    ("zero lookup denominator rejected", !(Ood.initialAccumulator challenges #[#[]]).isOk)
  ]

public def suite : IO UInt32 := runChecks "stage2-ood" checks

end Tests.MultiStark.Verify.Ood
