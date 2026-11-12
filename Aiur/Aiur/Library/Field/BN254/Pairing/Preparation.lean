import Aiur.Library.Field.BN254.Fq

/-! Deterministic fixed-anchor preparation over the BN254 base field.
The exporter checks compressed anchors, curve/subgroup membership and every
prepared coefficient before embedding a line table in a compiler artifact. -/
namespace Aiur.Library.Field.BN254.Pairing.Preparation

private def p : Nat := Fq.modulus

structure C where
  re : Nat
  im : Nat
  deriving DecidableEq, Repr

private def c (re im : Nat) : C := ⟨re % p, im % p⟩
private def zero : C := c 0 0
private def one : C := c 1 0
private def add (a b : C) : C := c (a.re + b.re) (a.im + b.im)
private def sub (a b : C) : C := c (a.re + p - b.re) (a.im + p - b.im)
private def neg (a : C) : C := sub zero a
private def mul (a b : C) : C :=
  c ((a.re * b.re) % p + p - (a.im * b.im) % p) (a.re * b.im + a.im * b.re)
private def scale (n : Nat) (a : C) : C := c (n * a.re) (n * a.im)
private def sq (a : C) : C := mul a a
private def conj (a : C) : C := c a.re (p - a.im)

structure Affine where
  x : C
  y : C
  deriving Repr

private structure Hom where
  x : C
  y : C
  z : C

private def b : C := c
  19485874751759354771024239261021720505790618469301721065564631296452457478373
  266929791119991161246907387137283842545076965332900288569378510910307636690
private def qx : C := c
  21575463638280843010398324269430826099269044274347216827212613867836435027261
  10307601595873709700152284273816112264069230130616436755625194854815875713954
private def qy : C := c
  2821565182194536844548159561693502659359617185244120367078079554186484126554
  3505843767911556378687030309984248845540243509899259641013678093033130930403

private def twist (a : Affine) : Affine := ⟨mul (conj a.x) qx, mul (conj a.y) qy⟩
private def hom (a : Affine) : Hom := ⟨a.x, a.y, one⟩
private def infinity : Hom := ⟨zero, one, zero⟩

private def doubleStep (r : Hom) : Hom × List C :=
  let a := scale ((p+1)/2) (mul r.x r.y)
  let bb := sq r.y
  let cc := sq r.z
  let e := mul b (scale 3 cc)
  let f := scale 3 e
  let g := scale ((p+1)/2) (add bb f)
  let h := sub (sq (add r.y r.z)) (add bb cc)
  let i := sub e bb
  let j := sq r.x
  (⟨mul a (sub bb f), sub (sq g) (scale 3 (sq e)), mul bb h⟩,
    [neg h, scale 3 j, i])

private def addStep (r : Hom) (q : Affine) : Hom × List C :=
  let theta := sub r.y (mul q.y r.z)
  let lambda := sub r.x (mul q.x r.z)
  let cc := sq theta
  let d := sq lambda
  let e := mul lambda d
  let f := mul r.z cc
  let g := mul r.x d
  let h := sub (add e f) (scale 2 g)
  let j := sub (mul theta q.x) (mul lambda q.y)
  (⟨mul lambda h, sub (mul theta (sub g h)) (mul e r.y), mul r.z e⟩,
    [lambda, neg theta, j])

private def completeAdd (r : Hom) (q : Affine) : Hom :=
  if r.z = zero then hom q
  else if r.x = mul q.x r.z then
    if r.y = mul q.y r.z then (doubleStep r).1 else infinity
  else (addStep r q).1

private def scalarMul (n : Nat) (q : Affine) : Hom := Id.run do
  let mut r := infinity
  for bit in (List.range (n.log2 + 1)).reverse do
    r := if r.z = zero then infinity else (doubleStep r).1
    if n.testBit bit then r := completeAdd r q
  return r

private def inSubgroup (q : Affine) : Bool :=
  let r := scalarMul (6 * 4965661367192848881^2) q
  let image := twist q
  decide (r.z ≠ zero ∧ r.x = mul image.x r.z ∧ r.y = mul image.y r.z)

private def little (n : Nat) : List Nat := (List.range 32).map fun i => (n / 256^i) % 256

def compressed (q : Affine) : List Nat :=
  let other := neg q.y
  let sign := q.y.im > other.im || (q.y.im == other.im && q.y.re > other.re)
  little q.x.re ++ (little q.x.im).modify 31 (· + if sign then 128 else 0)

def readAnchor (coordinates : List Nat) : Except String Affine := do
  let [x0,x1,y0,y1] := coordinates | throw "G2 anchor requires four Fq coordinates"
  unless coordinates.all (· < p) do throw "noncanonical G2 anchor coordinate"
  let q : Affine := ⟨c x0 x1, c y0 y1⟩
  unless sq q.y = add (mul (sq q.x) q.x) b do throw "G2 anchor is not on curve"
  unless inSubgroup q do throw "G2 anchor is not in the prime-order subgroup"
  return q

private def ate : List Int :=
  [0,0,0,1,0,1,0,-1,0,0,-1,0,0,0,1,0,0,-1,0,-1,0,0,0,1,0,-1,0,0,0,
   0,-1,0,0,1,0,-1,0,0,1,0,0,0,0,0,-1,0,0,-1,0,1,0,-1,0,0,0,-1,0,
   -1,0,0,0,1,0,1,1]

private def prepare (q : Affine) : List (Bool × List C) := Id.run do
  let mut r := hom q
  let mut lines := #[]
  for (bit,index) in (ate.reverse.drop 1).zipIdx do
    let (next,line) := doubleStep r
    r := next
    lines := lines.push (index != 0,line)
    if bit != 0 then
      let (next,line) := addStep r (if bit == 1 then q else {q with y := neg q.y})
      r := next
      lines := lines.push (false,line)
  let q1 := twist q
  let q2 := twist q1
  let (next,line) := addStep r q1
  let (_,last) := addStep next {q2 with y := neg q2.y}
  return (lines.push (false,line) |>.push (false,last)).toList

private def limbs (n : Nat) : List Nat := (List.range 4).map fun i => n / (2^80)^i % 2^80
private def flatten (values : List C) : List Nat := values.flatMap fun value => limbs value.re ++ limbs value.im

def lines (coordinates : List (List Nat)) (anchors : List Nat) : Except String (List (List Nat)) := do
  let [a,b] := coordinates | throw "exactly two G2 anchors are required"
  let a ← readAnchor a
  let b ← readAnchor b
  unless compressed a ++ compressed b == anchors do throw "G2 coordinates differ from compressed anchors"
  let paired := (prepare a).zip (prepare b)
  return paired.map fun ((square,a),(_,b)) =>
    [if square then 1 else 0,1,1] ++ flatten a ++ flatten b

def validate (coordinates : List (List Nat)) (anchors : List Nat)
    (candidate : List (List Nat)) : Except String Unit := do
  let expected ← lines coordinates anchors
  unless candidate == expected do throw "prepared pairing lines differ from the authenticated anchors"

end Aiur.Library.Field.BN254.Pairing.Preparation
