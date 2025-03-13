# Ixon: Ix Object Notation

Ixon is a self-describing binary serialization format for the Ix platform.

The format has three primary components:

1. **Universes** correspond to type-system hierarchy levels in Ix's Lean
   frontend, although structured slightly differently.
2. **Expressions** which are anonymized dependently-typed lambda calculus terms,
   corresponding to expressions in the Lean Frontend. Ixon expressions are
   alpha-invariant, meaning `fun (x : A, y: B) => x` and `fun (a : A, b : B) => a` map 
   to the same ```λ :`3 :`4 =>`0`` Ixon expression (where `A` and
   `B` in this example are referenced using local```n`` DeBruijn indexes)
3. **Constants** are top-level content-addressed global declarations such as
   typed definitions or inductive datatypes

## Ixon.Univ

Ixon Universes are defined as follows

```lean4
inductive Univ where
  -- tag: 0x0, syntax: 1, concrete type or sort level values
  | const : UInt64 -> Univ
  -- tag: 0x1, syntax: `1, level variables bound by a top-level constant
  | var : UInt64 -> Univ
  -- tag: 0x2, syntax: (add `1 `2), the sum of two universes
  | add : UInt64 -> Univ -> Univ
  -- tag: 0x3, syntax: (max x y), the maximum of two universes
  | max : Univ -> Univ -> Univ
  -- tag: 0x4, syntax: (imax x y), the impredicative maximum of two universes
  | imax : Univ -> Univ -> Univ
```

This is structured slightly differently from Ix universes or Lean Levels:

```lean4
namespace Ix.IR
  inductive Univ
    | zero
    | succ : Univ → Univ
    | max  : Univ → Univ → Univ
    | imax : Univ → Univ → Univ
    | var  : Lean.Name → Nat → Univ
end Ix.IR
```

The Ixon converts the latter into a form more amenable for serialization by
collecting the unary zero/succ level representation into either simple 
`Univ.const` values or possibly complex `Univ.add` values.

### Serialization

Universes are serialized in the following way:

First, each constructor is assigned a tag value between 0x00 and 0x04. This tag
value only requires 3 bits of space, so instead of using an entire byte, we
left-shift the Universe tag into the upper 3 bits of a tag-byte:

```
0bTTTL_SSSS
```

where the `T` bits hold the tag value.

The `L` bit is called the `large-flag` and the `SSSS` bits are called the
"small-size" field, and can store various information depending on the Universe
variant defined by the tag value.

For the `Univ.const` constructor, the large-flag and the small-size field are
used to hold in a single byte small values. For example, the following tag-byte

```
0bTTTL_SSSS
0b0000_1111
```

represents `Univ.const 15`. Larger values than 15 are represented with

```
tag-byte   , 1 large-size byte = small-size + 1
0bTTTL_SSSS, LS0
0b0001_0000, 0b1111_1111
(Univ.const 255)

tag-byte   , 2 large-size bytes = small-size + 1
0bTTTL_SSSS, LS0          LS1
0b0001_0001, 0b1111_1111, 0b1111_1111
(Univ.const 65536)
...
```

If the large-flag is set, the small-size field is used to store the number of
bytes of an variable length large-size field (with an off-by-one optimization).

This approach is used for `Univ.const` and `Univ.var`. For `Univ.max` and
`Univ.imax`, the large-flag and small size field are unused, and the
serialization of the parameters are directly concatenated. These sub-objects are
called the *body* fields. For example, the
serialization of `Univ.max (Univ.const 0) (Univ.const 15)` is:

```
tag-byte     body1         body2
             (tag-byte)   (tag-byte)
0bTTTL_SSSS, 0bTTTL_SSSS, 0bTTTL_SSSS
0b1000_0000, 0b0000_0000, 0b0000_1111
```

The number of body fields is determined by the the tag value.

Finally, Univ.add combines both a large-size field and a body field:

```
(Univ.add 15 (Univ.const 0))
tag-byte     body1
             (tag-byte)
0bTTTL_SSSS, 0bTTTL_SSSS
0b1000_1111, 0b0000_0000

(Univ.add 16 (Univ.const 0))

tag-byte     large-size   body1
0bTTTL_SSSS, LS0,       , 0bTTTL_SSSS
0b1001_0000, 0b0001_0000  0b0000_0000
```

## Ixon.Expr

Ixon expressions are defined as follows:

```lean4
-- tag-byte: 0xTTTT_LXXX
inductive Expr where
  -- tag: 0x0, syntax: ^1
  | vari (idx: UInt64) : Expr
  -- tag: 0x1, syntax: {max (add 1 2) (var 1)}
  | sort (univ: Univ) : Expr
  -- tag: 0x2, syntax #dead_beef_cafe_babe.{u1, u2, ... }
  | cnst (adr: Address) (lvls: List Univ) : Expr
  -- tag: 0x3, syntax: #1.{u1, u2, u3}
  | rec_ (idx: UInt64) (lvls: List Univ) : Expr
  -- tag: 0x4, syntax:  (f x y z)
  | apps (func: Expr) (arg: Expr) (args: List Expr) : Expr
  -- tag: 0x5, syntax: (λ A B C => body)
  | lams (types: List Expr) (body: Expr) : Expr
  -- tag: 0x6, syntax: (∀ A B C -> body)
  | alls (types: List Expr) (body: Expr) : Expr
  -- tag: 0x7, syntax: (let d : A in b)
  | let_ (nonDep: Bool) (type: Expr) (defn: Expr) (body: Expr) : Expr
  -- tag: 0x8, syntax: x.1
  | proj : UInt64 -> Expr -> Expr
  -- tag: 0x9, syntax: "foobar"
  | strl (lit: String) : Expr
  -- tag: 0xA, syntax: 0xdead_beef
  | natl (lit: Nat): Expr
-- virtual expression: array: 0xB
-- virtual expression: const: 0xC
```

This is largely similar to the Ix.Expr definition, which can be seen as a
content-addressable variation of Lean4 expressions once all metavariables have
been elaborated.

```lean4
namespace Ix.IR
  inductive Expr
    | var   : Nat → List Univ → Expr
    | sort  : Univ → Expr
    | const : Lean.Name → Address → Address → List Univ → Expr
    | app   : Expr → Expr → Expr
    | lam   : Expr → Expr → Expr
    | pi    : Expr → Expr → Expr
    | letE  : Bool -> Expr → Expr → Expr → Expr
    | lit   : Lean.Literal → Expr
    | proj  : Nat → Expr → Expr
end Ix.IR
```

The primary differences between these types are:

1. Non-computationally relevante metadata like Lean.Name, or BinderInfo are
   removed (TODO: update Ix.IR def once metadata is implemented)
2. Repeated lambda and forall binders are collected, so that e.g. `fun x y z => a` 
can be represented with a single `Expr.lam`.
3. Repeated application of arguments are collected into telescopes, so that e.g.
`(f a b c)` can be expressed with a single `Expr.app`
4. String and number literals are lifted into the Expr inductive

Expr has two reserved "virtual" constructors, which are used in order
to create the Ixon.constants, and will be explained in the next section.

### Serialization

Expression serialization is structurally similar to that for Universes.
Expression tags range from 0x0 to 0xF (with 0xB, 0xC used for Const, and 0xD
through 0xF reserved for future use), so they require 4 bits, rather than 3 for
universes. Otherwise, expressions have the same tag-byte structure as universes,
with a large-flag and a small-size field:

```
0xTTTT_LSSS
```

We will now work through serializations for each Expr constructor in detail:

#### Expr.var

```
-- tag: 0x0, syntax: ^1
| vari (idx: UInt64) : Expr
```

Variables are serialized similarly to Univ.var universe variables. The small or
large size field holds the index:

```
0xTTTT_LSSS
(.var 0)
0x0000_0000

(.var 7)
0x0000_0111

(.var 8)
0x0000_1000, 0x0000_1000

(.var 256)
0x0000_1001, 0x0000_0000, 0x0000_0001
```
The index, when large, is stored in little-endian format.

#### Expr.sort

```
-- tag: 0x1, syntax: {max (add 1 2) (var 1)}
| sort (univ: Univ) : Expr
```

Sorts are serialized identically to the universe serialization described above, 
with a single byte prefix. The size fields are not used.

```
(Expr.sort (Univ.var 0))
0xTTTT_LSSS 0bTTTL_SSSS
0x0001_0000 0b0000_0000
```

#### Expr.cnst

```
-- tag: 0x2, syntax #dead_beef_cafe_babe.{u1, u2, ... }
| cnst (adr: Address) (lvls: List Univ) : Expr
```

The const reference serialization uses the size fields to store the number of
universe arguments, which follow the fixed 256-bit/32-byte Address serialization 
as body fields:

```
(Expr.cnst <adr> [Univ.var 0,Univ.var 1, Univ.var 2])
0xTTTT_LSSS  32 Address bytes   body1        body2        body3
0x0002_0011, ...,             , 0b0000_0000, 0b0000_0001, 0b0000_0002
```

#### Expr.rec_

```
-- tag: 0x3, syntax: #1.{u1, u2, u3}
| rec_ (idx: UInt64) (lvls: List Univ) : Expr
```
Recursive references serialize like a combination of Expr.var and Expr.cnst. The
size fields store the index:

```
(.rec 0 [.var 0, .var 1])
0xTTTT_LSSS, body1,       body2
0x0011_0000, 0b0000_0000, 0b0000_0001

(.rec 8 [.var 0, .var 1])
0xTTTT_LSSS, L0,          body1,       body2
0x0011_1000, 0b0000_1000, 0b0000_0000, 0b0000_0001
```

#### Expr.apps

Applications serialize by storing the number of extra arguments in the size
field. There is a body field for the function and first argument, so total
number of body fields is the number of extra arguments plus 2.
```
(f x y z)
(.app (.vari 0) (.vari 1) [.vari 2, .vari 3])
0xTTTT_LSSS, body1,       body2,       body3,       body4
0x0100_0010, 0b0000_0000, 0b0000_0001, 0b0000_0010, 0b0000_0011
```

#### Expr.lams

Lambdas store the number of binders in the size fields, and then the binder
types in a corresponding number of body fields, plus an additional body field
for the function body.

```
(λ :A :B :C => b)
(.lams [.vari 0, .vari 1, .vari 2] .vari 3])
0xTTTT_LSSS, body1,       body2,       body3,       body4
0x0101_0011, 0b0000_0000, 0b0000_0001, 0b0000_0010, 0b0000_0011
```

#### Expr.alls

Foralls are identical to lambdas with a different tag:
```
(∀ :A :B :C => b)
(.alls [.vari 0, .vari 1, .vari 2] .vari 3])
0xTTTT_LSSS, body1,       body2,       body3,       body4
0x0110_0011, 0b0000_0000, 0b0000_0001, 0b0000_0010, 0b0000_0011
```

#### Expr.let_

Let bindings do not use the size fields and have 3 body fields:

```
(.let_ .vari 0, .vari 1, .vari 2)
0xTTTT_LSSS, body1,       body2,       body3
0x0111_0000, 0b0000_0000, 0b0000_0001, 0b0000_0011
```

#### Expr.proj

Projections store their index in the size fields and have 1 body field:

```
(.proj 0 .vari 0)
0xTTTT_LSSS, body1
0x1000_0000, 0x0000_0000
```

#### Expr.strl

String literals store the length of the utf8 text in bytes in the size fields:

```
(.strl "foobar")
0xTTTT_LSSS, body
0x1001_0100, 0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72
```

#### Expr.natl

Number literals store the length of the natural number's byte representation according to
the following algorithm:

```lean4
def natToBytesLE (x: Nat) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go x x)
  where
    go : Nat -> Nat -> List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x => Nat.toUInt8 x:: go f (x / 256)

def natFromBytesLE (xs: Array UInt8) : Nat :=
  xs.toList.enum.foldl (fun acc (i, b) => acc + (UInt8.toNat b) * 256 ^ i) 0
```

```
(.natl 0)
0xTTTT_LSSS, body
0x1010_0001, 0x0
```

## Ixon.Const

Ixon constants are defined as follows:

```lean4
inductive Const where
  -- 0xC0
  | axio : Axiom -> Const
  -- 0xC1
  | theo : Theorem -> Const
  -- 0xC2
  | opaq : Opaque -> Const
  -- 0xC3
  | defn : Definition -> Const
  -- 0xC4
  | quot : Quotient -> Const
  -- 0xC5
  | ctor : Constructor -> Const
  -- 0xC6
  | recr : Recursor -> Const
  -- 0xC7
  | indc : Inductive -> Const
  -- 0xC8
  | ctorProj : ConstructorProj -> Const
  -- 0xC9
  | recrProj : RecursorProj -> Const
  -- 0xCA
  | indcProj : InductiveProj -> Const
  -- 0xCB
  | defnProj : DefinitionProj -> Const
  -- 0xCC
  | mutDef : List Definition -> Const
  -- 0xCD
  | mutInd : List Inductive -> Const
  -- 0xCE
  | meta   : Metadata -> Const
  deriving BEq, Repr, Inhabited
```

The internal details of this inductive are quite detailed, but
corresponds to top-level declarations in the Lean4 frontend, rendered namelessly
content-addressable.

### Serialization

We will first describe the "virtual expression" constructors from the previous
section, then go through each Const variant and describe its serialization:

#### Arrays

The expression tag 0xB signifies an array of homogoneous body fields, and stores
the number of such fields in the expression size fields. The format of these
body fields must be known from context

#### Consts

The expression tag 0xC signnifies a constant. The large flag and small size
field are combined to store a second 4-bit tag indicating the const variant.
This is done to enable Ixon.Const and Ixon.Expr to live in the same "namespace"
of bytes, and remove possible ambiguities between them.

#### Const.axio

```lean4
-- tag: 0xC0
| axio : Axiom -> Const

structure Axiom where
  lvls  : Nat
  type  : Expr
```

Axioms serialize as a tag-byte and two Expr body fields:

```
tag-byte, body1,            body2
0xC0,     <Expr.natl lvls>, <type : Expr>
```

#### Const.theo

```lean4
-- tag: 0xC1
| theo : Theorem -> Const

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
```

Theorems serialize as a tag-byte and three Expr body fields:

```
tag-byte, body1,            body2,         body3
0xC1,     <Expr.natl lvls>, <type : Expr>, <value: Expr>
```

#### Const.opaq

```lean4
-- tag: 0xC2
| opaq : Opaque -> Const

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
```

Opaques are identical to theorems, except with tag 0xC2

#### Const.defn

```lean4
-- 0xC3
| defn : Definition -> Const

structure Definition where
  lvls  : Nat
  type  : Expr
  value : Expr
  part  : Bool
  deriving BEq, Repr
```

Definitions serialize as a tag byte, two Expr fields and a Bool field

```
tag-byte, body1,            body2,         body3,         body4
0xC3,     <Expr.natl lvls>, <type : Expr>, <value: Expr>, <part: Bool>
```

#### Const.quot

```lean4
-- 0xC4
| quot : Quotient -> Const

structure Quotient where
  lvls : Nat
  type : Expr
  kind : Lean.QuotKind
  deriving BEq, Repr
```

Quotients serialize as a tag-byte, an Expr field and a QuotKind field (a single
byte ranging from 0 to 3 according to the variant)

```
tag-byte, body1,            body2,         body3
0xC4,     <Expr.natl lvls>, <type : Expr>, <kind: QuotKind>
```

#### Const.ctor

TODO

#### Const.recr

TODO

#### Const.indc

TODO

#### Const.ctorProj

TODO

#### Const.recrProj

TODO

#### Const.indcProj

TODO

#### Const.defnProj

TODO

#### Const.mutDef

TODO

#### Const.mutInd

TODO

#### Const.meta

TODO
