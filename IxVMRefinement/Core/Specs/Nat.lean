import IxVMRefinement.Core.Specs.Common

/-! # Specs of the `Nat` and `String` natives: `KernelNatPrim`, `KernelKlimbs`, the division hints

A `Nat` literal is a list of little-endian 64-bit limbs (`KernelTypes::KLimbs`), read as its
value (`RepLimbs`); a limb list may carry trailing zero limbs, so the limb functions are stated on
values, and a result is claimed canonical (`RepLimbsC`, no trailing zero limb) only where the code
normalizes it. The native reductions target the kernel's rules: `Red.natLit`, `Red.natZeroLit`,
`Red.strLit`, `Red.natSucc`, `Red.natOp` (with `natOpResult`, the `Nat.pow` cap included),
`Red.natAddSucc`, `Red.natAddZero`, and the congruences `Red.appArg`/`appFn` for the stuck forms
the circuit keeps (`mk_nat_offset_stuck`, `mk_nat_binop_stuck`).

**Role facts.** The dispatchers fire on an operation's role (`natPrimOp`, the family-`1` column of
`KernelRoleSpec::role_prim_family`); the rules' stored-shape guards come from `EnvFacts`
(`natLit`, `strLit`, `natOps`, `natAdd`) once the roles they name are bound. A role the circuit
reads (`role_is`, `role_addr`, `role_used_implicitly`) is bound; the roles of its block and its
dependencies are then bound too (`RoleTable.check`, through `EnvFacts.tableWf`), and the key of a
bound address is its role (`keyOf`, no address bound twice). A proof of a spec below reads those
facts from `CoreFacts`; the specs themselves state no environment hypothesis. -/

namespace IxVM.Refinement.Core.Specs.Nat

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-! ## Vocabulary -/

/-- **A canonical limb list**: `RepLimbs` with no trailing zero limb (the empty list is `0`), so
the list is a function of its value. -/
def RepLimbsC (h : Heap F) (n : Nat) (p : SourceValue F) : Prop :=
  ∃ limbs, RepList limbListEnum RepU64 h limbs p ∧ limbsVal limbs = n ∧ limbs.getLast? ≠ some 0

/-- **The `Nat` primitive a role is**: its operation code in `KernelRoleSpec::role_prim_family`
(family `1`), by role. -/
def natPrimOp : Ix.Kernel.Role → Option Nat
  | .natSucc => some 1
  | .natPred => some 2
  | .natAdd => some 3
  | .natSub => some 4
  | .natMul => some 5
  | .natDiv => some 6
  | .natMod => some 7
  | .natGcd => some 8
  | .natPow => some 9
  | .natLand => some 10
  | .natLor => some 11
  | .natXor => some 12
  | .natShiftLeft => some 13
  | .natShiftRight => some 14
  | .natBeq => some 15
  | .natBle => some 16
  | _ => none

/-- **The address `a` is bound to the `Nat` operation with code `o`** by the run's table (what
`KernelWhnf::prim_family` reads before it dispatches). -/
def NatOpAt (c : Ctx) (a : Bytes.Address) (o : Nat) : Prop :=
  ∃ r, natPrimOp r = some o ∧ c.t.addressOf? r = some (ixAddr a)

/-- **The character list a string literal expands to**, over the expansion's `List.nil Char`
(`N`), `List.cons Char` (`C`) and `Char.ofNat` (`K`): `strLitToConstructor`'s fold. -/
def charList (N C K : KExpr) : List Char → KExpr
  | [] => N
  | ch :: cs => .app (.app C (.app K (.lit (.natVal ch.toNat)))) (charList N C K cs)

/-- The `Nat` literal of a value. -/
abbrev natLit (n : Nat) : KExpr := .lit (.natVal n)

abbrev mkAppN : KExpr → List KExpr → KExpr := Ix.Kernel.Expr.mkAppN

/-! ## `KernelKlimbs` -/

/-- `klimbs_succ(n)`: the successor, `n + 1`. -/
def klimbs_succ : SpecFn := fun c args h r h' calls =>
  ∀ a, args = [a] → Good c calls → ∀ n, RepLimbs h n a → RepLimbs h' (n + 1) r

/-- `klimbs_add_carry(a, b, carry)` with a carry `0` or `1`: `a + b + carry` (the callers pass
`0`, and recurse with the limbs' carry, which is at most `1`). -/
def klimbs_add_carry : SpecFn := fun c args h r h' calls =>
  ∀ a b (k : F), args = [a, b, .field k] → Good c calls → (ZMod.val k) ≤ 1 →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (n + m + (ZMod.val k)) r

/-- `klimbs_add(a, b)`: `a + b`. -/
def klimbs_add : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (n + m) r

/-- `klimbs_sub_borrow(a, b, borrow)` with a borrow `0` or `1`: the borrow out is `0` exactly when
`b + borrow ≤ a`, and then the limbs are `a - b - borrow`; at borrow out `1` the limbs are not
claimed. -/
def klimbs_sub_borrow : SpecFn := fun c args h r h' calls =>
  ∀ a b (β : F), args = [a, b, .field β] → Good c calls → (ZMod.val β) ≤ 1 →
    ∀ n m, RepLimbs h n a → RepLimbs h m b →
      ∃ (res : SourceValue F) (bf : F), r = .tuple [res, .field bf] ∧
        ((bf = 0 ∧ m + (ZMod.val β) ≤ n ∧ RepLimbs h' (n - m - (ZMod.val β)) res) ∨
          (bf = 1 ∧ n < m + (ZMod.val β)))

/-- `klimbs_normalize(n)`: the same value, canonical. -/
def klimbs_normalize : SpecFn := fun c args h r h' calls =>
  ∀ a, args = [a] → Good c calls → ∀ n, RepLimbs h n a → RepLimbsC h' n r

/-- `klimbs_sub(a, b)`: truncated subtraction `a - b` (`Nat`'s), canonical. -/
def klimbs_sub : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbsC h' (n - m) r

/-- `klimbs_le(a, b)`: `1` exactly when `a ≤ b` (exact both ways). -/
def klimbs_le : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → r = .field (if n ≤ m then 1 else 0)

/-- `klimbs_dec(a)`: truncated predecessor `a - 1`, canonical. -/
def klimbs_dec : SpecFn := fun c args h r h' calls =>
  ∀ a, args = [a] → Good c calls → ∀ n, RepLimbs h n a → RepLimbsC h' (n - 1) r

/-- `divmod_256(x, q)` at `x < 2^32` (the range of `UInt32::less_than_fields`, which it tests):
`(x mod 256, q + x div 256)`. -/
def divmod_256 : SpecFn := fun c args h r h' calls =>
  ∀ (x q : F), args = [.field x, .field q] → Good c calls → (ZMod.val x) < 2 ^ 32 →
    r = .tuple [.field (((ZMod.val x) % 256 : Nat) : F), .field (q + (((ZMod.val x) / 256 : Nat) : F))] ∧ h' = h

/-- `klimbs_mul(a, b)`: `a * b` (not canonical: a zero factor can leave zero limbs). -/
def klimbs_mul : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (n * m) r

/-- `klimbs_mul_outer(a, b, acc, shift)`: `acc + a * b * 2^(64 * shift)`. -/
def klimbs_mul_outer : SpecFn := fun c args h r h' calls =>
  ∀ a b acc (s : F), args = [a, b, acc, .field s] → Good c calls →
    ∀ n m k, RepLimbs h n a → RepLimbs h m b → RepLimbs h k acc →
      RepLimbs h' (k + n * m * 2 ^ (64 * (ZMod.val s))) r

/-- `klimbs_mul_single(a_limb, b, carry)`: `a_limb * b + carry`, for 64-bit `a_limb` and
`carry`. -/
def klimbs_mul_single : SpecFn := fun c args h r h' calls =>
  ∀ al b cr, args = [al, b, cr] → Good c calls →
    ∀ (x y : UInt64) m, RepU64 h x al → RepU64 h y cr → RepLimbs h m b →
      RepLimbs h' (x.toNat * m + y.toNat) r

/-- `klimbs_shl_limbs(x, shift)`: `x * 2^(64 * shift)` (`shift` zero limbs prepended). -/
def klimbs_shl_limbs : SpecFn := fun c args h r h' calls =>
  ∀ a (s : F), args = [a, .field s] → Good c calls →
    ∀ n, RepLimbs h n a → RepLimbs h' (n * 2 ^ (64 * (ZMod.val s))) r

/-- `klimbs_is_zero(x)`: `1` exactly when the value is `0` (exact both ways). -/
def klimbs_is_zero : SpecFn := fun c args h r h' calls =>
  ∀ a, args = [a] → Good c calls → ∀ n, RepLimbs h n a → r = .field (if n = 0 then 1 else 0)

/-- `klimbs_div_mod(a, b)`: `(a / b, a % b)` (`Nat`'s, so `(0, a)` at `b = 0`), both canonical.
The hint (`IxVMCompat::ordinary_div_mod`) is checked: `q * b + r = a`, `q = 0` at `b = 0`, and
`r < b` otherwise; so the claim does not rest on the hint. -/
def klimbs_div_mod : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b →
      ∃ q rr, r = .tuple [q, rr] ∧ RepLimbsC h' (n / m) q ∧ RepLimbsC h' (n % m) rr

/-- `klimbs_div(a, b)`: `a / b`, canonical. -/
def klimbs_div : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbsC h' (n / m) r

/-- `klimbs_mod(a, b)`: `a % b`, canonical. -/
def klimbs_mod : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbsC h' (n % m) r

/-- `klimbs_gcd(a, b)`: `Nat.gcd a b` (not canonical: at `b = 0` it returns `a` as given). -/
def klimbs_gcd : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.gcd n m) r

/-- `klimbs_pow(base, exp)`: `base ^ exp`, at every exponent (square and multiply). -/
def klimbs_pow : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (n ^ m) r

/-- `klimbs_land(a, b)`: `Nat.land a b` (limbwise, truncated to the shorter list). -/
def klimbs_land : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.land n m) r

/-- `klimbs_lor(a, b)`: `Nat.lor a b`. -/
def klimbs_lor : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.lor n m) r

/-- `klimbs_xor_op(a, b)`: `Nat.xor a b`. -/
def klimbs_xor_op : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.xor n m) r

/-- `klimbs_shl(a, n)`: `Nat.shiftLeft a n` (`a * 2^n`). -/
def klimbs_shl : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.shiftLeft n m) r

/-- `klimbs_shr(a, n)`: `Nat.shiftRight a n` (`a / 2^n`). -/
def klimbs_shr : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → RepLimbs h' (Nat.shiftRight n m) r

/-! ## The division hints (`IxVMCompat`) -/

/-- `IxVMCompat::divide_grow(a, b)` at a nonzero divisor: `(a / b, a % b)` (doubling the
divisor; no claim at `b = 0`, where it does not terminate). Values only. -/
def divide_grow : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → 0 < m →
      ∃ q rr, r = .tuple [q, rr] ∧ RepLimbs h' (n / m) q ∧ RepLimbs h' (n % m) rr

/-- `IxVMCompat::ordinary_div_mod(a, b)`: `(a / b, a % b)` (`Nat`'s, `(0, a)` at `b = 0`).
Values only. `klimbs_div_mod` checks the hint, so its own spec does not need this one. -/
def ordinary_div_mod : SpecFn := fun c args h r h' calls =>
  ∀ a b, args = [a, b] → Good c calls →
    ∀ n m, RepLimbs h n a → RepLimbs h m b →
      ∃ q rr, r = .tuple [q, rr] ∧ RepLimbs h' (n / m) q ∧ RepLimbs h' (n % m) rr

/-! ## `KernelNatPrim`: construction -/

/-- `mk_bool(rc, g)`: the closed `Bool.false` at `g = 0`, else `Bool.true` (the roles' keys at
an empty level list: `natOpResult`'s `Bool` results). -/
def mk_bool : SpecFn := fun c args h r h' calls =>
  ∀ rc (g : F), args = [rc, .field g] → Good c calls → c.rc h rc →
    c.tmc h' (.const (if g = 0 then Ix.Kernel.boolFalseName else Ix.Kernel.boolTrueName) []) r

/-- `mk_nat_lit(n)`: the closed literal of the limbs' value. -/
def mk_nat_lit : SpecFn := fun c args h r h' calls =>
  ∀ a, args = [a] → Good c calls → ∀ n, RepLimbs h n a → c.tmc h' (natLit n) r

/-- `np_apply_spine(head, spine)`: the application `mkAppN head spine`. -/
def np_apply_spine : SpecFn := fun c args h r h' calls =>
  ∀ hd sp, args = [hd, sp] → Good c calls →
    ∀ d Γ H As, c.tm d Γ h H hd → c.tml d Γ h As sp → c.tm d Γ h' (mkAppN H As) r

/-- `lvls_empty(lvls)`: `1` exactly when the level list is empty (exact both ways). -/
def lvls_empty : SpecFn := fun c args h r h' calls =>
  ∀ lp, args = [lp] → Good c calls →
    ∀ us, LvListRep h us lp → r = .field (if us = [] then 1 else 0) ∧ h' = h

/-- `split_u32(x)` at `x < 2^32`: its four base-256 digits, least significant first. -/
def split_u32 : SpecFn := fun c args h r h' calls =>
  ∀ (x : F), args = [.field x] → Good c calls → (ZMod.val x) < 2 ^ 32 →
    r = .tuple [.field (((ZMod.val x) % 256 : Nat) : F), .field (((ZMod.val x) / 256 % 256 : Nat) : F),
      .field (((ZMod.val x) / 65536 % 256 : Nat) : F), .field (((ZMod.val x) / 16777216 % 256 : Nat) : F)] ∧
      h' = h

/-- `klimbs_from_g(x)`: the canonical limbs of `x`'s value. The byte split is range-checked and
recomposed (`constrain_eq!`), so a derivation exists only at `x < 2^32`, which the claim
records. -/
def klimbs_from_g : SpecFn := fun c args h r h' calls =>
  ∀ (x : F), args = [.field x] → Good c calls → (ZMod.val x) < 2 ^ 32 ∧ RepLimbsC h' (ZMod.val x) r

/-- `mk_nat_offset_stuck(rc, base_w, n, post)`: tag `1`, and `base + n` in the offset rules'
spelling (`natAddLit`: the base itself at `n = 0`, else `Nat.add base (lit n)`), applied to
`post`. The `Nat.add` head is the role's key at an empty level list. -/
def mk_nat_offset_stuck : SpecFn := fun c args h r h' calls =>
  ∀ rc b np post, args = [rc, b, np, post] → Good c calls → c.rc h rc →
    ∀ d Γ B n Ps, c.tm d Γ h B b → RepLimbs h n np → c.tml d Γ h Ps post →
      ∃ x, r = .tuple [.field 1, x] ∧
        c.tm d Γ h' (mkAppN (Ix.Kernel.Rules.natAddLit B n) Ps) x

/-- `mk_nat_binop_stuck(op_addr, base_w, n, post)`: the operation applied to the base and the
literal, applied to `post`: `mkAppN (op base (lit n)) post`, the operation at its address's key
and an empty level list. -/
def mk_nat_binop_stuck : SpecFn := fun c args h r h' calls =>
  ∀ ap b np post, args = [ap, b, np, post] → Good c calls →
    ∀ a d Γ B n Ps, RepAddr h a ap → c.tm d Γ h B b → RepLimbs h n np → c.tml d Γ h Ps post →
      c.tm d Γ h' (mkAppN (.app (.app (.const (c.κ (ixAddr a)) []) B) (natLit n)) Ps) r

/-- `build_succ_offset(rc, base, lit)`: `Nat.succ (base + (lit - 1))` in the offset rules'
spelling (`natAddLit`), the right side of `Red.natAddSucc`. At `lit = 0` it builds
`Nat.succ base` (truncated predecessor). -/
def build_succ_offset : SpecFn := fun c args h r h' calls =>
  ∀ rc b lp, args = [rc, b, lp] → Good c calls → c.rc h rc →
    ∀ d Γ B n, c.tm d Γ h B b → RepLimbs h n lp →
      c.tm d Γ h' (.app (.const Ix.Kernel.natSuccName []) (Ix.Kernel.Rules.natAddLit B (n - 1))) r

/-! ## `KernelNatPrim`: UTF-8 and string literals -/

/-- `utf8_cont(b)`: a continuation byte's payload. A derivation exists only at
`128 ≤ b < 192`. -/
def utf8_cont : SpecFn := fun c args h r h' calls =>
  ∀ bp, args = [bp] → Good c calls → ∀ b : UInt8, RepU8 h b bp →
    128 ≤ b.toNat ∧ b.toNat < 192 ∧ r = .field ((b.toNat - 128 : Nat) : F) ∧ h' = h

/-- `utf8_decode_one(b0, rest)`: one UTF-8 scalar value off the front. A derivation exists only
on a valid (shortest-form, non-surrogate, at most `U+10FFFF`) encoding, so the bytes start with
the encoding (`String.utf8EncodeChar`) of a character whose code point is the result, and the rest
is returned. -/
def utf8_decode_one : SpecFn := fun c args h r h' calls =>
  ∀ bp rest, args = [bp, rest] → Good c calls → ∀ (b : UInt8) bs, RepU8 h b bp → RepBytes h bs rest →
    ∃ (ch : Char) (bs' : List UInt8) (rem : SourceValue F), b :: bs = String.utf8EncodeChar ch ++ bs' ∧
      r = .tuple [.field (ch.toNat : F), rem] ∧ RepBytes h' bs' rem

/-- `utf8_validate(bs)`: the bytes are a valid UTF-8 encoding of some characters (what
`Convert` reads off a string literal's blob; the term seam's `StrBytes` needs the string). -/
def utf8_validate : SpecFn := fun c args h r h' calls =>
  ∀ bp, args = [bp] → Good c calls → ∀ bs, RepBytes h bs bp →
    ∃ cs : List Char, cs.flatMap String.utf8EncodeChar = bs

/-- `build_char_list(bs, nil_app, cons_partial, con_const)`: the character list of the string
whose UTF-8 encoding the bytes are, over the given `List.nil Char`, `List.cons Char` and
`Char.ofNat` (`charList`). Stated for the characters the bytes encode (the caller knows them from
the literal: `StrBytes`). -/
def build_char_list : SpecFn := fun c args h r h' calls =>
  ∀ bp n cp k, args = [bp, n, cp, k] → Good c calls →
    ∀ bs, RepBytes h bs bp → ∀ cs : List Char, cs.flatMap String.utf8EncodeChar = bs →
      ∀ d Γ N C K, c.tm d Γ h N n → c.tm d Γ h C cp → c.tm d Γ h K k →
        c.tm d Γ h' (charList N C K cs) r

/-- `str_lit_to_ctor(rc, bs)`: the closed constructor form of the string literal
(`strLitToConstructor s`, the right side of `Red.strLit`), for the string `s` the bytes encode.
The constants are the roles' (`role_used_implicitly`: bound, and checked), at the level `0`
where `strLitToConstructor` writes one. -/
def str_lit_to_ctor : SpecFn := fun c args h r h' calls =>
  ∀ rc bp, args = [rc, bp] → Good c calls → c.rc h rc →
    ∀ bs s, RepBytes h bs bp → StrBytes s bs → c.tmc h' (Ix.Kernel.strLitToConstructor s) r

/-- `str_lit_delta_step(rc, expanded, types)` on a `String.ofList` application (the form
`str_lit_to_ctor` builds, its only callers' input): a reduct, by `Red.delta` at the role's
definition (level-free: `strLitSupported`'s `stringOfListTyOk`, through `EnvFacts.strLit`),
`Red.betaGate` at a `never` binder (`level_is_not_zero`), and `whnf_nd`'s `Red`. -/
def str_lit_delta_step : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ L, c.tm d Γ h (.app (.const Ix.Kernel.stringOfListName []) L) e →
      ∃ E', c.tm d Γ h' E' r ∧ Red c.env d (.app (.const Ix.Kernel.stringOfListName []) L) E'

/-- `str_lit_to_ctor_app_or_self(rc, e, types)`: a reduct (`Red.strLit` then
`str_lit_delta_step`, or `Red.refl` on any other term). -/
def str_lit_to_ctor_app_or_self : SpecFn := fun c args h r h' calls =>
  ∀ rc e types, args = [rc, e, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e →
      ∃ E', c.tm d Γ h' E' r ∧ Red c.env d E E'

/-! ## `KernelNatPrim`: reading and dispatching -/

/-- `try_extract_nat(rc, e)`: tag `1` reads a `Nat` value off a literal, `Nat.zero`, or
`Nat.succ x` with `x` readable, each at an empty level list: the term reduces to that literal
(`Red.refl`, `Red.natZeroLit`, `Red.natSucc`; `natLitSupported` from `EnvFacts.natLit`, the
`Nat` block being bound once `role_is` finds `Nat.zero` or `Nat.succ`). Nothing at tag `0`. -/
def try_extract_nat : SpecFn := fun c args h r h' calls =>
  ∀ rc e, args = [rc, e] → Good c calls → c.rc h rc →
    ∀ d Γ E, c.tm d Γ h E e → ∀ x, r = .tuple [.field 1, x] →
      ∃ n, RepLimbs h' n x ∧ Red c.env d E (natLit n)

/-- `try_extract_nat_app(rc, f, a)`: tag `1` at `f = Nat.succ` (empty level list) and `a`
readable: the application reduces to the successor literal (`Red.natSucc`). -/
def try_extract_nat_app : SpecFn := fun c args h r h' calls =>
  ∀ rc f a, args = [rc, f, a] → Good c calls → c.rc h rc →
    ∀ d Γ Fh A, c.tm d Γ h Fh f → c.tm d Γ h A a → ∀ x, r = .tuple [.field 1, x] →
      ∃ n, RepLimbs h' n x ∧ Red c.env d (.app Fh A) (natLit n)

/-- `try_nat_binop_addr(rc, op, a, b)`: tag `1` gives the closed term `natOpResult` gives for the
operation with code `op` on the two values (a canonical literal, or a `Bool` constructor;
`Nat.pow` only up to the exponent cap `2^24`, as `natOpResult`). Nothing at tag `0` (an
operation it does not fold, `succ` and `pred` among them). -/
def try_nat_binop_addr : SpecFn := fun c args h r h' calls =>
  ∀ rc (o : F) a b, args = [rc, .field o, a, b] → Good c calls → c.rc h rc →
    ∀ n m, RepLimbs h n a → RepLimbs h m b → ∀ x, r = .tuple [.field 1, x] →
      ∀ role, natPrimOp role = some (ZMod.val o) →
        ∃ E, Ix.Kernel.natOpResult (.role role) n m = some E ∧ c.tmc h' E x

/-- `try_match_nat_add(rc, head, args)`: tag `1` at a `Nat.add` head (any level list) applied to
exactly two arguments, the second a `Nat` literal: the base and the literal's limbs. -/
def try_match_nat_add : SpecFn := fun c args h r h' calls =>
  ∀ rc hd sp, args = [rc, hd, sp] → Good c calls → c.rc h rc →
    ∀ d Γ H As, c.tm d Γ h H hd → c.tml d Γ h As sp → ∀ b l, r = .tuple [.field 1, b, l] →
      ∃ us B n, H = .const Ix.Kernel.natAddName us ∧ As = [B, natLit n] ∧
        c.tm d Γ h' B b ∧ RepLimbs h' n l

/-- `cleanup_nat_offset_major(rc, e)`: a reduct: `Nat.add b (lit (k + 1))` becomes
`Nat.succ (b + k)` (`Red.natAddSucc`; `natLitSupported` and `natAddTyOk` from `EnvFacts`), any
other term itself. -/
def cleanup_nat_offset_major : SpecFn := fun c args h r h' calls =>
  ∀ rc e, args = [rc, e] → Good c calls → c.rc h rc →
    ∀ d Γ E, c.tm d Γ h E e → ∃ E', c.tm d Γ h' E' r ∧ Red c.env d E E'

/-- `try_nat_offset_dispatch(rc, head_addr, op, a0_w, nb, spine)`, at a head bound to the
operation `op`, a spine `A₀ :: A₁ :: post` whose first argument `a0_w` represents and whose second
reduces to the literal `nb`: a nonzero tag gives a reduct of the applied operation, its stuck
form (`Nat.add`: `A₀ + nb` by `Red.natAddZero` at `0`, else `Red.appArg`; `div`/`mod` by
`Red.appArg`). -/
def try_nat_offset_dispatch : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (o : F) a0 nb sp, args = [rc, ap, .field o, a0, nb, sp] → Good c calls → c.rc h rc →
    ∀ a, RepAddr h a ap → NatOpAt c a (ZMod.val o) →
      ∀ d Γ A₀ A₁ Ps n, c.tml d Γ h (A₀ :: A₁ :: Ps) sp → c.tm d Γ h A₀ a0 → RepLimbs h n nb →
        Red c.env d A₁ (natLit n) →
        ∀ (t : F) x, r = .tuple [.field t, x] → t ≠ 0 →
          ∃ E', c.tm d Γ h' E' x ∧
            Red c.env d (mkAppN (.const (c.κ (ixAddr a)) []) (A₀ :: A₁ :: Ps)) E'

/-- `try_nat_binop_dispatch(rc, head_addr, op, spine, spine_len)`, at a head bound to the
operation `op`: a nonzero tag gives a reduct of the operation applied (at an empty level list)
to the spine: `Red.natOp` on two readable arguments, or the offset dispatch's stuck form. -/
def try_nat_binop_dispatch : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (o : F) sp sl, args = [rc, ap, .field o, sp, sl] → Good c calls → c.rc h rc →
    ∀ a, RepAddr h a ap → NatOpAt c a (ZMod.val o) →
      ∀ d Γ As, c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → t ≠ 0 →
          ∃ E', c.tm d Γ h' E' x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) []) As) E'

/-- `try_nat_dispatch(rc, head_addr, op, spine, types)` (the spine already head-normalized by its
caller), at a head bound to the operation `op`: a nonzero tag gives a reduct of the operation
applied (at an empty level list) to the spine (`Red.natSucc` for `Nat.succ`; the binary
dispatch otherwise; `Nat.pred` is not native). -/
def try_nat_dispatch : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (o : F) sp types, args = [rc, ap, .field o, sp, types] → Good c calls → c.rc h rc →
    ∀ a, RepAddr h a ap → NatOpAt c a (ZMod.val o) →
      ∀ d Γ, c.types Γ h d types → ∀ As, c.tml d Γ h As sp →
        ∀ (t : F) x, r = .tuple [.field t, x] → t ≠ 0 →
          ∃ E', c.tm d Γ h' E' x ∧ Red c.env d (mkAppN (.const (c.κ (ixAddr a)) []) As) E'

/-! ## The family -/

/-- The functions of the family. -/
inductive Fn where
  | klimbs_succ | klimbs_add_carry | klimbs_add | klimbs_sub_borrow | klimbs_normalize
  | klimbs_sub | klimbs_le | klimbs_dec | divmod_256 | klimbs_mul | klimbs_mul_outer
  | klimbs_mul_single | klimbs_shl_limbs | klimbs_is_zero | klimbs_div_mod | klimbs_div
  | klimbs_mod | klimbs_gcd | klimbs_pow | klimbs_land | klimbs_lor | klimbs_xor_op
  | klimbs_shl | klimbs_shr
  | divide_grow | ordinary_div_mod
  | mk_bool | mk_nat_lit | np_apply_spine | lvls_empty | split_u32 | klimbs_from_g
  | mk_nat_offset_stuck | mk_nat_binop_stuck | build_succ_offset
  | utf8_cont | utf8_decode_one | utf8_validate | build_char_list | str_lit_to_ctor
  | str_lit_delta_step | str_lit_to_ctor_app_or_self
  | try_extract_nat | try_extract_nat_app | try_nat_binop_addr | try_match_nat_add
  | cleanup_nat_offset_major | try_nat_offset_dispatch | try_nat_binop_dispatch
  | try_nat_dispatch
  deriving DecidableEq, Repr

/-- The function's symbol, as `ObsFn` names it. -/
def Fn.name : Fn → String
  | .klimbs_succ => "KernelKlimbs::klimbs_succ"
  | .klimbs_add_carry => "KernelKlimbs::klimbs_add_carry"
  | .klimbs_add => "KernelKlimbs::klimbs_add"
  | .klimbs_sub_borrow => "KernelKlimbs::klimbs_sub_borrow"
  | .klimbs_normalize => "KernelKlimbs::klimbs_normalize"
  | .klimbs_sub => "KernelKlimbs::klimbs_sub"
  | .klimbs_le => "KernelKlimbs::klimbs_le"
  | .klimbs_dec => "KernelKlimbs::klimbs_dec"
  | .divmod_256 => "KernelKlimbs::divmod_256"
  | .klimbs_mul => "KernelKlimbs::klimbs_mul"
  | .klimbs_mul_outer => "KernelKlimbs::klimbs_mul_outer"
  | .klimbs_mul_single => "KernelKlimbs::klimbs_mul_single"
  | .klimbs_shl_limbs => "KernelKlimbs::klimbs_shl_limbs"
  | .klimbs_is_zero => "KernelKlimbs::klimbs_is_zero"
  | .klimbs_div_mod => "KernelKlimbs::klimbs_div_mod"
  | .klimbs_div => "KernelKlimbs::klimbs_div"
  | .klimbs_mod => "KernelKlimbs::klimbs_mod"
  | .klimbs_gcd => "KernelKlimbs::klimbs_gcd"
  | .klimbs_pow => "KernelKlimbs::klimbs_pow"
  | .klimbs_land => "KernelKlimbs::klimbs_land"
  | .klimbs_lor => "KernelKlimbs::klimbs_lor"
  | .klimbs_xor_op => "KernelKlimbs::klimbs_xor_op"
  | .klimbs_shl => "KernelKlimbs::klimbs_shl"
  | .klimbs_shr => "KernelKlimbs::klimbs_shr"
  | .divide_grow => "IxVMCompat::divide_grow"
  | .ordinary_div_mod => "IxVMCompat::ordinary_div_mod"
  | .mk_bool => "KernelNatPrim::mk_bool"
  | .mk_nat_lit => "KernelNatPrim::mk_nat_lit"
  | .np_apply_spine => "KernelNatPrim::np_apply_spine"
  | .lvls_empty => "KernelNatPrim::lvls_empty"
  | .split_u32 => "KernelNatPrim::split_u32"
  | .klimbs_from_g => "KernelNatPrim::klimbs_from_g"
  | .mk_nat_offset_stuck => "KernelNatPrim::mk_nat_offset_stuck"
  | .mk_nat_binop_stuck => "KernelNatPrim::mk_nat_binop_stuck"
  | .build_succ_offset => "KernelNatPrim::build_succ_offset"
  | .utf8_cont => "KernelNatPrim::utf8_cont"
  | .utf8_decode_one => "KernelNatPrim::utf8_decode_one"
  | .utf8_validate => "KernelNatPrim::utf8_validate"
  | .build_char_list => "KernelNatPrim::build_char_list"
  | .str_lit_to_ctor => "KernelNatPrim::str_lit_to_ctor"
  | .str_lit_delta_step => "KernelNatPrim::str_lit_delta_step"
  | .str_lit_to_ctor_app_or_self => "KernelNatPrim::str_lit_to_ctor_app_or_self"
  | .try_extract_nat => "KernelNatPrim::try_extract_nat"
  | .try_extract_nat_app => "KernelNatPrim::try_extract_nat_app"
  | .try_nat_binop_addr => "KernelNatPrim::try_nat_binop_addr"
  | .try_match_nat_add => "KernelNatPrim::try_match_nat_add"
  | .cleanup_nat_offset_major => "KernelNatPrim::cleanup_nat_offset_major"
  | .try_nat_offset_dispatch => "KernelNatPrim::try_nat_offset_dispatch"
  | .try_nat_binop_dispatch => "KernelNatPrim::try_nat_binop_dispatch"
  | .try_nat_dispatch => "KernelNatPrim::try_nat_dispatch"

/-- The function's spec. -/
def Fn.spec : Fn → SpecFn
  | .klimbs_succ => klimbs_succ
  | .klimbs_add_carry => klimbs_add_carry
  | .klimbs_add => klimbs_add
  | .klimbs_sub_borrow => klimbs_sub_borrow
  | .klimbs_normalize => klimbs_normalize
  | .klimbs_sub => klimbs_sub
  | .klimbs_le => klimbs_le
  | .klimbs_dec => klimbs_dec
  | .divmod_256 => divmod_256
  | .klimbs_mul => klimbs_mul
  | .klimbs_mul_outer => klimbs_mul_outer
  | .klimbs_mul_single => klimbs_mul_single
  | .klimbs_shl_limbs => klimbs_shl_limbs
  | .klimbs_is_zero => klimbs_is_zero
  | .klimbs_div_mod => klimbs_div_mod
  | .klimbs_div => klimbs_div
  | .klimbs_mod => klimbs_mod
  | .klimbs_gcd => klimbs_gcd
  | .klimbs_pow => klimbs_pow
  | .klimbs_land => klimbs_land
  | .klimbs_lor => klimbs_lor
  | .klimbs_xor_op => klimbs_xor_op
  | .klimbs_shl => klimbs_shl
  | .klimbs_shr => klimbs_shr
  | .divide_grow => divide_grow
  | .ordinary_div_mod => ordinary_div_mod
  | .mk_bool => mk_bool
  | .mk_nat_lit => mk_nat_lit
  | .np_apply_spine => np_apply_spine
  | .lvls_empty => lvls_empty
  | .split_u32 => split_u32
  | .klimbs_from_g => klimbs_from_g
  | .mk_nat_offset_stuck => mk_nat_offset_stuck
  | .mk_nat_binop_stuck => mk_nat_binop_stuck
  | .build_succ_offset => build_succ_offset
  | .utf8_cont => utf8_cont
  | .utf8_decode_one => utf8_decode_one
  | .utf8_validate => utf8_validate
  | .build_char_list => build_char_list
  | .str_lit_to_ctor => str_lit_to_ctor
  | .str_lit_delta_step => str_lit_delta_step
  | .str_lit_to_ctor_app_or_self => str_lit_to_ctor_app_or_self
  | .try_extract_nat => try_extract_nat
  | .try_extract_nat_app => try_extract_nat_app
  | .try_nat_binop_addr => try_nat_binop_addr
  | .try_match_nat_add => try_match_nat_add
  | .cleanup_nat_offset_major => cleanup_nat_offset_major
  | .try_nat_offset_dispatch => try_nat_offset_dispatch
  | .try_nat_binop_dispatch => try_nat_binop_dispatch
  | .try_nat_dispatch => try_nat_dispatch

end IxVM.Refinement.Core.Specs.Nat
