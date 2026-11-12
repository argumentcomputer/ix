import Aiur.Modules.Function

/-! # IxVM module `IxVMCompat`

Port adapters, which replace main's unconstrained helpers: IO hints, ordinary long
division (no quotient advice; division by zero follows `Nat.div`/`Nat.mod`),
stream equality, and `audit_div`, the division probe `IxVM::check_port_cases` runs.
They were `Compatibility.aiur` and `PortCases.aiur`, which the port generator
appended.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module IxVMCompat where

  -- The owned walk's per-constant entry, and the call a distributed proof routes to the
  -- worker that owns the constant. The constant must be claimable (not unsafe or
  -- partial, nor projected from such a block, nor an inert axiom of the binding); for
  -- a dependency of a safe constant the first always holds, since a safe constant
  -- references only safe ones.
def check_owned := aiur_fn⟦
  fn check_owned(binding: [UInt8::U8; 32], validator: Field, bytes: [UInt8::U8; 32]) -> () {
      let rc = KernelRoles::role_ctx_for_validator((&(binding)), validator);
      KernelClaim::assert_claimable(rc, (&(bytes)));
      KernelClaim::env_walk_all(rc, (&(bytes)))
    }
⟧

def io_get_info := aiur_fn⟦
  inline fn io_get_info(channel: Field, key: [UInt8::U8; 32]) -> (Field, Field) {
      hint::<(Field, Field)>("ixvm.io.info", (channel, Blake3::address_to_fields(key)))
  }
⟧

def ordinary_div_mod := aiur_fn⟦
  fn ordinary_div_mod(a: KernelTypes::KLimbs, b: KernelTypes::KLimbs) -> (KernelTypes::KLimbs, KernelTypes::KLimbs) {
      let a = KernelKlimbs::klimbs_normalize(a);
      let b = KernelKlimbs::klimbs_normalize(b);
      match KernelKlimbs::klimbs_is_zero(b) {
        1 => ((&(Lists::Node::Nil)), a),
        _ => divide_grow(a, b),
      }
  }
⟧

def divide_grow := aiur_fn⟦
  fn divide_grow(a: KernelTypes::KLimbs, b: KernelTypes::KLimbs) -> (KernelTypes::KLimbs, KernelTypes::KLimbs) {
      match KernelKlimbs::klimbs_le(b, a) {
        0 => ((&(Lists::Node::Nil)), a),
        _ => {
          let (q, r) = divide_grow(a, KernelKlimbs::klimbs_add(b, b));
          let q = KernelKlimbs::klimbs_add(q, q);
          match KernelKlimbs::klimbs_le(b, r) {
            0 => (q, r),
            _ => (KernelKlimbs::klimbs_succ(q), KernelKlimbs::klimbs_sub(r, b)),
          }
        },
      }
  }
⟧

def stream_equal := aiur_fn⟦
  fn stream_equal(a: Bytes::Stream, b: Bytes::Stream) -> Field {
      match ((*(a)), (*(b))) {
        (Lists::Node::Nil, Lists::Node::Nil) => 1,
        (Lists::Node::Cons(x, xs), Lists::Node::Cons(y, ys)) => {
          match UInt8::to_field(x) - UInt8::to_field(y) { 0 => stream_equal(xs, ys), _ => 0 }
        },
        _ => 0,
      }
  }
⟧

def default_binding_addr := aiur_fn⟦
  fn default_binding_addr() -> Bytes::AddressRef {
      (&([UInt8::BYTE_28, UInt8::BYTE_0, UInt8::BYTE_226, UInt8::BYTE_112,
             UInt8::BYTE_39, UInt8::BYTE_40, UInt8::BYTE_244, UInt8::BYTE_51,
             UInt8::BYTE_121, UInt8::BYTE_41, UInt8::BYTE_111, UInt8::BYTE_32,
             UInt8::BYTE_150, UInt8::BYTE_234, UInt8::BYTE_1, UInt8::BYTE_170,
             UInt8::BYTE_0, UInt8::BYTE_214, UInt8::BYTE_230, UInt8::BYTE_165,
             UInt8::BYTE_96, UInt8::BYTE_224, UInt8::BYTE_73, UInt8::BYTE_170,
             UInt8::BYTE_246, UInt8::BYTE_135, UInt8::BYTE_43, UInt8::BYTE_38,
             UInt8::BYTE_121, UInt8::BYTE_162, UInt8::BYTE_55, UInt8::BYTE_244]))
  }
⟧

def audit_div := aiur_fn⟦
  fn audit_div(a: KernelTypes::KLimbs, b: KernelTypes::KLimbs, expected_q: KernelTypes::KLimbs, expected_r: KernelTypes::KLimbs) -> () {
      let (q, r) = KernelKlimbs::klimbs_div_mod(a, b);
      assert_eq!(KernelLevels::klimbs_eq(q, expected_q), 1, "audit quotient");
      assert_eq!(KernelLevels::klimbs_eq(r, expected_r), 1, "audit remainder");
      ()
  }
⟧

end

end IxVM
