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
  -- partial, nor projected from such a block); for a dependency of a safe constant
  -- this always holds, since a safe constant references only safe ones.
def check_owned := aiur_fn⟦
  fn check_owned(binding: [UInt8::U8; 32], validator: Field, bytes: [UInt8::U8; 32]) -> () {
      KernelClaim::assert_claimable((&(bytes)));
      KernelClaim::env_walk_all(KernelRoles::role_ctx_for_validator((&(binding)), validator), (&(bytes)))
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
      (&([UInt8::BYTE_125, UInt8::BYTE_248, UInt8::BYTE_114, UInt8::BYTE_219,
             UInt8::BYTE_88, UInt8::BYTE_209, UInt8::BYTE_16, UInt8::BYTE_10,
             UInt8::BYTE_222, UInt8::BYTE_13, UInt8::BYTE_186, UInt8::BYTE_87,
             UInt8::BYTE_106, UInt8::BYTE_19, UInt8::BYTE_41, UInt8::BYTE_130,
             UInt8::BYTE_217, UInt8::BYTE_59, UInt8::BYTE_191, UInt8::BYTE_159,
             UInt8::BYTE_133, UInt8::BYTE_41, UInt8::BYTE_239, UInt8::BYTE_15,
             UInt8::BYTE_55, UInt8::BYTE_161, UInt8::BYTE_113, UInt8::BYTE_187,
             UInt8::BYTE_47, UInt8::BYTE_186, UInt8::BYTE_225, UInt8::BYTE_218]))
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
