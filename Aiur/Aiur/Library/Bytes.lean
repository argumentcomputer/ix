import Aiur.Library.U8
import Aiur.Library.List
import Aiur.Library.Frontend

/-! Common byte streams and addresses. Address equality compares all 32
checked bytes and does not assume a memory address or field-specific packing. -/
namespace Aiur.Library.Bytes
open Aiur

def dependencies : Modules.Program Nat := U8.templates.append List.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies r#"
module Bytes {
    type Stream = Lists::List<UInt8::U8>;
    type Address = [UInt8::U8; 32];
    type AddressRef = &Address;
fn address_eq_tail(a: AddressRef, b: AddressRef) -> Field {
    let [_, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = (*(a));
    let [_, b1, b2, b3, b4, b5, b6, b7,
         b8, b9, b10, b11, b12, b13, b14, b15,
         b16, b17, b18, b19, b20, b21, b22, b23,
         b24, b25, b26, b27, b28, b29, b30, b31] = (*(b));

    let pa1 = ((((((UInt8::to_field(a7) * 256) + UInt8::to_field(a6)) * 256 +
                 UInt8::to_field(a5)) * 256 + UInt8::to_field(a4)) * 256 +
                 UInt8::to_field(a3)) * 256 + UInt8::to_field(a2)) * 256 + UInt8::to_field(a1);
    let pb1 = ((((((UInt8::to_field(b7) * 256) + UInt8::to_field(b6)) * 256 +
                 UInt8::to_field(b5)) * 256 + UInt8::to_field(b4)) * 256 +
                 UInt8::to_field(b3)) * 256 + UInt8::to_field(b2)) * 256 + UInt8::to_field(b1);
    match pa1 - pb1 {
      0 => {
        let pa2 = ((((((UInt8::to_field(a14) * 256) + UInt8::to_field(a13)) * 256 +
                     UInt8::to_field(a12)) * 256 + UInt8::to_field(a11)) * 256 +
                     UInt8::to_field(a10)) * 256 + UInt8::to_field(a9)) * 256 + UInt8::to_field(a8);
        let pb2 = ((((((UInt8::to_field(b14) * 256) + UInt8::to_field(b13)) * 256 +
                     UInt8::to_field(b12)) * 256 + UInt8::to_field(b11)) * 256 +
                     UInt8::to_field(b10)) * 256 + UInt8::to_field(b9)) * 256 + UInt8::to_field(b8);
        match pa2 - pb2 {
          0 => {
            let pa3 = ((((((UInt8::to_field(a21) * 256) + UInt8::to_field(a20)) * 256 +
                         UInt8::to_field(a19)) * 256 + UInt8::to_field(a18)) * 256 +
                         UInt8::to_field(a17)) * 256 + UInt8::to_field(a16)) * 256 +
                         UInt8::to_field(a15);
            let pb3 = ((((((UInt8::to_field(b21) * 256) + UInt8::to_field(b20)) * 256 +
                         UInt8::to_field(b19)) * 256 + UInt8::to_field(b18)) * 256 +
                         UInt8::to_field(b17)) * 256 + UInt8::to_field(b16)) * 256 +
                         UInt8::to_field(b15);
            match pa3 - pb3 {
              0 => {
                let pa4 = ((((((UInt8::to_field(a28) * 256) + UInt8::to_field(a27)) * 256 +
                             UInt8::to_field(a26)) * 256 + UInt8::to_field(a25)) * 256 +
                             UInt8::to_field(a24)) * 256 + UInt8::to_field(a23)) * 256 +
                             UInt8::to_field(a22);
                let pb4 = ((((((UInt8::to_field(b28) * 256) + UInt8::to_field(b27)) * 256 +
                             UInt8::to_field(b26)) * 256 + UInt8::to_field(b25)) * 256 +
                             UInt8::to_field(b24)) * 256 + UInt8::to_field(b23)) * 256 +
                             UInt8::to_field(b22);
                match pa4 - pb4 {
                  0 => {
                    let pa5 = ((UInt8::to_field(a31) * 256) + UInt8::to_field(a30)) * 256 +
                                UInt8::to_field(a29);
                    let pb5 = ((UInt8::to_field(b31) * 256) + UInt8::to_field(b30)) * 256 +
                                UInt8::to_field(b29);
                    match pa5 - pb5 {
                      0 => {  1 } ,
                      _ => {  0 } ,
                    } } ,
                  _ => {  0 } ,
                } } ,
              _ => {  0 } ,
            } } ,
          _ => {  0 } ,
        } } ,
      _ => {  0 } ,
    }
  }

fn address_eq(a: AddressRef, b: AddressRef) -> Field {
    let av = (*(a));
    let bv = (*(b));
    match UInt8::to_field(av[0]) - UInt8::to_field(bv[0]) {
      0 => {  address_eq_tail(a, b) } ,
      _ => {  0 } ,
    }
  }
}
"#

end Aiur.Library.Bytes
