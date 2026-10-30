import Aiur.Library.List
import Aiur.Library.U32
import Aiur.Library.U64

/-! List operations whose sizes use checked words. Kept separate so the
polymorphic list library has no dependency on a field-specific word encoding. -/
namespace Aiur.Library.List.Word
open Aiur

def dependencies : Modules.Program Nat :=
  U32.templates.append U64.declarations |>.append List.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies r#"
module WordLists {
fn checked_depth_succ(depth: Field) -> Field {
    assert_eq!(UInt32::less_than_fields(depth, 4294967295), 1,
      "list depth exceeds u32");
    depth + 1
  }

fn depth_checked<T>(list: Lists::List<T>) -> Field {
    match (*(list)) {
      Lists::Node::Nil => {  0 } ,
      Lists::Node::Cons(_, rest) => {
        let depth = depth_checked(rest);
        checked_depth_succ(depth) } ,
    }
  }

fn length_u64<T>(list: Lists::List<T>) -> UInt64::U64 {
    match (*(list)) {
      Lists::Node::Nil => {  [UInt8::BYTE_0; 8] } ,
      Lists::Node::Cons(_, rest) => {  UInt64::wrapping_succ(length_u64(rest)) } ,
    }
  }

fn lookup_u64<T>(list: Lists::List<T>, idx: UInt64::U64) -> T {
    let Lists::Node::Cons(v, rest) = (*(list));
    let z = UInt64::is_zero(idx);
    match z {
      1 => {  v } ,
      0 => {  lookup_u64(rest, UInt64::saturating_pred(idx)) } ,
    }
  }
}
"#

end Aiur.Library.List.Word
