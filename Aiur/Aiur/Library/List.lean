import Aiur.Modules

namespace Aiur.Library.List
open Aiur

def declarations : Modules.Program Nat := aiur% "
module Lists {
    enum Node<T> { Cons(T, List<T>), Nil }
    type List<T> = &Node<T>;
    fn is_empty<T>(list: List<T>) -> Field {
        match *list { Node::Nil => 1, Node::Cons(_, _) => 0 }
    }
}"

end Aiur.Library.List
