import Ix.UInt128

namespace Binius

inductive ArithExpr
  | const : UInt128 → ArithExpr
  | var : USize → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
  | pow : ArithExpr → UInt64 → ArithExpr

end Binius
