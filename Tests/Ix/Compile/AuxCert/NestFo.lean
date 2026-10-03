/-! H2 variant: nested through the SECOND member of an external mutual family. -/
namespace NestFo
mutual
inductive Tr (α : Type)
  | node : α → Fo α → Tr α
inductive Fo (α : Type)
  | nil : Fo α
  | cons : Tr α → Fo α → Fo α
end

inductive U
  | mk : Fo U → U
end NestFo
