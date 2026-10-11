/-! H5: a nested auxiliary whose external family hides its index behind a
reducible alias (recursor.rs 1135-1154, 1293 peel indices syntactically). -/
namespace AliasIdx
abbrev Fam := Nat → Type

inductive Ext (α : Type) : Fam
  | mk : α → Ext α 0

inductive T
  | leaf
  | mk : Ext T 0 → T
end AliasIdx
