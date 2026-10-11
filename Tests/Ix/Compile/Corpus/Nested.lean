import Tests.Ix.Compile.Corpus.Shape

namespace Tests.Ix.Compile.Corpus

def containers : Array (String × String × String) := #[
  ("List", "List $T", ""), ("Array", "Array $T", ""), ("Option", "Option $T", ""),
  ("ProdTT", "$T × $T", ""), ("ProdNT", "Nat × $T", ""), ("Sum", "Sum $T Nat", ""),
  ("Box", "Box $T", "box"), ("Vec", "Vec $T 3", "vec"), ("VecN", "Vec $T n", "vec"),
  ("Pair", "Pair $T", "pair"), ("Fn", "Fn $T", "fn"),
  ("ListOpt", "List (Option $T)", ""), ("ArrList", "Array (List $T)", ""),
  ("OptProd", "Option ($T × $T)", ""), ("ListList", "List (List $T)", ""),
  ("ListBox", "List (Box $T)", "box"), ("Twice", "List $T → List $T", ""),
  ("DiffArgs", "List $T → List ($T × Nat)", ""), ("ListArr", "List $T → Array $T", ""),
  ("ProdSwap", "$T × Nat → Nat × $T", ""), ("Sigma", "(n : Nat) × Vec $T n", "vec"),
  ("Thunk", "Unit → List $T", "")]

def containerPrelude (kind : String) : String := "universe u\n" ++ match kind with
  | "box" => "structure Box (α : Type u) where\n  val : α\n"
  | "vec" => "inductive Vec (α : Type u) : Nat → Type u where\n  | nil : Vec α 0\n  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)\n"
  | "pair" => "structure Pair (α : Type u) where\n  fst : α\n  snd : α\n"
  | "fn" => "structure Fn (α : Type u) where\n  run : Nat → α\n"
  | _ => ""

def nestedDecl (cn cty pre form : String) : String :=
  let bound := if cn == "VecN" then "{n : Nat} → " else ""
  let (header, leaf, node, result) := match form with
    | "param" => ("(α : Type) : Type", "α → $T α", cty.replace "$T" "($T α)", "$T α")
    | "idx" => (": Nat → Type", "$T 0", cty.replace "$T" "($T 0)", "$T 1")
    | "univ" => ("(α : Type u) : Type u", "α → $T α", cty.replace "$T" "($T α)", "$T α")
    | _ => (": Type", "$T", cty, "$T")
  pre ++ s!"inductive $T {header} where\n  | leaf : {leaf}\n  | node : {bound}{node} → {result}\n" ++
    if form == "refl" then "  | lim : (Nat → $T) → $T\n" else ""

def nestedExtras (cn form : String) : Array (String × String) := Id.run do
  let mut out := #[
    ("auxref", "noncomputable def r := @$T.rec\nnoncomputable def b := @$T.brecOn\nnoncomputable def bl := @$T.below\nnoncomputable def c := @$T.casesOn\n"),
    ("auxref_N", "noncomputable def r1 := @$T.rec_1\nnoncomputable def b1 := @$T.brecOn_1\nnoncomputable def bl1 := @$T.below_1\n"),
    ("sizeof", "noncomputable def sz := @$T.node.sizeOf_spec\n")]
  if form == "plain" then
    let pair := match cn with
      | "List" => some ("ts", "sizeL", "List $T", "  | [] => 0\n  | t :: ts => t.size + sizeL ts", "l")
      | "Option" => some ("o", "sizeO", "Option $T", "  | none => 0\n  | some t => t.size", "o")
      | "ProdTT" => some ("p", "sizeP", "$T × $T", "  | (a, b) => a.size + b.size", "p")
      | _ => none
    if let some (arg, fn, ty, body, structuralArg) := pair then
      out := out.push ("srec", s!"mutual\ndef $T.size : $T → Nat\n  | .leaf => 1\n  | .node {arg} => {fn} {arg} + 1\n  termination_by structural t => t\ndef {fn} : {ty} → Nat\n{body}\n  termination_by structural {structuralArg} => {structuralArg}\nend\n")
    if cn == "Array" then
      out := out.push ("wf", "def $T.size : $T → Nat\n  | .leaf => 1\n  | .node ts => (ts.attach.map fun ⟨t, _⟩ => t.size).sum + 1\n")
  return out

def nestedShapes : Array Shape := Id.run do
  let mut out := #[]
  for (cn, cty, need) in containers do
    for form in #["plain", "param", "idx", "univ", "refl"] do
      let decl := nestedDecl cn cty (containerPrelude need) form
      let axes := #[("container", cn), ("form", form)]
      out := out.push
        { id := s!"N_{cn}_{form}", family := "nested", decl := decl, axes := axes,
          extras := nestedExtras cn form }
      out := out.push
        { id := s!"ND_{cn}_{form}", family := "nested-derived",
          decl := decl.trimAsciiEnd.toString ++ "\nderiving BEq, Repr, Hashable\n",
          axes := axes.push ("deriving", "BEq,Repr,Hashable") }
  return out

end Tests.Ix.Compile.Corpus
