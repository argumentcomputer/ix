import Tests.Ix.Compile.Corpus.Shape

namespace Tests.Ix.Compile.Corpus

/-! Port of the legacy single-inductive shape DSL: six result sorts, five
parameter forms, five index forms and six recursion forms. Impossible parameter
index combinations are excluded by the DSL, not by an elaboration result. -/

structure SingleInfo where
  binders : String
  params : String
  field : Bool
  indices : String
  recKind : String
  deriving Inhabited

def singleDecl (sk pk ik rk : String) : Option (String × SingleInfo) := do
  let (sort, univs) ← ([ ("P", ("Prop", "")), ("T", ("Type", "")),
    ("U", ("Type u", "u")), ("S", ("Sort u", "u")),
    ("M", ("Sort (max 1 u)", "u")), ("W", ("Type (max u v)", "u v")) ]).lookup sk
  let aSort := if sk == "S" || sk == "M" then "Sort u"
    else if sk == "U" || sk == "W" then "Type u" else "Type"
  let (pb, field, pa) ← match pk with
    | "0" => some ("", false, "")
    | "a" => some (s!"(α : {aSort}){if sk == "W" then " (β : Type v)" else ""}", true,
        if sk == "W" then "α β" else "α")
    | "n" => some ("(k : Nat)", false, "k")
    | "f" => some ("(f : Nat → Nat)", false, "f")
    | "d" => some (s!"(α : {aSort}) (β : α → {aSort})", true, "α β")
    | _ => none
  if ik == "par" && !field then none else do
    let t := "$T" ++ if pa.isEmpty then "" else " " ++ pa
    let (ity, base, ib, i, next, jb, j, comb) ← match ik with
      | "0" => some ("", "", "", "", "", "", "", "")
      | "n" => some ("Nat → ", " 0", "{n : Nat} → ", " n", " (n + 1)",
          "{m : Nat} → ", " m", " (n + m + 1)")
      | "nb" => some ("Nat → Bool → ", " 0 true", "{n : Nat} → {b : Bool} → ", " n b",
          " (n + 1) (!b)", "{m : Nat} → {c : Bool} → ", " m c", " (n + m + 1) (b && c)")
      | "dep" => some ("(n : Nat) → Fin (n + 1) → ", " 0 0", "{n : Nat} → {i : Fin (n + 1)} → ",
          " n i", " (n + 1) i.succ", "{m : Nat} → {j : Fin (m + 1)} → ", " m j", " (n + m + 1) 0")
      | "par" => some ("List α → ", " []", "{l : List α} → ", " l", " (x :: l)",
          "{l2 : List α} → ", " l2", " (l ++ l2)")
      | _ => none
    let pf := if field then "(x : α) → " else ""
    let baseCtor := s!"  | base : {t}{base}"
    let ctor ← match rk with
      | "none" => some s!"  | val : {pf}Bool → {t}{base}"
      | "dir" => some s!"  | succ : {ib}{pf}{t}{i} → {t}{next}"
      | "two" => some <| s!"  | node : {ib}{jb}{t}{i} → {t}{j} → {t}{comb}" ++
          (if field then s!"\n  | leaf : {pf}{t}{base}" else "")
      | "refl" => some s!"  | lim : {ib}{pf}(Nat → {t}{i}) → {t}{next}"
      | "dbind" => some <| match ik with
          | "0" => s!"  | dl : (j : Nat) → (Fin j → {t}) → {t}"
          | "n" => s!"  | dl : ((j : Nat) → {t} j) → {t} 0"
          | "nb" => s!"  | dl : ((j : Nat) → (b : Bool) → {t} j b) → {t} 0 false"
          | "dep" => s!"  | dl : ((j : Nat) → (i : Fin (j + 1)) → {t} j i) → {t} 0 0"
          | _ => s!"  | dl : ((l : List α) → {t} l) → {t} []"
      | "mix" => some <| if ik == "par" then
          s!"  | node : {ib}Nat → {t}{i} → Bool → {t}{i} → (x : α) → {t}{next}"
        else s!"  | node : {ib}Nat → {pf}{t}{i} → Bool → {t}{i} → {t}{next}"
      | _ => none
    let uv := if !univs.isEmpty && sk != "S" then s!"universe {univs}\n" else ""
    let opt := if sk == "S" then "set_option bootstrap.inductiveCheckResultingUniverse false in\n" else ""
    return (s!"{uv}{opt}inductive $T {pb} : {ity}{sort} where\n{baseCtor}\n{ctor}\n",
      ⟨pb, pa, field, ik, rk⟩)

def singleExtras (sk : String) (info : SingleInfo) : Array (String × String) := Id.run do
  let ik := info.indices
  let rk := info.recKind
  let ipb := info.binders.replace "(" "{" |>.replace ")" "}"
  let (ib, ia) := match ik with
    | "n" => ("{n : Nat} ", " n")
    | "nb" => ("{n : Nat} {b : Bool} ", " n b")
    | "dep" => ("{n : Nat} {i : Fin (n + 1)} ", " n i")
    | "par" => ("{l : List α} ", " l")
    | _ => ("", "")
  let t := "($T" ++ (if info.params.isEmpty then "" else " " ++ info.params) ++ ia ++ ")"
  let prop := sk == "P"
  let mut out := #[
    ("auxref", "noncomputable def auxRec := @$T.rec\nnoncomputable def auxCases := @$T.casesOn\nnoncomputable def auxRecOn := @$T.recOn\n" ++
      if rk != "none" then "noncomputable def auxBelow := @$T.below\nnoncomputable def auxBrecOn := @$T.brecOn\n" else ""),
    ("noconf", "noncomputable def auxNoConf := @$T.noConfusion\nnoncomputable def auxNoConfType := @$T.noConfusionType\n"),
    ("ctoridx", "noncomputable def auxCtorIdx := @$T.ctorIdx\n"),
    ("induction", s!"theorem indEx {ipb} {ib}(t : {t}) : True := by\n  induction t <;> trivial\n"),
    ("cases", s!"theorem casesEx {ipb} {ib}(t : {t}) : True := by\n  cases t <;> trivial\n")]
  if rk != "none" then
    let pv := if info.field && ik != "par" then "_ " else ""
    let one (r : String) := if prop then s!"go {r}" else s!"go {r} + 1"
    let two := if prop then "let _ := go a; go b" else "go a + go b + 1"
    let zero := if prop then "trivial" else "0"
    let arm := match rk with
      | "dir" => s!"| .succ {if ik == "par" then "_ " else pv}t => {one "t"}"
      | "two" => s!"| .node a b => {two}"
      | "refl" => s!"| .lim {if ik == "par" then "_ " else pv}g => {one "(g 0)"}"
      | "dbind" =>
        if ik == "0" then s!"| .dl 0 _ => {zero}\n  | .dl (_ + 1) g => {one "(g 0)"}"
        else
          let arg := match ik with
            | "n" => "(g 3)" | "nb" => "(g 3 true)" | "dep" => "(g 3 0)" | _ => "(g [])"
          s!"| .dl g => {one arg}"
      | _ => if ik == "par" then s!"| .node _ a _ b _ => {two}"
        else s!"| .node _ {pv}a _ b => {two}"
    let other := if rk == "two" && info.field then s!"\n  | .leaf _ => {zero}" else ""
    if sk != "S" then
      let srec := s!"{if prop then "theorem" else "def"} go {ipb} {ib}: {t} → {if prop then "True" else "Nat"}\n  | .base => {zero}{other}\n  {arm}\ntermination_by structural t => t\n"
      out := out.push ("srec", srec)
      out := out.push ("srec_eqns", srec ++ "noncomputable def goEq1 := @go.eq_1\nnoncomputable def goEqDef := @go.eq_def\n")
      out := out.push ("srec_induct", srec ++ "noncomputable def goInduct := @go.induct\n")
  if !prop then out := out.push ("match", s!"def isBase {ipb} {ib}: {t} → Bool\n  | .base => true\n  | _ => false\n")
  return out

def singles : Array Shape := Id.run do
  let mut out := #[]
  for sk in #["P", "T", "U", "S", "M", "W"] do
    for pk in #["0", "a", "n", "f", "d"] do
      for ik in #["0", "n", "nb", "dep", "par"] do
        for rk in #["none", "dir", "two", "refl", "dbind", "mix"] do
          if let some (decl, info) := singleDecl sk pk ik rk then
            out := out.push
              { id := s!"S_{sk}_{pk}_{ik}_{rk}", family := "single", decl := decl,
                axes := #[("sort", sk), ("params", pk), ("indices", ik), ("rec", rk)],
                extras := singleExtras sk info }
  for rk in #["none", "dir", "two"] do
    for pk in #["0", "a"] do
      if let some (decl, _) := singleDecl "T" pk "0" rk then
        for d in #["DecidableEq", "BEq", "Repr", "Hashable", "Ord", "Inhabited", "Nonempty"] do
          out := out.push
            { id := s!"D_{pk}_{rk}_{d}", family := "derived",
              decl := decl.trimAsciiEnd.toString ++ s!"\nderiving {d}\n",
              axes := #[("sort", "T"), ("params", pk), ("rec", rk), ("deriving", d)] }
  return out

end Tests.Ix.Compile.Corpus
