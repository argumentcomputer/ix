import Tests.Ix.Sharing

open Ixon

def simple : Array Expr :=
  let t := Expr.ref 0 #[]
  let e1 := Expr.all t (.sort 1)
  let e2 := Expr.all t e1
  let e3 := Expr.all t e2
  #[Expr.all t e3]

def contentHash : Array Expr := #[
  .all (.ref 0 #[]) (.sort 0),
  .all (.ref 0 #[]) (.sort 1),
  .all (.ref 0 #[]) (.sort 2)]

def recursor : Array Expr :=
  let tRef := Expr.ref 0 #[]
  let target := Expr.all tRef (.app (.var 1) (.var 0))
  let withMinor3 := Expr.all (.app (.var 3) (.ref 3 #[])) target
  let withMinor2 := Expr.all (.app (.var 2) (.ref 2 #[])) withMinor3
  let withMinor1 := Expr.all (.app (.var 1) (.ref 1 #[])) withMinor2
  let motiveType := Expr.all tRef (.sort 1)
  #[.all motiveType withMinor1, .var 1, .var 2, .var 3]

def forallImpReal : Array Expr :=
  let typ := Expr.all (.sort 0)
    (Expr.all (Expr.all (.var 0) (.sort 1))
      (Expr.all (Expr.all (.var 1) (.sort 1))
        (Expr.all
          (Expr.all (.var 2)
            (Expr.all (.app (.var 2) (.var 0))
                      (.app (.var 2) (.var 1))))
          (Expr.all
            (Expr.all (.var 3) (.app (.var 3) (.var 0)))
            (Expr.all (.var 4) (.app (.var 3) (.var 0)))))))
  let value := Expr.lam (.sort 0)
    (Expr.lam (Expr.all (.var 0) (.sort 1))
      (Expr.lam (Expr.all (.var 1) (.sort 1))
        (Expr.lam
          (Expr.all (.var 2)
            (Expr.all (.app (.var 2) (.var 0))
                      (.app (.var 2) (.var 1))))
          (Expr.lam
            (Expr.all (.var 3) (.app (.var 3) (.var 0)))
            (Expr.lam (.var 4)
              (Expr.app
                (Expr.app (.var 2) (.var 0))
                (Expr.app (.var 1) (.var 0))))))))
  #[typ, value]

def forallImpSharing : Array Expr :=
  let app21 := Expr.app (.var 2) (.var 1)
  let app20 := Expr.app (.var 2) (.var 0)
  let e1 := Expr.all app21 app20
  let e2 := Expr.all app20 app21
  #[.all (.var 3) e1, .all (.var 3) e2]

def flipCase : Array Expr :=
  let innerAll := Expr.all (.var 2) (.var 2)
  let funcType := Expr.all (.var 2) innerAll
  let resultType := Expr.all (.var 2) (Expr.all (.var 4) (.var 3))
  let typ := Expr.all (.sort 0)
    (Expr.all (.sort 1)
      (Expr.all (.sort 2) (Expr.all funcType resultType)))
  let body := Expr.app (Expr.app (.var 2) (.var 0)) (.var 1)
  let value := Expr.lam (.sort 0)
    (Expr.lam (.sort 1)
      (Expr.lam (.sort 2)
        (Expr.lam funcType
          (Expr.lam (.var 2) (Expr.lam (.var 4) body)))))
  #[typ, value]

def corpus : Array (String × Array Expr) := #[
  ("simple", simple),
  ("content-hash", contentHash),
  ("recursor", recursor),
  ("forall-imp-sharing", forallImpSharing),
  ("forall-imp-real", forallImpReal),
  ("flip", flipCase)]

def dump (name : String) (input : Array Expr) : IO Unit := do
  let (bodies, table) := Ix.Sharing.applySharing input
  IO.println s!"VECTOR {name}"
  IO.println s!"  bodies := {repr bodies}"
  IO.println s!"  table := {repr table}"

def main (_args : List String) : IO UInt32 := do
  let rc ← LSpec.lspecIO (.ofList [("sharing", Tests.Sharing.suite)]) []
  if rc != 0 then return rc
  for (name, input) in corpus do dump name input
  return 0
