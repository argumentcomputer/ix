/-!
Roots whose exported symbols collide (phase 1 plan, MT.4). `Rt.symbolOf`
maps a root's name (the sidecar's, with `«»` where Lean needs them) to
`cx_<name>` with every character other than an ASCII letter, digit or `_`
replaced by `_` (and `init` to `root_init`), so two distinct roots compiled
into one object can share a symbol; `Recheck.run` declines that object with
`stacking: stacking.symbols`. Each root alone compiles and runs.
-/

namespace A

def b (n : Nat) : Nat := n + 1

end A

def A_b (n : Nat) : Nat := n + 2

def «x-y» (n : Nat) : Nat := n + 3

def _x_y_ (n : Nat) : Nat := n + 4

def α (n : Nat) : Nat := n + 5

def β (n : Nat) : Nat := n + 6

def init (n : Nat) : Nat := n + 7

def root_init (n : Nat) : Nat := n + 8

/-- Two roots with the same body: one content address. -/
def twinA (n : Nat) : Nat := n * 7 + 1

def twinB (n : Nat) : Nat := n * 7 + 1

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "A.b", [x] => toString (A.b x)
        | "A_b", [x] => toString (A_b x)
        | "«x-y»", [x] => toString («x-y» x)
        | "_x_y_", [x] => toString (_x_y_ x)
        | "α", [x] => toString (α x)
        | "β", [x] => toString (β x)
        | "init", [x] => toString (init x)
        | "root_init", [x] => toString (root_init x)
        | "twinA", [x] => toString (twinA x)
        | "twinB", [x] => toString (twinB x)
        | _, _ => s!"unknown root {root} {args}"
