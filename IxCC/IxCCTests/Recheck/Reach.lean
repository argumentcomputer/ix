import IxCCTests.Recheck.Deep
import IxCC.Lam.Erase.Proof.Correct

/-! # Ingress reads what the seeds reach

`Recheck.ingress` reads only the records the seeds reach
(`Src.Ingress.reach`), a theorem's proof only where a proof seed reaches it
(`Src.Program.byStatement`). This module checks, on the role-bound builder and
on committed closures:

* a closure holding a theorem whose proof is over IxCC's consumer budget,
  which nothing reaches, compiles (the shape of the `binarytrees` wrapper's
  closure); one whose root reaches that theorem as a proof argument compiles,
  the theorem read by its statement (the shape of the string programs'
  closures); the same theorem named by a sidecar equation is read with its
  proof and refused at `ingress: decode`; a reached definition over the budget
  is refused there too, the record named;
* an unread proof is refused wherever a value could be taken as the theorem's
  proof (planted uses: the `eqn` and `csimp` checks, the unfolding table from a
  certificate, the axiom-closure check on both its branches, an annotation
  naming the value), and what only that proof names is not read;
* a theorem reached by its statement and then by an equation's proof is read
  with its proof; an equation on a member of a reached mutual block fires;
* the seeds are every root the sidecar names: a record over the budget that
  only another root reaches refuses a compile of a shallow root;
* a root named by a projection address whose record the artifact does not
  store is refused, saying so (the kernel accepts the artifact);
* on committed closures, the program read from the reached records and the one
  read from every record compile every root to the same object, and SrcEval
  gives the same results;
* a claim made under one sidecar is refused under a sidecar whose roots reach
  other records, and under its sidecar without the equation proposals its
  certificate's `eqn` entries need (the checker recomputes what is reached);
* the walk terminates on a reference cycle, is linear on a long fixpoint
  of equation proposals, and its time doubles, not quadruples, when the
  proposals naming one subject double. -/

namespace IxCCTests.Recheck.Reach

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCC.Sem (Obs Lang)
open IxCCTests.Recheck.Hostile
open IxCCTests.Src (Assert expect)
open IxCCTests.IxonV3.Builder (store arrow lambda)
open IxCCTests.Support.Bound (loadBase)

/-- The address the base's role table binds a role to. -/
def roleAddr (env : Env) (r : Ix.Kernel.Role) : IO Addr := do
  let some b := env.binding | throw (IO.userError "the base is unbound")
  let some t := Ix.Kernel.RoleTable.ofBytes b.bytes | throw (IO.userError "the base's table")
  let some k := t.addressOf? r | throw (IO.userError s!"the base binds no {repr r}")
  let some a := Address.ofBytes? k.hash | throw (IO.userError "an address")
  return a

/-- `idp (p : Prop) (h : p) : p := h`, `thm : c₀ = c₀` proved by `idp (c₀ = c₀)`
applied `n` times over `Eq.refl c₀` (one expression `n + 3` deep: past IxCC's
consumer budget for `n` over 253, within the kernel's depth bound), and `useProof (h : c₀ = c₀) :
E := c₁`; with the base, `thm`, `useProof` and `idp`. -/
def proofEnv (env0 : Env) (n : Nat) : IO (Base × Env × Addr × Addr × Addr) := do
  let b := base env0 3
  let eqA ← roleAddr env0 .eq
  let reflA ← roleAddr env0 .eqRefl
  let (e, idp) := store b.env ⟨defn (arrow (.sort 0) (arrow (.var 0) (.var 1)))
    (lambda (.sort 0) (lambda (.var 0) (.var 0))), #[], #[], #[.zero]⟩
  -- refs: 0 Eq, 1 E, 2 c₀, 3 Eq.refl, 4 idp; universes: 0 is `1`
  let prop : X := .app (.app (.app (.ref 0 #[0]) (.ref 1 #[])) (.ref 2 #[])) (.ref 2 #[])
  let mut pf : X := .app (.app (.ref 3 #[0]) (.ref 1 #[])) (.ref 2 #[])
  for _ in [0:n] do pf := .app (.app (.ref 4 #[]) prop) pf
  let (e, thm) := store e ⟨.defn ⟨.thm, .safe, 0, prop, pf⟩, #[],
    #[eqA, b.enumI, b.ctors[0]!, reflA, idp], #[.succ .zero]⟩
  -- refs: 0 Eq, 1 E, 2 c₀, 3 c₁
  let (e, use) := store e ⟨defn (arrow prop (.ref 1 #[])) (lambda prop (.ref 3 #[])), #[],
    #[eqA, b.enumI, b.ctors[0]!, b.ctors[1]!], #[.succ .zero]⟩
  return (b, e, thm, use, idp)

/-- `t' : c₀ = c₀ := t`: a theorem whose proof is the theorem `t`. -/
def proofOf (env0 : Env) (e : Env) (b : Base) (t : Addr) : IO (Env × Addr) := do
  let eqA ← roleAddr env0 .eq
  -- refs: 0 Eq, 1 E, 2 c₀, 3 t
  let prop : X := .app (.app (.app (.ref 0 #[0]) (.ref 1 #[])) (.ref 2 #[])) (.ref 2 #[])
  return store e ⟨.defn ⟨.thm, .safe, 0, prop, .ref 3 #[]⟩, #[], #[eqA, b.enumI, b.ctors[0]!, t],
    #[.succ .zero]⟩

/-- A sidecar naming `roots` and the equations `(definition, equation)`. -/
def sidecarWith (roots : List (String × Addr)) (eqns : List (Addr × Addr)) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ixcc/k1-equations/1"),
    ("roots", Lean.Json.arr (roots.map fun (n, a) =>
      Lean.Json.mkObj [("name", Lean.Json.str n), ("address", Lean.Json.str (toString a))]).toArray),
    ("equations", Lean.Json.arr (eqns.map fun (f, t) =>
      Lean.Json.mkObj [("definition", Lean.Json.str "f"), ("definition_address", Lean.Json.str (toString f)),
        ("equation", Lean.Json.str "t"), ("equation_address", Lean.Json.str (toString t))]).toArray)]

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The proof shapes, the planted uses of an unread proof, and the controls. -/
def proofs (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let (b, e, thm, use, idp) ← proofEnv env0 400
  -- unreached: `main := c₁`, `thm` in the closure
  let (eU, mainU) := store e ⟨defn enumC (.ref 1 #[]), #[], #[b.enumI, b.ctors[1]!], #[]⟩
  let inpU ← match Recheck.ingress (bytes eU) (sidecar [("main", mainU)]) [] with
    | .ok i => pure i
    | .error err => throw (IO.userError s!"unreached proof: ingress refused: {err.render}")
  expect a (inpU.program.lookup thm).isNone "unreached proof: the theorem was read"
  expect a (Recheck.compile {} (bytes eU) (sidecar [("main", mainU)]) []).isOk
    "unreached proof: the root does not compile"
  -- by statement: `main := useProof thm`
  let (eS, mainS) := store e ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, use, thm], #[]⟩
  let jsonS := sidecar [("main", mainS)]
  let inpS ← match Recheck.ingress (bytes eS) jsonS [] with
    | .ok i => pure i
    | .error err => throw (IO.userError s!"proof by statement: ingress refused: {err.render}")
  let P := inpS.program
  let some t := P.lookup thm | throw (IO.userError "proof by statement: the theorem is not in the program")
  let some m := P.lookup mainS | throw (IO.userError "proof by statement: no main")
  let some u := P.lookup use | throw (IO.userError "proof by statement: no useProof")
  expect a (P.byStatement.contains t) "proof by statement: the theorem is not recorded as read by its statement"
  expect a (match P.decl? t with
      | some (.defn .thm .safe _ _ v) => v == Src.Term.unreadProof
      | _ => false)
    "proof by statement: the theorem's stored value is not the unread proof"
  expect a (P.byStatement.toList.length == 1) s!"proof by statement: {P.byStatement.toList.length} theorems by statement"
  expect a (P.lookup idp).isNone "proof by statement: a constant only the unread proof names was read"
  match Recheck.compile {} (bytes eS) jsonS [] with
  | .error err => expect a false s!"proof by statement: the root does not compile: {err.render}"
  | .ok (_, art) =>
    match Lang.run (⟨art.src, art.checked⟩ : Lam.Erase.Proof.CheckedProgram) (0, []) 1000 with
    | .ok v => expect a (Lang.obs v).isSome "proof by statement: SrcEval observes nothing"
    | _ => expect a false "proof by statement: SrcEval did not return"
  -- planted uses of the unread proof, each refused
  let read := fun (r : Except String Src.Resolve) => match r with
    | .error msg => contains msg "read by its statement"
    | .ok _ => false
  expect a (read (Src.Table.checkEqn P m t)) "an eqn entry on a theorem read by its statement"
  expect a (read (Src.Table.checkCsimp P m u t)) "a csimp entry on a theorem read by its statement"
  expect a (!Src.Table.checkAxiomWalk P (P.size * 2 + 16) [t] [])
    "the axiom-closure walk through a theorem read by its statement"
  -- every axiom of `P` is standard, so this is the check's shortcut, which must not apply
  expect a ((List.range P.size).all fun c => match P.decl? c with
      | some (.axio ..) => Src.Table.isStandardAxiom P c
      | _ => true)
    "proof by statement: an axiom that is not standard (the next check would not reach its shortcut)"
  expect a (match Src.Table.checkAxiomClosure P t with
      | .error _ => true
      | .ok () => false)
    "the axiom-closure check (its all-standard shortcut) on a theorem read by its statement"
  expect a (!Src.Table.checkAxiomClosureRoots { P with roots := P.roots ++ [(thm, t)] })
    "the axiom-closure check of the roots, a theorem read by its statement among them"
  expect a (match Src.Table.ofCert {} P { resolve := [(m, .eqn t)] } with
      | .error msg => contains msg "read by its statement"
      | .ok _ => false)
    "a certificate's table naming a theorem read by its statement"
  expect a (match Recheck.checkRelevanceKeys P { nodes := [(.value t, [])] } with
      | .error err => err.code == "relevance-S1" && contains err.message "read by its statement"
      | .ok () => false)
    "an annotation naming the value of a theorem read by its statement"
  -- the same theorem as a sidecar equation is read with its proof: refused
  let jsonE := sidecarWith [("main", mainS)] [(mainS, thm)]
  expect a (match Recheck.ingress (bytes eS) jsonE [] with
      | .error err => err.code == "decode" && contains err.message "constant exceeds the consumer budget" &&
          contains err.message (toString thm)
      | .ok _ => false)
    "a proof seed over the budget is not refused at ingress: decode, naming it"
  -- a reached definition over the budget: refused, named
  let (eD, mainD) ← IO.ofExcept (Deep.hostileEnv env0 "flat:deepApp" 300)
  expect a (match Recheck.ingress (bytes eD) (sidecar [("main", mainD)]) [] with
      | .error err => err.code == "decode" && contains err.message (toString mainD)
      | .ok _ => false)
    "a reached record over the budget is not refused at ingress: decode, naming it"
  return #[s!"proofs: {P.size} constants read of {inpS.env.consts.size} records, {P.byStatement.toList.length} theorem by statement"]

/-- A theorem reached first by its statement (a proof argument of the root) and
then with its proof (the proof of an equation theorem a sidecar proposal names)
is read with its proof, and what that proof names is read; an equation proposal
whose subject is a member of a mutual block, named by the member's projection
address, makes its theorem a proof seed once the block is reached. -/
def reread (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let (b, e, thm, use, idp) ← proofEnv env0 3
  let (e, eq2) ← proofOf env0 e b thm
  -- `main := useProof thm`: `thm` is a proof argument
  let (e, main) := store e ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, use, thm], #[]⟩
  let read := fun (env : Env) (json : Lean.Json) => do
    match Recheck.ingress (bytes env) json [] with
    | .ok i => pure i.program
    | .error err => throw (IO.userError s!"re-read: ingress refused: {err.render}")
  let byStmt := fun (P : Src.Program) (x : Addr) => (P.lookup x).any P.byStatement.contains
  let P ← read e (sidecar [("main", main)])
  expect a (byStmt P thm && (P.lookup idp).isNone && (P.lookup eq2).isNone)
    "re-read: a proof argument alone is not read by its statement only"
  -- the proposal `(main, eq2)`: `eq2` is a proof seed, its proof names `thm`
  let Q ← read e (sidecarWith [("main", main)] [(main, eq2)])
  expect a ((Q.lookup thm).isSome && !byStmt Q thm && (Q.lookup eq2).isSome && !byStmt Q eq2 &&
      (Q.lookup idp).isSome)
    "re-read: a theorem reached by its statement, then by an equation's proof, is not read with its proof"
  expect a (match (Q.lookup thm).bind Q.decl? with
      | some (.defn .thm .safe _ _ v) => v != Src.Term.unreadProof
      | _ => false)
    "re-read: the theorem's stored value is the unread proof"
  -- a mutual block of two definitions; the root its member 0, a proposal on member 1
  let c : Constant := ⟨.muts #[.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩,
      .defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 2 #[]⟩], #[],
    #[b.enumI, b.ctors[0]!, b.ctors[1]!], #[]⟩
  let (eB, blk) := IxCCTests.IxonV3.Builder.block e c
  let m0 := V3.defnProjAddr blk 0
  let m1 := V3.defnProjAddr blk 1
  let R ← read eB (sidecarWith [("m0", m0)] [(m1, eq2)])
  expect a ((R.lookup m1).isSome && (R.lookup eq2).isSome && !byStmt R eq2 && !byStmt R thm)
    "re-read: an equation on a member of a reached block (by its projection address) is not read with its proof"
  let R0 ← read eB (sidecar [("m0", m0)])
  expect a (R0.lookup eq2).isNone "re-read: without the proposal, its theorem is read"
  return #[s!"re-read: by statement then with proofs; a block member's equation ({Q.size} constants)"]

/-- The seeds are every root the sidecar names, not only the roots a compile
chooses: a record over IxCC's consumer budget that only another sidecar root
reaches refuses `--root A` at `ingress: decode`, naming the record; with only
`A` in the sidecar, `A` is read. -/
def seeds (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let (eD, deepRoot) ← IO.ofExcept (Deep.hostileEnv env0 "flat:deepApp" 300)
  let b := base env0 3
  let e := { eD with consts := b.env.consts.fold (fun m k v => m.insert k v) eD.consts }
  let (e, shallow) := store e ⟨defn enumC (.ref 1 #[]), #[], #[b.enumI, b.ctors[1]!], #[]⟩
  expect a (match Recheck.ingress (bytes e) (sidecar [("A", shallow), ("B", deepRoot)]) ["A"] with
      | .error err => err.code == "decode" && contains err.message (toString deepRoot)
      | .ok _ => false)
    "seeds: --root A is not refused at ingress: decode for a record only the sidecar's root B reaches"
  expect a (Recheck.ingress (bytes e) (sidecar [("A", shallow)]) ["A"]).isOk
    "seeds: A alone in the sidecar is refused"
  return #["seeds: a record over the budget that only another sidecar root reaches refuses --root A"]

/-- A claim whose certificate holds `eqn` entries, verified under its own
sidecar, and under the same sidecar without its equation proposals: refused
there (the equations' theorems are no longer proof seeds, and the numbering
moves). -/
def verifierSidecar (a : Assert) : IO (Array String) := do
  let stem := "fixtures/ixon-v4/bench-k1/fib"
  let bs ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  let inp ← IO.ofExcept ((Recheck.ingress bs json []).mapError (·.render))
  let (claim, cert, _) ← IO.ofExcept ((CompileClaim.produce {} inp).mapError (·.render))
  expect a (contains cert "\"eqn\"") "verifier's sidecar: the certificate has no eqn entry (the test would show nothing)"
  expect a (CompileClaim.verifyBytes {} bs json claim cert) "verifier's sidecar: refused under its own sidecar"
  expect a (!CompileClaim.verifyBytes {} bs (json.setObjVal! "equations" (.arr #[])) claim cert)
    "verifier's sidecar: accepted under a sidecar without the proposals its eqn entries need"
  return #["verifier's sidecar: a claim with eqn entries refused under a sidecar without their proposals"]

/-- A root named by a block member's projection address, in an artifact that
stores the block but not that projection record (`ix compile` stores every
one): the kernel accepts the artifact and ingress refuses the root, saying what
is missing (the reader before 2026-11-12 laid out every block and read it); with
the projection records stored, the root compiles. -/
def projectionRoot (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let b := base env0 3
  let c : Constant := ⟨.muts #[.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩,
      .defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 2 #[]⟩], #[],
    #[b.enumI, b.ctors[0]!, b.ctors[1]!], #[]⟩
  let (eS, blk) := store b.env c
  let root := V3.defnProjAddr blk 1
  expect a (!eS.consts.contains root) "projection root: the projection record is stored (the test would show nothing)"
  expect a (match V3.decodeAnonymousEnv (bytes eS) with
      | .ok env => (Src.KernelFront.accept env).isOk
      | .error _ => false)
    "projection root: the kernel does not accept the artifact"
  expect a (match Recheck.ingress (bytes eS) (sidecar [("main", root)]) [] with
      | .error err => err.code == "ingress" && contains err.message "not a record the artifact stores"
      | .ok _ => false)
    "projection root: a root whose projection record is not stored is not refused, saying so"
  let (eB, _) := IxCCTests.IxonV3.Builder.block b.env c
  expect a (Recheck.compile {} (bytes eB) (sidecar [("main", root)]) []).isOk
    "projection root: with its projection records stored, the root does not compile"
  return #["projection root: refused when its projection record is not stored, compiled when it is"]

/-- Committed closures read from the reached records and from every record
(`Src.Ingress.readAll`) compile each root to the same object, and SrcEval
gives the same results on a few inputs. -/
def fullAgainstReached (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for stem in ["fixtures/ixon-v4/bench-k1/fib", "fixtures/ixon-v4/bench-k1/gcd",
      "fixtures/corpus/phase1-scalar/tuple", "fixtures/corpus/phase1-boundary/tags16"] do
    let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
    let inp ← match Recheck.ingress bytes json [] with
      | .ok i => pure i
      | .error err => throw (IO.userError s!"{stem}: ingress refused: {err.render}")
    let full ← IO.ofExcept (Src.Ingress.readAll inp.env (inp.program.roots.map (·.1)).toArray)
    let full := { full with known := { pins := Src.KernelFront.pinsOfTable inp.kernel.acc.table } }
    let full := { full with known := Src.Pinned.known full, resource := inp.hints.resource }
    let rd ← IO.ofExcept (Src.KernelFront.Reading.build inp.kernel.acc full)
    let inpF : Recheck.Input := { inp with program := full, kernel := { inp.kernel with rd } }
    expect a (full.size ≥ inp.program.size && full.byStatement.toList.isEmpty)
      s!"{stem}: the whole reading has {full.size} constants, the reached {inp.program.size}"
    for (name, i) in inp.names.zipIdx do
      let one := fun (x : Recheck.Input) =>
        Recheck.compileInput {} { x with program := { x.program with roots := [x.program.roots[i]!] } }
      match one inp, one inpF with
      | .ok (_, r), .ok (_, f) =>
        expect a (r.object == f.object) s!"{stem} {name}: the objects differ"
        let params := (r.roots.head?.map (·.params)).getD 0
        for k in [0, 3, 7] do
          let args := List.replicate params k
          let obs := fun (art : Recheck.Artifact) =>
            match Lang.run (⟨art.src, art.checked⟩ : Lam.Erase.Proof.CheckedProgram) (0, args) 100000 with
            | .ok v => s!"{repr (Lang.obs v)}"
            | .timeout => "timeout" | .stuck => "stuck" | .trap => "trap" | _ => "resource"
          expect a (obs r == obs f) s!"{stem} {name} {args}: SrcEval {obs r} and {obs f}"
      | .error e1, .error e2 =>
        expect a (e1.stage == e2.stage && e1.code == e2.code) s!"{stem} {name}: refused differently"
      | _, _ => expect a false s!"{stem} {name}: one reading compiles, the other does not"
    lines := lines.push s!"{stem}: {inp.program.size} constants reached of {full.size}, {inp.names.length} roots alike"
  return lines

/-- A claim made under one sidecar, refused under a sidecar whose roots reach
twenty more records (the numbering moves), accepted under its own. -/
def tamperedSidecar (a : Assert) : IO (Array String) := do
  let env0 ← loadBase
  let b := base env0 3
  let (e, main) := store b.env ⟨defn enumC (.app (.ref 1 #[]) (.ref 2 #[])), #[], #[b.enumI, b.idc, b.ctors[1]!], #[]⟩
  let mut e := e
  let mut extra : List (String × Addr) := []
  for i in [0:20] do
    let mut v : X := .ref 2 #[]
    for _ in [0:i + 1] do v := .app (.ref 1 #[]) v
    let (e', r) := store e ⟨defn enumC v, #[], #[b.enumI, b.idc, b.ctors[0]!], #[]⟩
    e := e'
    extra := extra ++ [(s!"x{i}", r)]
  let bs := bytes e
  let mine := sidecar [("main", main)]
  let other := sidecar ([("main", main)] ++ extra)
  let inp ← IO.ofExcept ((Recheck.ingress bs mine []).mapError (·.render))
  let inpO ← IO.ofExcept ((Recheck.ingress bs other ["main"]).mapError (·.render))
  let some c1 := inp.program.lookup main | throw (IO.userError "tampered sidecar: no main")
  let some c2 := inpO.program.lookup main | throw (IO.userError "tampered sidecar: no main")
  expect a (c1 != c2) "tampered sidecar: the numbering did not move (the test would show nothing)"
  let (claim, cert, _) ← IO.ofExcept ((CompileClaim.produce {} inp).mapError (·.render))
  expect a (CompileClaim.verifyBytes {} bs mine claim cert) "tampered sidecar: the claim is refused under its own sidecar"
  expect a (!CompileClaim.verifyBytes {} bs other claim cert)
    "tampered sidecar: the claim is accepted under a sidecar that reaches other records"
  return #[s!"tampered sidecar: main is constant {c1} under its sidecar, {c2} under the other"]

/-- `reach` on in-memory records: a reference cycle (records stored under
addresses that are not their hashes, which the walk does not check) is a
visited record; a chain of 20,000 equation proposals, each theorem's type
naming the next subject, is a linear fixpoint. -/
def walk (a : Assert) : IO (Array String) := do
  let addr := fun (i : Nat) => Address.blake3Pure (ByteArray.mk #[(i % 256).toUInt8, (i / 256 % 256).toUInt8, (i / 65536).toUInt8, 7])
  let rec_ := fun (refs : Array Addr) => constantBytes ⟨.axio ⟨false, 0, .sort 0⟩, #[], refs, #[.zero]⟩
  let x := addr 1
  let y := addr 2
  let cyc : Env := { consts := ({} : Std.HashMap Addr ByteArray).insert x (rec_ #[y]) |>.insert y (rec_ #[x]) }
  expect a (match Src.Ingress.reach cyc { statement := #[x] } with
      | .ok rs => rs.size == 2
      | .error _ => false)
    "the walk on a reference cycle"
  let n := 20000
  let f := fun (i : Nat) => addr (10 + 2 * i)
  let t := fun (i : Nat) => addr (11 + 2 * i)
  let mut consts : Std.HashMap Addr ByteArray := {}
  let mut eqns : Array (Addr × Addr) := #[]
  for i in [0:n] do
    consts := consts.insert (f i) (constantBytes ⟨defn (.sort 0) (.sort 0), #[], #[], #[.zero]⟩)
    let ty : X := .ref 0 #[]
    consts := consts.insert (t i) (constantBytes ⟨.defn ⟨.thm, .safe, 0, ty, .sort 0⟩, #[], #[f (i + 1)], #[.zero]⟩)
    eqns := eqns.push (f i, t i)
  let chain : Env := { consts }
  let t0 ← IO.monoMsNow
  -- matched in IO, so the walk runs before the second clock reading
  let ok ← match Src.Ingress.reach chain { statement := #[f 0], eqns } with
    | .ok rs => pure (rs.size == 2 * n && rs.all fun x => !Src.Ingress.hasTheorem x.constant || x.proofs)
    | .error _ => pure false
  let t1 ← IO.monoMsNow
  expect a ok s!"the walk over a fixpoint of {n} proposals"
  -- k proposals naming one subject (a sidecar may hold about 390,000): the walk's
  -- time about doubles from 200,000 to 400,000 (it quadrupled when each proposal
  -- copied its subject's group); the best of three runs each
  let fS := addr 3
  let tS := addr 4
  let consts1 : Std.HashMap Addr ByteArray :=
    (({} : Std.HashMap Addr ByteArray).insert fS
      (constantBytes ⟨defn (.sort 0) (.sort 0), #[], #[], #[.zero]⟩)).insert tS
      (constantBytes ⟨.defn ⟨.thm, .safe, 0, .sort 0, .sort 0⟩, #[], #[], #[.zero]⟩)
  let single : Env := { consts := consts1 }
  let best := fun (k : Nat) => do
    let s : Src.Ingress.Seeds := { statement := #[fS], eqns := Array.replicate k (fS, tS) }
    let mut ns := 0
    for i in [0:3] do
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure fun _ => Src.Ingress.reach single s
      let good := match r with
        | .ok rs => rs.size == 2 && rs.all fun x => x.address != tS || x.proofs
        | .error _ => false
      let dt := (← IO.monoNanosNow) - t0
      expect a good s!"the walk over {k} proposals naming one subject"
      ns := if i == 0 then dt else min ns dt
    return ns
  let n1 ← best 200000
  let n2 ← best 400000
  expect a (n2 < 3 * n1) s!"the walk over 400,000 proposals naming one subject took {n2 / 1000000} ms, \
    over three times its {n1 / 1000000} ms over 200,000"
  return #[s!"walk: a cycle, and a fixpoint of {n} proposals in {t1 - t0} ms; 200,000 and 400,000 \
    proposals naming one subject in {n1 / 1000000} and {n2 / 1000000} ms"]

def run (a : Assert) : IO (Array String) := do
  return (← proofs a) ++ (← reread a) ++ (← seeds a) ++ (← projectionRoot a) ++
    (← fullAgainstReached a) ++ (← tamperedSidecar a) ++ (← verifierSidecar a) ++ (← walk a)

end IxCCTests.Recheck.Reach
