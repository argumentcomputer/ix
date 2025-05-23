import Ix.Aiur.Term
import Ix.SmallMap

namespace Aiur

abbrev TermId := Nat
abbrev UniqTerm := TermId × Term

inductive SPattern
  | primitive : Primitive → SPattern
  | ref : Global → Array Local → SPattern
  | tuple : Array Local → SPattern
  deriving BEq, Hashable, Inhabited

structure Clause where
  pat : SPattern
  guards : Array (Pattern × UniqTerm)
  body : UniqTerm
  deriving Inhabited

structure ExtTerm where
  renames : Array (Local × Term)
  value : Term
  deriving Inhabited

def ExtTerm.modifyRenames (t : ExtTerm) (f : Array (Local × Term) → Array (Local × Term)) : ExtTerm :=
  { t with renames := f t.renames }

structure Row where
  clauses : Array Clause
  body : ExtTerm
  uniqId : TermId
  deriving Inhabited

structure Diagnostics where
  missing : Bool
  reachable : List Term

structure Compiler where
  uniqId : TermId
  decls : Decls
  diagnostics : Diagnostics

abbrev CompilerM := StateM Compiler

def setId (id : TermId) : CompilerM Unit :=
  modify fun stt => { stt with uniqId := id }

def newId : CompilerM TermId := do
  let varId ← Compiler.uniqId <$> get
  modify fun stt => { stt with uniqId := stt.uniqId + 1 }
  pure varId

def dnfProd (branches: List $ Pattern × UniqTerm) (body : ExtTerm) : CompilerM (Array Row) := do
  let initId ← Compiler.uniqId <$> get
  let rec aux := fun renames clauses branches body => match branches with
    | [] => do
      let id ← Compiler.uniqId <$> get
      let row := ⟨clauses, { body with renames := body.renames ++ renames }, id⟩
      setId initId
      pure #[row]
    | (.or patL patR, term) :: rest => do
      let rowsL ← aux renames clauses ((patL, term) :: rest) body
      let rowsR ← aux renames clauses ((patR, term) :: rest) body
      pure $ rowsL ++ rowsR
    | (.wildcard, _) :: rest => aux renames clauses rest body
    | (.var var, (_, term)) :: rest => aux (renames.push (var, term)) clauses rest body
    | (.primitive prim, term) :: rest => aux renames (clauses.push ⟨.primitive prim, #[], term⟩) rest body
    | (.tuple args, term) :: rest => do
      let (vars, guards) ← flattenArgs args
      let clause := ⟨.tuple vars, guards, term⟩
      aux renames (clauses.push clause) rest body
    | (.ref global args, term) :: rest => do
      let (vars, guards) ← flattenArgs args.toArray
      let clause := ⟨.ref global vars, guards, term⟩
      aux renames (clauses.push clause) rest body
  aux Array.empty Array.empty branches body
where
  flattenArgs args := do
    let varIds ← args.mapM fun _ => newId
    let guards := args.zip varIds |>.map fun (arg, id) => (arg, (id, .var (.idx id)))
    pure (varIds.map .idx, guards)

def toRows (clause : Pattern × UniqTerm) : ExtTerm → CompilerM (Array Row) :=
  dnfProd [clause]

inductive Decision
  | success : ExtTerm → Decision
  | failure
  | switch : Local → List (SPattern × Decision) → Decision → Decision
  | let : Local → Term → Decision → Decision
  deriving Inhabited

def modifyDiagnostics (f : Diagnostics → Diagnostics) : CompilerM Unit :=
  modify fun stt => { stt with diagnostics := f stt.diagnostics }

def patTypeLength (decls : Decls) : SPattern → Nat
  | .primitive (.u1 _) => 2
  | .primitive (.u8 _) => UInt8.size
  | .primitive (.u16 _) => UInt16.size
  | .primitive (.u32 _) => UInt32.size
  | .primitive (.u64 _) => UInt64.size
  | .tuple _ => 1
  | .ref global _ => typeLookup global |>.constructors.length
where
  typeLookup (global : Global) :=
    match global.popNamespace with
    | some (_, enum) => match decls.getByKey enum with
      | some (.dataType typ) => typ
      | _ => unreachable!
    | none => unreachable!

def extractSPatterns (rows : Array Row) (term : UniqTerm) : SmallMap SPattern (Array Row) :=
  rows.foldl (init := default) processRow
where
  processRow map row := row.clauses.foldl (init := map) processClause
  processClause map clause :=
    if term.fst == clause.body.fst then map.insert clause.pat #[] else map

def removeFirstInstance (find : α → Bool) (vec : Array α) : Option (α × Array α) :=
  match h : vec.findIdx? find with
  | none => none
  | some i =>
    let filtered := vec.extract 0 i ++ vec.extract (i + 1) vec.size
    have := Array.findIdx?_eq_some_iff_findIdx_eq.mp h |>.left
    some (vec[i], filtered)

def rowRemoveClause (row : Row) (term : UniqTerm) : Option (Clause × Row) :=
  let id := term.fst
  match removeFirstInstance (·.body.fst == id) row.clauses with
  | some (deletedClause, restClauses) => some (deletedClause, { row with clauses := restClauses })
  | none => none

def switch (cases : List (SPattern × Decision)) (fallback : Decision) : UniqTerm → Decision
  | (_, .var var) => .switch var cases fallback
  | (id, term) => let var := .idx id; .let var term (.switch var cases fallback)

mutual

partial def compileSwitch (rows : Array Row) (term : UniqTerm) : CompilerM Decision := do
  let stt ← get
  let numCases := patTypeLength stt.decls rows[0]!.clauses[0]!.pat
  let spatMap := extractSPatterns rows term
  let size := spatMap.size
  assert! size <= numCases
  if size == numCases then
    let (rowMap, _) ← rows.foldlM (init := (spatMap, #[])) processRow
    let cases ← rowMap.toList.mapM fun (pat, rows) => Prod.mk pat <$> compileRows rows
    setId stt.uniqId
    pure $ switch cases .failure term
  else
    let (rowMap, fallbackRows) ← rows.foldlM (init := (spatMap, #[])) processRow
    let cases ← rowMap.toList.mapM fun (pat, rows) => Prod.mk pat <$> compileRows rows
    let fallback ← compileRows fallbackRows
    setId stt.uniqId
    pure $ switch cases fallback term
where
  processRow pair row :=
    let (rowMap, fallbackRows) := pair
    match rowRemoveClause row term with
    | some (clause, row') => do
      setId row.uniqId
      let newRows ← dnfProd clause.guards.toList row'.body
      let newRows := newRows.map (fun r => { r with clauses := r.clauses ++ row'.clauses })
      let updatedMap := rowMap.update clause.pat (· ++ newRows)
      pure (updatedMap, fallbackRows)
    | none => pure (rowMap.map (·.push row), fallbackRows.push row)

partial def compileRows (rows : Array Row) : CompilerM Decision :=
  match rows[0]? with
  | some row => match row.clauses[0]? with
    | some clause => compileSwitch rows clause.body
    | none => do
      modifyDiagnostics fun d => { d with reachable := row.body.value :: d.reachable }
      pure $ .success row.body
  | none => do
    modifyDiagnostics fun d => { d with missing := true }
    pure .failure

end

def compile (term : Term) (rules : List (Pattern × Term)) : CompilerM (Decision × Diagnostics) := do
  let id ← newId
  let rows ← rules.foldlM (init := #[]) fun acc rule => do
    let newRows ← fromRule id rule
    pure $ acc ++ newRows
  let tree ← compileRows rows
  let diagnostics ← Compiler.diagnostics <$> get
  pure (tree, diagnostics)
where
  fromRule id rule :=
    let (pat, bod) := rule
    toRows (pat, (id, term)) ⟨#[], bod⟩

def runWithNewCompiler (typs : Decls) (f : CompilerM α) : α :=
  StateT.run' f ⟨0, typs, ⟨false, []⟩⟩

def runMatchCompiler (typs : Decls) (term : Term) (rules : List (Pattern × Term)) :
    Decision × Diagnostics :=
  runWithNewCompiler typs (compile term rules)

def spatternToPattern : SPattern → Pattern
  | .primitive prim => .primitive prim
  | .ref global vars => .ref global (vars.map .var).toList
  | .tuple vars => .tuple (vars.map .var)

mutual

partial def branchesToTerm (branches : List (SPattern × Decision)) (dec : Decision) :
    List (Pattern × Term) :=
  let toTerm := fun (spat, tree) =>
    decisionToTerm tree >>= fun term => some (spatternToPattern spat, term)
  match decisionToTerm dec with
  | some defTerm => branches.filterMap toTerm ++ [(Pattern.wildcard, defTerm)]
  | none => branches.filterMap toTerm

partial def decisionToTerm : Decision → Option Term
  | .success ⟨renames, value⟩ =>
    some $ renames.foldr (init := value) fun (x, y) acc => .let (.var x) y acc
  | .switch var branches dec => some $ .match (.var var) (branchesToTerm branches dec)
  | .let var term body => do
    let body' ← decisionToTerm body
    some $ .let (.var var) term body'
  | .failure => none

end

end Aiur
