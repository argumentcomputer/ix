import Ix.CompileCert.Entry
import Tests.Ix.Kernel.IxonFixtures

/-! Adversarial controls for direct source/reader association. Target
admission is deliberately unchanged in the source-tamper controls: they
distinguish association from merely checking a well-typed output. -/

namespace Tests.Ix.CompileCert.Direct

open _root_.Ix.CompileCert
open Tests.Ix.Kernel.IxonFixtures (address)

def sourceType : Lean.Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.bvar 2) .default) .default) .default

def sourceValue (first : Bool) : Lean.Expr :=
  .lam `α (.sort (.param `u))
    (.lam `a (.bvar 0) (.lam `b (.bvar 1) (.bvar (if first then 1 else 0)) .default) .default) .default

def sourceDef (n : Lean.Name) (value : Lean.Expr) : Lean.ConstantInfo :=
  .defnInfo {
    name := n
    levelParams := [`u]
    type := sourceType
    value := value
    hints := .opaque
    safety := .safe
    all := [n] }

def choiceRecord : Ixon.Constant :=
  let type := Ixon.Expr.leanAll (.sort 0)
    (.leanAll (.var 0) (.leanAll (.var 1) (.var 2)))
  let value := Ixon.Expr.leanLam (.sort 0)
    (.leanLam (.var 0) (.leanLam (.var 1) (.var 1)))
  ⟨.defn ⟨.defn, .safe, 1, type, value⟩, #[], #[], #[.var 0]⟩

def choiceInput : Input :=
  { source := ⟨[sourceDef `first (sourceValue true)]⟩
    roots := [`first]
    map := [⟨`first, address 71, .member (address 71) 0⟩]
    limits := ⟨1024, 1024, 1048576, 65536, 4096⟩
    records := [(address 71, Ixon.serConstant choiceRecord)]
    blobs := []
    hint := fun _ => some .opaque }

def aliases : Input :=
  { choiceInput with
    source := ⟨[sourceDef `first (sourceValue true), sourceDef `same (sourceValue true)]⟩
    roots := [`first, `same]
    map := [⟨`first, address 71, .member (address 71) 0⟩,
      ⟨`same, address 71, .member (address 71) 0⟩] }

def wrongAlias : Input :=
  { aliases with source := ⟨[sourceDef `first (sourceValue true), sourceDef `same (sourceValue false)]⟩ }

def dependent : Input :=
  { choiceInput with
    source := ⟨[sourceDef `first (sourceValue true),
      sourceDef `root (.const `first [.param `u])]⟩
    roots := [`root]
    map := choiceInput.map ++ [⟨`root, address 72, .member (address 72) 0⟩]
    records := choiceInput.records ++ [(address 72, Ixon.serConstant
      { choiceRecord with
        info := .defn ⟨.defn, .safe, 1,
          .leanAll (.sort 0) (.leanAll (.var 0) (.leanAll (.var 1) (.var 2))),
          .ref 0 #[0]⟩
        refs := #[address 71] })] }

def accepted (input : Input) : Bool := (checkCompiled input).isOk

def sourceMismatch (input : Input) : Bool :=
  match checkCompiled input with | .error .correspondence => true | _ => false

def domainMismatch (input : Input) : Bool :=
  match checkCompiled input with | .error .sourceDomain => true | _ => false

def mapMismatch (input : Input) : Bool :=
  match checkCompiled input with | .error .mapMismatch => true | _ => false

def malformedKeys (input : Input) : Bool :=
  match checkCompiled input with | .error (.malformedInput _) => true | _ => false

def outcomeClass (input : Input) (root : Lean.Name) : OutcomeClass :=
  (RootOutcome.mk root (checkRoot input root)).classification

def classificationControls : List (String × (Unit → Bool)) := [
  ("per-root certified classification", fun _ => outcomeClass choiceInput `first == .certified),
  ("per-root unsupported source classification", fun _ =>
    let source := choiceInput.source.declarations.map fun
      | .defnInfo d => Lean.ConstantInfo.defnInfo { d with safety := .unsafe }
      | ci => ci
    outcomeClass { choiceInput with source := ⟨source⟩ } `first == .unsupported),
  ("per-root missing dependency is blocked", fun _ => outcomeClass choiceInput `missing == .blocked),
  ("per-root wrong source body is rejected", fun _ => outcomeClass wrongAlias `same == .rejected),
  ("per-root malformed key is rejected", fun _ => outcomeClass
    { choiceInput with records := [(⟨ByteArray.empty⟩, Ixon.serConstant choiceRecord)] } `first == .rejected),
  ("kernel resource and unsupported declines remain distinct", fun _ =>
    admissionClass (.kernel (.notImplemented "direct sum: positivity walk fuel") 0) == .blocked &&
    admissionClass (.kernel (.notImplemented "unsupported positive shape") 0) == .unsupported)]

def controls : List (String × (Unit → Bool)) := classificationControls ++ [
  ("semantic names cover both members of a legitimate fiber", fun _ =>
    match checkCompiled aliases with
    | .error _ => false
    | .ok receipt =>
      let cx : ExportContext := ⟨aliases.source, aliases.map, receipt.pins⟩
      match cx.name `first with
      | .error _ => false
      | .ok targetName => decide (SemanticNamesAgree receipt (fun _ => targetName))),
  ("semantic names cannot borrow the checked representative for a wrong alias", fun _ =>
    match checkCompiled aliases with
    | .error _ => false
    | .ok receipt =>
      let cx : ExportContext := ⟨aliases.source, aliases.map, receipt.pins⟩
      match cx.name `first with
      | .error _ => false
      | .ok targetName =>
        !decide (SemanticNamesAgree receipt (fun name =>
          if name = sourceName `same then sourceName `wrong else targetName))),
  ("artifact aggregate rejects wrong forward name before installed comparison", fun _ =>
    match checkCompiled aliases with
    | .error _ => false
    | .ok receipt =>
      checkArtifactInstalledAssociation receipt ⟨[]⟩ (fun _ => sourceName `wrong) == some false),
  ("empty record key rejected before admission", fun _ => malformedKeys
    { choiceInput with records := [(⟨ByteArray.empty⟩, Ixon.serConstant choiceRecord)] }),
  ("short blob key rejected before admission", fun _ => malformedKeys
    { choiceInput with blobs := [(⟨ByteArray.empty⟩, ByteArray.empty)] }),
  ("short map record key rejected before lookup", fun _ => domainMismatch
    { choiceInput with map := [⟨`first, ⟨ByteArray.empty⟩, .member (address 71) 0⟩] }),
  ("short map target key rejected before lookup", fun _ => domainMismatch
    { choiceInput with map := [⟨`first, address 71, .member ⟨ByteArray.empty⟩ 0⟩] }),
  ("direct independently exported definition", fun _ => accepted choiceInput),
  ("legitimate many-to-one aliases", fun _ => accepted aliases),
  ("same-typed wrong-value alias", fun _ => sourceMismatch wrongAlias),
  ("closed direct dependency cone", fun _ => accepted dependent),
  ("unchanged root with changed dependency", fun _ => sourceMismatch
    { dependent with source := ⟨[sourceDef `first (sourceValue false),
        sourceDef `root (.const `first [.param `u])]⟩ }),
  ("missing dependency cannot be hidden", fun _ => domainMismatch
    { dependent with
      source := ⟨[sourceDef `root (.const `first [.param `u])]⟩
      map := [⟨`root, address 72, .member (address 72) 0⟩] }),
  ("duplicate source map keys", fun _ => domainMismatch
    { choiceInput with map := choiceInput.map ++ choiceInput.map }),
  ("fabricated member index", fun _ => mapMismatch
    { choiceInput with map := [⟨`first, address 71, .member (address 71) 1⟩] }),
  ("missing target record", fun _ => mapMismatch
    { choiceInput with map := [⟨`first, address 99, .member (address 71) 0⟩] }),
  ("wrong declaration kind", fun _ => sourceMismatch
    { choiceInput with source := ⟨[.opaqueInfo {
      name := `first
      levelParams := [`u]
      type := sourceType
      value := sourceValue true
      isUnsafe := false
      all := [`first] }]⟩ }),
  ("missing requested root", fun _ => domainMismatch
    { choiceInput with roots := [`missing] }),
  ("selected root ignores unrelated unsupported source", fun _ =>
    (checkRoot { choiceInput with source := ⟨choiceInput.source.declarations ++
      [.axiomInfo {
        name := `unsupported
        levelParams := []
        type := .sort .zero
        isUnsafe := true }]⟩ } `first).isOk),
  ("selected root retains changed dependency", fun (_ : Unit) =>
    match checkRoot { dependent with source := ⟨[sourceDef `first (sourceValue false),
        sourceDef `root (.const `first [.param `u])]⟩ } `root with
    | .error (.certification .correspondence) => true
    | _ => false),
  ("selection preserves source cycles", fun _ =>
    (selectSource ⟨[sourceDef `a (.const `b [.param `u]),
      sourceDef `b (.const `a [.param `u])]⟩ [`a]).isOk),
  ("selection refuses insufficient rounds", fun _ =>
    !(selectSource dependent.source [`root] 0).isOk),
  ("per-root coverage retains unsupported outcome", fun _ =>
    let input := { choiceInput with roots := [`first, `missing] }
    let outcomes : List (RootOutcome input) := checkRoots input
    outcomes.length == 2 &&
      (outcomes[0]?.map (fun (r : RootOutcome input) => r.result.isOk)).getD false &&
      !(outcomes[1]?.map (fun (r : RootOutcome input) => r.result.isOk)).getD true),
  ("allowed definition hint difference", fun _ =>
    accepted { choiceInput with hint := fun _ => some (.regular 7) }),
  ("hint difference cannot hide wrong value", fun _ =>
    sourceMismatch { wrongAlias with hint := fun _ => some (.regular 7) }),
  ("Ix cached hash is not structural identity", fun _ =>
    match ixExpr (.bvar 0 (address 1)), ixExpr (.bvar 1 (address 1)) with
    | .ok (.bvar 0), .ok (.bvar 1) => true
    | _, _ => false),
  ("Ix differing cached hashes do not alter structure", fun _ =>
    match ixExpr (.bvar 0 (address 1)), ixExpr (.bvar 0 (address 2)) with
    | .ok (.bvar 0), .ok (.bvar 0) => true
    | _, _ => false),
  ("Ix semantic metadata explicitly unsupported", fun _ =>
    !(ixExpr (.mdata #[] (.bvar 0 (address 1)) (address 1))).isOk),
  ("source capture rejects mismatched lookup identity", fun _ =>
    !(captureCone (fun _ => some (sourceDef `different (sourceValue true))) [`first] 8).isOk),
  ("literal support cannot disappear from source closure", fun _ =>
    (exprRefs (.lit (.natVal 4))).contains `Nat &&
      (exprRefs (.lit (.strVal "x"))).contains `String.ofList) ]

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  if failed != 0 then throw (IO.userError s!"{failed}/{controls.length} C1 controls failed")

end Tests.Ix.CompileCert.Direct
