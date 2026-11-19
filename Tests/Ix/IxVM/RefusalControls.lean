import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.RefusalControlsDefs


/-! # Negative controls for the program's later refusals

Each case reaches one assertion of the declaration checker, of role validation or of the
field classifier, with the control that shows which assertion it is. A case names the claim
form and the validator it runs under: a typing claim that validates its binding
(`assumed = false`), one that assumes it (`assumed = true`), or the binding claim.

* **A role at a member of a mutual or nested block.** `List`'s roles bound at a two-type
  block that holds `List`'s own type and constructors: refused at the type and at a
  constructor, by the binding claim and by typing claims under both validators.
* **A bound operation that is not a record of its own.** `Nat.pred` bound at a projection of a
  one-member definition block: refused by the binding claim.
* **A former that is not convertible with its telescope.** A family `T : A 2 3` whose former
  `A` is bound to `Nat.add`'s role: the telescope is read by unfolding `A`, conversion
  computes the sum instead. Refused under an assumed binding; under the default table the
  same family is accepted.
* **The field classifier.** A `Prop` structure whose field's type has a declared type headed
  by a projection, one whose field type is a primitive projection, and one whose field type's
  declared type takes 10,000 head steps to reach its sort (9,999 are accepted).
* **A projection out of a proof.** The data field of a `Prop` structure is refused; a
  proposition's propositional field is accepted through the checked guard.
* **A table that binds type-only anchors at adversarial records.** `True` bound at a
  definition of `False`, `True.intro` and `Lean.trustCompiler` at axioms of that type: the
  binding claim is accepted, and a theorem of `False` by the axiom is refused under both
  validators.
* **A role at a recursor of a mutual family.** `Iff.rec`'s role bound at the recursor: the
  family check refuses the typing claim whether it assumes the binding or validates it, and
  the binding claim for the table is refused; under the default table the typing claim is
  accepted.
* **Inert declarations.** Two blocks that are not strictly positive, each with a model of unit
  types and an empty recursor family: accepted as declarations, and refused at a projection.
* **A pinned basis record as the seed.** `Nat.rec` and `Nat` are accepted. -/

namespace Tests.Ix.IxVM.RefusalControls

open IxVM.ClaimHarness

abbrev E := Ixon.Expr

/-! ## Helpers -/

private def put (env : Ixon.Env) (c : Ixon.Constant)
    (hint : Lean.ReducibilityHints := .opaque) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.serConstant c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a hint }
    | _ => env
  (env, a)

private def prj (info : Ixon.ConstantInfo) : Ixon.Constant := ⟨info, #[], #[], #[], #[]⟩

/-- A safe constructor, the first of its type, with inherited field modes. -/
private def ctor (fields : UInt64) (typ : E) (params : UInt64 := 0) : Ixon.Constructor :=
  { isUnsafe := false, lvls := 0, cidx := 0, params, fields, typ }

private def base : Except String Ixon.Env := do
  withRoleTable {} (← Ix.Kernel.Reader.defaultTableBytes)

/-- `table` with the roles of `pairs` bound at their addresses. -/
private def rebind (table : Ix.Kernel.RoleTable) (pairs : List (Ix.Kernel.Role × Address)) : Ix.Kernel.RoleTable :=
  { table with bound := table.bound.map fun (r, a) => (r, (pairs.lookup r).getD a) }

/-- `env` bound to `table`, once the table is well formed. -/
private def bound (env : Ixon.Env) (table : Ix.Kernel.RoleTable) : Except String Ixon.Env := do
  table.check
  withRoleTable env table.toBytes

private def typing (label : String) (env : Ixon.Env) (target : Address) (assumed accept : Bool)
    (reject : Option String := none) : Except String Case := do
  let some binding := env.roleBinding | throw "missing role binding"
  let ctx ← Ix.ClaimContext.ofBinding binding.address assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  Case.ofClaim s!"{how}: {label}" env (.check ctx target none) {} accept reject

private def bindingClaim (label : String) (env : Ixon.Env) (accept : Bool)
    (reject : Option String := none) : Except String Case := do
  let some binding := env.roleBinding | throw "missing role binding"
  Case.ofClaim s!"binding: {label}" env (.binding (← Ix.SpecDigest.specDigest) binding.address)
    {} accept reject

private def addressOf (table : Ix.Kernel.RoleTable) (r : Ix.Kernel.Role) : Except String Address :=
  match table.addressOf? r with
  | some a => pure a
  | none => throw s!"the default table does not bind {repr r}"

/-! ## A role at a member of a mutual or nested block -/

private def modeledInductive : String := "a modeled inductive is bound to a role"
private def modeledConstructor : String := "a modeled constructor is bound to a role"

/-- `List`'s block with a second type of `List`'s type and no constructor: a two-type block,
whose members the program checks on the modeled route. The first type keeps `List`'s type and
constructors, so each has the type its role specifies once `List`'s role is bound at it. The
new type's binder data are the first type's. Returns the type, `nil` and `cons`. -/
private def twoTypeList (env : Ixon.Env) (table : Ix.Kernel.RoleTable) :
    Except String (Ixon.Env × Address × Address × Address) := do
  let listA ← addressOf table .list
  let some lw := env.getConst? listA | throw "List's record is missing"
  let .iPrj lp := lw.info | throw "List is not a projection of an inductive block"
  let some lb := env.getConst? lp.block | throw "List's block is missing"
  let .muts ms := lb.info | throw "List's block is not a mutual record"
  unless ms.size == 1 && lp.idx == 0 do throw "List's block has more than one member"
  let some (Ixon.MutConst.indc ind) := ms[(0 : Nat)]? | throw "List's member is not an inductive"
  let some typeData := lb.binders.find? fun b => !b.shared && b.index == 0
    | throw "List's type carries no binder data"
  let peerRoot := (1 + ind.ctors.size).toUInt64
  let binders := lb.binders.filter (!·.shared) ++ #[{ typeData with index := peerRoot }] ++
    lb.binders.filter (·.shared)
  let block : Ixon.Constant :=
    { lb with info := .muts #[.indc ind, .indc { ind with ctors := #[] }], binders }
  let (env, b) := put env block
  let (env, l) := put env (prj (.iPrj ⟨0, b⟩))
  let (env, _) := put env (prj (.iPrj ⟨1, b⟩))
  let (env, nil) := put env (prj (.cPrj ⟨0, 0, b⟩))
  let (env, cons) := put env (prj (.cPrj ⟨0, 1, b⟩))
  return (env, l, nil, cons)

/-- The cases of a role at a modeled member. `which`: 0 the binding claim with all three
roles rebound; 1 a typing claim on the type with all three rebound; 2 a typing claim on the
type with `List.nil`'s role alone rebound; 3 a typing claim on the constructor with that
table; 4 the type under the default table. -/
private def roleCase (which : Nat) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let (env, l, nil, cons) ← twoTypeList env table
  match which with
  | 0 =>
    let env ← bound env (rebind table [(.list, l), (.listNil, nil), (.listCons, cons)])
    bindingClaim "List's roles at a two-type block" env false (some modeledInductive)
  | 1 =>
    let env ← bound env (rebind table [(.list, l), (.listNil, nil), (.listCons, cons)])
    typing "List's role at a type of a two-type block, the type claimed" env l assumed false
      (some modeledInductive)
  | 2 =>
    let env ← bound env (rebind table [(.listNil, nil)])
    typing "List.nil's role at a constructor of a two-type block, the type claimed" env l
      assumed false (some modeledConstructor)
  | 3 =>
    let env ← bound env (rebind table [(.listNil, nil)])
    typing "List.nil's role at a constructor of a two-type block, the constructor claimed" env
      nil assumed false (some modeledConstructor)
  | _ =>
    -- the same block with no role at it: refused later, for want of a model
    typing "the two-type block under the default table" env l assumed false
      (some "no model advice for a mutual or nested block")

/-! ## A bound operation that is not a record of its own -/

private def standaloneOperation : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let a ← addressOf table .natPred
  let some c := env.getConst? a | throw "Nat.pred's record is missing"
  let .defn d := c.info | throw "Nat.pred's record is not a definition record"
  let (env, b) := put env { c with info := .muts #[.defn d] }
  let (env, p) := put env (prj (.dPrj ⟨0, b⟩))
  let env ← bound env (rebind table [(.natPred, p)])
  bindingClaim "Nat.pred's role at a projection of a one-member definition block" env false
    (some "a bound operation is not a standalone definition")

/-! ## A former that is not convertible with its telescope -/

private def notConvertible : String :=
  "a former declared at a definition is not convertible with its telescope"

/-- `A : Nat → Nat → Type 1 := fun _ _ => Nat → Type` and the family `T : A 2 3` with one
index and no constructor. With `rebound`, `Nat.add`'s role is bound at `A`: conversion then
computes `A 2 3` as a sum. `mode`: 0 binding assumed, 1 binding validated. -/
private def formerCase (rebound assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let nat ← addressOf table .nat
  let natE : E := .ref 0 #[]
  let aliasRecord ← _root_.IxVM.RecordSections.withSection env
    ⟨.defn ⟨.defn, .safe, {}, 0, .all natE (.all natE (.sort 1)),
        .lam natE (.lam natE (.all natE (.sort 0)))⟩,
      #[], #[nat], #[.succ .zero, .succ (.succ .zero)], #[]⟩
  let (env, a) := put env aliasRecord .abbrev
  let (env, two) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 2))
  let (env, three) := env.storeBlob (ByteArray.mk (Nat.toBytesLE 3))
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 1,
    typ := .app (.app (.ref 0 #[]) (.nat 1)) (.nat 2), ctors := #[] }
  let (env, b) := put env ⟨.muts #[.indc family], #[], #[a, two, three], #[], #[]⟩
  let (env, t) := put env (prj (.iPrj ⟨0, b⟩))
  if rebound then
    let env ← bound env (rebind table [(.natAdd, a)])
    -- validated, the binding is refused when the native rule first asks for the role
    typing "a family whose former is bound to Nat.add's role" env t assumed false
      (if assumed then some notConvertible else none)
  else
    let c ← typing "a family whose former is an unbound definition applied to literals" env t
      assumed true
    return { c with exercises := some "KernelCheck::former_tele_at" }

/-! ## The field classifier -/

private def defs (n : String) : Lean.Name := `Tests.Ix.IxVM.RefusalControlsDefs ++ n.toName

/-- A claim on the compiled constant `n`. -/
private def compiled (env : Ixon.Env) (n : String) (assumed accept : Bool)
    (reject : Option String := none) (exercises : Option String := none) : Except String Case := do
  let some target := env.getAddr? (Ix.Name.fromLeanName (defs n))
    | throw s!"{defs n} is not in the Ixon environment"
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  let c ← Case.ofClaim s!"{how}: {n}" env (.check ctx target none) {} accept reject
  return { c with exercises }

/-- `W (p : Prop × Prop) : Prop | mk : p.1 → W p`, the field's type a primitive projection. -/
private def projectionField (env : Ixon.Env) (assumed : Bool) : Except String Case := do
  let some prod := env.getAddr? (Ix.Name.fromLeanName ``Prod) | throw "Prod is not compiled"
  let pair : E := .app (.app (.ref 0 #[0, 0]) (.sort 0)) (.sort 0)
  let ctorType : E := .all pair (.all (.prj 0 0 (.var 0)) (.app (.recur 0 #[]) (.var 1)))
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 1, indices := 0, typ := .all pair (.sort 0),
    ctors := #[ctor 1 ctorType (params := 1)] }
  -- binder data: `W`'s type lands in `Type`; the constructor's two binders bind into `W p`
  let block : Ixon.Constant := ⟨.muts #[.indc family], #[], #[prod], #[.zero],
    #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.zero {}, .zero {}]⟩]⟩
  let (env, b) := put env block
  let (env, w) := put env (prj (.iPrj ⟨0, b⟩))
  let (env, _) := put env (prj (.cPrj ⟨0, 0, b⟩))
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  Case.ofClaim s!"{how}: a Prop structure whose field type is a primitive projection" env
    (.check ctx w none) {} false (some "field classifier: unsupported field type")

/-- `let x : Type := …; x` nested `n` deep around `Prop`. -/
private def lets : Nat → E
  | 0 => .sort 0
  | n + 1 => .leanLet false (.sort 1) (lets n) (.var 0)

/-- `Q : (n nested lets around Prop) := True` and `W : Prop | mk : Q → W`: the classifier
reaches the sort of `Q`'s declared type in `n + 1` head steps. -/
private def depthCase (n : Nat) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let trueA ← addressOf table .true
  let (env, q) := put env ⟨.defn ⟨.defn, .safe, {}, 0, lets n, .ref 0 #[]⟩, #[], #[trueA],
    #[.zero, .succ .zero], #[]⟩
  let family : Ixon.Inductive := {
    isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
    ctors := #[ctor 1 (.all (.ref 0 #[]) (.recur 0 #[]))] }
  let (env, b) := put env ⟨.muts #[.indc family], #[], #[q], #[.zero],
    #[⟨false, 1, 0, #[.zero {}]⟩]⟩
  let (env, w) := put env (prj (.iPrj ⟨0, b⟩))
  let (env, _) := put env (prj (.cPrj ⟨0, 0, b⟩))
  let limit := 10000
  typing s!"a Prop structure whose field's sort is {n} lets deep" env w assumed (n < limit)
    (if n < limit then none else some "field classifier: head depth exceeded")

/-! ## A projection out of a proof -/

/-- `boxValue` with its value replaced by the projection of `PropBox`'s data field. -/
private def dataOutOfProof (env : Ixon.Env) (assumed : Bool) : Except String Case := do
  let some a := env.getAddr? (Ix.Name.fromLeanName (defs "boxValue")) | throw "boxValue is not compiled"
  let some box := env.getAddr? (Ix.Name.fromLeanName (defs "PropBox")) | throw "PropBox is not compiled"
  let some c := env.getConst? a | throw "boxValue's record is missing"
  let .defn d := c.info | throw "boxValue is not a definition record"
  let some i := c.refs.findIdx? (· == box) | throw "boxValue's record does not reference PropBox"
  let .lam ty _ := d.value | throw "boxValue's value is not a λ"
  let (env, p) := put env { c with info := .defn { d with value := .lam ty (.prj i.toUInt64 0 (.var 0)) } }
  let ctx ← Ix.ClaimContext.ofEnv env assumed
  let how := if assumed then "typing, binding assumed" else "typing, binding validated"
  Case.ofClaim s!"{how}: the data field of a Prop structure projected out of a proof" env
    (.check ctx p none) {} false (some "projection on a Prop structure: the field's guard is not zero")

/-! ## A table that binds type-only anchors at adversarial records -/

private def nonStandardAxiom : String := "an axiom that is not one of Lean's standard axioms"

/-- `True`'s role at `T' : Prop := False`, `True.intro`'s and `Lean.trustCompiler`'s at two
axioms of type `T'`. `which`: 0 the binding claim; 1 the theorem `bad : False := evil`. -/
private def anchorTable (which : Nat) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let falseA ← addressOf table .false
  let (env, t') := put env ⟨.defn ⟨.defn, .safe, {}, 0, .sort 0, .ref 0 #[]⟩, #[], #[falseA],
    #[.zero], #[]⟩
  let (env, evil) := put env ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[t'], #[], #[]⟩
  let (env, evil2) := put env ⟨.axio ⟨false, 0, .share 0⟩, #[.ref 0 #[]], #[t'], #[], #[]⟩
  let (env, bad) := put env ⟨.defn ⟨.thm, .safe, {}, 0, .ref 0 #[], .ref 1 #[]⟩, #[],
    #[falseA, evil], #[], #[]⟩
  let env ← bound env (rebind table [(.true, t'), (.trueIntro, evil), (.trustCompiler, evil2)])
  match which with
  | 0 => bindingClaim "True at a definition of False, True.intro at an axiom of it" env true
  | _ => typing "False by the axiom bound at True.intro" env bad assumed false (some nonStandardAxiom)

/-! ## A covered role at a recursor of a mutual family -/

/-- `Iff.rec`'s role bound at `TA.rec`, the recursor of a mutual pair. `which`: 0 `taIota`
under the default table (the recursor is walked); 1 `taIota` under the table; 2 the binding
claim for the table. -/
private def coveredRecursor (env : Ixon.Env) (which : Nat) (assumed : Bool) : Except String Case := do
  let table ← Ix.Kernel.Reader.defaultTable
  let some x := env.getAddr? (Ix.Name.fromLeanName (defs "TA.rec")) | throw "TA.rec is not compiled"
  let some target := env.getAddr? (Ix.Name.fromLeanName (defs "taIota")) | throw "taIota is not compiled"
  match which with
  | 0 =>
    -- the family check runs at the recursor, which the default table binds to no role
    typing "a reduction through a mutual family's recursor, the default table" env target assumed
      true
  | 1 =>
    let env ← bound env (rebind table [(.iffRec, x)])
    -- the family check refuses a family whose recursor is bound to a role, whether or not the
    -- binding is validated
    typing "a reduction through a mutual family's recursor bound at Iff.rec's role" env target
      assumed false (some "a modeled recursor is bound to a role")
  | _ =>
    let env ← bound env (rebind table [(.iffRec, x)])
    bindingClaim "Iff.rec's role at a mutual family's recursor" env false

/-! ## Inert declarations

A block of the modeled route is checked against a model the witness supplies. A model whose
types are `PUnit`, whose constructors are constant, and whose recursor family is the empty
block has every type the check asks for, whatever the block's constructors say: positivity
is not checked on this route. Such a block is accepted as a declaration and is inert:
nothing eliminates it. -/

private def modeledProjection : String := "projection on a member of a mutual or nested block"

/-- The model payload of `Ix.IxVM.Model.Payload`. -/
private def payload (family : Address) (advice : Array Address)
    (witnesses : Array (Address × Nat × List Nat × List Nat))
    (typeModels ctorModels : Array Address) : ByteArray :=
  ({ recBlock := family, advice, witnesses, typeModels, ctorModels, recModels := #[],
     iotas := #[] } : _root_.IxVM.Model.Payload).ser

/-- `env` with `block`'s payload and the records the payload names. -/
private def withModel (env : Ixon.Env) (block : Address) (bytes : ByteArray)
    (records : Array (Address × Ixon.Constant)) : Ixon.Env :=
  { env with
    models := env.models.insert block bytes
    modelRecords := records.foldl (fun m (a, c) => m.insert a c) env.modelRecords
    modelHints := records.foldl (fun m (a, c) => match c.info with
      | .defn _ => m.insert a .abbrev
      | _ => m) env.modelHints
    modelDeps := env.modelDeps.insert block (records.map (·.1))
    modelsAttached := true }

private def addr (c : Ixon.Constant) : Address := Address.blake3 (Ixon.serConstant c)

/-- The recursor family with no recursor. -/
private def emptyFamily : Ixon.Constant := ⟨.muts #[], #[], #[], #[], #[]⟩

/-- `U : Type := PUnit.{1}`. -/
private def unitModel (punit : Address) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, {}, 0, .sort 0, .ref 0 #[0]⟩, #[], #[punit], #[.succ .zero], #[]⟩

/-- `mutual A | mk : B → A; B | mk : (A → False) → B end` with its unit model. `which`: 0 the
type `A`; 1 `fun a => a.1`, a projection at `A`. -/
private def inertMutual (which : Nat) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let falseA ← addressOf table .false
  let punit ← addressOf table .punit
  let unit ← addressOf table .punitUnit
  let block : Ixon.Constant := ⟨.muts #[
      .indc ⟨false, 0, 0, 0, .sort 0, #[ctor 1 (.all (.recur 1 #[]) (.recur 0 #[]))]⟩,
      .indc ⟨false, 0, 0, 0, .sort 0,
        #[ctor 1 (.all (.all (.recur 0 #[]) (.ref 0 #[])) (.recur 1 #[]))]⟩],
    #[], #[falseA], #[.succ .zero],
    #[⟨false, 1, 0, #[.never {}]⟩, ⟨false, 3, 0, #[.never {}, .zero {}]⟩]⟩
  let (env, b) := put env block
  let (env, a) := put env (prj (.iPrj ⟨0, b⟩))
  let (env, bb) := put env (prj (.iPrj ⟨1, b⟩))
  let (env, _) := put env (prj (.cPrj ⟨0, 0, b⟩))
  let (env, _) := put env (prj (.cPrj ⟨1, 0, b⟩))
  -- the model: both types `U`, `A.mk' : U → U`, `B.mk' : (U → False) → U`
  let u := unitModel punit
  let uA := addr u
  let mkA : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0, .all (.ref 0 #[]) (.ref 0 #[]),
      .lam (.ref 0 #[]) (.ref 1 #[0])⟩, #[], #[uA, unit], #[.succ .zero],
    #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
  let mkB : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0,
      .all (.all (.ref 0 #[]) (.ref 1 #[])) (.ref 0 #[]),
      .lam (.all (.ref 0 #[]) (.ref 1 #[])) (.ref 2 #[0])⟩, #[], #[uA, falseA, unit],
    #[.succ .zero],
    #[⟨false, 0, 0, #[.never {}, .zero {}]⟩, ⟨false, 1, 0, #[.never {}, .zero {}]⟩]⟩
  let bytes := payload (addr emptyFamily) #[uA, addr mkA, addr mkB]
    #[(punit, 0, [], []), (unit, 0, [], []), (falseA, 1, [1], [])]
    #[uA, uA] #[addr mkA, addr mkB]
  let modelRecs := #[(uA, u), (addr mkA, mkA), (addr mkB, mkB), (addr emptyFamily, emptyFamily)]
  match which with
  | 0 =>
    let env := withModel env b bytes modelRecs
    typing "a mutual pair with a negative occurrence, modeled by unit types" env a assumed true
  | _ =>
    let (env, p) := put env ⟨.defn ⟨.defn, .safe, {}, 0, .all (.ref 0 #[]) (.ref 1 #[]),
        .lam (.ref 0 #[]) (.prj 0 0 (.var 0))⟩, #[], #[a, bb], #[],
      #[⟨false, 0, 0, #[.never {}]⟩, ⟨false, 1, 0, #[.never {}]⟩]⟩
    let env := withModel env b bytes modelRecs
    typing "a projection at the mutual pair with a negative occurrence" env p assumed false
      (some modeledProjection)

/-- `I : Type → Type | mk : I Nat` and `Bad | mk : (I Bad → Nat) → (Bad → False) → Bad`, a
one-type block that the occurrence in `I`'s index routes to the model check, with its unit
model. `which`: 0 `I`; 1 `Bad`; 2 `fun b => b.2 b : Bad → False`. -/
private def inertIndexed (which : Nat) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let falseA ← addressOf table .false
  let nat ← addressOf table .nat
  let punit ← addressOf table .punit
  let unit ← addressOf table .punitUnit
  let iBlock : Ixon.Constant := ⟨.muts #[
      .indc ⟨false, 0, 0, 1, .all (.sort 0) (.sort 0),
        #[ctor 0 (.app (.recur 0 #[]) (.ref 0 #[]))]⟩],
    #[], #[nat], #[.succ .zero], #[⟨false, 0, 0, #[.never {}]⟩]⟩
  let (env, ib) := put env iBlock
  let (env, i) := put env (prj (.iPrj ⟨0, ib⟩))
  let (env, _) := put env (prj (.cPrj ⟨0, 0, ib⟩))
  -- mk : (I Bad → Nat) → (Bad → False) → Bad; references: I, Nat, False
  let mkType (bad : E) : E :=
    .all (.all (.app (.ref 0 #[]) bad) (.ref 1 #[])) (.all (.all bad (.ref 2 #[])) bad)
  let block : Ixon.Constant := ⟨.muts #[
      .indc ⟨false, 0, 0, 0, .sort 0, #[ctor 2 (mkType (.recur 0 #[]))]⟩],
    #[], #[i, nat, falseA], #[.succ .zero],
    #[⟨false, 1, 0, #[.never {}, .never {}, .never {}, .zero {}]⟩]⟩
  let (env, b) := put env block
  let (env, bad) := put env (prj (.iPrj ⟨0, b⟩))
  let (env, _) := put env (prj (.cPrj ⟨0, 0, b⟩))
  -- the model: `Bad' := U`, `mk' : (I U → Nat) → (U → False) → U`; references: I, Nat, False, U, unit
  let u := unitModel punit
  let uA := addr u
  let mk : Ixon.Constant := ⟨.defn ⟨.defn, .safe, {}, 0, mkType (.ref 3 #[]),
      .lam (.all (.app (.ref 0 #[]) (.ref 3 #[])) (.ref 1 #[]))
        (.lam (.all (.ref 3 #[]) (.ref 2 #[])) (.ref 4 #[0]))⟩,
    #[], #[i, nat, falseA, uA, unit], #[.succ .zero],
    #[⟨false, 0, 0, #[.never {}, .never {}, .never {}, .zero {}]⟩,
      ⟨false, 1, 0, #[.never {}, .never {}, .never {}, .zero {}]⟩]⟩
  let bytes := payload (addr emptyFamily) #[uA, addr mk]
    #[(punit, 0, [], []), (unit, 0, [], []), (nat, 0, [], []), (i, 1, [1], []), (falseA, 1, [3], [])]
    #[uA] #[addr mk]
  let modelRecs := #[(uA, u), (addr mk, mk), (addr emptyFamily, emptyFamily)]
  match which with
  | 0 =>
    let env := withModel env b bytes modelRecs
    typing "an indexed family I : Type → Type with one constructor at Nat" env i assumed true
  | 1 =>
    let env := withModel env b bytes modelRecs
    typing "a type with a negative occurrence, nested in an index, modeled by a unit type" env bad
      assumed true
  | _ =>
    let (env, p) := put env ⟨.defn ⟨.defn, .safe, {}, 0, .all (.ref 0 #[]) (.ref 1 #[]),
        .lam (.ref 0 #[]) (.app (.prj 0 1 (.var 0)) (.var 0))⟩, #[], #[bad, falseA], #[],
      #[⟨false, 0, 0, #[.zero {}]⟩, ⟨false, 1, 0, #[.zero {}]⟩]⟩
    let env := withModel env b bytes modelRecs
    typing "a projection at the type with a negative occurrence nested in an index" env p assumed
      false (some modeledProjection)

/-! ## A pinned basis record as the seed -/

private def basisSeed (role : Ix.Kernel.Role) (assumed : Bool) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let a ← addressOf table role
  typing s!"the pinned basis record of {repr role} as the seed" env a assumed true

/-! ## The suite -/

private def compiledNames : Array Lean.Name :=
  #[``Prod, defs "PropBox", defs "boxValue", defs "andFst", defs "TA", defs "TA.rec",
    defs "taIota"]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let missing := (compiledNames.push (defs "HeadProj")).filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-refusal-controls] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv compiledNames leanEnv
  -- compiled on its own: if the compiler declines the structure, only its case is lost
  let headEnv? : Except String Ixon.Env ← try
      pure (.ok (← loadSharedIxonEnv #[defs "HeadProj"] leanEnv))
    catch e => pure (.error s!"HeadProj did not compile: {e}")
  let mut cases : Array Builder := #[fun _ => roleCase 0 false, fun _ => standaloneOperation]
  for assumed in [false, true] do
    for which in [1, 2, 3, 4] do
      cases := cases.push (fun _ => roleCase which assumed)
    cases := cases.push (fun _ => formerCase true assumed)
    cases := cases.push (fun _ => formerCase false assumed)
    cases := cases.push (fun _ => do
      compiled (← headEnv?) "HeadProj" assumed false (some "field classifier: unsupported type head"))
    cases := cases.push (fun _ => projectionField env assumed)
    cases := cases.push (fun _ => depthCase 9999 assumed)
    cases := cases.push (fun _ => depthCase 10000 assumed)
    cases := cases.push (fun _ => dataOutOfProof env assumed)
    cases := cases.push (fun _ => compiled env "andFst" assumed true none
      (some "KernelGuard::proj_walk_checked"))
    cases := cases.push (fun _ => anchorTable 1 assumed)
    cases := cases.push (fun _ => coveredRecursor env 0 assumed)
    cases := cases.push (fun _ => coveredRecursor env 1 assumed)
    for which in [0, 1] do
      cases := cases.push (fun _ => inertMutual which assumed)
    for which in [0, 1, 2] do
      cases := cases.push (fun _ => inertIndexed which assumed)
    cases := cases.push (fun _ => basisSeed .natRec assumed)
    cases := cases.push (fun _ => basisSeed .nat assumed)
  cases := cases.push (fun _ => anchorTable 0 false)
  cases := cases.push (fun _ => coveredRecursor env 2 false)
  runCases "ixvm-refusal-controls" cases (jobs := 4) (circuit := some true)

end Tests.Ix.IxVM.RefusalControls
