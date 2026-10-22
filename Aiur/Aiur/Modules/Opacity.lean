import Aiur.Modules.Elaborate

/-! Opacity is static module information. These checks run on retained type
names, before representation aliases are normalized. They do not rewrite code. -/
namespace Aiur.Modules

def Item.declaredOpaqueTypes (item : Item α) : List String :=
  match item.decl.body with
  | .definitions d => d.opaqueTypes.map (rename item.key.symbol)
  | .alias _ => []

/-- Input permissions come from the view supplied to a client. The defining
module may inspect its representation, but its own opaque declarations still
cannot be supplied as entry arguments or hint results. -/
def opaqueNames (p : Program α) (w : World α) (owner : Ref) : List String :=
  w.items.flatMap fun item =>
    item.declaredOpaqueTypes ++
      if item.key == owner then [] else
        ((item.decl.signature.bind p.findSignature?).toList.flatMap fun s =>
          (s.types.filter (·.isOpaque)).map fun t => rename item.key.symbol t.name)

/-- Recursive input admissibility. Abstract signature parameters may promise
admissibility; pointers are intrinsically opaque. Empty arrays still inspect
their element type, and all enum variants are inspected. -/
def nonOpaque (p : Generic.Program α) (opaqueTypes parameters : List String) :
    Nat → Generic.Ty → Bool
  | 0, _ => false
  | fuel + 1, type => match type with
    | .field => true
    | .ptr _ => false
    | .param name => parameters.contains name
    | .tuple types => types.all (nonOpaque p opaqueTypes parameters fuel)
    | .array type _ => nonOpaque p opaqueTypes parameters fuel type
    | .named name args =>
        if opaqueTypes.contains name then false else
        match p.aliases.find? (·.name == name) with
        | some d => d.typeParams.length == args.length &&
            nonOpaque p opaqueTypes parameters fuel (d.target.subst (d.typeParams.zip args))
        | none => match p.findEnum? name with
          | none => false
          | some d => d.typeParams.length == args.length &&
              d.constructors.all fun c => c.fields.all fun t =>
                nonOpaque p opaqueTypes parameters fuel (t.subst (d.typeParams.zip args))

def checkNonOpaque (p : Generic.Program α) (opaqueTypes : List String)
    (context : String) (type : Generic.Ty) (parameters : List String := []) : Except String Unit :=
  if nonOpaque p opaqueTypes parameters 1024 type then .ok ()
  else .error s!"{context} requires a recursively non-opaque type (pointers are opaque): {repr type}"

@[simp] theorem nonOpaque_pointer :
    nonOpaque p opaqueTypes parameters fuel (.ptr type) = false := by
  cases fuel <;> rfl

theorem nonOpaque_declared (present : opaqueTypes.contains name = true) :
    nonOpaque p opaqueTypes parameters fuel (.named name args) = false := by
  cases fuel <;> simp only [nonOpaque, present, ite_true]

@[simp] theorem nonOpaque_array :
    nonOpaque p opaqueTypes parameters (fuel + 1) (.array type length) =
      nonOpaque p opaqueTypes parameters fuel type := rfl

/-- Input permissions are independent of the field and of numeric literals. -/
theorem nonOpaque_map (f : α → β) (p : Generic.Program α) (opaqueTypes parameters)
    (fuel : Nat) (type : Generic.Ty) :
    nonOpaque (p.map f) opaqueTypes parameters fuel type =
      nonOpaque p opaqueTypes parameters fuel type := by
  induction fuel generalizing type with
  | zero => rfl
  | succ fuel ih =>
      have aliases : (p.map f).aliases = p.aliases := rfl
      have enums : (p.map f).findEnum? = p.findEnum? := rfl
      have same : nonOpaque (p.map f) opaqueTypes parameters fuel =
          nonOpaque p opaqueTypes parameters fuel := funext ih
      cases type <;> simp only [nonOpaque, aliases, enums, same]

/-- A client's nominal placeholder is private to checking and never enters
the source evaluation environment or a circuit layout. -/
def sealTypes (p : Generic.Program α) (names : List String) : Generic.Program α :=
  let declarations := p.nominals.map (fun d => (d.name, d.typeParams)) ++
    p.aliases.map (fun d => (d.name, d.typeParams))
  { p with
    aliases := p.aliases.filter (fun d => !names.contains d.name)
    structs := p.structs.filter (fun d => !names.contains d.name)
    enums := p.enums.filter (fun d => !names.contains d.name) ++
      (declarations.filter (fun d => names.contains d.1)).map fun (name, params) =>
        ⟨name, params, [⟨"@opaque", [.ptr .field]⟩]⟩ }

/-- Collect every explicitly requested witness type, including inactive code
and hint keys. The source expression itself is left untouched. -/
def hintTypes : Generic.Expr α → List Generic.Ty
  | .literal _ | .var _ | .global _ _ => []
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs |
      .record _ xs | .builtin _ xs | .update _ xs | .call _ _ xs => xs.flatMap hintTypes
  | .control _ x | .repeat x _ | .index x _ | .slice x _ _ | .member x _ |
      .project x _ | .store x | .load x | .neg x => hintTypes x
  | .hint t key channel => t :: hintTypes key
  | .binary _ x y | .letValue _ x y => hintTypes x ++ hintTypes y
  | .matchValue x arms => hintTypes x ++ arms.flatMap (fun arm => hintTypes arm.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try omega
  all_goals cases ‹Generic.Pattern α × Generic.Expr α›; simp_all only [Prod.mk.sizeOf_spec]; omega

end Aiur.Modules
