import Ix.Compiler.UniqueReuse.TargetHeap

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

def point (schema : Schema) (reuse : Bool) (block pc : Nat) (store : Store)
    (heapFuel : Nat) (values : Array RVal) (credits : Array (Option Credit) := #[]) : Machine :=
  { store, heapFuel, control := .running
      { definition := UniqueLower.function schema reuse, block, pc, values, credits } [] }

def loop (schema : Schema) (reuse : Bool) (store : Store) (heapFuel : Nat)
    (accumulator major : RVal) : Machine :=
  point schema reuse 0 0 store heapFuel #[accumulator, major]

theorem switchNil (ctx : Context) (mode : Interpretation) (schema : Schema) (reuse : Bool)
    (store : Store) (fuel location : Nat) (acc : RVal)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (nilId schema) #[]⟩) :
    Step ctx mode (loop schema reuse store fuel acc (.loc location))
      (point schema reuse 1 0 store fuel #[acc, .loc location]) := by
  apply Step.switchCtor (alternative := ⟨nilId schema, ⟨1, #[.reg 0, .reg 1], #[]⟩⟩)
    rfl rfl rfl rfl rfl found rfl
  · simp
  · exact EdgeTransfer.baseline (block := UniqueLower.nilBlock schema)
      (values := #[acc, .loc location]) rfl rfl rfl rfl rfl rfl

theorem switchCons (ctx : Context) (mode : Interpretation) (schema : Schema) (reuse : Bool)
    (store : Store) (fuel location head : Nat) (tail acc : RVal)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩) :
    Step ctx mode (loop schema reuse store fuel acc (.loc location))
      (point schema reuse 2 0 store fuel #[acc, .loc location]) := by
  apply Step.switchCtor (alternative := ⟨consId schema, ⟨2, #[.reg 0, .reg 1], #[]⟩⟩)
    rfl rfl rfl rfl rfl found rfl
  · simp [Ne.symm (cons_ne_nil schema)]
  · exact EdgeTransfer.baseline (block := UniqueLower.consBlock schema reuse)
      (values := #[acc, .loc location]) rfl rfl rfl rfl rfl rfl

theorem nilSteps (ctx : Context) (mode : Interpretation) (schema : Schema) (reuse : Bool)
    (store : Store) (fuel location : Nat) (acc : RVal)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (nilId schema) #[]⟩)
    (world : acc.hasWorld (store.kill location) .unique = true) :
    Steps ctx mode 4 (loop schema reuse store fuel acc (.loc location))
      { store := store.kill location, heapFuel := fuel, control := .halted acc } := by
  have schemaAt : ctx.schemas .unique (nilId schema) = some (nilSchema schema) :=
    schemas ▸ nilSchemaAt schema
  have first := (switchNil ctx mode schema reuse store fuel location acc found).toSteps rfl
  have finish := Step.retHaltCleared (context := ctx) (interpretation := mode)
    (machine := point schema reuse 1 2 (store.kill location) fuel #[acc, .loc location] #[none])
    rfl rfl rfl rfl rfl (by simp [NoLiveCredits]) world
  cases mode with
  | logical =>
      have take := Step.takeUniqueLogical (context := ctx)
        (machine := point schema reuse 1 0 store fuel #[acc, .loc location])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
      have discard := Step.discardCreditLogical (context := ctx)
        (machine := point schema reuse 1 1 (store.kill location) fuel #[acc, .loc location]
          #[some ⟨(nilSchema schema).layout, .present none⟩])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl
      exact ((first.trans (take.toSteps rfl)).trans (discard.toSteps rfl)).trans (finish.toSteps rfl)
  | physical =>
      have take := Step.takeUniquePhysical (context := ctx)
        (machine := point schema reuse 1 0 store fuel #[acc, .loc location])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
      have discard := Step.discardCreditPhysical (context := ctx)
        (machine := point schema reuse 1 1 (store.reserve location) fuel #[acc, .loc location]
          #[some ⟨(nilSchema schema).layout, .present (some location)⟩])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl
        (reserveRelease found)
      exact ((first.trans (take.toSteps rfl)).trans (discard.toSteps rfl)).trans (finish.toSteps rfl)

theorem consBaselineSteps (ctx : Context) (mode : Interpretation) (schema : Schema)
    (store : Store) (fuel location head : Nat) (tail acc : RVal)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (fields : FieldWorlds (store.kill location) (consSchema schema) #[.lit (.nat head), acc]) :
    let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
    Steps ctx mode 5 (loop schema false store fuel acc (.loc location))
      (loop schema false allocated.1 fuel (.loc allocated.2) tail) := by
  dsimp only
  have schemaAt : ctx.schemas .unique (consId schema) = some (consSchema schema) :=
    schemas ▸ consSchemaAt schema
  let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
  have first := (switchCons ctx mode schema false store fuel location head tail acc found).toSteps rfl
  have alloc := Step.alloc (context := ctx) (interpretation := mode)
    (machine := point schema false 2 2 (store.kill location) fuel #[acc, .loc location, .lit (.nat head), tail] #[none])
    rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl fields
  have call := Step.tailCallSelfCleared (context := ctx) (interpretation := mode)
    (machine := point schema false 2 3 allocated.1 fuel
      #[acc, .loc location, .lit (.nat head), tail, .loc allocated.2] #[none])
    rfl rfl rfl rfl (by simp [NoLiveCredits]) rfl rfl rfl
  cases mode with
  | logical =>
      have take := Step.takeUniqueLogical (context := ctx)
        (machine := point schema false 2 0 store fuel #[acc, .loc location])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
      have discard := Step.discardCreditLogical (context := ctx)
        (machine := point schema false 2 1 (store.kill location) fuel #[acc, .loc location, .lit (.nat head), tail]
          #[some ⟨(consSchema schema).layout, .present none⟩])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl
      exact (((first.trans (take.toSteps rfl)).trans (discard.toSteps rfl)).trans (alloc.toSteps rfl)).trans
        (call.toSteps rfl)
  | physical =>
      have take := Step.takeUniquePhysical (context := ctx)
        (machine := point schema false 2 0 store fuel #[acc, .loc location])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
      have discard := Step.discardCreditPhysical (context := ctx)
        (machine := point schema false 2 1 (store.reserve location) fuel #[acc, .loc location, .lit (.nat head), tail]
          #[some ⟨(consSchema schema).layout, .present (some location)⟩])
        rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl (reserveRelease found)
      exact (((first.trans (take.toSteps rfl)).trans (discard.toSteps rfl)).trans (alloc.toSteps rfl)).trans
        (call.toSteps rfl)

theorem consLogicalSteps (ctx : Context) (schema : Schema)
    (store : Store) (fuel location head : Nat) (tail acc : RVal)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (fields : FieldWorlds (store.kill location) (consSchema schema) #[.lit (.nat head), acc]) :
    let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
    Steps ctx .logical 4 (loop schema true store fuel acc (.loc location))
      (loop schema true allocated.1 fuel (.loc allocated.2) tail) := by
  dsimp only
  have schemaAt : ctx.schemas .unique (consId schema) = some (consSchema schema) :=
    schemas ▸ consSchemaAt schema
  let allocated := (store.kill location).allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), acc])
  have first := (switchCons ctx .logical schema true store fuel location head tail acc found).toSteps rfl
  have take := Step.takeUniqueLogical (context := ctx)
    (machine := point schema true 2 0 store fuel #[acc, .loc location])
    rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
  have alloc := Step.allocWithLogical (context := ctx)
    (machine := point schema true 2 1 (store.kill location) fuel #[acc, .loc location, .lit (.nat head), tail]
      #[some ⟨(consSchema schema).layout, .present none⟩])
    rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl fields (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl rfl
  have call := Step.tailCallSelfCleared (context := ctx) (interpretation := .logical)
    (machine := point schema true 2 2 allocated.1 fuel
      #[acc, .loc location, .lit (.nat head), tail, .loc allocated.2] #[none])
    rfl rfl rfl rfl (by simp [NoLiveCredits]) rfl rfl rfl
  exact ((first.trans (take.toSteps rfl)).trans (alloc.toSteps rfl)).trans (call.toSteps rfl)

theorem consPhysicalSteps (ctx : Context) (schema : Schema)
    (store : Store) (fuel location head : Nat) (tail acc : RVal)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (fields : FieldWorlds (store.reserve location) (consSchema schema) #[.lit (.nat head), acc]) :
    let output := reuseAt store location (.ctorN (consId schema) #[.lit (.nat head), acc]) 2
    Steps ctx .physical 4 (loop schema true store fuel acc (.loc location))
      (loop schema true output fuel (.loc location) tail) := by
  dsimp only
  have schemaAt : ctx.schemas .unique (consId schema) = some (consSchema schema) :=
    schemas ▸ consSchemaAt schema
  let output := reuseAt store location (.ctorN (consId schema) #[.lit (.nat head), acc]) 2
  have first := (switchCons ctx .physical schema true store fuel location head tail acc found).toSteps rfl
  have take := Step.takeUniquePhysical (context := ctx)
    (machine := point schema true 2 0 store fuel #[acc, .loc location])
    rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl (ConstructorView.of_box found rfl rfl) rfl
  have alloc := Step.allocWithPhysical (context := ctx)
    (machine := point schema true 2 1 (store.reserve location) fuel #[acc, .loc location, .lit (.nat head), tail]
      #[some ⟨(consSchema schema).layout, .present (some location)⟩])
    rfl rfl (by simp [UniqueLower.function, UniqueLower.nilBlock, UniqueLower.consBlock]) rfl schemaAt rfl fields (CreditTake.of_lookup (CreditLookup.of_getElem rfl)) rfl rfl
    (reserveReuse found _ 2)
  have call := Step.tailCallSelfCleared (context := ctx) (interpretation := .physical)
    (machine := point schema true 2 2 output fuel
      #[acc, .loc location, .lit (.nat head), tail, .loc location] #[none])
    rfl rfl rfl rfl (by simp [NoLiveCredits]) rfl rfl rfl
  exact ((first.trans (take.toSteps rfl)).trans (alloc.toSteps rfl)).trans (call.toSteps rfl)

end Ix.Compiler.UniqueReuse.Target
