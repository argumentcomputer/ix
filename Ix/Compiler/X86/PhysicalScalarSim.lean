import Ix.Compiler.X86.PhysicalScalarControl

namespace Ix.Compiler.X86.PhysicalScalar
open IxIR2.Eval

structure FunctionContract (context : Context) (mode : Interpretation) (definition : IxIR2.Function)
    (functions : Array Scalar.Function) (target : Scalar.Function) : Prop where
  arity : target.parameters = definition.signature.params.size
  nonempty : definition.blocks.isEmpty = false
  evaluates : ∀ (values : Array Word) (result : Option Word), values.size = target.parameters →
    Scalar.Evaluates functions target.body values result →
    ∃ word, result = some word ∧ Runs context mode (frame definition 0 0 values) word

def Declarations (context : Context) (entries : Entries) : Prop :=
  ∀ (index : Nat) address definition, entries[index]? = some (address, definition) →
    context.declarations address = some (.fn definition)

def Callees (context : Context) (mode : Interpretation) (entries : Entries)
    (functions : Array Scalar.Function) (current : Nat) : Prop :=
  ∀ index address definition target, entries[index]? = some (address, definition) → index < current →
    functions[index]? = some target → FunctionContract context mode definition functions target

theorem Callees.call {context mode entries functions current index address definition arguments values result}
    (callees : Callees context mode entries functions current)
    (found : entries[index]? = some (address, definition)) (earlier : index < current)
    (evaluated : Scalar.Evaluates functions (.call index arguments) values result) :
    ∃ supplied word, arguments.mapM (Scalar.Atom.eval values) = some supplied ∧
      supplied.size = definition.signature.params.size ∧ definition.blocks.isEmpty = false ∧
      result = some word ∧ Runs context mode (frame definition 0 0 supplied) word := by
  cases evaluated with
  | call targetAt argumentsAt arity evaluated =>
    have contract := callees _ _ _ _ found earlier targetAt
    obtain ⟨word, same, executed⟩ := contract.evaluates _ _ arity evaluated
    exact ⟨_, word, argumentsAt, arity.trans contract.arity, contract.nonempty, same, executed⟩

/-- Every syntax certificate preserves its physical execution. The induction
composes code at each block/PC and uses only earlier function contracts at a
call. In particular it covers every accepted CFG, without recognizing a
complete graph or requiring a runtime evaluation certificate. -/
theorem Code.simulate {entries current definition block pc bindings locals expression}
    (code : Code entries current definition block pc bindings locals expression)
    {context : Context} {mode : Interpretation} {functions : Array Scalar.Function}
    (declarations : Declarations context entries) (callees : Callees context mode entries functions current)
    {native physical : Array Word} {result : Option Word}
    (size : native.size = locals) (environment : EnvRel bindings native physical)
    (evaluated : Scalar.Evaluates functions expression native result) :
    ∃ word, result = some word ∧ Runs context mode (frame definition block pc physical) word := by
  induction code generalizing native physical result with
  | ret blockAt endAt term atom =>
    cases evaluated with
    | atom value =>
      exact ⟨_, rfl, Runs.ret blockAt endAt term (atom_resolves environment atom value)⟩
  | move blockAt instruction atom rest ih =>
    obtain ⟨value, found, resolved⟩ := atom_sound environment atom
    obtain ⟨word, same, executed⟩ := ih size (environment.push found) evaluated
    exact ⟨word, same, executed.move blockAt instruction resolved⟩
  | retain blockAt instruction atom rest ih =>
    obtain ⟨value, found, resolved⟩ := atom_sound environment atom
    obtain ⟨word, same, executed⟩ := ih size (environment.push found) evaluated
    exact ⟨word, same, executed.retain blockAt instruction resolved⟩
  | release blockAt instruction atom rest ih =>
    obtain ⟨value, _, resolved⟩ := atom_sound environment atom
    obtain ⟨word, same, executed⟩ := ih size environment evaluated
    exact ⟨word, same, executed.release blockAt instruction resolved⟩
  | drop blockAt instruction atom rest ih =>
    obtain ⟨value, _, resolved⟩ := atom_sound environment atom
    obtain ⟨word, same, executed⟩ := ih size environment evaluated
    exact ⟨word, same, executed.drop blockAt instruction resolved⟩
  | jump blockAt endAt term atoms ready rest ih =>
    obtain ⟨arguments, argsEnvironment, _, resolved⟩ := atoms_sound environment atoms
    obtain ⟨word, same, executed⟩ := ih size argsEnvironment evaluated
    exact ⟨word, same, executed.jump blockAt endAt term ready argsEnvironment.size.symm resolved⟩
  | branch blockAt endAt term atom zeroAtoms succAtoms zeroReady succReady zeroCode succCode ihZero ihSucc =>
    cases evaluated with
    | zero found taken =>
      obtain ⟨arguments, argsEnvironment, _, resolved⟩ := atoms_sound environment zeroAtoms
      obtain ⟨word, same, executed⟩ := ihZero size argsEnvironment taken
      exact ⟨word, same, executed.zero blockAt endAt term (atom_resolves environment atom found)
        zeroReady argsEnvironment.size.symm resolved⟩
    | @successor _ _ _ _ value _ found positive taken =>
      cases taken with
      | letOverflow first => cases first
      | letE first rest =>
        cases first with
        | @sub _ _ _ a b left right =>
          have leftSame := Option.some.inj (left.symm.trans found)
          have rightSame : b = 1 := (Option.some.inj right).symm
          subst a b
          obtain ⟨arguments, argsEnvironment, _, resolved⟩ := atoms_sound environment succAtoms
          obtain ⟨word, same, executed⟩ := ihSucc (by simpa using size)
            (argsEnvironment.prepend size (ExactNat.sub value 1)) rest
          exact ⟨word, same, executed.successor blockAt endAt term positive (atom_resolves environment atom found)
            succReady argsEnvironment.size.symm resolved⟩
  | call blockAt instruction atoms found earlier arity rest ih =>
    obtain ⟨arguments, argsEnvironment, argumentsAt, resolved⟩ := atoms_sound environment atoms
    cases evaluated with
    | letOverflow first =>
      obtain ⟨_, _, _, _, _, impossible, _⟩ := callees.call found earlier first
      contradiction
    | @letE _ _ _ bound _ first tail =>
      obtain ⟨supplied, value, suppliedAt, suppliedArity, nonempty, same, called⟩ := callees.call found earlier first
      have suppliedSame := Option.some.inj (suppliedAt.symm.trans argumentsAt)
      have valueSame := Option.some.inj same
      subst supplied bound
      obtain ⟨word, same, continuation⟩ := ih (by simpa using size) (environment.bind size value) tail
      exact ⟨word, same, Runs.call blockAt instruction resolved (declarations _ _ _ found)
        suppliedArity nonempty called continuation⟩
  | tailCall blockAt endAt term atoms found earlier arity =>
    obtain ⟨arguments, argsEnvironment, argumentsAt, resolved⟩ := atoms_sound environment atoms
    obtain ⟨supplied, word, suppliedAt, suppliedArity, nonempty, same, called⟩ := callees.call found earlier evaluated
    have suppliedSame := Option.some.inj (suppliedAt.symm.trans argumentsAt)
    subst supplied
    exact ⟨word, same, called.tailCall blockAt endAt term resolved (declarations _ _ _ found) suppliedArity nonempty⟩

end Ix.Compiler.X86.PhysicalScalar
