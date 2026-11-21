import Aiur.Constant

namespace Aiur

inductive HintError where
  | unavailable
  | invalidValue (expected actual : Ty)
  | message (text : String)
  deriving Repr, BEq, DecidableEq

/-- Host advice consumes and returns constants. Channels are static names;
neither the callback nor its algorithm is part of the program's semantics. -/
abbrev HintFunction (F : Type) := Constant F → Except HintError (Constant F)
abbrev HintDispatcher (F : Type) := String → HintFunction F

/-- The evaluator may encounter ill-typed syntax; never expose addresses to a
host callback even in that case. -/
def HintDispatcher.provide (dispatcher : HintDispatcher F) (channel : String)
    (key : SourceValue F) : Except HintError (Constant F) := do
  let some key := key.toConstant? | throw (.message "hint key contains pointers")
  dispatcher channel key

/-- Successful hints carry their typing proof. Constants are values with no address leaves. -/
abbrev HintProvider (F : Type) (decls : Declarations) :=
  String → SourceValue F → (type : Ty) →
    Except HintError { value : Constant F // value.WellTyped decls type }

namespace HintProvider

/-- Existing callers need no provider unless execution actually reaches a hint. -/
def unavailable : HintProvider F decls := fun _ _ _ => .error .unavailable

/-- Adapt an untrusted value producer by checking the complete nominal value type. -/
def checked (decls : Declarations)
    (dispatcher : HintDispatcher F) : HintProvider F decls :=
  fun channel key type => do
    let value ← dispatcher.provide channel key
    if valid : value.hasType decls type = true then return ⟨value, valid⟩
    else throw (.invalidValue type value.type)

end HintProvider

end Aiur
