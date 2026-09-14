import Compilatrix.Ixby.Runtime.ConversionCode

/-! Complete templates for the emitted Nat arithmetic and comparison
helpers. Indices are supplied by the actual image and checked propositionally.
These specifications do not change the builder or the reference evaluator. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic

open Ix.Ixby Conversion

def binary (natural : FunctionId) (cached raw field : Constructor)
    (natOp wordOp : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive natOp [.local 2, .local 3]) 3⟩,
    ⟨5, .caseCtor (.local 0) [⟨cached, 4⟩, ⟨raw, 5⟩, ⟨field, 6⟩]⟩,
    ⟨7, .caseCtor (.local 1) [⟨cached, 7⟩, ⟨raw, 8⟩, ⟨field, 9⟩]⟩,
    ⟨6, .letOp (.construct raw [.local 4]) 14⟩,
    ⟨6, .letOp (.construct raw [.local 4]) 15⟩,
    ⟨9, .letOp (.primitive wordOp [.local 6, .local 8]) 10⟩,
    ⟨8, .letOp (.construct raw [.local 4]) 12⟩,
    ⟨8, .letOp (.construct raw [.local 4]) 13⟩,
    ⟨10, .letOp (.construct cached [.local 4, .local 9]) 11⟩,
    ⟨11, .ret (.local 10)⟩,
    ⟨9, .ret (.local 8)⟩,
    ⟨9, .ret (.local 8)⟩,
    ⟨7, .ret (.local 6)⟩,
    ⟨7, .ret (.local 6)⟩] }

def subtract (natural : FunctionId) (cached raw field : Constructor) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natLt [.local 2, .local 3]) 3⟩,
    ⟨5, .branch (.local 4) 4 5⟩,
    ⟨5, .letOp (.construct cached [N 0, W 0]) 6⟩,
    ⟨5, .letOp (.call natural [.local 0]) 7⟩,
    ⟨6, .ret (.local 5)⟩,
    ⟨6, .letOp (.call natural [.local 1]) 8⟩,
    ⟨7, .letOp (.primitive .natSub [.local 5, .local 6]) 9⟩,
    ⟨8, .caseCtor (.local 0) [⟨cached, 10⟩, ⟨raw, 11⟩, ⟨field, 12⟩]⟩,
    ⟨10, .caseCtor (.local 1) [⟨cached, 13⟩, ⟨raw, 14⟩, ⟨field, 15⟩]⟩,
    ⟨9, .letOp (.construct raw [.local 7]) 20⟩,
    ⟨9, .letOp (.construct raw [.local 7]) 21⟩,
    ⟨12, .letOp (.primitive .word32Sub [.local 9, .local 11]) 16⟩,
    ⟨11, .letOp (.construct raw [.local 7]) 18⟩,
    ⟨11, .letOp (.construct raw [.local 7]) 19⟩,
    ⟨13, .letOp (.construct cached [.local 7, .local 12]) 17⟩,
    ⟨14, .ret (.local 13)⟩,
    ⟨12, .ret (.local 11)⟩,
    ⟨12, .ret (.local 11)⟩,
    ⟨10, .ret (.local 9)⟩,
    ⟨10, .ret (.local 9)⟩] }

def quotientRemainder (natural fromRaw : FunctionId) (operation : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive operation [.local 2, .local 3]) 3⟩,
    ⟨5, .tailCall fromRaw [.local 4]⟩] }

def less (natural : FunctionId) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natLt [.local 2, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

def lessEqual (natural : FunctionId) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natLt [.local 3, .local 2]) 3⟩,
    ⟨5, .branch (.local 4) 4 5⟩,
    ⟨5, .ret (.literal (.bool false))⟩,
    ⟨5, .ret (.literal (.bool true))⟩] }

def equal (natural : FunctionId) (cached raw field : Constructor) : Function := {
  arity := 2, blocks := #[
    ⟨2, .caseCtor (.local 0) [⟨cached, 1⟩, ⟨raw, 2⟩, ⟨field, 3⟩]⟩,
    ⟨4, .letOp (.call natural [.local 0]) 4⟩,
    ⟨3, .letOp (.call natural [.local 0]) 7⟩,
    ⟨3, .caseCtor (.local 1) [⟨cached, 10⟩, ⟨raw, 11⟩, ⟨field, 12⟩]⟩,
    ⟨5, .letOp (.call natural [.local 1]) 5⟩,
    ⟨6, .letOp (.primitive .natEq [.local 4, .local 5]) 6⟩,
    ⟨7, .ret (.local 6)⟩,
    ⟨4, .letOp (.call natural [.local 1]) 8⟩,
    ⟨5, .letOp (.primitive .natEq [.local 3, .local 4]) 9⟩,
    ⟨6, .ret (.local 5)⟩,
    ⟨5, .letOp (.call natural [.local 0]) 13⟩,
    ⟨4, .letOp (.call natural [.local 0]) 16⟩,
    ⟨4, .letOp (.primitive .fieldEq [.local 2, .local 3]) 19⟩,
    ⟨6, .letOp (.call natural [.local 1]) 14⟩,
    ⟨7, .letOp (.primitive .natEq [.local 5, .local 6]) 15⟩,
    ⟨8, .ret (.local 7)⟩,
    ⟨5, .letOp (.call natural [.local 1]) 17⟩,
    ⟨6, .letOp (.primitive .natEq [.local 4, .local 5]) 18⟩,
    ⟨7, .ret (.local 6)⟩,
    ⟨5, .ret (.local 4)⟩] }

end Compilatrix.Ixby.Runtime.NatArithmetic
