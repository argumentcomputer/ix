import Compilatrix.Ixby.Runtime.ConversionCode

/-! Exact code specifications for the three recursive Nat helpers and their
public wrappers. All function and constructor indices come from the image. -/

namespace Compilatrix.Ixby.Runtime.NatLoops

open Ix.Ixby ScalarFunction Conversion

def shiftRightLoop (self fromRaw : FunctionId) (cached : Constructor) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive .natEq [.local 1, N 0]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .tailCall fromRaw [.local 0]⟩,
    ⟨3, .letOp (.primitive .natEq [.local 0, N 0]) 4⟩,
    ⟨4, .branch (.local 3) 5 6⟩,
    ⟨4, .letOp (.construct cached [N 0, W 0]) 7⟩,
    ⟨4, .letOp (.primitive .natDiv [.local 0, N 2]) 8⟩,
    ⟨5, .ret (.local 4)⟩,
    ⟨5, .letOp (.primitive .natSub [.local 1, N 1]) 9⟩,
    ⟨6, .tailCall self [.local 4, .local 5]⟩] }

def shiftRight (natural loop : FunctionId) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .tailCall loop [.local 2, .local 3]⟩] }

def log2Loop (self fromRaw : FunctionId) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive .natLt [.local 0, N 2]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .tailCall fromRaw [.local 1]⟩,
    ⟨3, .letOp (.primitive .natDiv [.local 0, N 2]) 4⟩,
    ⟨4, .letOp (.primitive .natAdd [.local 1, N 1]) 5⟩,
    ⟨5, .tailCall self [.local 3, .local 4]⟩] }

def log2 (natural loop : FunctionId) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.call natural [.local 0]) 1⟩,
    ⟨2, .tailCall loop [.local 1, N 0]⟩] }

def powLoop (self mul : FunctionId) : Function := {
  arity := 3, blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 1, N 0]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .ret (.local 2)⟩,
    ⟨4, .letOp (.primitive .natDiv [.local 1, N 2]) 4⟩,
    ⟨5, .letOp (.primitive .natMod [.local 1, N 2]) 5⟩,
    ⟨6, .letOp (.primitive .natEq [.local 5, N 1]) 6⟩,
    ⟨7, .branch (.local 6) 7 8⟩,
    ⟨7, .letOp (.call mul [.local 2, .local 0]) 9⟩,
    ⟨7, .letOp (.primitive .natEq [.local 4, N 0]) 14⟩,
    ⟨8, .letOp (.primitive .natEq [.local 4, N 0]) 10⟩,
    ⟨9, .branch (.local 8) 11 12⟩,
    ⟨9, .ret (.local 7)⟩,
    ⟨9, .letOp (.call mul [.local 0, .local 0]) 13⟩,
    ⟨10, .tailCall self [.local 9, .local 4, .local 7]⟩,
    ⟨8, .branch (.local 7) 15 16⟩,
    ⟨8, .ret (.local 2)⟩,
    ⟨8, .letOp (.call mul [.local 0, .local 0]) 17⟩,
    ⟨9, .tailCall self [.local 8, .local 4, .local 2]⟩] }

def pow (natural loop : FunctionId) (cached : Constructor) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 1]) 1⟩,
    ⟨3, .letOp (.construct cached [N 1, W 1]) 2⟩,
    ⟨4, .tailCall loop [.local 0, .local 2, .local 3]⟩] }

end Compilatrix.Ixby.Runtime.NatLoops
