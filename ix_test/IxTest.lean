-- This module serves as the root of the `IxTest` library.
-- Import modules here that should be built as part of the library.
import IxTest.Basic
import Init
import Std

def id' (A: Type) (x: A) := x
def ref (A: Type) (_x : A) := hello

def idX {A: Type} : A -> A := fun x => x
def idY {A: Type} : A -> A := fun y => y
def idSquared {A: Type} : A -> A := idX idY

def one : Nat := 1
