import Init
import Std

def id' (A: Type) (x: A) := x

def idX {A: Type} : A -> A := fun x => x
def idY {A: Type} : A -> A := fun y => y
def idSquared {A: Type} : A -> A := idX idY

def one : Nat := 1
