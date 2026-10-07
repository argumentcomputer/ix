import Ix.Compile.Canon.Graph
open Ix.Compile.Canon
#print Array.set!
#check @TarjanState.popComponent.go
#print TarjanState.popComponent
#check @Array.getElem?_setIfInBounds
#check @List.Pairwise
#check @tarjanLoop.eq_def
#check @Array.size_setIfInBounds
#check @Array.mem_push
#check @Array.getElem?_push
#check @List.foldl_cons
example (st : TarjanState) (w : Nat) : (st.visit w).stack = w :: st.stack := by cases st; rfl
