import IxCC.Rt.Rc.Proof.Detach

/-! Actual block8 continuation: compute the next field, load before reducing
the scan byte, then dispatch the child with one charged backedge. The memory
load premise uses the actual machine-computed field address. Deriving it from
the cursor/suffix invariant is a separate required bridge. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def nextFieldAddress (address cls remaining : Word) : Word :=
  address + (cls-1-remaining)*8 + 8
def resumeParent (mem : X86.Memory) (address remaining : Word) : X86.Memory :=
  mem.write .w8 address (remaining-1)
def resumeEnv (env : Env) (cls remaining child : Word) : Env :=
  (((env.insert 11 (cls-1)).insert 12 (cls-1-remaining)).insert 13 child).insert 14 (remaining-1)

theorem resume_child (mem : X86.Memory) (context address cls remaining child : Word)
    (env : Env) (ha : env[8]? = some address) (hc : env[10]? = some cls)
    (hr : env[9]? = some remaining)
    (hchild : loadWord mem .w64 .zero (nextFieldAddress address cls remaining) = some child)
    (hw : mem.writable address = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 8 0) 1
      (releaseState (resumeParent mem address remaining) context
        (((resumeEnv env cls remaining child).insert 1 child).insert 2 address) 1 0) := by
  let e1 := env.insert 11 (cls-1)
  let e2 := e1.insert 12 (cls-1-remaining)
  let e3 := e2.insert 13 child
  let e4 := resumeEnv env cls remaining child
  have h11 : e1[11]? = some (cls-1) := by simp only [e1, Std.HashMap.getElem?_insert]; rfl
  have hr1 : e1[9]? = some remaining := by
    simp only [e1, Std.HashMap.getElem?_insert]
    change env[9]? = some remaining
    exact hr
  have h12 : e2[12]? = some (cls-1-remaining) := by simp only [e2, Std.HashMap.getElem?_insert]; rfl
  have ha2 : e2[8]? = some address := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    change env[8]? = some address
    exact ha
  have hr3 : e3[9]? = some remaining := by
    simp only [e3, e2, e1, Std.HashMap.getElem?_insert]
    change env[9]? = some remaining
    exact hr
  have ha4 : e4[8]? = some address := by
    simp only [e4, resumeEnv, Std.HashMap.getElem?_insert]
    change env[8]? = some address
    exact ha
  have h14 : e4[14]? = some (remaining-1) := by
    simp only [e4, resumeEnv, Std.HashMap.getElem?_insert]; rfl
  have h13 : e4[13]? = some child := by
    simp only [e4, resumeEnv, Std.HashMap.getElem?_insert]; rfl
  have hw' : mem.write? .w8 address (remaining-1) = .ok (resumeParent mem address remaining) := by
    apply write?_ok
    intro j hj
    have : j = 0 := by simp only [X86.Width.bytes] at hj; omega
    subst j
    simpa using hw
  have hchild' : loadWord mem .w64 .zero (address+(cls-1-remaining)*8+8) = some child := hchild
  apply Sem.Star.free (s' := releaseState mem context e1 8 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, Stmt.exec, Rhs.eval,
      Arg.eval, BinOp.eval, hc, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 8 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, Stmt.exec, Rhs.eval,
      Arg.eval, BinOp.eval, h11, hr1, e2]
  apply Sem.Star.free (s' := releaseState mem context e3 8 3)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, X86.Scale.word, ha2, h12, hchild', e3]
  apply Sem.Star.free (s' := releaseState mem context e4 8 4)
  · apply semStep_next.mpr
    have he : e3.insert 14 (remaining-1) = e4 := rfl
    simp [step, releaseProgram, releaseState, dec, v, i, Stmt.exec, Rhs.eval,
      Arg.eval, BinOp.eval, hr3, he]
  apply Sem.Star.free (s' := releaseState (resumeParent mem address remaining) context e4 8 5)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, cellAddr, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha4, h14, hw']
  apply Sem.Star.charge
    (s' := releaseState (resumeParent mem address remaining) context
      ((e4.insert 1 child).insert 2 address) 1 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, h13, ha4]
  exact .refl _


end IxCC.Rt.Rc.Procs
