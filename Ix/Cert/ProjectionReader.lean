module
public import IxC.Kernel.Ixon.Reader
import all IxC.Kernel.Ixon.Reader
namespace Ix.Cert.ProjectionRoots
open Ix.Kernel Ix.Kernel.Reader
public theorem owner_read_eq {md : Mode} {cx : Ctx md} {st : State md} {a : Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} (info : c.info = .muts ms)
    (hi : ms.any (fun | .indc _ => true | _ => false) = true)
    (hn : ms.any (fun | .defn _ => true | _ => false) = false) :
    readRecord cx st a c = readInductive cx st a c ms := by
  unfold readRecord; rw [info]
  iterate 2 all_goals (split <;> simp_all)
  · intro i h bad; exact (Bool.false_ne_true ((hn i h).symm.trans bad)).elim
  · rename_i absent; obtain ⟨i, h, good⟩ := hi; exact (Bool.false_ne_true ((absent i h).symm.trans good)).elim
end Ix.Cert.ProjectionRoots
