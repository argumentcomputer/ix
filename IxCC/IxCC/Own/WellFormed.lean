import IxCC.Own.Immortal
import IxCC.Fir.WellFormed

/-! # Own well-formedness

`Own.WellFormed q` (the premise of `Cfg.lower_correct`, 03 §7): each
function's signature has one entry per parameter, and the erasure is a
well-formed Fir program (`Fir.WellFormed`), which gives scoping, single
binding, saturated calls and constructor keys. Ownership itself is the
checker's business (`checkImmortal` in Phase 1, `Own.check` in Phase 2). -/

namespace IxCC.Own

/-- Well-formedness with the first violation. -/
def check (q : Program) : Except String Unit := do
  for (f, fd) in q.funList do
    if fd.sig.params.length != fd.params.length then
      throw s!"f{f}: {fd.sig.params.length} parameter signatures for {fd.params.length} parameters"
  Fir.check (erase q)

def wellFormed (q : Program) : Bool := (check q).isOk

def WellFormed (q : Program) : Prop := wellFormed q = true

instance (q : Program) : Decidable (WellFormed q) := inferInstanceAs (Decidable (_ = true))

end IxCC.Own
