import IxCC.Src.Relevance.Proof.P1.Defs

/-! # P1's root, stated

`RunLiveStmt` is the statement of P1's root theorem `run_live` as a proposition: under L1's facts
(`Facts`) and one constructor per inductive and index (`ShapeOk`), `Src.run` on a root and literal
inputs whose run's sort events agree (`RunSortAgree`) returns a `Live` value. `run_live`
(`IxCC.Src.Relevance.Proof.P1.Main`) proves it. The consumption (`Recheck.Front.goesWrong_live`,
`Recheck.sound_live`) takes it as a hypothesis, and `IxCC.Recheck.Proof.LiveClosed` gives it
`run_live` (`Recheck.Front.goesWrong_live_closed`, `Recheck.sound_live_closed`). -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src

/-- **P1's root, as a proposition.** `Src.run` on literal inputs returns a `Live` value. -/
def RunLiveStmt : Prop :=
  ∀ {p : Program} {ann : Ann} {ch : Checked}, Facts p ann ch → ShapeOk p →
    ∀ {k : Nat} {root : CId} {ns : List Nat} {v : Value}, (∃ a, (a, root) ∈ p.roots) →
      RunSortAgree p ann k root (ns.map .lit) → Src.run p k root (ns.map .lit) = .ok v →
        Live p ann ch v

end IxCC.Src.Relevance.Proof.P1
