module
public import Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.Basic

public section

open Ix.Sharing.Exact

namespace AreaBench

def rows (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat) (area pos : Array Nat)
    (fl : Array Bool) : Nat → Nat → Array Nat → Array Nat → Array Nat → Array Nat →
      Array Nat × Array Nat × Array Nat × Array Nat
  | _, 0, C, I, S, B => (C, I, S, B)
  | i, n + 1, C, I, S, B =>
    match tRow p opaq tb.tLen tb.tTail w (avA pos fl) (rdA pos C tb.cost)
        (rdA pos S tb.sides) (rdA pos B tb.below) area[i]! with
    | (c, inl, s, b) => rows p opaq tb w area pos fl (i + 1) n
        (C.push c) (I.push inl) (S.push s) (B.push b)

theorem rows_eq (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat)
    (area pos : Array Nat) (fl : Array Bool) (n : Nat) :
    ∀ i C I S B, rows p opaq tb w area pos fl i n C I S B =
      foldRange (fun (st : Array Nat × Array Nat × Array Nat × Array Nat) j =>
        match st with
        | (C, I, S, B) =>
          match tRow p opaq tb.tLen tb.tTail w (avA pos fl) (rdA pos C tb.cost)
              (rdA pos S tb.sides) (rdA pos B tb.below) area[j]! with
          | (c, inl, s, b) => (C.push c, I.push inl, S.push s, B.push b))
        i n (C, I, S, B) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i C I S B
    simp only [rows, foldRange]
    exact ih _ _ _ _ _

def areaFoldFlat (p : Prep) (opaq : Array Bool) (tb : TBase) (w : Nat)
    (area pos : Array Nat) (fl : Array Bool) : Array Nat × Array Nat × Array Nat × Array Nat :=
  let k := area.size
  rows p opaq tb w area pos fl 0 k
    (Array.mkEmpty k) (Array.mkEmpty k) (Array.mkEmpty k) (Array.mkEmpty k)

theorem areaFold_eq_flat : @areaFold = @areaFoldFlat := by
  funext p opaq tb w area pos fl
  exact (rows_eq p opaq tb w area pos fl area.size 0 _ _ _ _).symm

#print axioms areaFold_eq_flat

def sample (n shape : Nat) : Prep × Array Bool × TBase × Array Nat × Array Nat × Array Bool := Id.run do
  let mut nodes : Array Node := #[⟨.var 0, #[]⟩, ⟨.var 1, #[]⟩]
  for i in [2:n] do
    nodes := nodes.push <|
      if shape == 0 then ⟨.app, #[i - 1, i % 2]⟩
      else if shape == 1 then ⟨.lam default, #[i % 2, i - 1]⟩
      else if i % 3 == 0 then ⟨.app, #[i - 1, i - 2]⟩
      else ⟨.prj 0 0, #[i - 1]⟩
  let p := Prep.ofDag ⟨nodes⟩
  let opaq := (Array.range n).map fun i => i % 11 == 2
  let tb := TBase.ofPrep p 2 opaq
  let area := (Array.range n).filter fun i => i % 3 != 1
  let pos := area.zipIdx.foldl (fun (a : Array Nat) (i, j) => a.set! i (j + 1))
    (Array.replicate n 0)
  let fl := area.map fun i => i % 5 == 0
  return (p, opaq, tb, area, pos, fl)

@[noinline] def runOld (x : Prep × Array Bool × TBase × Array Nat × Array Nat × Array Bool)
    (rounds : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:rounds] do
    let r := areaFold x.1 x.2.1 x.2.2.1 (1 + i % 3) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
    acc := acc + r.1.back! + r.2.1.back! + r.2.2.1.back! + r.2.2.2.back!
  return acc

@[noinline] def runFlat (x : Prep × Array Bool × TBase × Array Nat × Array Nat × Array Bool)
    (rounds : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:rounds] do
    let r := areaFoldFlat x.1 x.2.1 x.2.2.1 (1 + i % 3) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
    acc := acc + r.1.back! + r.2.1.back! + r.2.2.1.back! + r.2.2.2.back!
  return acc

def timed (label : String) (work : Unit → Nat) : IO Nat := do
  let t ← IO.monoNanosNow
  let r ← IO.lazyPure work
  IO.println s!"{label}: {(← IO.monoNanosNow) - t} ns; checksum {r}"
  return r

end AreaBench

def main : IO Unit := do
  for n in #[64, 256, 1024, 4096] do
    for shape in [:3] do
      let x ← IO.lazyPure fun _ => AreaBench.sample n shape
      let old := areaFold x.1 x.2.1 x.2.2.1 2 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
      let flat := AreaBench.areaFoldFlat x.1 x.2.1 x.2.2.1 2 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
      unless old == flat do throw (IO.userError "unequal row tables")
      let rounds := 2000000 / n
      for trial in [:4] do
        let tag := s!"size={n} shape={shape} trial={trial}"
        let (a, b) ← if trial % 2 == 0 then do
            let a ← AreaBench.timed s!"{tag} old" fun _ => AreaBench.runOld x rounds
            let b ← AreaBench.timed s!"{tag} flat" fun _ => AreaBench.runFlat x rounds
            pure (a, b)
          else do
            let b ← AreaBench.timed s!"{tag} flat" fun _ => AreaBench.runFlat x rounds
            let a ← AreaBench.timed s!"{tag} old" fun _ => AreaBench.runOld x rounds
            pure (a, b)
        unless a == b do throw (IO.userError "unequal checksums")
