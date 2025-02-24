import LSpec
import Ix.ByteArray

def arrays : List ByteArray := [
  ⟨#[]⟩, ⟨#[1]⟩, ⟨#[0, 3]⟩, ⟨#[1, 1, 1]⟩, ⟨#[3, 3, 3, 3]⟩, ⟨#[13]⟩
]

def arrays' : List ByteArray := [
  ⟨#[1]⟩, ⟨#[2]⟩, ⟨#[0, 3, 0]⟩, ⟨#[1, 2, 1]⟩, ⟨#[3, 3, 4, 3]⟩, ⟨#[13, 0]⟩
]

open LSpec

def beq : TestSeq :=
  arrays.zip arrays |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} == {y}" $ x.beq y && x.beqNoFFI y && y.beq x && y.beqNoFFI x)

def neq : TestSeq :=
  arrays.zip arrays' |>.foldl (init := .done) fun tSeq (x, y) =>
    tSeq ++ (test s!"{x} != {y}" $ !x.beq y && !x.beqNoFFI y && !y.beq x && !y.beqNoFFI x)

def main := lspecIO $ beq ++ neq ++
  test "ByteArray.zeros works" (ByteArray.zeros 5 == .mk #[0, 0, 0, 0, 0])
