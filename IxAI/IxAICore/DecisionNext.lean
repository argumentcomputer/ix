import IxAICore.Decision

/-!
# Variants of decision-model helpers for new specifications

`probabilities` and `chunk` are part of the certified triage runs (`card`, the gate decisions and
`Config.schedule` evaluate them), so they stay as they are. These variants fix two edge cases and
are meant for specifications written from now on.

* `probabilitiesNonneg` clamps outputs only below, at `0`. `probabilities` also clamps above, at
  `1`, which discards every margin past `1.0`: outputs `[256, 512]` become `[128, 128]`, a tie,
  while the model's answer (`argmax`) is the second.
* `chunkPos` cuts chunks of at least one element. `chunk 0` returns `fuel` empty chunks.
-/

namespace IxAICore

/-- Probabilities from outputs: negative outputs count as `0`, the rest are normalized; uniform if
every output is zero or negative. Values are in units of `1/256`. -/
def probabilitiesNonneg (os : List Fx) : List Fx :=
  let cs := os.map Fx.relu
  let total := Fx.sumRaw cs
  if total ≤ 0 then os.map fun _ => ⟨(256 : Int) / os.length⟩
  else cs.map fun c => ⟨c.raw * 256 / total⟩

/-- Consecutive chunks of `max k 1` elements, at most `fuel` of them. -/
def chunkPos {α : Type} (k : Nat) (l : List α) (fuel : Nat) : List (List α) :=
  chunk (max k 1) l fuel

theorem chunk_ne_nil {α : Type} (k : Nat) (hk : 0 < k) :
    ∀ (fuel : Nat) (l : List α), ∀ c ∈ chunk k l fuel, c ≠ []
  | 0, _, c, h => by simp [chunk] at h
  | fuel + 1, l, c, h => by
    unfold chunk at h
    split at h
    · simp at h
    · rename_i hl
      simp only [List.mem_cons] at h
      rcases h with h | h
      · rw [h]
        cases l with
        | nil => simp at hl
        | cons a as =>
          cases k with
          | zero => omega
          | succ k => simp
      · exact chunk_ne_nil k hk fuel _ c h

/-- No chunk of `chunkPos` is empty. -/
theorem chunkPos_ne_nil {α : Type} (k fuel : Nat) (l : List α) :
    ∀ c ∈ chunkPos k l fuel, c ≠ [] :=
  chunk_ne_nil (max k 1) (by omega) fuel l

end IxAICore
