module

public import ConLeche.Semantics.Tower.FixCaseI
public import ConLeche.Semantics.Tower.SumRec

@[expose] public section

/-!
# The ih spellings (tasks #188, #202)

The `AnnotTerm` spellings shared by the P tier's readings of the kernel's
generated recursor rules and the semantic recursor body: the recursive
positions, a field's index expressions and telescope moved to an ih
frame (`ihIdxAt`, `ihIdxAtM`, `ihTeleAtR`), the ih application under a
field's telescope (`ihAppAVb`, generic in the elimination bit and in
the number of extra binders between the fields and the minors), and
the squash regime's recursor body (`sqFixBodyAV`, task #202 A2): the
(only) minor at the fields read off the indices (`srcAV`) with the ih
applications, as a β-redex over the constructor's field telescope.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The recursive positions -/

/-- The recursive positions among the first `k` fields. -/
def recIdx (rs : List Bool) (k : Nat) : List Nat :=
  (List.range k).filter fun i => rs.getD i false

theorem mem_recIdx {rs : List Bool} {k i : Nat} :
    i ∈ recIdx rs k ↔ i < k ∧ rs.getD i false = true := by
  unfold recIdx
  rw [List.mem_filter, List.mem_range]


/-! ## The ih frame -/

/-- Field `i`'s index expression (read at the field's own frame: the
parameters, the `i` earlier fields) moved under all `nF` fields, `l`
ih binders below them and `o` extras between the parameters and the
fields — `structIdxAt`'s reading. -/
def ihIdxAt (nF o i l : Nat) (E : AnnotTerm) : AnnotTerm :=
  (E.liftN (nF - i + l) 0).liftN o (nF + l)

/-- `structIdxAt nF o i l m`'s reading: field `i`'s expression sitting
under `m` binders of the field's own telescope, moved as `ihIdxAt`
moves it (task #202). -/
def ihIdxAtM (nF o i l m : Nat) (E : AnnotTerm) : AnnotTerm :=
  (E.liftN (nF - i + l) m).liftN o (nF + l + m)

/-- `structTeleAt`'s reading: field `i`'s telescope (its entries read
at the field's own frame, binder `k` under `k` earlier telescope
binders) moved to the ih binder's frame. -/
def ihTeleAtGo (nF o i l : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: tl => (d.1, d.2.1, ihIdxAtM nF o i l k d.2.2) :: ihTeleAtGo nF o i l (k + 1) tl

/-- The whole telescope moved (binder `k` under `k` earlier ones). -/
def ihTeleAtR (nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ihTeleAtGo nF o i l 0 tl

@[simp] theorem ihTeleAtR_nil (nF o i l : Nat) : ihTeleAtR nF o i l [] = [] := rfl

theorem ihTeleAtGo_length (nF o i l : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)), (ihTeleAtGo nF o i l k tl).length = tl.length
  | _, [] => rfl
  | k, _ :: tl => by simp [ihTeleAtGo, ihTeleAtGo_length nF o i l (k + 1) tl]

theorem ihTeleAtR_length (nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    (ihTeleAtR nF o i l tl).length = tl.length := ihTeleAtGo_length nF o i l 0 tl

theorem mem_ihTeleAtGo {nF o i l : Nat} :
    ∀ {k : Nat} {tl : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm},
      d ∈ ihTeleAtGo nF o i l k tl → ∃ d' ∈ tl, d.2.1 = d'.2.1
  | _, [], _, h => nomatch h
  | k, d' :: tl, d, h => by
    simp only [ihTeleAtGo, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d', List.mem_cons_self, rfl⟩
    · obtain ⟨d'', hd'', he⟩ := mem_ihTeleAtGo h
      exact ⟨d'', List.mem_cons_of_mem _ hd'', he⟩


/-- The recursor's `(p⃗, M, m⃗)` variables under `m` binders below the
`nF` fields (`recPrefixBvarsM`'s shape). -/
def prefixVarsAV (nP n nF m : Nat) : List AnnotTerm :=
  ((List.range nP).map fun k => AnnotTerm.bvar (nP + nF + n + 1 + m - 1 - k)) ++ [.bvar (nF + n + m)] ++
    (List.range n).map fun l => AnnotTerm.bvar (nF + n - 1 - l + m)

/-- **The ih application** for recursive field `i` under `e` extra
binders between the fields and the minors: under the field's telescope
(a λ-tower at bit `b`), the function `Rm m` (spelled under the `m`
telescope binders) at the block's variables, the field's index
readings moved under the fields and the field applied to the
telescope's variables — `λ a⃗, r p⃗ M m⃗ e⃗_i(a⃗) (f_i a⃗)`. -/
def ihAppAVb (b : Nat) (Rm : Nat → AnnotTerm) (nP n nF e i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) : AnnotTerm :=
  mkLamsC b (ihTeleAtR nF (n + 1 + e) i 0 tl)
    (AnnotTerm.mkAppN (Rm tl.length) (prefixVarsAV nP n nF (tl.length + e) ++
      Eis.map (ihIdxAtM nF (n + 1 + e) i 0 tl.length) ++
      [AnnotTerm.mkAppN (.bvar (nF - 1 - i + tl.length)) (teleVarsAV tl.length)]))

/-! ## The squash regime's body -/

/-- The source of field `j` among the constructor's index expressions:
the first index position whose expression is the field's variable
(`none` when the field is not an index — a `Prop` field under the
subsingleton criterion). -/
def srcOfEs (Es : List AnnotTerm) (nF j : Nat) : Option Nat :=
  (List.range Es.length).find? fun l =>
    match Es.getD l default with
    | .bvar k => k = nF - 1 - j
    | _ => false

/-- The sources of all `nF` fields. -/
def srcList (Es : List AnnotTerm) (nF : Nat) : List (Option Nat) :=
  (List.range nF).map (srcOfEs Es nF)

/-- The constructor's field telescope lifted `o` under (past the block
between the fields and the parameters), as binder data. -/
def fieldTeleAt (o : Nat) (Fs : List AnnotTerm) : List (Nat × Nat × AnnotTerm) :=
  (liftFields o 0 Fs).map fun F => (0, 0, F)

/-- **The squash regime's recursor body** at depth `1` below the
K-frame (task #202 A2): the field telescope (lifted past the major,
the indices, the minors and the motive) bound at the elimination bit,
the (only) minor at the field variables and the ih applications (the
function below the parameters, `nIdx + 1` extras between the fields
and the minors), applied to the sources — the fields read off the
index variables. -/
def sqFixBodyAV (ℓ nP n nIdx : Nat) (Fs Es : List AnnotTerm) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN
    (mkLamsC ℓ (fieldTeleAt (nIdx + n + 2) Fs)
      (AnnotTerm.mkAppN (.bvar (Fs.length + 1 + nIdx + n - 1))
        (teleVarsAV Fs.length ++ (recIdx rs Fs.length).map fun i =>
          ihAppAVb ℓ (fun m => .bvar (m + Fs.length + 1 + nIdx + n + 1 + nP)) nP n Fs.length
            (nIdx + 1) i (tls.getD i []) (Eis.getD i []))))
    ((srcList Es Fs.length).map (srcAV nIdx 1))

end ConLeche.Semantics
