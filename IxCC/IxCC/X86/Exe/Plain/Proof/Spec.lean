import IxCC.X86.Exe.Code
import IxCC.X86.Exe.Process

/-! # Specification of the Plain Standalone Executable Shell

Defines the exact observable system-call behavior (`PlainShows`) of the plain
`--exe` shell (`X86.Exe.Code.shell`) under the **same three platform
specifications** as the proved `--machine` shell (`Process.Loaded`,
`Process.Syscall`, `Process.Step`):

1. Confinement: `prctl(PR_SET_NO_NEW_PRIVS, 1)` then `seccomp(SET_MODE_FILTER, 0, &fprog)`.
   If either returns nonzero, writes `Message.confine` to stderr and exits 75.
2. Argument count & decimal parsing (`parseArgBytes`, `parseArgsList`):
   - Wrong count (`argc ≠ arity + 1`) → writes `Message.count` to stderr, exits 2.
   - Any argument empty or containing a non-ASCII-digit byte → writes `Message.numeral`, exits 3.
   - Any argument a valid decimal numeral `≥ 2^64` → writes `Message.natOverflow`, exits 67.
   - Otherwise yields `ns : List Nat` (`ns.length = arity`, `∀ n ∈ ns, n < 2^64`).
3. Two object calls (`cx_init` then `root(region, ns[0], ..., ns[4])`) under
   valid `X86.LinkedAt` drivers keeping `Driver.Ok textSize`:
   - `.ok (some (.nat v))` (for `.nat`) or `.ok (some (.ctor c []))` (`c < n`, for `.enum n`):
     writes `renderPlain result v` to stdout and exits 0 (or 74 if a write fails).
   - Wrongly tagged / out-of-range result word → writes `Message.notValue` to stderr, exits 71.
   - `.resource .heap | .stack | .natOverflow` / `.trap` → writes matching error message, exits 65..68.
   - `.timeout` → makes no system calls past confinement.
   - `.stuck` → the only case where arbitrary system calls past confinement are permitted. -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.Sem (Result Obs)

/-! ## Decimal argument parsing specification -/

/-- Outcome of parsing one C-string argument as an unsigned 64-bit decimal numeral. -/
inductive ParseResult where
  | ok (n : Nat)
  | overflow
  | bad
  deriving DecidableEq, Repr

/-- Accumulate decimal digits from ASCII byte values (`48..57`), returning `none`
on the first non-digit byte. -/
def parseDigitsAux (acc : Nat) : List Nat → Option Nat
  | [] => some acc
  | b :: rest =>
    if 48 ≤ b ∧ b ≤ 57 then parseDigitsAux (acc * 10 + (b - 48)) rest
    else none

/-- Parse one argument's bytes as a non-empty decimal natural number (`< 2^64`). -/
def parseArgBytes : List Nat → ParseResult
  | [] => .bad
  | b :: rest =>
    match parseDigitsAux 0 (b :: rest) with
    | none => .bad
    | some n => if n < 2 ^ 64 then .ok n else .overflow

/-- Outcome of parsing an argument list left-to-right (stopping at the first error). -/
inductive ParseArgsResult where
  | ok (ns : List Nat)
  | overflow
  | bad
  deriving DecidableEq, Repr

/-- Parse a list of argument byte-lists left-to-right. -/
def parseArgsList : List (List Nat) → ParseArgsResult
  | [] => .ok []
  | a :: rest =>
    match parseArgBytes a with
    | .ok n =>
      match parseArgsList rest with
      | .ok ns => .ok (n :: ns)
      | .overflow => .overflow
      | .bad => .bad
    | .overflow => .overflow
    | .bad => .bad

theorem parseArgsList_ok_length {args : List (List Nat)} {ns : List Nat}
    (h : parseArgsList args = .ok ns) : ns.length = args.length := by
  induction args generalizing ns with
  | nil => simp [parseArgsList] at h; subst h; rfl
  | cons a rest ih =>
    simp only [parseArgsList] at h
    cases ha : parseArgBytes a with
    | overflow => simp [ha] at h
    | bad => simp [ha] at h
    | ok n =>
      simp only [ha] at h
      cases hr : parseArgsList rest with
      | overflow => simp [hr] at h
      | bad => simp [hr] at h
      | ok ns' =>
        simp only [hr, ParseArgsResult.ok.injEq] at h
        subst h
        simp [ih hr]

theorem parseArgsList_ok_lt {args : List (List Nat)} {ns : List Nat}
    (h : parseArgsList args = .ok ns) : ∀ n ∈ ns, n < 2 ^ 64 := by
  induction args generalizing ns with
  | nil => simp [parseArgsList] at h; subst h; intro _ hm; cases hm
  | cons a rest ih =>
    simp only [parseArgsList] at h
    cases ha : parseArgBytes a with
    | overflow => simp [ha] at h
    | bad => simp [ha] at h
    | ok n =>
      simp only [ha] at h
      cases hr : parseArgsList rest with
      | overflow => simp [hr] at h
      | bad => simp [hr] at h
      | ok ns' =>
        simp only [hr, ParseArgsResult.ok.injEq] at h
        subst h
        have hn : n < 2 ^ 64 := by
          cases a with
          | nil => simp [parseArgBytes] at ha
          | cons b bs =>
            simp only [parseArgBytes] at ha
            cases hd : parseDigitsAux 0 (b :: bs) with
            | none => simp [hd] at ha
            | some m =>
              simp only [hd] at ha
              split at ha
              · cases ha; assumption
              · cases ha
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hn
        · exact ih hr x hmem

/-! ## Decimal result rendering specification -/

/-- Fuel-bounded helper for decimal ASCII digit rendering (least-significant digit first into `acc`). -/
def natDecimalAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let q := n / 10
    let r := n % 10
    let acc' := UInt8.ofNat (r + 48) :: acc
    if q == 0 then acc' else natDecimalAux fuel q acc'

/-- Canonical ASCII decimal digits of a natural number `n`. -/
def natDecimal (n : Nat) : List UInt8 :=
  natDecimalAux (n + 1) n []

/-- Exact output bytes written to stdout by the plain `--exe` shell:
`"<decimal>\n"` for `.nat` and `"#<decimal>\n"` for `.enum _`. -/
def renderPlain (kind : ResultKind) (v : Nat) : List UInt8 :=
  match kind with
  | .nat => natDecimal v ++ [10]
  | .enum _ => (35 : UInt8) :: natDecimal v ++ [10]

theorem natDecimalAux_fuel_irrel :
    ∀ (f1 f2 n : Nat) (acc : List UInt8), n < f1 → n < f2 →
      natDecimalAux f1 n acc = natDecimalAux f2 n acc
  | 0, _, _, _, h1, _ => by omega
  | _, 0, _, _, _, h2 => by omega
  | f1 + 1, f2 + 1, n, acc, h1, h2 => by
    unfold natDecimalAux
    dsimp only
    by_cases hq : n / 10 == 0
    · simp [hq]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      have hqlt : n / 10 < n := Nat.div_lt_self (by
        have : n / 10 ≠ 0 := by simpa using hq
        omega) (by decide)
      exact natDecimalAux_fuel_irrel f1 f2 (n / 10) _ (by omega) (by omega)

theorem natDecimal_eq_step (n : Nat) (h : n / 10 ≠ 0) :
    natDecimal n = natDecimal (n / 10) ++ [UInt8.ofNat (n % 10 + 48)] := by
  have aux_app : ∀ (f m : Nat) (a b : List UInt8),
      natDecimalAux f m (a ++ b) = natDecimalAux f m a ++ b := by
    intro f
    induction f with
    | zero => intro m a b; rfl
    | succ f ih =>
      intro m a b
      unfold natDecimalAux
      dsimp only
      split
      · simp
      · rw [show UInt8.ofNat (m % 10 + 48) :: (a ++ b) = (UInt8.ofNat (m % 10 + 48) :: a) ++ b from rfl]
        exact ih (m / 10) _ b
  unfold natDecimal
  show natDecimalAux (n + 1) n [] = _
  rw [natDecimalAux]
  have hq : (n / 10 == 0) = false := by simpa using h
  rw [hq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hqlt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
  rw [natDecimalAux_fuel_irrel n (n / 10 + 1) (n / 10) [UInt8.ofNat (n % 10 + 48)] hqlt (Nat.lt_succ_self _)]
  have := aux_app (n / 10 + 1) (n / 10) [] [UInt8.ofNat (n % 10 + 48)]
  simpa using this

theorem natDecimal_lt_ten {n : Nat} (h : n < 10) :
    natDecimal n = [UInt8.ofNat (n + 48)] := by
  unfold natDecimal
  unfold natDecimalAux
  have hq : n / 10 = 0 := Nat.div_eq_of_lt h
  have hr : n % 10 = n := Nat.mod_eq_of_lt h
  simp [hq, hr]

theorem natDecimal_length_le (n : Nat) (h : n < 2 ^ 63) :
    1 ≤ (natDecimal n).length ∧ (natDecimal n).length ≤ 19 := by
  have hstep : ∀ (k m : Nat), m < 10 ^ k → 1 ≤ k → 1 ≤ (natDecimal m).length ∧ (natDecimal m).length ≤ k := by
    intro k
    induction k with
    | zero => intro _ _ hk; omega
    | succ k ih =>
      intro m hm _
      by_cases h10 : m < 10
      · rw [natDecimal_lt_ten h10]; simp
      · have hq0 : m / 10 ≠ 0 := by omega
        rw [natDecimal_eq_step m hq0, List.length_append]
        have hk1 : 1 ≤ k := by
          cases k with
          | zero => simp at hm; omega
          | succ _ => omega
        have hqm : m / 10 < 10 ^ k := by
          rw [Nat.pow_succ] at hm; omega
        have ⟨hl, hu⟩ := ih (m / 10) hqm hk1
        simp only [List.length_singleton]
        omega
  exact hstep 19 n (by omega) (by decide)

/-! ## Generic `write` loop + exit trace specification -/

/-- The system calls of writing `rest` to file descriptor `fd` (possibly in
multiple short writes) and then exiting with `status` (if `ok = true`), or
exiting with `writeFailed` (`74`) when a write returns `≤ 0` or `> rest.length`
(`ok = false`). -/
inductive WriteSeq (fd : Word) (status : Nat) : List UInt8 → Bool → List Sys → Prop where
  | done : WriteSeq fd status [] true [.exit (UInt64.ofNat status)]
  | step {rest : List UInt8} {r : Word} {ok : Bool} {ρ : List Sys}
      (hne : rest ≠ []) (hpos : 0 < r.toNat) (hle : r.toNat ≤ rest.length)
      (hrest : WriteSeq fd status (rest.drop r.toNat) ok ρ) :
      WriteSeq fd status rest ok (.write fd rest r :: ρ)
  | refused {rest : List UInt8} {r : Word}
      (hne : rest ≠ []) (hbad : r.toNat = 0 ∨ 2 ^ 63 ≤ r.toNat ∨ rest.length < r.toNat) :
      WriteSeq fd status rest false [.write fd rest r, .exit (UInt64.ofNat writeFailed)]

theorem writeSeq_nil (fd : Word) (status : Nat) (m : List UInt8) :
    ∃ ok ρ, WriteSeq fd status m ok ρ ∧ ([] : List Sys) <+: ρ := by
  cases m with
  | nil => exact ⟨true, _, .done, List.nil_prefix⟩
  | cons x xs => exact ⟨false, _, .refused (r := 0) (List.cons_ne_nil x xs) (.inl rfl), List.nil_prefix⟩

/-- A prefix of a stderr error report for message `m` (at arity `arity`). -/
def ReportsMsg (arity : Nat) (m : Message) (ρ : List Sys) : Prop :=
  ∃ ok full, WriteSeq 2 m.status ((m.text arity).toUTF8.toList) ok full ∧ ρ <+: full

/-- A prefix of a stdout result write for `(kind, v)` followed by `exit(0)`. -/
def PrintsResult (kind : ResultKind) (v : Nat) (ρ : List Sys) : Prop :=
  ∃ ok full, WriteSeq 1 0 (renderPlain kind v) ok full ∧ ρ <+: full

/-- Confinement refusal for the plain shell (at arity `arity`, read-only data at `D`). -/
def PlainRefused (arity D : Nat) (σ : List Sys) : Prop :=
  (∃ r ρ, r ≠ 0 ∧ ReportsMsg arity .confine ρ ∧
    σ <+: .prctl prSetNoNewPrivs 1 r :: ρ) ∨
  (∃ r ρ, r ≠ 0 ∧ ReportsMsg arity .confine ρ ∧
    σ <+: .prctl prSetNoNewPrivs 1 0 :: .seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr D)) r :: ρ)

/-! ## Object-call outcomes & top-level `PlainShows` specification -/

/-- Outcome of one invocation of `(cx_init, root)` on parsed arguments `ns`. -/
inductive PlainOutcome where
  | value (v : Nat)
  | notValue
  | fail (m : Message)
  | timeout
  | stuck
  deriving DecidableEq, Repr

/-- What `L.call r ns k` says about the plain shell's outcome for `result : ResultKind`. -/
def PlainCallMatches (result : ResultKind) (res : Result (Option Obs)) : PlainOutcome → Prop
  | .value v =>
    match result with
    | .nat => res = .ok (some (.nat v)) ∧ v < 2 ^ 63
    | .enum n => res = .ok (some (.ctor v [])) ∧ v < n
  | .notValue =>
    match result with
    | .nat => res = .ok none ∨ (∃ o, res = .ok (some o) ∧ ∀ v, o ≠ .nat v)
    | .enum n => res = .ok none ∨ (∃ o, res = .ok (some o) ∧ ∀ c, c < n → o ≠ .ctor c [])
  | .fail .heap => res = .resource .heap
  | .fail .stack => res = .resource .stack
  | .fail .natOverflow => res = .resource .natOverflow
  | .fail .trap => res = .trap
  | .fail _ => False
  | .timeout => res = .timeout
  | .stuck => res = .stuck

/-- Relation between `(linked, textSize, ns)` and a `PlainOutcome` across valid
`X86.LinkedAt` drivers (`Driver.Ok textSize` at both `cx_init` and root sites). -/
def objPlainCall (linked : Driver → Driver.Site → LinkedAt) (textSize : Nat) (result : ResultKind)
    (ns : List Nat) (out : PlainOutcome) : Prop :=
  ∃ (D : Driver) (site : Driver.Site) (r : Linked.Root) (k : Nat),
    (linked D site).linked.roots[0]? = some r ∧
    D.Ok textSize ∧
    (D.withSite site).Ok textSize ∧
    PlainCallMatches result ((linked D site).call r ns k) out

/-- **Top-level observable trace specification of the plain `--exe` shell**:
from `Process.Loaded`, every finite system-call trace `σ` is either:
- a confinement refusal (`PlainRefused`), or
- a prefix of `started D` (stopped during confinement), or
- `started D ++ ρ` where:
  - wrong argument count (`args.length ≠ arity`, or `argc = 0` with `args = []`) → `ReportsMsg arity .count ρ`;
  - valid count & `parseArgsList args = .overflow` → `ReportsMsg arity .natOverflow ρ`;
  - valid count & `parseArgsList args = .bad` → `ReportsMsg arity .numeral ρ`;
  - valid count & `parseArgsList args = .ok ns` → either:
    - `objPlainCall ... .value v` and `PrintsResult result v ρ`,
    - `objPlainCall ... .notValue` and `ReportsMsg arity .notValue ρ`,
    - `objPlainCall ... (.fail m)` and `ReportsMsg arity m ρ`,
    - `objPlainCall ... .timeout` and `ρ = []`, or
    - `objPlainCall ... .stuck` (the ONLY case allowing arbitrary syscalls past `started D`). -/
def PlainShows (linked : Driver → Driver.Site → LinkedAt) (textSize arity : Nat) (result : ResultKind)
    (D : Nat) (args : List (List Nat)) (σ : List Sys) : Prop :=
  PlainRefused arity D σ ∨
  σ <+: started D ∨
  ∃ ρ, σ = started D ++ ρ ∧
    ((args.length ≠ arity ∨ args = []) ∧ ReportsMsg arity .count ρ ∨
     args.length = arity ∧
      match parseArgsList args with
      | .overflow => ReportsMsg arity .natOverflow ρ
      | .bad => ReportsMsg arity .numeral ρ
      | .ok ns =>
        (∃ v, objPlainCall linked textSize result ns (.value v) ∧ PrintsResult result v ρ) ∨
        (objPlainCall linked textSize result ns .notValue ∧ ReportsMsg arity .notValue ρ) ∨
        (∃ m, objPlainCall linked textSize result ns (.fail m) ∧ ReportsMsg arity m ρ) ∨
        (objPlainCall linked textSize result ns .timeout ∧ ρ = []) ∨
        objPlainCall linked textSize result ns .stuck)

/-! ## `other` syscall exclusion (for `plain_shell_unspecified`) -/

private theorem no_other_writeSeq {fd : Word} {status : Nat} {m : List UInt8} {ok : Bool}
    {ρ : List Sys} (h : WriteSeq fd status m ok ρ) : ∀ w, .other w ∉ ρ := by
  induction h with
  | done => intro w hm; simp at hm
  | step _ _ _ _ ih =>
    intro w hm
    rcases List.mem_cons.mp hm with h1 | h2
    · cases h1
    · exact ih w h2
  | refused _ _ =>
    intro w hm
    simp at hm

private theorem no_other_prefix {p q : List Sys} (hp : p <+: q) {w : Word}
    (hq : .other w ∉ q) : .other w ∉ p := by
  obtain ⟨t, rfl⟩ := hp
  intro hm
  exact hq (List.mem_append_left t hm)

private theorem no_other_started {D : Nat} {w : Word} : .other w ∉ started D := by
  simp [started]

/-- **An undocumented system call (`Sys.other`) occurs in `PlainShows` ONLY when
argument count & parsing succeeded (`args.length = arity`, `parseArgsList args = .ok ns`)
and the object call is `.stuck`!** -/
theorem PlainShows.stuck_of_other {linked : Driver → Driver.Site → LinkedAt} {textSize arity : Nat} {result : ResultKind}
    {D : Nat} {args : List (List Nat)} {σ : List Sys} {w : Word}
    (h : PlainShows linked textSize arity result D args (σ ++ [.other w])) :
    args.length = arity ∧
    ∃ ns, parseArgsList args = .ok ns ∧
      objPlainCall linked textSize result ns .stuck ∧
      started D <+: σ := by
  have hmem : .other w ∈ σ ++ [.other w] := by simp
  rcases h with href | hpre | ⟨ρ, heq, hbody⟩
  · rcases href with ⟨r, ρ, _, ⟨ok, full, hw, hp⟩, hpre⟩ | ⟨r, ρ, _, ⟨ok, full, hw, hp⟩, hpre⟩
    · have h1 := no_other_prefix hpre (by
        intro hm
        rcases List.mem_cons.mp hm with h0 | h0
        · cases h0
        · exact no_other_prefix hp (no_other_writeSeq hw w) h0)
      exact absurd hmem h1
    · have h1 := no_other_prefix hpre (by
        intro hm
        rcases List.mem_cons.mp hm with h0 | h0
        · cases h0
        · rcases List.mem_cons.mp h0 with h0 | h0
          · cases h0
          · exact no_other_prefix hp (no_other_writeSeq hw w) h0)
      exact absurd hmem h1
  · exact absurd hmem (no_other_prefix hpre no_other_started)
  · have hmemρ : .other w ∈ ρ := by
      rw [heq] at hmem
      rcases List.mem_append.mp hmem with hs | hr
      · exact absurd hs no_other_started
      · exact hr
    have hstPre : started D <+: σ := by
      have hlen : (started D).length ≤ σ.length := by
        by_cases hle : (started D).length ≤ σ.length
        · exact hle
        · have hlt' : σ.length < (started D).length := by omega
          have hmemS : .other w ∈ started D := by
            have hi : σ.length < (started D ++ ρ).length := by rw [← heq]; simp
            have hg : (started D ++ ρ)[σ.length] = .other w := by
              have := congrArg (fun l => l[σ.length]?) heq
              simp at this
              rw [List.getElem?_eq_getElem hi] at this
              exact Option.some.inj this.symm
            rw [List.getElem_append_left hlt'] at hg
            rw [← hg]
            exact List.getElem_mem hlt'
          exact absurd hmemS no_other_started
      have htk := congrArg (List.take (started D).length) heq
      rw [List.take_append_of_le_length hlen, List.take_left] at htk
      exact ⟨σ.drop (started D).length, by
        have htd := List.take_append_drop (started D).length σ
        rw [htk] at htd
        exact htd⟩
    rcases hbody with ⟨_, ⟨ok, full, hw, hp⟩⟩ | ⟨hlen, hparse⟩
    · exact absurd hmemρ (no_other_prefix hp (no_other_writeSeq hw w))
    · cases hp : parseArgsList args with
      | overflow =>
        rw [hp] at hparse
        obtain ⟨ok, full, hw, hpr⟩ := hparse
        exact absurd hmemρ (no_other_prefix hpr (no_other_writeSeq hw w))
      | bad =>
        rw [hp] at hparse
        obtain ⟨ok, full, hw, hpr⟩ := hparse
        exact absurd hmemρ (no_other_prefix hpr (no_other_writeSeq hw w))
      | ok ns =>
        rw [hp] at hparse
        rcases hparse with ⟨v, _, ⟨ok, full, hw, hpr⟩⟩ | ⟨_, ⟨ok, full, hw, hpr⟩⟩ |
          ⟨m, _, ⟨ok, full, hw, hpr⟩⟩ | ⟨_, rfl⟩ | hstuck
        · exact absurd hmemρ (no_other_prefix hpr (no_other_writeSeq hw w))
        · exact absurd hmemρ (no_other_prefix hpr (no_other_writeSeq hw w))
        · exact absurd hmemρ (no_other_prefix hpr (no_other_writeSeq hw w))
        · simp at hmemρ
        · exact ⟨hlen, ns, rfl, hstuck, hstPre⟩

end IxCC.X86.Exe.Plain
