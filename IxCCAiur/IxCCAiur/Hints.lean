import Aiur.Library.U32.Hints
import Aiur.Library.U64.Hints
import Aiur.Library.U32.Goldilocks
import Aiur.Modules.Link

/-! # Host advice for lowered programs

The lowered module reads host advice (`hint`) on:
* `bytes_le` (`Aiur.Library.U64.hints`),
* `u32.{bytes,sub,add,add3,lt}` (`Aiur.Library.U32.hints`),
* `ixcc.divmod` (quotient and remainder for 56-bit field division helpers),
* `ixcc.divmod64` (quotient and remainder for 64-bit word division helper `Lower.wDivmod`),
* `ixcc.guess.<fn>` (Tier-2 verified `guess` hints answered by evaluating the
  original pure-Lean function in the unmodified pre-guess advice program).

Advice is outside the program's meaning. In Formal Aiur's source semantics a
hint evaluates to any constant of its type (`Aiur.Generic.SourceSemantics`,
rule `hint`), and the lowered program checks what it is given: the division
helpers check `q * y + r = x` and `r < y` on range-checked words
(`Gadgets.divmod_sound`, `Gadgets.wDivmod_sound`). A wrong answer here loses
a derivation; it cannot make a wrong one.

`dispatcher` and `dispatcherWithAdvice` are the honest providers for the Lean
evaluator (`Aiur.Modules.Prepared.run`). The Rust host registers the same
channels (`crates/aiur/src/library/{u32,u64,ixcc}.rs`). -/

namespace IxCC.AiurBackend.Hints

/-- The number whose little-endian bytes are `bytes`: eight fields, each below `256`. -/
def wordOfBytes {F : Type} (toNat : F → Nat) (bytes : List (Aiur.Constant F)) : Option Nat :=
  if bytes.length != 8 then none else
    bytes.foldr (fun b acc => match b, acc with
      | .field x, some n => if toNat x < 256 then some (toNat x + 256 * n) else none
      | _, _ => none) (some 0)

/-- The honest advice for a lowered program over a field whose elements are
read as naturals by `toNat`: `(x / y, x % y)` on `ixcc.divmod` (Lean's
conventions at `y = 0`: quotient `0`, remainder `x`); on `ixcc.divmod64`, for
two 64-bit words given as their little-endian bytes, the quotient and the
remainder as 32-bit halves `(q % 2^32, q / 2^32, r % 2^32, r / 2^32)` (the same
conventions at `y = 0`); plus `UInt64` and `UInt32` library advice on every
other channel. -/
def dispatcher {F : Type} [NatCast F] (toNat : F → Nat) : Aiur.HintDispatcher F :=
  fun channel key =>
    match channel, key with
    | "ixcc.divmod", .tuple [.field x, .field y] =>
      .ok (.tuple [.field ((toNat x / toNat y : Nat) : F), .field ((toNat x % toNat y : Nat) : F)])
    | "ixcc.divmod", _ => .error (.message "invalid divmod key")
    | "ixcc.divmod64", .tuple [.tuple xs, .tuple ys] =>
      match wordOfBytes toNat xs, wordOfBytes toNat ys with
      | some x, some y =>
        let q := x / y
        let r := x % y
        .ok (.tuple [.field ((q % 4294967296 : Nat) : F), .field ((q / 4294967296 : Nat) : F),
          .field ((r % 4294967296 : Nat) : F), .field ((r / 4294967296 : Nat) : F)])
      | _, _ => .error (.message "invalid divmod64 key")
    | "ixcc.divmod64", _ => .error (.message "invalid divmod64 key")
    | _, _ =>
      Aiur.Library.U64.hints toNat
        (Aiur.Library.U32.hints toNat (fun _ _ => .error .unavailable)) channel key

/-- Extended honest host advice supporting Tier-2 `"ixcc.guess.<fn>"` channels by
executing the corresponding pure-Lean entrypoint (`Prog::<fn>_advice` if present,
otherwise `Prog::<fn>`) in the unmodified pre-guess `Aiur.Modules.Prepared` program. -/
def dispatcherWithAdvice {F : Type} [Field F] [DecidableEq F] (toNat : F → Nat)
    (advice : Option (Σ p : Aiur.Modules.Program F, Aiur.Modules.Prepared p))
    (fuel : Nat := 100000000) : Aiur.HintDispatcher F :=
  let base := dispatcher toNat
  fun channel key =>
    if channel.startsWith "ixcc.guess." then
      match advice with
      | none => .error (.message s!"no advice program provided for guess channel '{channel}'")
      | some ⟨_, prep⟩ =>
        let fnName := String.ofList (channel.toList.drop 11)
        let advEntry := "Prog::" ++ fnName ++ "_advice"
        let entryName := if (prep.find? advEntry).isSome then advEntry else "Prog::" ++ fnName
        match key with
        | .tuple args =>
          let adviceHints := prep.environment.source.checkedHints base
          match prep.run entryName (args.map Aiur.Constant.toValue) fuel adviceHints with
          | .ok (value, _) =>
            match value.toConstant? with
            | some c => .ok c
            | none => .error (.message s!"guess advice '{entryName}' returned pointer-bearing value")
          | .error e => .error (.message s!"guess advice '{entryName}' failed: {e}")
        | _ => .error (.message s!"invalid guess key for '{channel}': expected tuple")
    else
      base channel key

end IxCC.AiurBackend.Hints
