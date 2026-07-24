module

public import LSpec
public import Ix.Tc

/-!
`tc-accel-diff` (ignored runner): differential fixtures for the
Ix-specific semantic shortcuts vs the pure path (`TcState.noAccel`,
CLI `IX_TC_NO_ACCEL=1`). The accelerations are shared trusted code in
BOTH kernels (BitVec natives, Decidable natives, `reduceBool`/`reduceNat`
markers, `Fin.val`-through-`Decidable.rec`), so cross-kernel diffing is
structurally blind to a common bug — these fixtures check accelerated
results against genuine pure reduction over the real env
(`IX_PINS_IXE`; the pure path needs real definitions to delta-unfold).
Small literals only: the pure path is exponential in literal size by
design (see `TcState.noAccel`).

Comparison discipline: representation-producing accels (BitVec→Nat,
`ult`) must match the pure result ADDRESS; proof-producing accels
(Decidable) must match the pure result's head CTOR and be def-eq to it —
the canonical accel proof term is a different-but-def-eq witness.
-/

namespace Tests.Tc.AccelDiff

open LSpec
open Ix.Tc

abbrev AE := KExpr .anon

def natLit (n : Nat) : AE := .mkNatLit n
def cA (a : Address) : AE := .mkConst ⟨a, ()⟩ #[]
def appN (f : AE) (args : List AE) : AE := args.foldl .mkApp f

def P := PrimAddrs.canonical

/-- Fresh lazy anon state over the env with the accel switch set. -/
def mkState (ixonEnv : Ixon.Env) (noAccel : Bool) : TcState .anon :=
  { TcState.newLazyAnon ixonEnv with noAccel }

def whnfIn (ixonEnv : Ixon.Env) (noAccel : Bool) (e : AE) :
    Except (TcError .anon) AE :=
  match (TcM.whnf e).run (mkState ixonEnv noAccel) with
  | .ok r _ => .ok r
  | .error err _ => .error err

/-- Head of the result spine references the constant at `a`. -/
def headIs (e : AE) (a : Address) : Bool :=
  match e.collectSpine.1 with
  | .const id _ _ => id.addr == a
  | _ => false

/-- Accel and pure whnf agree on the exact result address. -/
def addrCase (ixonEnv : Ixon.Env) (name : String) (e : AE) : TestSeq :=
  test s!"accel≡pure (addr): {name}"
    ((match whnfIn ixonEnv false e, whnfIn ixonEnv true e with
      | .ok a, .ok p => a.addr == p.addr
      | _, _ => false) : Bool)

/-- Accel and pure whnf agree on the head ctor and are def-eq. -/
def ctorCase (ixonEnv : Ixon.Env) (name : String) (e : AE)
    (expectHead : Address) : TestSeq :=
  test s!"accel≡pure (ctor+defeq): {name}"
    ((match whnfIn ixonEnv false e, whnfIn ixonEnv true e with
      | .ok a, .ok p =>
        headIs a expectHead && headIs p expectHead
          && (match (TcM.isDefEq a p).run (mkState ixonEnv false) with
              | .ok r _ => r
              | .error _ _ => false)
      | _, _ => false) : Bool)

public def run : IO UInt32 := do
  IO.println "tc-accel-diff"
  let some path ← IO.getEnv "IX_PINS_IXE"
    | IO.println "tc-accel-diff: IX_PINS_IXE unset — skipping (needs a \
                  compileinitstd-style .ixe for the pure path's definitions)"
      return 0
  let bytes ← IO.FS.readBinFile path
  match Ixon.deEnvAnon bytes with
  | .error e =>
    IO.eprintln s!"tc-accel-diff: deserialize failed: {e}"
    return 1
  | .ok ixonEnv =>
    let bv (n : Nat) : AE := appN (cA P.bitVecOfNat) [natLit 8, natLit n]
    let seq : TestSeq :=
      addrCase ixonEnv "BitVec.toNat (ofNat 8 5)"
        (appN (cA P.bitVecToNat) [natLit 8, bv 5])
      ++ addrCase ixonEnv "BitVec.ult 8 3 7"
        (appN (cA P.bitVecUlt) [natLit 8, bv 3, bv 7])
      ++ ctorCase ixonEnv "Nat.decLe 3 5 → isTrue"
        (appN (cA P.natDecLe) [natLit 3, natLit 5]) P.decidableIsTrue
      ++ ctorCase ixonEnv "Nat.decEq 4 6 → isFalse"
        (appN (cA P.natDecEq) [natLit 4, natLit 6]) P.decidableIsFalse
      ++ test "verdict parity: checkConst Nat.decLe in both modes"
        ((let ok (noAccel : Bool) : Bool :=
            match (TcM.checkConst (m := .anon) ⟨P.natDecLe, ()⟩).run
                (mkState ixonEnv noAccel) with
            | .ok () _ => true
            | .error _ _ => false
          ok false == ok true && ok false) : Bool)
    lspecIO (.ofList [("tc-accel-diff", [seq])]) []

end Tests.Tc.AccelDiff
