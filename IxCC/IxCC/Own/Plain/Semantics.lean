import IxCC.Own.Plain.Program
import IxCC.Own.Rc.Release
import IxCC.Own.Rc.Reuse
import IxCC.Own.Semantics

/-! Executable plain-RC semantics. The source clock/join discipline is the
existing Fir/Own discipline; inc and total dropAll stutter at that clock.
Plain.Proof.Candidate proves refinement for the actual checked body map.
-/

namespace IxCC.Own.Plain
open IxCC.Sem (Result)
open IxCC.Fir (Var FunId JoinId)

def Program.tables (P : Program) : Own.Tables :=
  { ctors := P.source.ctors, known := P.source.known }

mutual
def Code.size : Code → Nat
  | .act _ k | .bind _ _ k | .reset _ _ _ _ _ k | .reuse _ _ _ _ _ k | .dropSlot _ k => k.size + 1
  | .jp _ _ _ _ b k => b.size + k.size + 1
  | .case _ alts d => Code.altsSize alts + Code.optSize d + 2
  | _ => 1
def Code.altsSize : List Alt → Nat
  | [] => 0
  | .mk _ b :: rest => b.size + Code.altsSize rest
def Code.optSize : Option Code → Nat
  | none => 0
  | some c => c.size
end

theorem Code.size_pos (c : Code) : 0 < c.size := by
  cases c <;> simp [Code.size]

/-- The placeholder body written into a reset cell: same constructor, all fields `.erased`
(immediates), preserving `BodyCtorOk`, `HeapOk`, and `Readback.Scanned`. -/
def resetShell (ctor : Fir.CtorInfo) : Own.Body :=
  { ctor, fields := List.replicate ctor.arity .erased }

def incList (H : Own.Heap) : List Own.RVal → Option Own.Heap
  | [] => some H
  | v :: vs => do incList (← Rc.inc H v 1) vs

/-- Execute a `reset` of variable `x` with live-field bitmask `mask` (`bit j = 1` means field `j`
is kept live; `0` means field `j` is dead and dropped on the unique path). -/
def evalResetMask (ρ : Own.Env) (H : Own.Heap) (x : Var) (ctor : Fir.CtorInfo)
    (mask : Nat) (uniq : Bool) : Result (Own.RVal × Own.Heap) :=
  if ctor.fieldless then .stuck else
  match ρ.get? x with
  | none => .stuck
  | some (.loc l) =>
    match H.cell? l with
    | some (.live 1 .dyn b) =>
      let deadFields := (b.fields.zipIdx).filterMap fun (u, j) =>
        if !Nat.testBit mask j then some u else none
      match Rc.reuseCell H l (resetShell ctor) with
      | some (sv, H₁) => Result.ofOption ((Rc.dropAll H₁ deadFields).map (sv, ·))
      | none => .stuck
    | some (.live _ _ b) =>
      if uniq then .stuck
      else
        let liveFields := (b.fields.zipIdx).filterMap fun (u, j) =>
          if Nat.testBit mask j then some u else none
        match incList H liveFields with
        | some H₁ => Result.ofOption ((Rc.dropAll H₁ [.loc l]).map (.erased, ·))
        | none => .stuck
    | _ => .stuck
  | some _ => if uniq || mask != 0 then .stuck else .ok (.erased, H)

/-- Execute a `reuse` of slot value `sv` for constructor `ctor` with arguments `args`. -/
def evalReuseVal (ρ : Own.Env) (H : Own.Heap) (sv : Own.RVal) (ctor : Fir.CtorInfo)
    (args : List Fir.Arg) (uniq : Bool) : Result (Own.RVal × Own.Heap) :=
  match Own.evalArgs ρ args with
  | none => .stuck
  | some vs =>
    if !ctor.fieldless && vs.length = ctor.arity then
      match sv with
      | .loc l => Result.ofOption (Rc.reuseCell H l { ctor, fields := vs })
      | .erased => if uniq then .stuck else .ok (Own.Heap.alloc .rc H { ctor, fields := vs })
      | _ => .stuck
    else .stuck

/-- Drop an unused reset slot value (`loc` is recycled via `dropAll`, `.erased` is a no-op). -/
def evalDropVal (H : Own.Heap) (sv : Own.RVal) : Result Own.Heap :=
  Result.ofOption (Rc.dropAll H [sv])

def evalAction (ρ : Own.Env) (H : Own.Heap) : Action → Result Own.Heap
  | .inc x n =>
    match ρ.get? x with
    | some v => Result.ofOption (Rc.inc H v n)
    | none => .stuck
  | .dec x =>
    match ρ.get? x with
    | some v => Result.ofOption (Rc.dropAll H [v])
    | none => .stuck

def evalRhs (T : Own.Tables) (ρ : Own.Env) (H : Own.Heap) (r : Fir.Rhs) :
    Result (Own.RVal × Own.Heap) :=
  Own.evalRhs .rc T ρ H (match r with
    | .ctor c args => .alloc c args .shared
    | .proj x c i => .proj x c i
    | _ => .fir r)

structure JEntry where
  id : JoinId
  charged : Bool
  env : Own.Env
  params : List Var
  body : Code
  isRec : Bool

def JEntry.weight (e : JEntry) : Nat := if e.charged then 0 else e.body.size

def jweight : List JEntry → Nat
  | [] => 0
  | e :: J => e.weight + jweight J

def lookupJ (j : JoinId) : List JEntry → Option (JEntry × List JEntry)
  | [] => none
  | e :: J => if e.id = j then some (e, J) else lookupJ j J

theorem lookupJ_weight (j : JoinId) :
    ∀ {J : List JEntry} {e : JEntry} {rest : List JEntry},
      lookupJ j J = some (e, rest) → e.weight + jweight rest ≤ jweight J
  | [], _, _, h => by simp [lookupJ] at h
  | e' :: J, e, rest, h => by
    simp only [lookupJ] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jweight]
    · have := lookupJ_weight j h
      simp only [jweight]
      omega

def JEntry.after (e : JEntry) (rest : List JEntry) : List JEntry :=
  if e.isRec then { e with charged := true } :: rest else rest

theorem JEntry.jweight_after (e : JEntry) (rest : List JEntry) :
    jweight (e.after rest) = jweight rest := by
  unfold JEntry.after
  split <;> simp [jweight, JEntry.weight]

mutual
def eval (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry) (H : Own.Heap)
    (c : Code) (slots : Src.NatMap Own.RVal := .leaf) : Result (Own.RVal × Own.Heap) :=
  match c with
  | .act a c' =>
    match evalAction ρ H a with
    | .ok H' => eval P k ρ J H' c' slots
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .bind x (.call f args) c' =>
    match Own.evalArgs ρ args with
    | some vs =>
      match evalCall P k f vs H with
      | .ok (v, H') => eval P k (ρ.insert x v) J H' c' slots
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .bind x r c' =>
    match evalRhs P.tables ρ H r with
    | .ok (v, H') => eval P k (ρ.insert x v) J H' c' slots
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .reset s x ctor fields uniq c' =>
    match evalResetMask ρ H x ctor (fieldsMask fields) uniq with
    | .ok (sv, H') => eval P k ρ J H' c' (slots.insert s sv)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .reuse x s ctor args uniq c' =>
    match slots.get? s with
    | some sv =>
      match evalReuseVal ρ H sv ctor args uniq with
      | .ok (v, H') => eval P k (ρ.insert x v) J H' c' (slots.erase s)
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .dropSlot s c' =>
    match slots.get? s with
    | some sv =>
      match evalDropVal H sv with
      | .ok H' => eval P k ρ J H' c' (slots.erase s)
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .jp j ps _ rec body c' =>
    eval P k ρ ({
      id := j, charged := false, env := ρ, params := ps,
      body, isRec := rec } :: J) H c' slots
  | .jmp j args =>
    match _h : lookupJ j J, Own.evalArgs ρ args with
    | some (e, rest), some vs =>
      if vs.length = e.params.length then
        if _hc : e.charged then
          match k with
          | 0 => .timeout
          | k + 1 => eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body .leaf
        else eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body .leaf
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.source.known H with
      | some (key, _) => evalAlts P k ρ J H key alts d slots
      | none => .stuck
    | none => .stuck
  | .ret a =>
    match Own.evalArg ρ a with
    | some v => .ok (v, H)
    | none => .stuck
  | .tcall f args =>
    match Own.evalArgs ρ args with
    | some vs => evalCall P k f vs H
    | none => .stuck
  | .trap => .trap
termination_by (k, c.size + jweight J)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hw := lookupJ_weight j _h
       rw [JEntry.jweight_after]
       simp only [JEntry.weight, _hc, Bool.false_eq_true, ↓reduceIte] at hw
       simp only [Code.size]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size]
       omega)

def evalAlts (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry) (H : Own.Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code)
    (slots : Src.NatMap Own.RVal := .leaf) : Result (Own.RVal × Own.Heap) :=
  match alts with
  | [] => match d with
    | some c => eval P k ρ J H c slots
    | none => .stuck
  | .mk key' body :: rest =>
    if key' = key then eval P k ρ J H body slots else evalAlts P k ρ J H key rest d slots
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

def evalCall (P : Program) (k : Nat) (f : FunId) (vs : List Own.RVal) (H : Own.Heap) :
    Result (Own.RVal × Own.Heap) :=
  match P.source.fun? f, P.bodies.get? f with
  | some fd, some body =>
    if vs.length = fd.params.length then
      match k with
      | 0 => .timeout
      | k + 1 => eval P k (Own.bindAll .leaf (fd.params.map (·.1)) vs) [] H body .leaf
    else .stuck
  | _, _ => .stuck
termination_by (k, 0)
end

def run (P : Program) (k : Nat) (f : FunId) (args : List Own.RVal) (H : Own.Heap := {}) :
    Result (Own.RVal × Own.Heap) := evalCall P k f args H

end IxCC.Own.Plain
