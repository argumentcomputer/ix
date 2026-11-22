import IxCC.Own.Plain.Proof.Owned.Roots
import IxCC.Own.Plain.Proof.StackScope
import IxCC.Own.Plain.Proof.CaptureIdentity
import IxCC.Own.Plain.Proof.Results
import IxCC.Fir.Proof.Env

/-! # The induction invariant over a typing context

`OwnedState` is the invariant of the checked simulation: the lexical scope `live` is kept (the
source checker's scope and the capture identities need it) and ownership is the context's: its
tokens' values are what `Balance` counts, every available variable denotes, every immediate is an
immediate value, every borrowed variable's value can be incremented.

`OwnedStack` says each saved join's body was checked from the context its declaration entered,
the current join context `Δ` maps the join to its captured list, and the saved environments agree
with the current ones on the declaration's lexical scope. A captured variable's denotation is not
kept on the stack: it is taken at the jump, where the checker has made the variable available. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var)

/-- A saved join: its body is checked from the context its declaration entered (`Γd`, the join
context then `Δd`), and `Δ` (the current one) maps it to its captured list. -/
structure OwnedEntry (Δ Δd : JCtx) (Γd : Ctx) (lexd captured : List Var)
    (older : List Fir.JEntry) (ef : Fir.JEntry) (eo : JEntry) : Prop where
  id : eo.id = ef.id
  charged : eo.charged = ef.charged
  params : eo.params = ef.params
  isRec : eo.isRec = ef.isRec
  erases : eraseCode eo.body = ef.body
  typed : checkCode (if ef.isRec then Δd.insert ef.id captured else Δd)
    (Γd.enter captured ef.params) eo.body = .ok ()
  /-- Immediates of the declaration denote themselves in every heap. -/
  imm : ∀ x, Γd.isImm x = true → ∃ v w, eo.env.get? x = some v ∧ ef.env.get? x = some w ∧
    ImmVal v ∧ ∀ H : Heap, Proof.Den H v w
  immIn : ∀ x, Γd.isImm x = true → x ∈ lexd
  sub : ∀ c, c ∈ captured → c ∈ lexd
  nodup : captured.Nodup
  here : Δ.get? ef.id = some captured
  agree : ∀ e, e ∈ older → Δd.get? e.id = Δ.get? e.id
  fresh : ∀ e, e ∈ older → e.id ≠ ef.id

/-- The join stack (Fir and Own side by side), each entry with its declaration's lexical scope. -/
inductive OwnedStack (Δ : JCtx) : Fir.Env → Own.Env → List Var → Joins → List Fir.JEntry →
    List JEntry → Prop
  | nil (ρf : Fir.Env) (ρo : Own.Env) (live : List Var) : OwnedStack Δ ρf ρo live [] [] []
  | cons {ρf : Fir.Env} {ρo : Own.Env} {live lexd captured : List Var} {older : Joins}
      {Δd : JCtx} {Γd : Ctx} {ef : Fir.JEntry} {eo : JEntry} {jf : List Fir.JEntry}
      {jo : List JEntry}
      (entry : OwnedEntry Δ Δd Γd lexd captured jf ef eo)
      (oview : CaptureView eo.env ρo lexd live)
      (fview : ∀ x, x ∈ lexd → ef.env.get? x = ρf.get? x)
      (tail : OwnedStack Δ ef.env eo.env lexd older jf jo) :
      OwnedStack Δ ρf ρo live ((ef.id, lexd) :: older) (ef :: jf) (eo :: jo)

/-- **The simulation invariant** over a typing context. -/
structure OwnedState (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Var) (Γ : Ctx) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (lex : Joins) (Δ : JCtx) (Jf : List Fir.JEntry) (Jo : List JEntry) : Prop where
  den : ∀ x, Γ.avail x = true → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w
  roots : ∃ toks, Ctx.Tokens Γ toks ∧ EnvRoots ρo toks owned
  counts : Balance H external owned
  known : ∀ x, Γ.known x = true → x ∈ live
  distinct : live.Nodup
  immOk : ∀ x, Γ.isImm x = true → ∃ v, ρo.get? x = some v ∧ ImmVal v
  borrowed : ∀ x, Γ.borrowed x = true → ∃ v, ρo.get? x = some v ∧ CanDup H v
  epochs : ∀ x e, Γ.brw.get? x = some e → e ≤ Γ.epoch
  stack : OwnedStack Δ ρf ρo live lex Jf Jo
  scope : StackScope functions live lex Jf

def AtClockOwned (F : Fir.Program) (candidate : Src.NatMap Code) (k : Nat) : Prop :=
  ∀ {H : Heap} {external : Nat → Nat} {live : List Var} {Γ : Ctx} {Δ : JCtx}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (c : Code),
    OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo →
    scopeOk (signatures F) live (stackArities Jf) (eraseCode c) = true →
    checkCode Δ Γ c = .ok () →
    ResultRel H external (Fir.eval F k ρf Jf (eraseCode c))
      (eval { source := F, bodies := candidate } k ρo Jo H c)

/-! ## The stack under bindings, declarations and jumps -/

theorem StackScope.cons_inv {functions : Signatures} {live : List Var}
    {p : Fir.JoinId × List Var} {older : Joins} {e : Fir.JEntry} {rest : List Fir.JEntry}
    (h : StackScope functions live (p :: older) (e :: rest)) :
    p = (e.id, p.2) ∧ p.2.Sublist live ∧ EntryScope functions p.2 rest e ∧
      StackScope functions p.2 older rest := by
  cases h with
  | cons order entry tail => exact ⟨rfl, order, entry, tail⟩

namespace OwnedStack

theorem bind {Δ : JCtx} {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (h : OwnedStack Δ ρf ρo live lex Jf Jo)
    (x : Var) (v : RVal) (w : Fir.Val) (hx : x ∉ live) :
    OwnedStack Δ (ρf.insert x w) (ρo.insert x v) (live ++ [x]) lex Jf Jo := by
  cases h with
  | nil => exact .nil _ _ _
  | cons entry oview fview tail =>
    refine .cons entry (oview.bind x v hx) (fun y hy => ?_) tail
    have hne : y ≠ x := by intro he; subst he; exact hx (oview.order.subset hy)
    rw [Src.NatMap.get?_insert_ne _ _ hne]
    exact fview y hy

theorem rebind {Δ : JCtx} {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (h : OwnedStack Δ ρf ρo live lex Jf Jo)
    (params : List Var) (vs : List RVal) (ws : List Fir.Val) (hf : fresh live params = true) :
    OwnedStack Δ (Fir.bindAll ρf params ws) (Own.bindAll ρo params vs) (live ++ params) lex Jf Jo := by
  cases h with
  | nil => exact .nil _ _ _
  | cons entry oview fview tail =>
    refine .cons entry (oview.rebind params vs hf) (fun y hy => ?_) tail
    rw [Fir.Proof.bindAll_get_notin (fresh_avoids hf (oview.order.subset hy))]
    exact fview y hy

/-- Another join context that agrees on every join of the stack. -/
theorem transfer {Δ Δ' : JCtx} {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (h : OwnedStack Δ ρf ρo live lex Jf Jo)
    (ha : ∀ e, e ∈ Jf → Δ'.get? e.id = Δ.get? e.id) :
    OwnedStack Δ' ρf ρo live lex Jf Jo := by
  induction h with
  | nil => exact .nil _ _ _
  | @cons ρf ρo live lexd captured older Δd Γd ef eo jf jo entry oview fview tail ih =>
    refine .cons (Δd := Δd) (Γd := Γd) (captured := captured) ?_ oview fview
      (ih (fun e he => ha e (List.mem_cons_of_mem _ he)))
    exact { entry with
      here := (ha ef List.mem_cons_self).trans entry.here
      agree := fun e he => (entry.agree e he).trans (ha e (List.mem_cons_of_mem _ he)).symm }

/-- What a jump finds: the entry, its views onto the current environments, and its tail. -/
theorem lookup {functions : Signatures} {Δ : JCtx} {ρf : Fir.Env} {ρo : Own.Env}
    {live : List Var} {lex : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack Δ ρf ρo live lex Jf Jo) (hs : StackScope functions live lex Jf)
    {j : Fir.JoinId} {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (hl : Fir.lookupJ j Jf = some (ef, restf)) :
    ∃ (lexd captured : List Var) (older : Joins) (Δd : JCtx) (Γd : Ctx) (eo : JEntry)
      (resto : List JEntry),
      lookupJ j Jo = some (eo, resto) ∧ OwnedEntry Δ Δd Γd lexd captured restf ef eo ∧
      CaptureView eo.env ρo lexd live ∧ (∀ x, x ∈ lexd → ef.env.get? x = ρf.get? x) ∧
      OwnedStack Δ ef.env eo.env lexd older restf resto ∧
      EntryScope functions lexd restf ef ∧ StackScope functions lexd older restf := by
  revert hs hl
  induction h with
  | nil => intro _ hl; simp [Fir.lookupJ] at hl
  | @cons ρf ρo live lexd captured older Δd Γd ef₀ eo₀ jf jo entry oview fview tail ih =>
    intro hs hl
    obtain ⟨_, _, escope, tscope⟩ := StackScope.cons_inv hs
    by_cases hid : ef₀.id = j
    · have hh : ef₀ = ef ∧ jf = restf := by simpa [Fir.lookupJ, hid] using hl
      obtain ⟨rfl, rfl⟩ := hh
      refine ⟨lexd, captured, older, Δd, Γd, eo₀, jo, ?_, entry, oview, fview, tail, escope,
        tscope⟩
      simp [lookupJ, entry.id, hid]
    · have hl' : Fir.lookupJ j jf = some (ef, restf) := by simpa [Fir.lookupJ, hid] using hl
      obtain ⟨lexd', captured', older', Δd', Γd', eo, resto, hlo, entry', oview', fview', tail',
        escope', tscope'⟩ := ih tscope hl'
      refine ⟨lexd', captured', older', Δd', Γd', eo, resto, ?_, entry', oview'.trans oview,
        fun x hx => (fview' x hx).trans (fview x (oview'.order.subset hx)), tail', escope',
        tscope'⟩
      have hid' : eo₀.id ≠ j := by rw [entry.id]; exact hid
      simp [lookupJ, hid', hlo]

end OwnedStack

theorem lookup_none_fresh {j : Fir.JoinId} :
    ∀ {J : List Fir.JEntry}, (stackArities J).lookup j = none → ∀ e, e ∈ J → e.id ≠ j
  | [], _, _, he => by cases he
  | e₀ :: J, h, e, he => by
    have hb : (j == e₀.id) = false := by
      cases hc : (j == e₀.id)
      · rfl
      · simp [stackArities, List.lookup, hc] at h
    have h' : (stackArities J).lookup j = none := by
      simpa [stackArities, List.lookup, hb] using h
    rcases List.mem_cons.mp he with rfl | he
    · intro hid; rw [hid] at hb; simp at hb
    · exact lookup_none_fresh h' e he

end IxCC.Own.Plain
