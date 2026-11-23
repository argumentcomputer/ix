import IxCC.Own.Plain.Proof.Owned.Roots
import IxCC.Own.Plain.Proof.StackScope
import IxCC.Own.Plain.Proof.CaptureIdentity
import IxCC.Own.Plain.Proof.Results
import IxCC.Fir.Proof.Env

/-! # The induction invariant over a typing context

`OwnedState` is the invariant of the checked simulation: the lexical scope `live` is kept (the
source checker's scope and the capture identities need it) and ownership is the context's: its
tokens' values (plus live reset slots) are what `Balance` counts, every available variable denotes,
every immediate is an immediate value, every epoch-borrowed variable is backed by a live cell edge,
every caller-backed `pbrw` variable is reachable from external roots, every `ctorOf`/`projOf`
annotation matches runtime `asCtor`, every `uniq` variable is statically unique, every live reset
slot holds a valid shell or `.erased`, and private locations are hidden from the activation.

`OwnedStack` says each saved join's body was checked from the context its declaration entered,
the current join context `Δ` maps the join to its captured list, and the saved environments agree
with the current ones on the declaration's lexical scope. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var)

/-- A saved join: its body is checked from the context its declaration entered (`Γd`, the join
context then `Δd`), and `Δ` (the current one) maps it to its captured list. -/
structure OwnedEntry (borrows : BorrowSigs) (uniqs : UniqSigs) (retUniq : Bool)
    (ctors : List Lam.CtorInfo) (known : Lam.Known) (Δ Δd : JCtx) (pbrw : Src.NatSet) (Γd : Ctx)
    (lexd captured : List Var) (older : List Fir.JEntry) (ef : Fir.JEntry) (eo : JEntry) : Prop where
  id : eo.id = ef.id
  charged : eo.charged = ef.charged
  params : eo.params = ef.params
  isRec : eo.isRec = ef.isRec
  erases : eraseCode eo.body = ef.body
  typed : checkCode (if ef.isRec then Δd.insert ef.id captured else Δd)
    (Γd.enter captured ef.params) eo.body borrows uniqs retUniq ctors known = .ok ()
  /-- Immediates of the declaration denote themselves in every heap (and valid immediates keep `ImmUniq`). -/
  imm : ∀ x, Γd.isImm x = true → ∃ v w, eo.env.get? x = some v ∧ ef.env.get? x = some w ∧
    ImmVal v ∧ (Γd.isUniq x = true → ImmUniq ctors v) ∧ ∀ H : Heap, Proof.Den H v w
  immIn : ∀ x, Γd.isImm x = true → x ∈ lexd
  pbrwIn : ∀ x, Γd.isPbrw x = true → x ∈ lexd
  pbrwSub : ∀ x, Γd.isPbrw x = true → pbrw.contains x = true
  sub : ∀ c, c ∈ captured → c ∈ lexd
  nodup : captured.Nodup
  here : Δ.get? ef.id = some captured
  agree : ∀ e, e ∈ older → Δd.get? e.id = Δ.get? e.id
  fresh : ∀ e, e ∈ older → e.id ≠ ef.id

/-- The join stack (Fir and Own side by side), each entry with its declaration's lexical scope. -/
inductive OwnedStack (borrows : BorrowSigs) (uniqs : UniqSigs) (retUniq : Bool)
    (ctors : List Lam.CtorInfo) (known : Lam.Known) (Δ : JCtx) :
    Src.NatSet → Fir.Env → Own.Env → List Var → Joins → List Fir.JEntry → List JEntry → Prop
  | nil (pbrw : Src.NatSet) (ρf : Fir.Env) (ρo : Own.Env) (live : List Var) :
      OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live [] [] []
  | cons {pbrw : Src.NatSet} {ρf : Fir.Env} {ρo : Own.Env} {live lexd captured : List Var}
      {older : Joins} {Δd : JCtx} {Γd : Ctx} {ef : Fir.JEntry} {eo : JEntry}
      {jf : List Fir.JEntry} {jo : List JEntry}
      (entry : OwnedEntry borrows uniqs retUniq ctors known Δ Δd pbrw Γd lexd captured jf ef eo)
      (oview : CaptureView eo.env ρo lexd live)
      (fview : ∀ x, x ∈ lexd → ef.env.get? x = ρf.get? x)
      (tail : OwnedStack borrows uniqs retUniq ctors known Δ Γd.pbrw ef.env eo.env lexd older jf jo) :
      OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live ((ef.id, lexd) :: older) (ef :: jf) (eo :: jo)

/-- **The simulation invariant** over a typing context. -/
structure OwnedState (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Var) (Γ : Ctx) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (lex : Joins) (Δ : JCtx) (Jf : List Fir.JEntry) (Jo : List JEntry)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf)
    (retUniq : Bool := false) (ctors : List Lam.CtorInfo := []) (K : Lam.Known := {})
    (priv : Nat → Prop := fun _ => False)
    (slots : Src.NatMap RVal := .leaf) (slotVals : List RVal := []) : Prop where
  den : ∀ x, Γ.avail x = true → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w
  roots : ∃ toks, Ctx.Tokens Γ toks ∧ EnvRoots ρo toks owned
  slotRoots : ∃ skeys, Ctx.SlotKeys Γ skeys ∧ EnvRoots slots skeys slotVals
  counts : Balance H external (owned ++ slotVals)
  known : ∀ x, Γ.known x = true → x ∈ live
  distinct : live.Nodup
  immOk : ∀ x, Γ.isImm x = true → ∃ v, ρo.get? x = some v ∧ ImmVal v
  borrowed : ∀ x, Γ.borrowed x = true → ∃ v, ρo.get? x = some v ∧ BorrowVal H v
  pbrwOk : ∀ x, Γ.isPbrw x = true → ∃ v, ρo.get? x = some v ∧ ReachableFrom H external v
  epochs : ∀ x e, Γ.brw.get? x = some e → e ≤ Γ.epoch
  ctorOfKnown : ∀ x key, Γ.ctorOf.get? x = some key → x ∈ live
  projOfKnown : ∀ v x key idx, Γ.projOf.get? v = some (x, key, idx) → v ∈ live ∧ x ∈ live
  ctorOfOk : ∀ x key, Γ.avail x = true → Γ.ctorOf.get? x = some key →
    ∃ v fields, ρo.get? x = some v ∧ v.asCtor K H = some (key, fields)
  projOfOk : ∀ v x key idx, Γ.avail x = true → Γ.avail v = true →
    Γ.projOf.get? v = some (x, key, idx) →
    ∃ vx fields uv, ρo.get? x = some vx ∧ vx.asCtor K H = some (key, fields) ∧
      fields[idx]? = some uv ∧ ρo.get? v = some uv
  uniqOk : ∀ x, Γ.isUniq x = true →
    (Γ.isImm x = false → Γ.tokens x = 1 ∧ Γ.isPbrw x = false) ∧
    ∃ v, ρo.get? x = some v ∧ UniqVal ctors H external (owned ++ slotVals) v
  rsetOk : ∀ s cls u, Γ.rset.get? s = some (cls, u) →
    ∃ sv, slots.get? s = some sv ∧
      ((sv = .erased ∧ u = false) ∨
       (∃ l b, sv = .loc l ∧ H.cell? l = some (.live 1 .dyn b) ∧
         Ctx.validReuseCtor b.ctor = some cls ∧ b.fields = List.replicate b.ctor.arity .erased ∧
         external l = 0 ∧ edgeCount H l = 0 ∧ refsIn l (owned ++ slotVals) = 1))
  privBound : ∀ l, priv l → l < H.size
  privNoEdge : ∀ l, priv l → edgeCount H l = 0
  privNoVar : ∀ l, priv l → ∀ x, Γ.avail x = true → ρo.get? x ≠ some (.loc l)
  privNoSlot : ∀ l, priv l → ∀ s, Γ.rset.contains s = true → slots.get? s ≠ some (.loc l)
  stack : OwnedStack borrows uniqs retUniq ctors K Δ Γ.pbrw ρf ρo live lex Jf Jo
  scope : StackScope functions live lex Jf

def AtClockOwned (F : Fir.Program) (candidate : Src.NatMap Code) (k : Nat)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Prop :=
  ∀ {H : Heap} {external : Nat → Nat} {priv : Nat → Prop} {retUniq : Bool}
    {live : List Var} {Γ : Ctx} {Δ : JCtx} {ρf : Fir.Env} {ρo : Own.Env}
    {owned : List RVal} {slots : Src.NatMap RVal} {slotVals : List RVal}
    {lex : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry} (c : Code),
    OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv slots slotVals →
    scopeOk (signatures F) live (stackArities Jf) (eraseCode c) = true →
    checkCode Δ Γ c borrows uniqs retUniq F.ctors F.known = .ok () →
    ResultRelFull H external priv F.ctors retUniq (Fir.eval F k ρf Jf (eraseCode c))
      (eval { source := F, bodies := candidate, borrows, uniqs } k ρo Jo H c slots)

/-! ## The stack under bindings, declarations and jumps -/

theorem StackScope.cons_inv {functions : Signatures} {live : List Var}
    {p : Fir.JoinId × List Var} {older : Joins} {e : Fir.JEntry} {rest : List Fir.JEntry}
    (h : StackScope functions live (p :: older) (e :: rest)) :
    p = (e.id, p.2) ∧ p.2.Sublist live ∧ EntryScope functions p.2 rest e ∧
      StackScope functions p.2 older rest := by
  cases h with
  | cons order entry tail => exact ⟨rfl, order, entry, tail⟩

namespace OwnedStack

theorem bind {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} {Δ : JCtx} {pbrw : Src.NatSet}
    {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live lex Jf Jo)
    (x : Var) (v : RVal) (w : Fir.Val) (hx : x ∉ live) :
    OwnedStack borrows uniqs retUniq ctors known Δ pbrw (ρf.insert x w) (ρo.insert x v)
      (live ++ [x]) lex Jf Jo := by
  cases h with
  | nil => exact .nil _ _ _ _
  | cons entry oview fview tail =>
    refine .cons entry (oview.bind x v hx) (fun y hy => ?_) tail
    have hne : y ≠ x := by intro he; subst he; exact hx (oview.order.subset hy)
    rw [Src.NatMap.get?_insert_ne _ _ hne]
    exact fview y hy

theorem rebind {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} {Δ : JCtx} {pbrw : Src.NatSet}
    {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live lex Jf Jo)
    (params : List Var) (vs : List RVal) (ws : List Fir.Val) (hf : fresh live params = true) :
    OwnedStack borrows uniqs retUniq ctors known Δ pbrw (Fir.bindAll ρf params ws)
      (Own.bindAll ρo params vs) (live ++ params) lex Jf Jo := by
  cases h with
  | nil => exact .nil _ _ _ _
  | cons entry oview fview tail =>
    refine .cons entry (oview.rebind params vs hf) (fun y hy => ?_) tail
    rw [Fir.Proof.bindAll_get_notin (fresh_avoids hf (oview.order.subset hy))]
    exact fview y hy

/-- Extending `pbrw` preserves the join stack. -/
theorem mono_pbrw {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} {Δ : JCtx} {pbrw pbrw' : Src.NatSet}
    {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live lex Jf Jo)
    (hsub : ∀ x, pbrw.contains x = true → pbrw'.contains x = true) :
    OwnedStack borrows uniqs retUniq ctors known Δ pbrw' ρf ρo live lex Jf Jo := by
  cases h with
  | nil => exact .nil _ _ _ _
  | cons entry oview fview tail =>
    exact .cons { entry with pbrwSub := fun x hx => hsub x (entry.pbrwSub x hx) } oview fview tail

/-- Another join context that agrees on every join of the stack. -/
theorem transfer {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} {Δ Δ' : JCtx} {pbrw : Src.NatSet}
    {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live lex Jf Jo)
    (ha : ∀ e, e ∈ Jf → Δ'.get? e.id = Δ.get? e.id) :
    OwnedStack borrows uniqs retUniq ctors known Δ' pbrw ρf ρo live lex Jf Jo := by
  induction h with
  | nil => exact .nil _ _ _ _
  | @cons pbrw ρf ρo live lexd captured older Δd Γd ef eo jf jo entry oview fview tail ih =>
    refine .cons (Δd := Δd) (Γd := Γd) (captured := captured) ?_ oview fview
      (ih (fun e he => ha e (List.mem_cons_of_mem _ he)))
    exact { entry with
      here := (ha ef List.mem_cons_self).trans entry.here
      agree := fun e he => (entry.agree e he).trans (ha e (List.mem_cons_of_mem _ he)).symm }

/-- What a jump finds: the entry, its views onto the current environments, and its tail. -/
theorem lookup {functions : Signatures} {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} {Δ : JCtx} {pbrw : Src.NatSet}
    {ρf : Fir.Env} {ρo : Own.Env} {live : List Var} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : OwnedStack borrows uniqs retUniq ctors known Δ pbrw ρf ρo live lex Jf Jo)
    (hs : StackScope functions live lex Jf)
    {j : Fir.JoinId} {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (hl : Fir.lookupJ j Jf = some (ef, restf)) :
    ∃ (lexd captured : List Var) (older : Joins) (Δd : JCtx) (Γd : Ctx) (eo : JEntry)
      (resto : List JEntry),
      lookupJ j Jo = some (eo, resto) ∧
      OwnedEntry borrows uniqs retUniq ctors known Δ Δd pbrw Γd lexd captured restf ef eo ∧
      CaptureView eo.env ρo lexd live ∧ (∀ x, x ∈ lexd → ef.env.get? x = ρf.get? x) ∧
      OwnedStack borrows uniqs retUniq ctors known Δ Γd.pbrw ef.env eo.env lexd older restf resto ∧
      EntryScope functions lexd restf ef ∧ StackScope functions lexd older restf := by
  revert hs hl
  induction h with
  | nil => intro _ hl; simp [Fir.lookupJ] at hl
  | @cons pbrw ρf ρo live lexd captured older Δd Γd ef₀ eo₀ jf jo entry oview fview tail ih =>
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
      refine ⟨lexd', captured', older', Δd', Γd', eo, resto, ?_,
        { entry' with pbrwSub := fun x hx => entry.pbrwSub x (entry'.pbrwSub x hx) },
        oview'.trans oview,
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
