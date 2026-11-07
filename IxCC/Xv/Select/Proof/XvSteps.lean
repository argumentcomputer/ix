import IxCC.Xv.Select.Proof.Program

/-!
# Xv steps through selected code

The steps `Xv.step` takes through a selected block: a run of instructions
other than calls (`xv_star_seq`), a call, and each terminator. A selected
block's body is its statements' segments followed by the terminator's
prefix; `off segs i` is the Xv position of Lir position `i`.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env Frame State)
open IxCC.Xv.Select

variable {q : VProgram} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame} {xf : Func VReg}
  {xb : Block VReg}

theorem xv_step_inst {i : Inst VReg} {σ' : Env} {mem' : X86.Memory}
    (hf : q.funcs[fr.fn]? = some xf) (hb : xf.blocks[fr.label]? = some xb) (hi : xb.body.toList[fr.pos]? = some i)
    (hx : i.exec fr.env mem ctx = some (σ', mem')) :
    Xv.step q { mem, ctx, stack := fr :: rest } =
      .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := σ' } :: rest } false := by
  have hlt : fr.pos < xb.body.size := by
    have := (List.getElem?_eq_some_iff.1 hi).1; simpa using this
  have hi' : xb.body[fr.pos] = i := by
    have := (List.getElem?_eq_some_iff.1 hi).2; simpa using this
  unfold Xv.step
  simp only [hf, hb, hlt, ↓reduceDIte, hi']
  cases i with
  | call => simp [Inst.exec] at hx
  | op o defs args => simp only [hx]
  | fused p pargs c defs cargs => simp only [hx]
  | move dst src => simp only [hx]
  | zero x => simp only [hx]

/-- Instructions other than calls, laid out from the frame's position, run
as free steps. -/
theorem xv_star_seq (hf : q.funcs[fr.fn]? = some xf) (hb : xf.blocks[fr.label]? = some xb) :
    ∀ (is A B : List (Inst VReg)) (fr₀ : Frame) (mem₀ mem' : X86.Memory) (σ' : Env),
      fr₀.fn = fr.fn → fr₀.label = fr.label → xb.body.toList = A ++ is ++ B → fr₀.pos = A.length →
      execSeq fr₀.env mem₀ ctx is = some (σ', mem') →
      Sem.Star (Xv.step q) { mem := mem₀, ctx, stack := fr₀ :: rest } 0
        { mem := mem', ctx, stack := { fr₀ with pos := A.length + is.length, env := σ' } :: rest }
  | [], A, B, fr₀, mem₀, mem', σ', _, _, _, hpos, hx => by
      simp only [execSeq_nil, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨fn₀, l₀, p₀, e₀, d₀⟩ := fr₀
      simp only at hpos ⊢
      subst hpos
      try simp only [Nat.add_zero]
      exact .refl _
  | i :: is, A, B, fr₀, mem₀, mem', σ', hfn, hl, hbody, hpos, hx => by
      simp only [execSeq, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨⟨σ₁, mem₁⟩, h₁, hx⟩ := hx
      have hi : xb.body.toList[fr₀.pos]? = some i := by
        rw [hbody, hpos]; simp
      have hstep := xv_step_inst (rest := rest) (fr := fr₀) (by rw [hfn]; exact hf) (by rw [hl]; exact hb) hi h₁
      have hrest := xv_star_seq hf hb is (A ++ [i]) B { fr₀ with pos := fr₀.pos + 1, env := σ₁ } mem₁ mem' σ'
        hfn hl (by rw [hbody]; simp) (by simp [hpos]) hx
      have := Sem.Star.free hstep hrest
      have he : ({ { fr₀ with pos := fr₀.pos + 1, env := σ₁ } with pos := (A ++ [i]).length + is.length, env := σ' } :
          Frame) = { fr₀ with pos := A.length + (i :: is).length, env := σ' } := by
        simp; omega
      rw [he] at this
      exact this

theorem xv_step_call {g : Lir.FunId} {vs : List VReg} {rs : List VReg} {vals : List Word} {callee : Frame}
    (hf : q.funcs[fr.fn]? = some xf) (hb : xf.blocks[fr.label]? = some xb)
    (hi : xb.body.toList[fr.pos]? = some (.call g vs rs)) (hv : readAll fr.env vs = some vals)
    (he : Xv.enter q g vals = some callee) :
    Xv.step q { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := callee :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } true := by
  have hlt : fr.pos < xb.body.size := by
    have := (List.getElem?_eq_some_iff.1 hi).1; simpa using this
  have hi' : xb.body[fr.pos] = .call g vs rs := by
    have := (List.getElem?_eq_some_iff.1 hi).2; simpa using this
  unfold Xv.step
  simp [hf, hb, hlt, hi', hv, he]

theorem xv_step_term (hf : q.funcs[fr.fn]? = some xf) (hb : xf.blocks[fr.label]? = some xb)
    (hpos : fr.pos = xb.body.size) :
    Xv.step q { mem, ctx, stack := fr :: rest } =
      match xb.term with
      | .jmp e => takeEdge xf { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .jcc p' pargs defs c t e =>
          match execJcc p' pargs defs c fr.env mem ctx with
          | some (ρ, mem', taken) => takeEdge xf { mem := mem', ctx, stack := fr :: rest } fr rest ρ (if taken then t else e)
          | none => .stuck
      | .ret vs =>
          match readAll fr.env vs with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done (vals, mem)
              | caller :: rest' =>
                  match Lir.bindParams caller.env caller.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g args =>
          match readAll fr.env args >>= Xv.enter q g with
          | some callee => .next { mem, ctx, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  have hlt : ¬ fr.pos < xb.body.size := by omega
  unfold Xv.step
  simp only [hf, hb, hlt, ↓reduceDIte]
  rfl

end IxCC.Xv.Select.Proof
