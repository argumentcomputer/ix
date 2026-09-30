import Compilatrix.Xv.Operands

/-!
# Renaming operands

Functor maps on Xv syntax (`Inst.map` and friends) and the facts that
binding (`bindRow`), operand metadata (`Inst.operands`) and substitution
(`Inst.substitute`) commute with them. With these, an Xv instruction and
the Xl instruction `apply` substitutes for it are two images of one paired
instruction over `VReg × Loc` (`Inst.pair_of_substitute`): the paired
instruction's bound operands carry each operand's register and location
together, in the order the validator checks them.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (Operand)

variable {α β γ σ : Type}

/-! ## Maps -/

def Base.map (f : α → β) : Base α → Base β
  | .r x => .r (f x)
  | .ctx => .ctx

def Amode.map (f : α → β) (a : Amode α) : Amode β :=
  { base := a.base.map (Base.map f), index := a.index.map (fun p => (f p.1, p.2)), disp := a.disp }

def XArg.map (f : α → β) : XArg α → XArg β
  | .r x => .r (f x)
  | .m a => .m (a.map f)
  | .i w => .i w

def Bound.map (f : α → β) : Bound α → Bound β
  | .input s a => .input s (a.map f)
  | .output s x => .output s (f x)
  | .tied s a x => .tied s (f a) (f x)
  | .memory s m => .memory s (m.map f)
  | .fixedUse i a => .fixedUse i (f a)
  | .fixedDef i x => .fixedDef i (f x)
  | .fixedTied i a x => .fixedTied i (f a) (f x)

def Inst.map (f : α → β) : Inst α → Inst β
  | .op o defs args => .op o (defs.map f) (args.map (XArg.map f))
  | .fused p pargs c defs cargs =>
      .fused p (pargs.map (XArg.map f)) c (defs.map f) (cargs.map (XArg.map f))
  | .move dst src => .move (f dst) (f src)
  | .zero x => .zero (f x)
  | .call g args rets => .call g (args.map f) (rets.map f)

/-- An operand with its register renamed. -/
def opMap (f : α → β) (o : Operand α) : Operand β := ⟨f o.v, o.kind, o.pos, o.con⟩

@[simp] theorem opMap_v (f : α → β) (o : Operand α) : (opMap f o).v = f o.v := rfl
@[simp] theorem opMap_kind (f : α → β) (o : Operand α) : (opMap f o).kind = o.kind := rfl
@[simp] theorem opMap_pos (f : α → β) (o : Operand α) : (opMap f o).pos = o.pos := rfl
@[simp] theorem opMap_con (f : α → β) (o : Operand α) : (opMap f o).con = o.con := rfl

theorem Amode.map_map (f : α → β) (g : β → γ) (a : Amode α) :
    (a.map f).map g = a.map (g ∘ f) := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;> rfl

theorem Amode.map_id (a : Amode α) : a.map id = a := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;> rfl

theorem XArg.map_map (f : α → β) (g : β → γ) (a : XArg α) : (a.map f).map g = a.map (g ∘ f) := by
  cases a <;> simp [XArg.map, Amode.map_map]

theorem Bound.map_map (f : α → β) (g : β → γ) (b : Bound α) : (b.map f).map g = b.map (g ∘ f) := by
  cases b <;> simp [Bound.map, XArg.map_map, Amode.map_map]

theorem Inst.map_map (f : α → β) (g : β → γ) (i : Inst α) : (i.map f).map g = i.map (g ∘ f) := by
  cases i <;> simp [Inst.map, List.map_map, XArg.map_map, Function.comp_def]

/-! ## Registers -/

@[simp] theorem Amode.regs_map (f : α → β) (a : Amode α) : (a.map f).regs = a.regs.map f := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;> rfl

@[simp] theorem XArg.regs_map (f : α → β) (a : XArg α) : (a.map f).regs = a.regs.map f := by
  cases a <;> simp [XArg.map, XArg.regs]

@[simp] theorem xargsRegs_map (f : α → β) (as : List (XArg α)) :
    xargsRegs (as.map (XArg.map f)) = (xargsRegs as).map f := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [xargsRegs] at ih ⊢; simp [ih]

/-! ## Binding commutes with renaming -/

theorem bindSlots_map (f : α → β) :
    ∀ (slots : List X86.Slot) (defs : List α) (args : List (XArg α)),
      bindSlots slots (defs.map f) (args.map (XArg.map f)) =
        (bindSlots slots defs args).map
          (fun r => (r.1.map (Bound.map f), r.2.1.map f, r.2.2.map (XArg.map f)))
  | [], defs, args => by simp [bindSlots]
  | ⟨kinds, width, role⟩ :: ss, defs, args => by
      have ih := bindSlots_map f ss
      cases role with
      | read | address =>
        cases args with
        | nil => simp [bindSlots]
        | cons a args => simp [bindSlots, ih, Bound.map, Function.comp_def]
      | readWrite =>
        cases args with
        | nil => simp [bindSlots]
        | cons a args =>
          cases a with
          | r a =>
            cases defs with
            | nil => simp [bindSlots, XArg.map]
            | cons x defs => simp [bindSlots, XArg.map, ih, Bound.map, Function.comp_def]
          | m m => simp [bindSlots, XArg.map, ih, Bound.map, Function.comp_def]
          | i w => simp [bindSlots, XArg.map]
      | write =>
        cases args with
        | nil =>
          cases defs with
          | nil => simp [bindSlots]
          | cons x defs =>
            have := ih defs []
            simp only [List.map_nil] at this
            simp [bindSlots, this, Bound.map, Function.comp_def]
        | cons a args =>
          cases a with
          | m m =>
            by_cases hk : X86.ArgKind.mem ∈ kinds
            · simp [bindSlots, XArg.map, ih, Bound.map, hk, Function.comp_def]
            · cases defs with
              | nil => simp [bindSlots, XArg.map, hk]
              | cons x defs =>
                have := ih defs (.m m :: args)
                simp only [List.map_cons, XArg.map] at this
                simp [bindSlots, XArg.map, this, Bound.map, hk, Function.comp_def]
          | r a =>
            cases defs with
            | nil => simp [bindSlots, XArg.map]
            | cons x defs =>
              have := ih defs (.r a :: args)
              simp only [List.map_cons, XArg.map] at this
              simp [bindSlots, XArg.map, this, Bound.map, Function.comp_def]
          | i w =>
            cases defs with
            | nil => simp [bindSlots, XArg.map]
            | cons x defs =>
              have := ih defs (.i w :: args)
              simp only [List.map_cons, XArg.map] at this
              simp [bindSlots, XArg.map, this, Bound.map, Function.comp_def]

theorem bindImplicits_map (f : α → β) :
    ∀ (is : List X86.Implicit) (defs : List α) (args : List (XArg α)),
      bindImplicits is (defs.map f) (args.map (XArg.map f)) =
        (bindImplicits is defs args).map (List.map (Bound.map f))
  | [], [], [] => rfl
  | [], _ :: _, _ => by simp [bindImplicits]
  | [], [], _ :: _ => by simp [bindImplicits]
  | i :: is, defs, args => by
      have ih := bindImplicits_map f is
      cases hr : i.role.reads <;> cases hw : i.role.writes
      · cases args <;> cases defs <;> simp [bindImplicits, hr, hw]
      · cases defs with
        | nil => cases args <;> simp [bindImplicits, hr, hw]
        | cons x defs =>
          have := ih defs args
          cases args with
          | nil =>
            simp only [List.map_nil] at this
            simp [bindImplicits, hr, hw, this, Bound.map, Function.comp_def]
          | cons a args =>
            cases a <;> simp only [List.map_cons, XArg.map] at this <;>
              simp [bindImplicits, hr, hw, this, Bound.map, XArg.map, Function.comp_def]
      · cases args with
        | nil => simp [bindImplicits, hr, hw]
        | cons a args =>
          have := ih defs args
          cases a <;> simp [bindImplicits, hr, hw, this, Bound.map, XArg.map, Function.comp_def]
      · cases args with
        | nil => simp [bindImplicits, hr, hw]
        | cons a args =>
          cases defs with
          | nil => cases a <;> simp [bindImplicits, hr, hw, XArg.map]
          | cons x defs =>
            have := ih defs args
            cases a <;> simp [bindImplicits, hr, hw, this, Bound.map, XArg.map, Function.comp_def]

theorem bindRow_map (f : α → β) (o : X86.Op) (defs : List α) (args : List (XArg α)) :
    bindRow o (defs.map f) (args.map (XArg.map f)) = (bindRow o defs args).map (List.map (Bound.map f)) := by
  unfold bindRow
  rw [bindSlots_map]
  cases bindSlots (X86.desc o).slots defs args with
  | none => rfl
  | some r =>
    obtain ⟨bs, defs', args'⟩ := r
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, bindImplicits_map]
    cases bindImplicits (X86.desc o).implicit defs' args' <;> simp

/-! ## Operand metadata commutes with renaming -/

@[simp] theorem Bound.narrowOutput_map (f : α → β) (b : Bound α) :
    (b.map f).narrowOutput = b.narrowOutput := by
  cases b <;> rfl

theorem boundUses_map (f : α → β) (bs : List (Bound α)) :
    boundUses (bs.map (Bound.map f)) = (boundUses bs).map (opMap f) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, boundUses, List.map_append, ih]
    congr 1
    cases b with
    | input s a => cases a <;> simp [Bound.map, XArg.map, useAt, opMap, List.map_map, Function.comp_def]
    | memory s m => simp [Bound.map, useAt, opMap, List.map_map, Function.comp_def]
    | _ => simp [Bound.map, useAt, opMap]

theorem boundUses_length_map (f : α → β) (b : Bound α) :
    (boundUses [b.map f]).length = (boundUses [b]).length := by
  have := boundUses_map f [b]
  simp only [List.map_cons, List.map_nil] at this
  rw [this, List.length_map]

theorem boundDefs_map (f : α → β) (z : Bool) :
    ∀ (i : Nat) (bs : List (Bound α)),
      boundDefs z i (bs.map (Bound.map f)) = (boundDefs z i bs).map (opMap f)
  | _, [] => rfl
  | i, b :: bs => by
      simp only [List.map_cons, boundDefs, List.map_append, boundUses_length_map,
        boundDefs_map f z _ bs]
      congr 1
      cases b <;> simp [Bound.map, defAt, earlyDefAt, opMap, Bound.narrowOutput] <;> split <;> rfl

theorem boundOperands_map (f : α → β) (bs : List (Bound α)) (z : Bool) :
    boundOperands (bs.map (Bound.map f)) z = (boundOperands bs z).map (opMap f) := by
  simp [boundOperands, boundUses_map, boundDefs_map]

theorem conUses_map (f : α → β) (con : Nat → Lir.Con) (xs : List α) :
    conUses con (xs.map f) = (conUses con xs).map (opMap f) := by
  simp [conUses, List.zipIdx_map, List.map_map, Function.comp_def, useAt, opMap]

theorem conDefs_map (f : α → β) (con : Nat → Lir.Con) (xs : List α) :
    conDefs con (xs.map f) = (conDefs con xs).map (opMap f) := by
  simp [conDefs, List.zipIdx_map, List.map_map, Function.comp_def, defAt, opMap]

theorem Inst.operands_map (f : α → β) (i : Inst α) :
    (i.map f).operands = i.operands.map (opMap f) := by
  cases i with
  | op o defs args =>
    simp only [Inst.map, Inst.operands, bindRow_map]
    cases bindRow o defs args <;> simp [boundOperands_map]
  | fused p pargs c defs cargs =>
    simp only [Inst.map, Inst.operands]
    have hp := bindRow_map f p [] pargs
    simp only [List.map_nil] at hp
    rw [hp, bindRow_map]
    cases bindRow p [] pargs <;> cases bindRow c defs cargs <;>
      simp only [Option.map_some, Option.map_none] <;> (try rw [← List.map_append, boundOperands_map]) <;> rfl

  | move dst src => simp [Inst.map, Inst.operands, useAt, defAt, opMap]
  | zero x => simp [Inst.map, Inst.operands, defAt, opMap]
  | call g args rets => simp [Inst.map, Inst.operands, conUses_map, conDefs_map]

/-! ## Substitution commutes with renaming -/

theorem Amode.substitute_map (g : σ → γ) (a : Amode α) (ls : List σ) :
    a.substitute (ls.map g) = (a.substitute ls).map fun r => (r.1.map g, r.2.map g) := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;>
    rcases ls with _ | ⟨l₁, _ | ⟨l₂, ls⟩⟩ <;>
      simp [Amode.substitute, takeOne, Amode.map, Base.map]

theorem XArg.substitute_map (g : σ → γ) (a : XArg α) (ls : List σ) :
    a.substitute (ls.map g) = (a.substitute ls).map fun r => (r.1.map g, r.2.map g) := by
  cases a with
  | r x => cases ls <;> simp [XArg.substitute, takeOne, XArg.map]
  | m am =>
    simp only [XArg.substitute, Amode.substitute_map]
    cases am.substitute ls <;> simp [XArg.map]
  | i w => simp [XArg.substitute, XArg.map]

theorem substituteArgs_map (g : σ → γ) :
    ∀ (as : List (XArg α)) (ls : List σ),
      substituteArgs as (ls.map g) = (substituteArgs as ls).map fun r => (r.1.map (XArg.map g), r.2.map g)
  | [], ls => by simp [substituteArgs]
  | a :: as, ls => by
      simp only [substituteArgs, XArg.substitute_map]
      cases a.substitute ls with
      | none => rfl
      | some r =>
        obtain ⟨a', ls'⟩ := r
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, substituteArgs_map g as ls']
        cases substituteArgs as ls' <;> simp

theorem Inst.substitute_map (g : σ → γ) (i : Inst α) (ls : List σ) :
    i.substitute (ls.map g) = (i.substitute ls).map (Inst.map g) := by
  cases i with
  | op o defs args =>
    simp only [Inst.substitute, substituteArgs_map]
    cases substituteArgs args ls with
    | none => rfl
    | some r =>
      obtain ⟨args', rest⟩ := r
      by_cases h : rest.length = defs.length <;> simp [h, Inst.map, guard, Function.comp_def]
  | fused p pargs c defs cargs =>
    simp only [Inst.substitute, substituteArgs_map]
    cases substituteArgs pargs ls with
    | none => rfl
    | some r =>
      obtain ⟨pargs', rest⟩ := r
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, substituteArgs_map]
      cases substituteArgs cargs rest with
      | none => rfl
      | some r' =>
        obtain ⟨cargs', rest'⟩ := r'
        by_cases h : rest'.length = defs.length <;> simp [h, Inst.map, guard, Function.comp_def]
  | move dst src =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, ls⟩⟩⟩ <;> simp [Inst.substitute, Inst.map]
  | zero x =>
    rcases ls with _ | ⟨a, _ | ⟨b, ls⟩⟩ <;> simp [Inst.substitute, Inst.map]
  | call f args rets =>
    by_cases h : ls.length = args.length + rets.length <;>
      simp [Inst.substitute, Inst.map, h, List.map_take, List.map_drop]

/-! ## What substitution consumes -/

/-- The operands `substitute` replaces, in the order it consumes them. -/
def Inst.consumed : Inst α → List α
  | .op _ defs args => xargsRegs args ++ defs
  | .fused _ pargs _ defs cargs => xargsRegs pargs ++ xargsRegs cargs ++ defs
  | .move dst src => [src, dst]
  | .zero x => [x]
  | .call _ args rets => args ++ rets

theorem Amode.substitute_eq {a : Amode α} {ls : List σ} {a' : Amode σ} {rest : List σ}
    (h : a.substitute ls = some (a', rest)) : a'.regs ++ rest = ls ∧ a'.regs.length = a.regs.length ∧
      a'.map (fun _ => ()) = a.map (fun _ => ()) := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;>
    rcases ls with _ | ⟨l₁, _ | ⟨l₂, ls⟩⟩ <;>
      simp [Amode.substitute, takeOne] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [Amode.regs, Amode.map, Base.map]

theorem XArg.substitute_eq {a : XArg α} {ls : List σ} {a' : XArg σ} {rest : List σ}
    (h : a.substitute ls = some (a', rest)) : a'.regs ++ rest = ls ∧ a'.regs.length = a.regs.length := by
  cases a with
  | r x =>
    cases ls <;> simp [XArg.substitute, takeOne] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [XArg.regs]
  | m am =>
    simp only [XArg.substitute] at h
    cases hs : am.substitute ls with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨am', rest'⟩ := r
      simp [hs] at h
      obtain ⟨rfl, rfl⟩ := h
      have := Amode.substitute_eq hs
      exact ⟨this.1, this.2.1⟩
  | i w =>
    simp [XArg.substitute] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [XArg.regs]

theorem substituteArgs_eq :
    ∀ {as : List (XArg α)} {ls : List σ} {as' : List (XArg σ)} {rest : List σ},
      substituteArgs as ls = some (as', rest) →
        xargsRegs as' ++ rest = ls ∧ (xargsRegs as').length = (xargsRegs as).length
  | [], ls, as', rest, h => by
      simp [substituteArgs] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [xargsRegs]
  | a :: as, ls, as', rest, h => by
      simp only [substituteArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨a', ls'⟩, ha, ⟨as'', rest'⟩, has, he⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h1 := XArg.substitute_eq ha
      have h2 := substituteArgs_eq has
      simp only [xargsRegs, List.flatMap_cons, List.append_assoc, List.length_append] at h1 h2 ⊢
      exact ⟨by rw [h2.1, h1.1], by rw [h1.2, h2.2]⟩

/-- A substituted instruction's operands are the list substituted in. -/
theorem Inst.substitute_consumed {i : Inst α} {ls : List σ} {i' : Inst σ}
    (h : i.substitute ls = some i') : i'.consumed = ls ∧ ls.length = i.consumed.length := by
  cases i with
  | op o defs args =>
    simp only [Inst.substitute] at h
    cases hs : substituteArgs args ls with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨args', rest⟩ := r
      have := substituteArgs_eq hs
      by_cases hl : rest.length = defs.length
      · simp [hs, hl, guard, failure] at h
        subst h
        refine ⟨this.1, ?_⟩
        rw [← this.1]
        simp [Inst.consumed, this.2, hl]
      · simp [hs, hl, guard, failure] at h
  | fused p pargs c defs cargs =>
    simp only [Inst.substitute] at h
    cases hs : substituteArgs pargs ls with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨pargs', rest⟩ := r
      cases hs' : substituteArgs cargs rest with
      | none => simp [hs, hs'] at h
      | some r' =>
        obtain ⟨cargs', rest'⟩ := r'
        have h1 := substituteArgs_eq hs
        have h2 := substituteArgs_eq hs'
        by_cases hl : rest'.length = defs.length
        · simp [hs, hs', hl, guard, failure] at h
          subst h
          refine ⟨by simp [Inst.consumed, h2.1, h1.1], ?_⟩
          rw [← h1.1, ← h2.1]
          simp [Inst.consumed, h1.2, h2.2, hl]
        · simp [hs, hs', hl, guard, failure] at h
  | move dst src =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, ls⟩⟩⟩ <;> simp [Inst.substitute] at h
    subst h
    simp [Inst.consumed]
  | zero x =>
    rcases ls with _ | ⟨a, _ | ⟨b, ls⟩⟩ <;> simp [Inst.substitute] at h
    subst h
    simp [Inst.consumed]
  | call f args rets =>
    simp only [Inst.substitute] at h
    split at h
    · rename_i hl
      cases h
      simp only [beq_iff_eq] at hl
      simp [Inst.consumed, hl]
    · simp at h

theorem Amode.substitute_self (a : Amode α) (rest : List α) :
    a.substitute (a.regs ++ rest) = some (a, rest) := by
  rcases a with ⟨base, index, disp⟩
  rcases base with _ | (_ | _) <;> rcases index with _ | ⟨_, _⟩ <;>
    simp [Amode.substitute, Amode.regs, takeOne]

theorem XArg.substitute_self (a : XArg α) (rest : List α) :
    a.substitute (a.regs ++ rest) = some (a, rest) := by
  cases a with
  | r x => simp [XArg.substitute, XArg.regs, takeOne]
  | m am => simp [XArg.substitute, XArg.regs, Amode.substitute_self]
  | i w => simp [XArg.substitute, XArg.regs]

theorem substituteArgs_self :
    ∀ (as : List (XArg α)) (rest : List α), substituteArgs as (xargsRegs as ++ rest) = some (as, rest)
  | [], rest => by simp [substituteArgs, xargsRegs]
  | a :: as, rest => by
      simp only [substituteArgs, xargsRegs, List.flatMap_cons, List.append_assoc]
      rw [XArg.substitute_self]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have := substituteArgs_self as rest
      simp only [xargsRegs] at this
      simp [this]

/-- Substituting an instruction's own operands gives it back. -/
theorem Inst.substitute_self (i : Inst α) : i.substitute i.consumed = some i := by
  cases i with
  | op o defs args =>
    simp [Inst.substitute, Inst.consumed, substituteArgs_self, guard]
  | fused p pargs c defs cargs =>
    simp [Inst.substitute, Inst.consumed, List.append_assoc, substituteArgs_self, guard]
  | move dst src => rfl
  | zero x => rfl
  | call f args rets => simp [Inst.substitute, Inst.consumed]

/-- An instruction and its substitution are the two projections of one
instruction over pairs, whose operands pair each original operand with its
replacement. -/
theorem Inst.pair_of_substitute {i : Inst α} {ls : List σ} {i' : Inst σ}
    (h : i.substitute ls = some i') :
    ∃ pi : Inst (α × σ), pi.map Prod.fst = i ∧ pi.map Prod.snd = i' ∧ pi.consumed = i.consumed.zip ls := by
  have hlen := (Inst.substitute_consumed h).2
  have h1 : (i.consumed.zip ls).map Prod.fst = i.consumed := List.map_fst_zip (by omega)
  have h2 : (i.consumed.zip ls).map Prod.snd = ls := List.map_snd_zip (by omega)
  have hs := Inst.substitute_map Prod.snd i (i.consumed.zip ls)
  rw [h2, h] at hs
  cases hp : i.substitute (i.consumed.zip ls) with
  | none => rw [hp] at hs; simp at hs
  | some pi =>
    rw [hp] at hs
    have hf := Inst.substitute_map Prod.fst i (i.consumed.zip ls)
    rw [h1, Inst.substitute_self, hp] at hf
    simp only [Option.map_some, Option.some.injEq] at hs hf
    exact ⟨pi, hf.symm, hs.symm, (Inst.substitute_consumed hp).1⟩

/-! ## What binding consumes -/

theorem boundUses_v (bs : List (Bound α)) : (boundUses bs).map (·.v) = bs.flatMap Bound.uses := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [boundUses, List.map_append, ih, List.flatMap_cons]
    congr 1
    cases b with
    | input s a => cases a <;> simp [useAt, Bound.uses, XArg.regs, List.map_map, Function.comp_def]
    | memory s m => simp [useAt, Bound.uses, List.map_map, Function.comp_def]
    | _ => simp [useAt, Bound.uses]

theorem boundDefs_v (z : Bool) : ∀ (i : Nat) (bs : List (Bound α)),
    (boundDefs z i bs).map (·.v) = bs.flatMap Bound.defs
  | _, [] => rfl
  | i, b :: bs => by
      simp only [boundDefs, List.map_append, boundDefs_v z _ bs, List.flatMap_cons]
      congr 1
      cases b with
      | output s x =>
        simp only [Bound.defs]
        split <;> rfl
      | _ => rfl

theorem bindSlots_regs :
    ∀ {slots : List X86.Slot} {defs : List α} {args : List (XArg α)}
      {bs : List (Bound α)} {defs' : List α} {args' : List (XArg α)},
      bindSlots slots defs args = some (bs, defs', args') →
      bs.flatMap Bound.uses ++ xargsRegs args' = xargsRegs args ∧
        bs.flatMap Bound.defs ++ defs' = defs
  | [], defs, args, bs, defs', args', h => by
      simp [bindSlots] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
  | ⟨kinds, width, role⟩ :: ss, defs, args, bs, defs', args', h => by
      have cons_eq : ∀ (b : Bound α) (defs₁ : List α) (args₁ : List (XArg α)),
          ((fun r => (b :: r.1, r.2)) <$> bindSlots ss defs₁ args₁) = some (bs, defs', args') →
          ∃ bs₁, bs = b :: bs₁ ∧ bindSlots ss defs₁ args₁ = some (bs₁, defs', args') := by
        intro b defs₁ args₁ h
        cases hb : bindSlots ss defs₁ args₁ with
        | none => simp [hb] at h
        | some r =>
          obtain ⟨bs₁, d, a⟩ := r
          simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨bs₁, rfl, rfl⟩
      cases role with
      | read | address =>
        cases args with
        | nil => simp [bindSlots] at h
        | cons a args =>
          obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
          have := bindSlots_regs h₁
          simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append, xargsRegs,
            List.append_assoc] at this ⊢
          exact ⟨by rw [this.1], this.2⟩
      | readWrite =>
        cases args with
        | nil => simp [bindSlots] at h
        | cons a args =>
          cases a with
          | r a =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs =>
              obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
              have := bindSlots_regs h₁
              simp only [List.flatMap_cons, Bound.uses, Bound.defs, xargsRegs, XArg.regs,
                List.cons_append, List.nil_append] at this ⊢
              exact ⟨by rw [this.1], by rw [this.2]⟩
          | m m =>
            obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
            have := bindSlots_regs h₁
            simp only [List.flatMap_cons, Bound.uses, Bound.defs, xargsRegs, XArg.regs,
              List.nil_append, List.append_assoc] at this ⊢
            exact ⟨by rw [this.1], this.2⟩
          | i w => simp [bindSlots] at h
      | write =>
        cases args with
        | nil =>
          cases defs with
          | nil => simp [bindSlots] at h
          | cons x defs =>
            obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
            have := bindSlots_regs h₁
            simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append,
              List.singleton_append] at this ⊢
            exact ⟨this.1, by rw [List.cons_append, this.2]⟩
        | cons a args =>
          cases a with
          | m m =>
            by_cases hk : X86.ArgKind.mem ∈ kinds
            · have hk' : kinds.contains .mem = true := List.contains_iff_mem.2 hk
              simp only [bindSlots, hk', ↓reduceIte] at h
              obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
              have := bindSlots_regs h₁
              simp only [List.flatMap_cons, Bound.uses, Bound.defs, xargsRegs, XArg.regs,
                List.nil_append, List.append_assoc] at this ⊢
              exact ⟨by rw [this.1], this.2⟩
            · have hk' : kinds.contains .mem = false := by
                cases hc : kinds.contains .mem
                · rfl
                · exact absurd (List.contains_iff_mem.1 hc) hk
              cases defs with
              | nil => simp [bindSlots, hk] at h
              | cons x defs =>
                simp only [bindSlots, hk', Bool.false_eq_true, ↓reduceIte] at h
                obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
                have := bindSlots_regs h₁
                simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append,
                  List.singleton_append] at this ⊢
                exact ⟨this.1, by rw [List.cons_append, this.2]⟩
          | r a =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs =>
              obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
              have := bindSlots_regs h₁
              simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append,
                List.singleton_append] at this ⊢
              exact ⟨this.1, by rw [List.cons_append, this.2]⟩
          | i w =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs =>
              obtain ⟨bs₁, rfl, h₁⟩ := cons_eq _ _ _ h
              have := bindSlots_regs h₁
              simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append,
                List.singleton_append] at this ⊢
              exact ⟨this.1, by rw [List.cons_append, this.2]⟩

theorem bindImplicits_regs :
    ∀ {is : List X86.Implicit} {defs : List α} {args : List (XArg α)} {bs : List (Bound α)},
      bindImplicits is defs args = some bs →
      bs.flatMap Bound.uses = xargsRegs args ∧ bs.flatMap Bound.defs = defs
  | [], [], [], bs, h => by simp [bindImplicits] at h; subst h; simp [xargsRegs]
  | [], _ :: _, _, _, h => by simp [bindImplicits] at h
  | [], [], _ :: _, _, h => by simp [bindImplicits] at h
  | i :: is, defs, args, bs, h => by
      have map_eq : ∀ (b : Bound α) (defs₁ : List α) (args₁ : List (XArg α)),
          ((b :: ·) <$> bindImplicits is defs₁ args₁) = some bs →
          ∃ bs₁, bs = b :: bs₁ ∧ bindImplicits is defs₁ args₁ = some bs₁ := by
        intro b defs₁ args₁ h
        cases hb : bindImplicits is defs₁ args₁ with
        | none => simp [hb] at h
        | some bs₁ =>
          simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          exact ⟨bs₁, h.symm, rfl⟩
      cases hr : i.role.reads <;> cases hw : i.role.writes
      · cases args <;> cases defs <;> simp [bindImplicits, hr, hw] at h
      · cases defs with
        | nil => cases args <;> simp [bindImplicits, hr, hw] at h
        | cons x defs =>
          have h' : ((Bound.fixedDef i x :: ·) <$> bindImplicits is defs args) = some bs := by
            cases args with
            | nil => simpa [bindImplicits, hr, hw] using h
            | cons a args => cases a <;> simpa [bindImplicits, hr, hw] using h
          obtain ⟨bs₁, rfl, h₁⟩ := map_eq _ _ _ h'
          have := bindImplicits_regs h₁
          simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append,
            List.singleton_append] at this ⊢
          exact ⟨this.1, by rw [this.2]⟩
      · cases args with
        | nil => simp [bindImplicits, hr, hw] at h
        | cons a args =>
          cases a with
          | r a =>
            simp only [bindImplicits, hr, hw] at h
            obtain ⟨bs₁, rfl, h₁⟩ := map_eq _ _ _ h
            have := bindImplicits_regs h₁
            simp only [List.flatMap_cons, Bound.uses, Bound.defs, List.nil_append, xargsRegs,
              XArg.regs, List.singleton_append] at this ⊢
            exact ⟨by rw [this.1], this.2⟩
          | m m => simp [bindImplicits, hr, hw] at h
          | i w => simp [bindImplicits, hr, hw] at h
      · cases args with
        | nil => simp [bindImplicits, hr, hw] at h
        | cons a args =>
          cases a with
          | r a =>
            cases defs with
            | nil => simp [bindImplicits, hr, hw] at h
            | cons x defs =>
              simp only [bindImplicits, hr, hw] at h
              obtain ⟨bs₁, rfl, h₁⟩ := map_eq _ _ _ h
              have := bindImplicits_regs h₁
              simp only [List.flatMap_cons, Bound.uses, Bound.defs, xargsRegs, XArg.regs,
                List.singleton_append] at this ⊢
              exact ⟨by rw [this.1], by rw [this.2]⟩
          | m m => cases defs <;> simp [bindImplicits, hr, hw] at h
          | i w => cases defs <;> simp [bindImplicits, hr, hw] at h

/-- A bound row consumes its arguments' registers as uses and its
definitions as definitions, in order. -/
theorem bindRow_regs {o : X86.Op} {defs : List α} {args : List (XArg α)} {bs : List (Bound α)}
    (h : bindRow o defs args = some bs) :
    bs.flatMap Bound.uses = xargsRegs args ∧ bs.flatMap Bound.defs = defs := by
  unfold bindRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨bs₁, defs', args'⟩, h₁, bs₂, h₂, he⟩ := h
  cases he
  have r₁ := bindSlots_regs h₁
  have r₂ := bindImplicits_regs h₂
  simp only [List.flatMap_append]
  exact ⟨by rw [r₂.1, r₁.1], by rw [r₂.2, r₁.2]⟩

/-- The operands of a bound row, as registers: its consumed operands. -/
theorem boundOperands_v {o : X86.Op} {defs : List α} {args : List (XArg α)} {bs : List (Bound α)}
    (h : bindRow o defs args = some bs) (z : Bool) :
    (boundOperands bs z).map (·.v) = xargsRegs args ++ defs := by
  simp [boundOperands, boundUses_v, boundDefs_v, bindRow_regs h]

end Compilatrix.Xv
