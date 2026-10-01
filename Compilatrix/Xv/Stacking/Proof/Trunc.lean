import Compilatrix.X86.Width

/-!
# A row reads only the low bits of a `read` slot

Xl runs a row with each stack cell in a borrowed register holding the
cell's whole word; the stacked code reads the cell as a memory operand at
the slot's width, which yields only the word's low bits. Every table row
writes only what the low bits of its `read` slots determine: its results,
truncated to the widths they are written at, its implicit results so
truncated, and its flags and outcome are the same (`sem_rel`). Inputs from
`readWrite` and `address` slots, and implicit registers, must be equal.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86

/-- Values equal at a width (`some w`), or equal outright (`none`). -/
def TruncEq : Option Width → Word → Word → Prop
  | some w, a, b => w.truncate a = w.truncate b
  | none, a, b => a = b

/-- Two input lists, pointwise `TruncEq` at the given widths. -/
def RelW : List (Option Width) → List Word → List Word → Prop
  | [], [], [] => True
  | w :: ws, a :: as, b :: bs => TruncEq w a b ∧ RelW ws as bs
  | _, _, _ => False

/-- The width each slot's input may be compared at: a `read` slot's own
width; `readWrite` and `address` slots exactly. -/
def inWidths (slots : List Slot) : List (Option Width) :=
  slots.filterMap fun s => match s.role with
    | .read => some (some s.width)
    | .readWrite | .address => some none
    | .write => none

/-- The widths at which a row's written slots store their results. -/
def outWidths (slots : List Slot) : List Width :=
  slots.filterMap fun s => if s.role.writes then some s.width else none

/-- The widths at which a row's written implicit registers store theirs. -/
def implicitOutWidths (is : List Implicit) : List Width :=
  (is.filter (·.role.writes)).map (·.width)

/-- The widths of every input of a row without stack traffic: its slots,
then the implicit registers it reads (compared exactly). -/
def rowInWidths (o : Op) : List (Option Width) :=
  inWidths (desc o).slots ++ ((desc o).implicit.filter (·.role.reads)).map fun _ => none

/-- Results equal at their widths, position by position (`headD 0`, as
`writeSlots` consumes them). -/
def ResW (ws : List Width) (rs₁ rs₂ : List Word) : Prop :=
  ∀ (i : Nat) (w : Width), ws[i]? = some w → w.truncate (rs₁.getD i 0) = w.truncate (rs₂.getD i 0)

/-- Two semantic outcomes a row cannot tell apart once written. -/
def SemRel (o : Op) : Except SemFault SemOut → Except SemFault SemOut → Prop
  | .ok o₁, .ok o₂ => o₁.flags = o₂.flags ∧ o₁.taken = o₂.taken ∧
      ResW (outWidths (desc o).slots) o₁.results o₂.results ∧
      ResW (implicitOutWidths (desc o).implicit) o₁.implicit o₂.implicit
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

theorem RelW.length {ws : List (Option Width)} :
    ∀ {as bs : List Word}, RelW ws as bs → as.length = ws.length ∧ bs.length = ws.length := by
  induction ws with
  | nil => intro as bs h; cases as <;> cases bs <;> simp_all [RelW]
  | cons w ws ih =>
      intro as bs h
      cases as <;> cases bs <;> simp_all [RelW]
      exact ⟨(ih h.2).1, (ih h.2).2⟩

/-! ## Words compared at a width -/

theorem setWidth_of_truncate {w : Width} {a b : Word} (h : w.truncate a = w.truncate b) :
    a.toBitVec.setWidth w.bits = b.toBitVec.setWidth w.bits := by
  have h' := congrArg UInt64.toNat h
  rw [Encode.truncate_nat, Encode.truncate_nat] at h'
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.toNat_setWidth] using h'

theorem truncate_of_eq {w : Width} {a b : Word} (h : a = b) : w.truncate a = w.truncate b := by rw [h]

theorem TruncEq.truncate {o : Option Width} {w : Width} {a b : Word} (h : TruncEq o a b)
    (hw : o = none ∨ o = some w) : w.truncate a = w.truncate b := by
  rcases hw with rfl | rfl
  · exact truncate_of_eq h
  · exact h

theorem aluFlags_congr (op : AluOp) (w : Width) {l₁ l₂ r₁ r₂ : Word} (hl : w.truncate l₁ = w.truncate l₂)
    (hr : w.truncate r₁ = w.truncate r₂) : ByteEval.aluFlags op w l₁ r₁ = ByteEval.aluFlags op w l₂ r₂ := by
  simp only [ByteEval.aluFlags, setWidth_of_truncate hl, setWidth_of_truncate hr]

theorem mulFlags_congr (w : Width) {l₁ l₂ r₁ r₂ : Word} (hl : w.truncate l₁ = w.truncate l₂)
    (hr : w.truncate r₁ = w.truncate r₂) : ByteEval.mulFlags w l₁ r₁ = ByteEval.mulFlags w l₂ r₂ := by
  simp only [ByteEval.mulFlags, setWidth_of_truncate hl, setWidth_of_truncate hr]

theorem shiftCount_congr (w : Width) {a b : Word} (h : w.truncate a = w.truncate b) :
    shiftCount w a = shiftCount w b := by
  have h' := congrArg UInt64.toNat h
  rw [Encode.truncate_nat, Encode.truncate_nat] at h'
  unfold shiftCount
  cases w
  all_goals
    simp only [Width.bits] at h'
    simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, UInt64.toNat_and]
  · have : a.toNat % 2 ^ 5 = b.toNat % 2 ^ 5 := by
      have := congrArg (· % 2 ^ 5) h'
      rwa [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)] at this
    rw [show (31 : Word).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, this]
  · have : a.toNat % 2 ^ 5 = b.toNat % 2 ^ 5 := by
      have := congrArg (· % 2 ^ 5) h'
      rwa [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)] at this
    rw [show (31 : Word).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, this]
  · have : a.toNat % 2 ^ 5 = b.toNat % 2 ^ 5 := by
      have := congrArg (· % 2 ^ 5) h'
      rwa [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)] at this
    rw [show (31 : Word).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, this]
  · have : a.toNat % 2 ^ 6 = b.toNat % 2 ^ 6 := by
      have := congrArg (· % 2 ^ 6) h'
      rwa [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)] at this
    rw [show (63 : Word).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, this]

/-! ## Each semantic function -/

/-- `SemRel` over explicit output widths. -/
def SemRelW (outs imps : List Width) : Except SemFault SemOut → Except SemFault SemOut → Prop
  | .ok o₁, .ok o₂ => o₁.flags = o₂.flags ∧ o₁.taken = o₂.taken ∧ ResW outs o₁.results o₂.results ∧
      ResW imps o₁.implicit o₂.implicit
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

theorem ResW.nil (rs₁ rs₂ : List Word) : ResW [] rs₁ rs₂ := fun _ _ h => by simp at h

theorem ResW.same (ws : List Width) (rs : List Word) : ResW ws rs rs := fun _ _ _ => rfl

theorem ResW.one {ws : List Width} {a b : Word} (h : ∀ w ∈ ws, w.truncate a = w.truncate b)
    (hl : ws.length ≤ 1) : ResW ws [a] [b] := by
  intro i w hw
  cases i with
  | zero => exact h w (List.mem_of_getElem? hw)
  | succ i =>
      have := (List.getElem?_eq_some_iff.1 hw).1
      omega

/-- Width conditions: each compared input is exact or compared at `w`. -/
def AtWidth (w : Width) (x : Option Width) : Prop := x = none ∨ x = some w

theorem RelW.two {x y : Option Width} {vs₁ vs₂ : List Word} (h : RelW [x, y] vs₁ vs₂) :
    ∃ a₁ b₁ a₂ b₂, vs₁ = [a₁, b₁] ∧ vs₂ = [a₂, b₂] ∧ TruncEq x a₁ a₂ ∧ TruncEq y b₁ b₂ := by
  rcases vs₁ with _ | ⟨a₁, _ | ⟨b₁, _ | ⟨_, _⟩⟩⟩ <;> rcases vs₂ with _ | ⟨a₂, _ | ⟨b₂, _ | ⟨_, _⟩⟩⟩ <;>
    simp_all [RelW] <;> exact ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, h.1, h.2⟩

theorem RelW.one {x : Option Width} {vs₁ vs₂ : List Word} (h : RelW [x] vs₁ vs₂) :
    ∃ a₁ a₂, vs₁ = [a₁] ∧ vs₂ = [a₂] ∧ TruncEq x a₁ a₂ := by
  rcases vs₁ with _ | ⟨a₁, _ | ⟨_, _⟩⟩ <;> rcases vs₂ with _ | ⟨a₂, _ | ⟨_, _⟩⟩ <;> simp_all [RelW]

theorem RelW.three {x y z : Option Width} {vs₁ vs₂ : List Word} (h : RelW [x, y, z] vs₁ vs₂) :
    ∃ a₁ b₁ c₁ a₂ b₂ c₂, vs₁ = [a₁, b₁, c₁] ∧ vs₂ = [a₂, b₂, c₂] ∧ TruncEq x a₁ a₂ ∧ TruncEq y b₁ b₂ ∧
      TruncEq z c₁ c₂ := by
  rcases vs₁ with _ | ⟨a₁, _ | ⟨b₁, _ | ⟨c₁, _ | ⟨_, _⟩⟩⟩⟩ <;>
    rcases vs₂ with _ | ⟨a₂, _ | ⟨b₂, _ | ⟨c₂, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all [RelW] <;>
    exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩, h.1, h.2.1, h.2.2⟩

theorem RelW.nil' {vs₁ vs₂ : List Word} (h : RelW [] vs₁ vs₂) : vs₁ = [] ∧ vs₂ = [] := by
  cases vs₁ <;> cases vs₂ <;> simp_all [RelW]

theorem aluSem_rel (op : AluOp) (w : Width) {x y : Option Width} (hx : AtWidth w x) (hy : AtWidth w y)
    {outs : List Width} (houts : ∀ v ∈ outs, v = w) (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word}
    (h : RelW [x, y] vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.aluSem op w ⟨vs₁, obs⟩) (Table.aluSem op w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  have ha' := ha.truncate hx
  have hb' := hb.truncate hy
  refine ⟨aluFlags_congr op w ha' hb', rfl, ResW.one (fun v hv => ?_) hl, ResW.nil _ _⟩
  rw [houts v hv, Encode.truncate_alu, ha', hb', ← Encode.truncate_alu]

theorem cmpSem_rel (w : Width) {x y : Option Width} (hx : AtWidth w x) (hy : AtWidth w y)
    (outs : List Width) {vs₁ vs₂ : List Word} (h : RelW [x, y] vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.cmpSem w ⟨vs₁, obs⟩) (Table.cmpSem w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  exact ⟨aluFlags_congr .sub w (ha.truncate hx) (hb.truncate hy), rfl, fun _ _ _ => rfl, ResW.nil _ _⟩

theorem testSem_rel (w : Width) {x y : Option Width} (hx : AtWidth w x) (hy : AtWidth w y)
    (outs : List Width) {vs₁ vs₂ : List Word} (h : RelW [x, y] vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.testSem w ⟨vs₁, obs⟩) (Table.testSem w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  exact ⟨aluFlags_congr .and w (ha.truncate hx) (hb.truncate hy), rfl, fun _ _ _ => rfl, ResW.nil _ _⟩

theorem moveSem_rel (w : Width) {x : Option Width} (hx : AtWidth w x) {outs : List Width}
    (houts : ∀ v ∈ outs, v = w) (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word} (h : RelW [x] vs₁ vs₂)
    (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.moveSem ⟨vs₁, obs⟩) (Table.moveSem ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, a₂, rfl, rfl, ha⟩ := h.one
  exact ⟨rfl, rfl, ResW.one (fun v hv => by rw [houts v hv]; exact ha.truncate hx) hl, ResW.nil _ _⟩

theorem zeroExtendSem_rel (src : Width) {x : Option Width} (hx : AtWidth src x) (outs : List Width)
    (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word} (h : RelW [x] vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.zeroExtendSem src ⟨vs₁, obs⟩) (Table.zeroExtendSem src ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, a₂, rfl, rfl, ha⟩ := h.one
  exact ⟨rfl, rfl, ResW.one (fun v _ => by rw [ha.truncate hx]) hl, ResW.nil _ _⟩

theorem mulSem_rel (w : Width) {x y : Option Width} (hx : AtWidth w x) (hy : AtWidth w y)
    {outs : List Width} (houts : ∀ v ∈ outs, v = w) (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word}
    (h : RelW [x, y] vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.mulSem w ⟨vs₁, obs⟩) (Table.mulSem w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  have ha' := ha.truncate hx
  have hb' := hb.truncate hy
  refine ⟨mulFlags_congr w ha' hb', rfl, ResW.one (fun v hv => ?_) hl, ResW.nil _ _⟩
  rw [houts v hv, Encode.truncate_mul, ha', hb', ← Encode.truncate_mul]

theorem shiftSem_rel (op : ShiftOp) (w : Width) {y : Option Width} (hy : AtWidth w y) {outs : List Width}
    (houts : ∀ v ∈ outs, v = w) (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word} (h : RelW [none, y] vs₁ vs₂)
    (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.shiftSem op w ⟨vs₁, obs⟩) (Table.shiftSem op w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  simp only [TruncEq] at ha
  subst ha
  have hc := shiftCount_congr w (hb.truncate hy)
  simp only [Table.shiftSem, hc]
  exact ⟨rfl, rfl, ResW.same _ _, ResW.nil _ _⟩

theorem divSem_rel (w : Width) {x : Option Width} (hx : AtWidth w x) (outs : List Width) {imps : List Width}
    (himps : ∀ v ∈ imps, v = w) {vs₁ vs₂ : List Word} (h : RelW [x, none, none] vs₁ vs₂)
    (obs : ByteEval.Flags) :
    SemRelW outs imps (Table.divSem w ⟨vs₁, obs⟩) (Table.divSem w ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, rfl, rfl, ha, hb, hc⟩ := h.three
  simp only [TruncEq] at hb hc
  subst hb hc
  have ha' := ha.truncate hx
  simp only [Table.divSem, ha']
  split
  · rfl
  · exact ⟨rfl, rfl, fun _ _ _ => rfl, ResW.same _ _⟩

theorem setccSem_rel (c : Condition) (outs imps : List Width) {vs₁ vs₂ : List Word} (obs : ByteEval.Flags) :
    SemRelW outs imps (Table.setccSem c ⟨vs₁, obs⟩) (Table.setccSem c ⟨vs₂, obs⟩) := by
  simp only [Table.setccSem]
  split
  · exact ⟨rfl, rfl, ResW.same _ _, ResW.same _ _⟩
  · rfl

theorem cmovSem_rel (c : Condition) (w : Width) {y : Option Width} (hy : AtWidth w y) {outs : List Width}
    (houts : ∀ v ∈ outs, v = w) (hl : outs.length ≤ 1) {vs₁ vs₂ : List Word} (h : RelW [none, y] vs₁ vs₂)
    (obs : ByteEval.Flags) :
    SemRelW outs [] (Table.cmovSem c ⟨vs₁, obs⟩) (Table.cmovSem c ⟨vs₂, obs⟩) := by
  obtain ⟨a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := h.two
  simp only [TruncEq] at ha
  subst ha
  have hb' := hb.truncate hy
  simp only [Table.cmovSem]
  split
  · rename_i holds _
    refine ⟨rfl, rfl, ResW.one (fun v hv => ?_) hl, ResW.nil _ _⟩
    rw [houts v hv]
    cases holds <;> simp [hb']
  · rfl

theorem controlSem_rel (outs imps : List Width) (vs₁ vs₂ : List Word) (obs : ByteEval.Flags) :
    SemRelW outs imps (Table.controlSem ⟨vs₁, obs⟩) (Table.controlSem ⟨vs₂, obs⟩) :=
  ⟨rfl, rfl, ResW.same _ _, ResW.same _ _⟩

theorem jccSem_rel (c : Condition) (outs imps : List Width) (vs₁ vs₂ : List Word) (obs : ByteEval.Flags) :
    SemRelW outs imps (Table.jccSem c ⟨vs₁, obs⟩) (Table.jccSem c ⟨vs₂, obs⟩) := by
  simp only [Table.jccSem]
  split
  · exact ⟨rfl, rfl, ResW.same _ _, ResW.same _ _⟩
  · rfl

/-! ## Every row -/

theorem arith_rel (arith : Table.Arith) (w : Width) (form : OpEn) {vs₁ vs₂ : List Word}
    (h : RelW (inWidths (Table.arithDesc arith w form).slots) vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW (outWidths (Table.arithDesc arith w form).slots) []
      ((Table.arithDesc arith w form).sem ⟨vs₁, obs⟩) ((Table.arithDesc arith w form).sem ⟨vs₂, obs⟩) := by
  have aw : AtWidth w (some w) := .inr rfl
  have an : AtWidth w none := .inl rfl
  rcases arith with ⟨op | _, digit, wide, name⟩ <;>
    cases form <;>
    simp only [Table.arithDesc, Table.Arith.role, Table.Arith.sem, Option.isSome_some, Option.isSome_none,
      ↓reduceIte, Bool.false_eq_true, inWidths, outWidths, Table.rmSlot, Table.regSlot, Table.immSlot,
      List.filterMap_cons, List.filterMap_nil, Role.writes] at h ⊢ <;>
    first
    | exact aluSem_rel _ w an aw (by simp) (by simp) h obs
    | exact aluSem_rel _ w aw aw (by simp) (by simp) h obs
    | exact cmpSem_rel w aw aw _ h obs

theorem arithDesc_implicit (arith : Table.Arith) (w : Width) (form : OpEn) :
    (Table.arithDesc arith w form).implicit = [] := by
  cases form <;> rfl

theorem sem_rel (o : Op) (hstack : (desc o).stack = .none) {vs₁ vs₂ : List Word}
    (h : RelW (rowInWidths o) vs₁ vs₂) (obs : ByteEval.Flags) :
    SemRelW (outWidths (desc o).slots) (implicitOutWidths (desc o).implicit)
      ((desc o).sem ⟨vs₁, obs⟩) ((desc o).sem ⟨vs₂, obs⟩) := by
  have aw : ∀ w : Width, AtWidth w (some w) := fun _ => .inr rfl
  have an : ∀ w : Width, AtWidth w none := fun _ => .inl rfl
  rcases o with ⟨mn, w, form, src⟩
  cases mn
  case add | or | and | sub | xor | cmp =>
    simp only [rowInWidths, desc, arithDesc_implicit, List.filter_nil, List.map_nil, List.append_nil,
      implicitOutWidths] at h ⊢
    exact arith_rel _ w form h obs
  case mov =>
    cases form <;>
    simp only [rowInWidths, desc, Table.movDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.regSlot, Table.immSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte,
      Bool.false_eq_true, List.filter_nil, List.map_nil, List.append_nil] at h ⊢ <;>
    exact moveSem_rel w (aw w) (by simp) (by simp) h obs
  case movzx =>
    simp only [rowInWidths, desc, Table.movzxDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.regSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte, Bool.false_eq_true,
      List.filter_nil, List.map_nil, List.append_nil] at h ⊢
    exact zeroExtendSem_rel src (aw src) _ (by simp) h obs
  case lea =>
    simp only [rowInWidths, desc, Table.leaDesc, inWidths, outWidths, implicitOutWidths, Table.regSlot,
      List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte, Bool.false_eq_true,
      List.filter_nil, List.map_nil, List.append_nil] at h ⊢
    exact moveSem_rel w (an w) (by simp) (by simp) h obs
  case imul =>
    cases form <;>
    simp only [rowInWidths, desc, Table.imulDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.regSlot, Table.immSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte,
      Bool.false_eq_true, List.filter_nil, List.map_nil, List.append_nil] at h ⊢ <;>
    first
    | exact mulSem_rel w (aw w) (aw w) (by simp) (by simp) h obs
    | exact mulSem_rel w (an w) (aw w) (by simp) (by simp) h obs
  case test =>
    cases form <;>
    simp only [rowInWidths, desc, Table.testDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.regSlot, Table.immSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte,
      Bool.false_eq_true, List.filter_nil, List.map_nil, List.append_nil] at h ⊢ <;>
    exact testSem_rel w (aw w) (aw w) _ h obs
  case shl | shr | sar =>
    cases form <;>
    simp only [rowInWidths, desc, Table.shiftDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.immSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, Role.reads, ↓reduceIte,
      Bool.false_eq_true, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append] at h ⊢ <;>
    first
    | exact shiftSem_rel _ w (aw w) (by simp) (by simp) h obs
    | exact shiftSem_rel _ w (an w) (by simp) (by simp) h obs
  case div =>
    simp only [rowInWidths, desc, Table.divDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      List.filterMap_cons, List.filterMap_nil, Role.writes, Role.reads, ↓reduceIte, Bool.false_eq_true,
      List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h ⊢
    exact divSem_rel w (aw w) _ (by simp) h obs
  case setcc c =>
    simp only [rowInWidths, desc, Table.setccDesc, outWidths, implicitOutWidths]
    exact setccSem_rel c _ _ obs
  case cmovcc c =>
    simp only [rowInWidths, desc, Table.cmovDesc, inWidths, outWidths, implicitOutWidths, Table.rmSlot,
      Table.regSlot, List.filterMap_cons, List.filterMap_nil, Role.writes, ↓reduceIte, Bool.false_eq_true,
      List.filter_nil, List.map_nil, List.append_nil] at h ⊢
    exact cmovSem_rel c w (aw w) (by simp) (by simp) h obs
  case push | pop | call | ret => simp [desc, Table.pushDesc, Table.popDesc, Table.callDesc, Table.retDesc] at hstack
  case jmp => exact controlSem_rel _ _ vs₁ vs₂ obs
  case jcc c => exact jccSem_rel c _ _ vs₁ vs₂ obs

end Compilatrix.Xv.Stacking.Proof
