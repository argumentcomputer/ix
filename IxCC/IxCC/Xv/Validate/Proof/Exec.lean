import IxCC.X86.Table.Exec

/-!
# A row on corresponding cores

The table executor (`X86.Op.run`) reads a row's operands only through its
machine arguments and implicit registers, so two runs whose operands hold
the same values compute the same results, whatever registers hold them. This
is the fact behind Xv/Xl agreement (05 §3, "metadata from the table"): Xv
places each operand in its own scratch register, Xl in its allocated
location, and `op_run_corr` shows the row cannot tell them apart.

`SlotsCorr c₁ c₂` relates the machine arguments of two runs slot by slot:
the same immediate, memory operands at the same address, or registers
holding the same value, except that a write-only 32- or 64-bit register slot
may start with anything (the write replaces or zero-extends it). Under that
relation, with no stack traffic and with each run writing every register at
most once, the runs agree on the outcome, the memory, the flags and each
written register (`WrittenCorr`), and leave every other register alone.
-/

namespace IxCC.Xv.Validate

open IxCC.X86

/-! ## Register writes -/

/-- The value a register write of width `w` leaves when the register held
`old`: 64 bits replace it, 32 zero-extend, 8 and 16 keep the other bits. -/
def mergeWrite (w : Width) (old v : Word) : Word :=
  match w with
  | .w64 => v
  | .w32 => w.truncate v
  | .w8 | .w16 => (old &&& (0xffffffffffffffff ^^^ w.mask)) ||| w.truncate v

/-- A write that does not read the old value: 32 or 64 bits. -/
def Wide (w : Width) : Prop := w = .w32 ∨ w = .w64

theorem mergeWrite_wide {w : Width} (h : Wide w) (old old' v : Word) :
    mergeWrite w old v = mergeWrite w old' v := by
  rcases h with rfl | rfl <;> rfl

theorem readReg_setReg (c : Core) (r r' : GPR) (v : Word) :
    (c.setReg r v).readReg r' = if r' = r then v else c.readReg r' := by
  simp [Core.setReg, Core.readReg, Registers.set]

theorem readReg_writeReg (c : Core) (w : Width) (r r' : GPR) (v : Word) :
    (c.writeReg w r v).readReg r' =
      if r' = r then mergeWrite w (c.readReg r) v else c.readReg r' := by
  cases w <;> simp [Core.writeReg, readReg_setReg, mergeWrite]

@[simp] theorem memory_writeReg (c : Core) (w : Width) (r : GPR) (v : Word) :
    (c.writeReg w r v).memory = c.memory := by
  cases w <;> rfl

/-! ## Corresponding arguments -/

/-- Two machine operands of slot `s` that the row cannot tell apart. -/
def SlotCorr (c₁ c₂ : Core) (s : Slot) : Arg → Arg → Prop
  | .reg r₁, .reg r₂ => (s.role = .write ∧ Wide s.width) ∨ c₁.readReg r₁ = c₂.readReg r₂
  | .mem m₁, .mem m₂ => m₁.eval c₁ = m₂.eval c₂
  | .imm v₁, .imm v₂ => v₁ = v₂
  | _, _ => False

/-- Corresponding arguments, one per slot. -/
def SlotsCorr (c₁ c₂ : Core) : List Slot → List Arg → List Arg → Prop
  | [], [], [] => True
  | s :: ss, a₁ :: as₁, a₂ :: as₂ => SlotCorr c₁ c₂ s a₁ a₂ ∧ SlotsCorr c₁ c₂ ss as₁ as₂
  | _, _, _ => False

/-- The registers a row's slots write, in order. -/
def slotWrites : List Slot → List Arg → List GPR
  | s :: ss, .reg r :: as => (if s.role.writes then [r] else []) ++ slotWrites ss as
  | _ :: ss, _ :: as => slotWrites ss as
  | _, _ => []

/-- The implicit registers a row writes. -/
def implicitWrites (is : List Implicit) : List GPR := (is.filter (·.role.writes)).map (·.reg)

/-- Every register the row writes. -/
def rowWrites (o : Op) (args : List Arg) : List GPR :=
  slotWrites (desc o).slots args ++ implicitWrites (desc o).implicit

/-- The written register slots end with equal values. -/
def WrittenCorr (f₁ f₂ : Core) : List Slot → List Arg → List Arg → Prop
  | s :: ss, a₁ :: as₁, a₂ :: as₂ =>
      (s.role.writes = true → ∀ r₁ r₂, a₁ = .reg r₁ → a₂ = .reg r₂ → f₁.readReg r₁ = f₂.readReg r₂) ∧
        WrittenCorr f₁ f₂ ss as₁ as₂
  | _, _, _ => True

/-! ## Reading -/

theorem readSlots_corr {c₁ c₂ : Core} (hmem : c₁.memory = c₂.memory) :
    ∀ {slots : List Slot} {as₁ as₂ : List Arg}, SlotsCorr c₁ c₂ slots as₁ as₂ →
      readSlots c₁ slots as₁ = readSlots c₂ slots as₂
  | [], [], [], _ => rfl
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim
  | ⟨kinds, width, role⟩ :: ss, a₁ :: as₁, a₂ :: as₂, ⟨h, hs⟩ => by
      have ih := readSlots_corr hmem hs
      cases role with
      | write => simp only [readSlots]; exact ih
      | read | readWrite =>
        simp only [readSlots]
        have : Arg.load c₁ width a₁ = Arg.load c₂ width a₂ := by
          cases a₁ <;> cases a₂ <;> simp only [SlotCorr, reduceCtorEq, false_and, false_or] at h
          all_goals simp [Arg.load, h, hmem]
        rw [this, ih]
      | address =>
        simp only [readSlots]
        have : Arg.address c₁ a₁ = Arg.address c₂ a₂ := by
          cases a₁ <;> cases a₂ <;> simp only [SlotCorr, reduceCtorEq, false_and, false_or] at h
          all_goals simp [Arg.address, h]
        rw [this, ih]

theorem readImplicits_corr {c₁ c₂ : Core} :
    ∀ {is : List Implicit}, (∀ i ∈ is, i.role.reads = true → c₁.readReg i.reg = c₂.readReg i.reg) →
      readImplicits c₁ is = readImplicits c₂ is
  | [], _ => rfl
  | i :: is, h => by
      have ih := readImplicits_corr (is := is) fun j hj => h j (List.mem_cons_of_mem _ hj)
      unfold readImplicits at ih ⊢
      simp only [List.filterMap_cons]
      by_cases hr : i.role.reads = true
      · simp [hr, h i List.mem_cons_self hr, ih]
      · simp [hr, ih]

/-! ## Writing -/

/-- Corresponding written operands, for `writeSlots`: memory operands at the
same address in the cores before the row (`b₁`, `b₂`), and registers whose
current values agree unless the write ignores them. -/
def WriteArgCorr (b₁ b₂ cur₁ cur₂ : Core) (s : Slot) : Arg → Arg → Prop
  | .reg r₁, .reg r₂ => Wide s.width ∨ cur₁.readReg r₁ = cur₂.readReg r₂
  | .mem m₁, .mem m₂ => m₁.eval b₁ = m₂.eval b₂
  | .imm _, .imm _ => True
  | _, _ => False

def WriteCorr (b₁ b₂ cur₁ cur₂ : Core) : List Slot → List Arg → List Arg → Prop
  | [], [], [] => True
  | s :: ss, a₁ :: as₁, a₂ :: as₂ =>
      (s.role.writes = true → WriteArgCorr b₁ b₂ cur₁ cur₂ s a₁ a₂) ∧ WriteCorr b₁ b₂ cur₁ cur₂ ss as₁ as₂
  | _, _, _ => False

theorem WriteCorr.update {b₁ b₂ cur₁ cur₂ cur₁' cur₂' : Core} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, WriteCorr b₁ b₂ cur₁ cur₂ ss as₁ as₂ →
      (∀ r ∈ slotWrites ss as₁, cur₁'.readReg r = cur₁.readReg r) →
      (∀ r ∈ slotWrites ss as₂, cur₂'.readReg r = cur₂.readReg r) →
      WriteCorr b₁ b₂ cur₁' cur₂' ss as₁ as₂
  | [], [], [], _, _, _ => trivial
  | [], [], _ :: _, h, _, _ => h.elim
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _ => h.elim
  | s :: ss, a₁ :: as₁, a₂ :: as₂, ⟨h, hs⟩, h₁, h₂ => by
      have hw₁ : ∀ r ∈ slotWrites ss as₁, cur₁'.readReg r = cur₁.readReg r := fun r hr =>
        h₁ r (by cases a₁ <;> simp [slotWrites, hr])
      have hw₂ : ∀ r ∈ slotWrites ss as₂, cur₂'.readReg r = cur₂.readReg r := fun r hr =>
        h₂ r (by cases a₂ <;> simp [slotWrites, hr])
      refine ⟨fun hwr => ?_, WriteCorr.update hs hw₁ hw₂⟩
      have := h hwr
      cases a₁ <;> cases a₂ <;> simp only [WriteArgCorr] at this ⊢
      · rename_i r₁ r₂
        rw [h₁ r₁ (by simp [slotWrites, hwr]), h₂ r₂ (by simp [slotWrites, hwr])]
        exact this
      all_goals exact this

theorem slotWrites_nodup_tail {s : Slot} {ss : List Slot} {a : Arg} {as : List Arg}
    (h : (slotWrites (s :: ss) (a :: as)).Nodup) : (slotWrites ss as).Nodup := by
  cases a <;> simp only [slotWrites] at h
  · exact (List.nodup_append.1 h).2.1
  all_goals exact h

theorem writeSlots_frame {before : Core} :
    ∀ {slots : List Slot} {as : List Arg} {results : List Word} {cur fin : Core},
      writeSlots before cur slots as results = .ok fin →
      fin.memory = fin.memory ∧ ∀ r, r ∉ slotWrites slots as → fin.readReg r = cur.readReg r
  | [], _, _, _, _, h => by
      simp only [writeSlots, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨rfl, fun _ _ => rfl⟩
  | _ :: _, [], _, _, _, h => by
      simp only [writeSlots, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨rfl, fun _ _ => rfl⟩
  | ⟨kinds, width, role⟩ :: ss, a :: as, results, cur, fin, h => by
      refine ⟨rfl, fun r hr => ?_⟩
      cases role with
      | read | address =>
        simp only [writeSlots] at h
        exact (writeSlots_frame h).2 r (by cases a <;> simp_all [slotWrites, Role.writes])
      | write | readWrite =>
        simp only [writeSlots, bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i cur' hst
          rw [(writeSlots_frame h).2 r (by cases a <;> simp_all [slotWrites, Role.writes])]
          cases a with
          | reg r' =>
            simp only [Arg.store, Except.ok.injEq] at hst
            subst hst
            rw [readReg_writeReg]
            have : r ≠ r' := by simp_all [slotWrites, Role.writes]
            simp [this]
          | mem m =>
            simp only [Arg.store, bind, Except.bind] at hst
            split at hst
            · simp at hst
            · simp only [pure, Except.pure, Except.ok.injEq] at hst
              subst hst; rfl
          | imm v =>
            simp only [Arg.store, Except.ok.injEq] at hst
            subst hst; rfl

theorem writeSlots_corr {b₁ b₂ : Core} :
    ∀ {slots : List Slot} {as₁ as₂ : List Arg} {results : List Word} {cur₁ cur₂ fin₁ : Core},
      cur₁.memory = cur₂.memory → WriteCorr b₁ b₂ cur₁ cur₂ slots as₁ as₂ →
      (slotWrites slots as₁).Nodup → (slotWrites slots as₂).Nodup →
      writeSlots b₁ cur₁ slots as₁ results = .ok fin₁ →
      ∃ fin₂, writeSlots b₂ cur₂ slots as₂ results = .ok fin₂ ∧ fin₁.memory = fin₂.memory ∧
        WrittenCorr fin₁ fin₂ slots as₁ as₂
  | [], [], [], _, _, cur₂, _, hmem, _, _, _, h => by
      simp only [writeSlots, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨cur₂, rfl, hmem, trivial⟩
  | [], [], _ :: _, _, _, _, _, _, h, _, _, _ => h.elim
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, h, _, _, _ => h.elim
  | ⟨kinds, width, role⟩ :: ss, a₁ :: as₁, a₂ :: as₂, results, cur₁, cur₂, fin₁, hmem, ⟨h, hs⟩,
      hn₁, hn₂, hrun => by
      have hn₁' := slotWrites_nodup_tail hn₁
      have hn₂' := slotWrites_nodup_tail hn₂
      cases role with
      | read | address =>
        simp only [writeSlots] at hrun ⊢
        obtain ⟨fin₂, h₂, hm, hw⟩ := writeSlots_corr hmem hs hn₁' hn₂' hrun
        exact ⟨fin₂, h₂, hm, fun hw' => by simp [Role.writes] at hw', hw⟩
      | write | readWrite =>
        have hwr : (Role.writes (.write)) = true ∧ Role.writes .readWrite = true := ⟨rfl, rfl⟩
        simp only [writeSlots, bind, Except.bind] at hrun ⊢
        split at hrun
        · simp at hrun
        rename_i cur₁' hst₁
        have ha := h (by first | exact hwr.1 | exact hwr.2)
        -- The stored cores, with equal memory, and the tail's correspondence.
        have key : ∃ cur₂', Arg.store b₂ width (results.headD 0) cur₂ a₂ = .ok cur₂' ∧
            cur₁'.memory = cur₂'.memory ∧
            (∀ r₁ r₂, a₁ = .reg r₁ → a₂ = .reg r₂ → cur₁'.readReg r₁ = cur₂'.readReg r₂) ∧
            (∀ r, (∀ r₁, a₁ = .reg r₁ → r ≠ r₁) → cur₁'.readReg r = cur₁.readReg r) ∧
            (∀ r, (∀ r₂, a₂ = .reg r₂ → r ≠ r₂) → cur₂'.readReg r = cur₂.readReg r) := by
          cases a₁ <;> cases a₂ <;> simp only [WriteArgCorr] at ha
          · rename_i r₁ r₂
            simp only [Arg.store, Except.ok.injEq] at hst₁
            subst hst₁
            refine ⟨_, rfl, by simp [hmem], ?_, ?_, ?_⟩
            · intro r₁' r₂' e₁ e₂
              cases e₁; cases e₂
              rw [readReg_writeReg, readReg_writeReg]
              simp only [↓reduceIte]
              rcases ha with hw | he
              · exact mergeWrite_wide hw _ _ _
              · rw [he]
            · intro r hr
              rw [readReg_writeReg, ite_eq_right (hr r₁ rfl)]
            · intro r hr
              rw [readReg_writeReg, ite_eq_right (hr r₂ rfl)]
          · rename_i m₁ m₂
            simp only [Arg.store, bind, Except.bind] at hst₁ ⊢
            split at hst₁
            · simp at hst₁
            rename_i mem' hw
            simp only [pure, Except.pure, Except.ok.injEq] at hst₁
            subst hst₁
            rw [← hmem, ← ha, hw]
            exact ⟨_, rfl, rfl, by simp, fun _ _ => rfl, fun _ _ => rfl⟩
          · simp only [Arg.store, Except.ok.injEq] at hst₁
            subst hst₁
            exact ⟨_, rfl, hmem, by simp, fun _ _ => rfl, fun _ _ => rfl⟩
        obtain ⟨cur₂', hst₂, hmem', hreg, hf₁, hf₂⟩ := key
        rw [hst₂]
        have hs' : WriteCorr b₁ b₂ cur₁' cur₂' ss as₁ as₂ := by
          refine hs.update (fun r hr => hf₁ r fun r₁ e => ?_) (fun r hr => hf₂ r fun r₂ e => ?_)
          · subst e
            intro hrr; subst hrr
            simp only [slotWrites, Role.writes, ↓reduceIte, List.singleton_append,
              List.nodup_cons] at hn₁
            exact hn₁.1 hr
          · subst e
            intro hrr; subst hrr
            simp only [slotWrites, Role.writes, ↓reduceIte, List.singleton_append,
              List.nodup_cons] at hn₂
            exact hn₂.1 hr
        obtain ⟨fin₂, h₂, hm, hw⟩ := writeSlots_corr hmem' hs' hn₁' hn₂' hrun
        refine ⟨fin₂, h₂, hm, fun _ r₁ r₂ e₁ e₂ => ?_, hw⟩
        subst e₁ e₂
        have hr₁ : r₁ ∉ slotWrites ss as₁ := by
          simp only [slotWrites, Role.writes, ↓reduceIte, List.singleton_append,
            List.nodup_cons] at hn₁
          exact hn₁.1
        have hr₂ : r₂ ∉ slotWrites ss as₂ := by
          simp only [slotWrites, Role.writes, ↓reduceIte, List.singleton_append,
            List.nodup_cons] at hn₂
          exact hn₂.1
        rw [(writeSlots_frame hrun).2 r₁ hr₁, (writeSlots_frame h₂).2 r₂ hr₂]
        exact hreg r₁ r₂ rfl rfl

/-! ## Implicit registers -/

theorem writeImplicits_memory :
    ∀ {is : List Implicit} {res : List Word} {cur : Core}, (writeImplicits cur is res).memory = cur.memory
  | [], _, _ => by simp
  | i :: is, res, cur => by
      simp only [writeImplicits]
      split
      · rw [writeImplicits_memory, memory_writeReg]
      · exact writeImplicits_memory

theorem writeImplicits_frame {r : GPR} :
    ∀ {is : List Implicit} {res : List Word} {cur : Core}, r ∉ implicitWrites is →
      (writeImplicits cur is res).readReg r = cur.readReg r
  | [], _, _, _ => by simp
  | i :: is, res, cur, hr => by
      simp only [writeImplicits]
      split
      · rename_i hw
        have hr' : r ∉ implicitWrites is ∧ r ≠ i.reg := by
          simp only [implicitWrites, List.filter_cons, hw, ↓reduceIte, List.map_cons,
            List.mem_cons, not_or] at hr
          exact ⟨by simpa [implicitWrites] using hr.2, hr.1⟩
        rw [writeImplicits_frame hr'.1, readReg_writeReg, ite_eq_right hr'.2]
      · rename_i hw
        have : r ∉ implicitWrites is := by
          simpa [implicitWrites, List.filter_cons, hw] using hr
        exact writeImplicits_frame this

theorem writeImplicits_corr :
    ∀ {is : List Implicit} {res : List Word} {cur₁ cur₂ : Core}, (implicitWrites is).Nodup →
      (∀ i ∈ is, i.role.writes = true → Wide i.width ∨ cur₁.readReg i.reg = cur₂.readReg i.reg) →
      ∀ i ∈ is, i.role.writes = true →
        (writeImplicits cur₁ is res).readReg i.reg = (writeImplicits cur₂ is res).readReg i.reg
  | [], _, _, _, _, _, i, hi, _ => by simp at hi
  | j :: is, res, cur₁, cur₂, hn, h, i, hi, hw => by
      simp only [writeImplicits]
      by_cases hj : j.role.writes = true
      · simp only [hj, ↓reduceIte]
        have hn' : j.reg ∉ implicitWrites is ∧ (implicitWrites is).Nodup := by
          simpa [implicitWrites, List.filter_cons, hj] using hn
        have h' : ∀ i ∈ is, i.role.writes = true →
            Wide i.width ∨ (cur₁.writeReg j.width j.reg (res.headD 0)).readReg i.reg =
              (cur₂.writeReg j.width j.reg (res.headD 0)).readReg i.reg := by
          intro i' hi' hw'
          rcases h i' (List.mem_cons_of_mem _ hi') hw' with hw'' | he
          · exact .inl hw''
          · refine .inr ?_
            have : i'.reg ≠ j.reg := fun e => hn'.1 (by
              simp only [implicitWrites, List.mem_map, List.mem_filter]
              exact ⟨i', ⟨hi', hw'⟩, e⟩)
            rw [readReg_writeReg, readReg_writeReg, ite_eq_right this, ite_eq_right this, he]
        rcases List.mem_cons.1 hi with rfl | hi
        · rw [writeImplicits_frame hn'.1, writeImplicits_frame hn'.1, readReg_writeReg,
            readReg_writeReg]
          simp only [↓reduceIte]
          rcases h i (List.mem_cons_self) hw with hw' | he
          · exact mergeWrite_wide hw' _ _ _
          · rw [he]
        · exact writeImplicits_corr hn'.2 h' i hi hw
      · simp only [hj, Bool.false_eq_true, ↓reduceIte]
        have hn' : (implicitWrites is).Nodup := by
          simpa [implicitWrites, List.filter_cons, hj] using hn
        rcases List.mem_cons.1 hi with rfl | hi
        · exact absurd hw hj
        · exact writeImplicits_corr hn' (fun i' hi' => h i' (List.mem_cons_of_mem _ hi')) i hi hw

/-! ## A row -/

/-- The corresponding argument lists give the write-back correspondence. -/
theorem SlotsCorr.write {c₁ c₂ : Core} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, SlotsCorr c₁ c₂ ss as₁ as₂ →
      WriteCorr c₁ c₂ c₁ c₂ ss as₁ as₂
  | [], [], [], _ => trivial
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim
  | s :: ss, a₁ :: as₁, a₂ :: as₂, ⟨h, hs⟩ => by
      refine ⟨fun _ => ?_, SlotsCorr.write hs⟩
      cases a₁ <;> cases a₂ <;> simp only [SlotCorr, WriteArgCorr] at h ⊢
      · rcases h with ⟨_, hw⟩ | he
        · exact .inl hw
        · exact .inr he
      all_goals trivial

theorem WrittenCorr.frame {f₁ f₂ g₁ g₂ : Core} :
    ∀ {ss : List Slot} {as₁ as₂ : List Arg}, WrittenCorr f₁ f₂ ss as₁ as₂ →
      (∀ r ∈ slotWrites ss as₁, g₁.readReg r = f₁.readReg r) →
      (∀ r ∈ slotWrites ss as₂, g₂.readReg r = f₂.readReg r) →
      WrittenCorr g₁ g₂ ss as₁ as₂
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _ => trivial
  | s :: ss, a₁ :: as₁, a₂ :: as₂, ⟨h, hs⟩, h₁, h₂ => by
      refine ⟨fun hw r₁ r₂ e₁ e₂ => ?_, WrittenCorr.frame hs
        (fun r hr => h₁ r (by cases a₁ <;> simp [slotWrites, hr]))
        (fun r hr => h₂ r (by cases a₂ <;> simp [slotWrites, hr]))⟩
      subst e₁ e₂
      rw [h₁ r₁ (by simp [slotWrites, hw]), h₂ r₂ (by simp [slotWrites, hw])]
      exact h hw r₁ r₂ rfl rfl

/-- `Op.run` without stack traffic: read the slots and implicit registers,
run the semantics, write the slots, then the implicit registers. -/
theorem run_eq {o : Op} (hstack : (desc o).stack = .none) (args : List Arg) (core : Core)
    (obs : ByteEval.Flags) :
    o.run args core obs =
      (match readSlots core (desc o).slots args with
      | .error e => .error (.memory e)
      | .ok vals =>
        match (desc o).sem ⟨vals ++ readImplicits core (desc o).implicit, obs⟩ with
        | .error e => .error (.semantic e)
        | .ok out =>
          match writeSlots core core (desc o).slots args out.results with
          | .error e => .error (.memory e)
          | .ok fin => .ok (writeImplicits fin (desc o).implicit out.implicit, out)) := by
  simp only [Op.run, Op.inputs, Op.stage, hstack]
  cases readSlots core (desc o).slots args with
  | error e => rfl
  | ok vals =>
    simp only [bind, Except.bind, pure, Except.pure, Except.mapError]
    cases (desc o).sem ⟨vals ++ readImplicits core (desc o).implicit, obs⟩ with
    | error e => rfl
    | ok out =>
      simp only
      cases writeSlots core core (desc o).slots args out.results <;> rfl

/-- A row with no stack traffic, run on two cores whose arguments correspond,
with each run writing each register at most once: both succeed or neither,
with the same results, memory and written values, and every other register
unchanged. -/
theorem op_run_corr {o : Op} {as₁ as₂ : List Arg} {c₁ c₂ : Core} {obs : ByteEval.Flags}
    {f₁ : Core} {out : SemOut}
    (hstack : (desc o).stack = .none) (hmem : c₁.memory = c₂.memory)
    (hslots : SlotsCorr c₁ c₂ (desc o).slots as₁ as₂)
    (himp : ∀ i ∈ (desc o).implicit, (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg)
    (hw₁ : (rowWrites o as₁).Nodup) (hw₂ : (rowWrites o as₂).Nodup)
    (h : o.run as₁ c₁ obs = .ok (f₁, out)) :
    ∃ f₂, o.run as₂ c₂ obs = .ok (f₂, out) ∧ f₁.memory = f₂.memory ∧
      WrittenCorr f₁ f₂ (desc o).slots as₁ as₂ ∧
      (∀ i ∈ (desc o).implicit, i.role.writes = true → f₁.readReg i.reg = f₂.readReg i.reg) ∧
      (∀ r, r ∉ rowWrites o as₁ → f₁.readReg r = c₁.readReg r) ∧
      (∀ r, r ∉ rowWrites o as₂ → f₂.readReg r = c₂.readReg r) := by
  have hn₁ := List.nodup_append.1 hw₁
  have hn₂ := List.nodup_append.1 hw₂
  rw [run_eq hstack] at h ⊢
  rw [← readSlots_corr hmem hslots, ← readImplicits_corr (fun i hi hr => himp i hi (.inl hr))]
  cases hr : readSlots c₁ (desc o).slots as₁ with
  | error e => simp [hr] at h
  | ok vals =>
    simp only [hr] at h ⊢
    cases hs : (desc o).sem ⟨vals ++ readImplicits c₁ (desc o).implicit, obs⟩ with
    | error e => simp [hs] at h
    | ok out' =>
      simp only [hs] at h ⊢
      cases hw : writeSlots c₁ c₁ (desc o).slots as₁ out'.results with
      | error e => simp [hw] at h
      | ok fin₁ =>
        simp only [hw, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨fin₂, h₂, hm, hwc⟩ := writeSlots_corr hmem hslots.write hn₁.1 hn₂.1 hw
        rw [h₂]
        have hfr₁ := (writeSlots_frame hw).2
        have hfr₂ := (writeSlots_frame h₂).2
        have hsi₁ : ∀ r ∈ slotWrites (desc o).slots as₁, r ∉ implicitWrites (desc o).implicit :=
          fun r hr hi => hn₁.2.2 r hr r hi rfl
        have hsi₂ : ∀ r ∈ slotWrites (desc o).slots as₂, r ∉ implicitWrites (desc o).implicit :=
          fun r hr hi => hn₂.2.2 r hr r hi rfl
        have himpw : ∀ i ∈ (desc o).implicit, i.role.writes = true →
            i.reg ∈ implicitWrites (desc o).implicit := fun i hi hw => by
          simp only [implicitWrites, List.mem_map, List.mem_filter]
          exact ⟨i, ⟨hi, hw⟩, rfl⟩
        refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [writeImplicits_memory, writeImplicits_memory, hm]
        · exact hwc.frame (fun r hr => writeImplicits_frame (hsi₁ r hr))
            (fun r hr => writeImplicits_frame (hsi₂ r hr))
        · refine writeImplicits_corr hn₁.2.1 (fun i hi hwi => ?_)
          by_cases hwide : Wide i.width
          · exact .inl hwide
          · refine .inr ?_
            have hni₁ : i.reg ∉ slotWrites (desc o).slots as₁ := fun hm' =>
              hsi₁ _ hm' (himpw i hi hwi)
            have hni₂ : i.reg ∉ slotWrites (desc o).slots as₂ := fun hm' =>
              hsi₂ _ hm' (himpw i hi hwi)
            rw [hfr₁ _ hni₁, hfr₂ _ hni₂]
            exact himp i hi (.inr ⟨hwi, hwide⟩)
        · intro r hr
          simp only [rowWrites, List.mem_append, not_or] at hr
          rw [writeImplicits_frame hr.2, hfr₁ r hr.1]
        · intro r hr
          simp only [rowWrites, List.mem_append, not_or] at hr
          rw [writeImplicits_frame hr.2, hfr₂ r hr.1]

/-- `op_run_corr` for `Op.exec`: the flags agree too. -/
theorem op_exec_corr {o : Op} {as₁ as₂ : List Arg} {c₁ c₂ : Core} {flags : ByteEval.Flags}
    {f₁ : Core} {flags' : ByteEval.Flags}
    (hstack : (desc o).stack = .none) (hmem : c₁.memory = c₂.memory)
    (hslots : SlotsCorr c₁ c₂ (desc o).slots as₁ as₂)
    (himp : ∀ i ∈ (desc o).implicit, (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg)
    (hw₁ : (rowWrites o as₁).Nodup) (hw₂ : (rowWrites o as₂).Nodup)
    (h : o.exec as₁ c₁ flags = .ok (f₁, flags')) :
    ∃ f₂, o.exec as₂ c₂ flags = .ok (f₂, flags') ∧ f₁.memory = f₂.memory ∧
      WrittenCorr f₁ f₂ (desc o).slots as₁ as₂ ∧
      (∀ i ∈ (desc o).implicit, i.role.writes = true → f₁.readReg i.reg = f₂.readReg i.reg) ∧
      (∀ r, r ∉ rowWrites o as₁ → f₁.readReg r = c₁.readReg r) ∧
      (∀ r, r ∉ rowWrites o as₂ → f₂.readReg r = c₂.readReg r) := by
  simp only [Op.exec, bind, Except.bind] at h ⊢
  cases hr : o.run as₁ c₁ (flags.restrict (desc o).flagsIn) with
  | error e => simp [hr] at h
  | ok res =>
    obtain ⟨fin, out⟩ := res
    simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨f₂, h₂, rest⟩ := op_run_corr hstack hmem hslots himp hw₁ hw₂ hr
    rw [h₂]
    exact ⟨f₂, rfl, rest⟩

end IxCC.Xv.Validate
