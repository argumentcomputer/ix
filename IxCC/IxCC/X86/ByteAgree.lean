import IxCC.X86.ByteEval

/-!
# The byte machine on the process's memory

A compiled object's call is modelled on a memory whose permissions are the
driver's mapping (`Driver.mapped`: the region and the call stack). A process
runs the same instructions on a memory with the same bytes and its own
permissions (its file, the shell's own bytes, the initial stack). Two facts
connect them, for every row of the instruction table (through `Op.exec`'s
`read?`, `write?`, `read64?` and `write64?`) and every control row:

* **Agreement or fault** (`step_agree`, `run_agree`): where the byte machine
  steps on the model's memory, it steps alike on a memory with the same
  registers and bytes and any permissions, or faults there on a memory
  access. The bytes it writes are the same; the permissions are the
  process's own.
* **The frame** (`step_frame`, `run_frame`): a step that succeeds changes no
  permission and no byte its memory does not let it write.

Together: a run the model shows non-faulting is the process's run, or the
process stops on a fault, and it writes nothing outside the model's mapping.
This replaces the ledgers' "a run the model shows non-faulting touches only
modelled memory" with a theorem.
-/

set_option autoImplicit false

namespace IxCC.X86

/-- A memory with other permissions and the same bytes. -/
def Memory.withPerms (m : Memory) (r w : Word → Bool) : Memory := { m with readable := r, writable := w }

/-- A core with other permissions and the same registers and bytes. -/
def Core.withPerms (c : Core) (r w : Word → Bool) : Core := { c with memory := c.memory.withPerms r w }

/-- A byte-machine state with other permissions. -/
def ByteEval.State.withPerms (s : ByteEval.State) (r w : Word → Bool) : ByteEval.State :=
  { s with core := s.core.withPerms r w }

namespace ByteAgree

/-- `e` is `.ok v`, or a memory fault. -/
def OkOr {α : Type} : Except MemoryFault α → α → Prop
  | .ok x, v => x = v
  | .error _, _ => True

/-- `e` is `.ok v`, or a memory fault (an executor's fault). -/
def OkOrE {α : Type} : Except ExecFault α → α → Prop
  | .ok x, v => x = v
  | .error (.memory _), _ => True
  | .error (.semantic _), _ => False

/-- `e` is `.ok v`, or a memory fault (the byte machine's fault). -/
def OkOrF {α : Type} : Except ByteEval.Fault α → α → Prop
  | .ok x, v => x = v
  | .error (.memory _), _ => True
  | .error _, _ => False

/-- A step's frame: the permissions kept, and no byte changed that the memory
does not let it write. -/
structure Frame (c c' : Core) : Prop where
  readable : c'.memory.readable = c.memory.readable
  writable : c'.memory.writable = c.memory.writable
  bytes : ∀ a, c.memory.writable a = false → c'.memory.bytes a = c.memory.bytes a

theorem Frame.refl (c : Core) : Frame c c := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {c₁ c₂ c₃ : Core} (h₁ : Frame c₁ c₂) (h₂ : Frame c₂ c₃) : Frame c₁ c₃ :=
  ⟨h₂.readable.trans h₁.readable, h₂.writable.trans h₁.writable, fun a ha => by
    rw [h₂.bytes a (by rw [h₁.writable]; exact ha), h₁.bytes a ha]⟩

theorem Frame.of_memory {c c' : Core} (h : c'.memory = c.memory) : Frame c c' :=
  ⟨by rw [h], by rw [h], fun _ _ => by rw [h]⟩

/-! ## `Except` -/

theorem bind_ok {ε α β : Type} {e : Except ε α} {k : α → Except ε β} {b : β} (h : (e >>= k) = .ok b) :
    ∃ a, e = .ok a ∧ k a = .ok b := by
  cases e with
  | error x => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {e : Except ε α} {a : α} (h : e.mapError f = .ok a) :
    e = .ok a := by
  cases e with
  | error x => cases h
  | ok x => cases h; rfl

theorem OkOr.bind {α β : Type} {e : Except MemoryFault α} {a : α} {k : α → Except MemoryFault β} {b : β}
    (he : OkOr e a) (hk : OkOr (k a) b) : OkOr (e >>= k) b := by
  cases e with
  | error _ => trivial
  | ok x => cases he; exact hk

theorem OkOrE.bind {α β : Type} {e : Except ExecFault α} {a : α} {k : α → Except ExecFault β} {b : β}
    (he : OkOrE e a) (hk : OkOrE (k a) b) : OkOrE (e >>= k) b := by
  cases e with
  | error f => cases f with
    | memory _ => trivial
    | semantic _ => cases he
  | ok x => cases he; exact hk

theorem OkOr.mapError {α : Type} {e : Except MemoryFault α} {a : α} (h : OkOr e a) :
    OkOrE (e.mapError ExecFault.memory) a := by
  cases e with
  | error _ => trivial
  | ok x => exact h

theorem OkOrF.bind {α β : Type} {e : Except ByteEval.Fault α} {a : α} {k : α → Except ByteEval.Fault β} {b : β}
    (he : OkOrF e a) (hk : OkOrF (k a) b) : OkOrF (e >>= k) b := by
  cases e with
  | error f => cases f <;> first | trivial | cases he
  | ok x => cases he; exact hk

theorem OkOr.mapErrorF {α : Type} {e : Except MemoryFault α} {a : α} (h : OkOr e a) :
    OkOrF (e.mapError ByteEval.Fault.memory) a := by
  cases e with
  | error _ => trivial
  | ok x => exact h

theorem OkOrE.mapErrorF {α : Type} {e : Except ExecFault α} {a : α} (h : OkOrE e a) :
    OkOrF (e.mapError ByteEval.Fault.ofExec) a := by
  cases e with
  | error f => cases f with
    | memory _ => trivial
    | semantic _ => cases h
  | ok x => exact h

variable {R W : Word → Bool}

/-! ## Memory -/

theorem writeLittle_withPerms (m : Memory) (a v : Word) (n : Nat) :
    (m.withPerms R W).writeLittle a v n = (m.writeLittle a v n).withPerms R W := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Memory.writeLittle, ih]; rfl

theorem readLittle_withPerms (m : Memory) (a : Word) (n : Nat) :
    (m.withPerms R W).readLittle a n = m.readLittle a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Memory.readLittle, ih]; rfl

theorem writeLittle_perms (m : Memory) (a v : Word) (n : Nat) :
    (m.writeLittle a v n).readable = m.readable ∧ (m.writeLittle a v n).writable = m.writable := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact ih

theorem writeLittle_out (m : Memory) (a v : Word) {x : Word} (hx : m.writable x = false) :
    ∀ n, Memory.rangeAllowed m.writable a n = true → (m.writeLittle a v n).bytes x = m.bytes x
  | 0, _ => rfl
  | n + 1, hr => by
    simp only [Memory.rangeAllowed, Bool.and_eq_true] at hr
    have hne : x ≠ a + UInt64.ofNat n := fun he => by rw [he] at hx; rw [hx] at hr; exact absurd hr.2 (by simp)
    simp only [Memory.writeLittle, Memory.writeByte, beq_iff_eq, hne, ↓reduceIte]
    exact writeLittle_out m a v hx n hr.1

theorem read?_agree {m : Memory} {w : Width} {a v : Word} (h : m.read? w a = .ok v) :
    OkOr ((m.withPerms R W).read? w a) v := by
  have hv : m.read w a = v := by
    unfold Memory.read? at h
    split at h
    · cases h; rfl
    · cases h
  unfold Memory.read?
  split
  · show (m.withPerms R W).readLittle a w.bytes = v
    rw [readLittle_withPerms]; exact hv
  · trivial

theorem write?_agree {m m' : Memory} {w : Width} {a v : Word} (h : m.write? w a v = .ok m') :
    OkOr ((m.withPerms R W).write? w a v) (m'.withPerms R W) := by
  have hm : m.write w a v = m' := by
    unfold Memory.write? at h
    split at h
    · cases h; rfl
    · cases h
  unfold Memory.write?
  split
  · show (m.withPerms R W).writeLittle a v w.bytes = m'.withPerms R W
    rw [writeLittle_withPerms, ← hm]; rfl
  · trivial

theorem write?_frame {m m' : Memory} {w : Width} {a v : Word} (h : m.write? w a v = .ok m') :
    m'.readable = m.readable ∧ m'.writable = m.writable ∧ ∀ x, m.writable x = false → m'.bytes x = m.bytes x := by
  unfold Memory.write? at h
  split at h
  · rename_i hr
    cases h
    exact ⟨(writeLittle_perms m a v _).1, (writeLittle_perms m a v _).2, fun x hx => writeLittle_out m a v hx _ hr⟩
  · cases h

/-! ## Operands -/

@[simp] theorem withPerms_readReg (c : Core) (r : GPR) : (c.withPerms R W).readReg r = c.readReg r := rfl

theorem withPerms_writeReg (c : Core) (w : Width) (r : GPR) (v : Word) :
    (c.withPerms R W).writeReg w r v = (c.writeReg w r v).withPerms R W := by
  cases w <;> rfl

theorem writeReg_memory (c : Core) (w : Width) (r : GPR) (v : Word) : (c.writeReg w r v).memory = c.memory := by
  cases w <;> rfl

theorem withPerms_setReg (c : Core) (r : GPR) (v : Word) :
    (c.withPerms R W).setReg r v = (c.setReg r v).withPerms R W := rfl

theorem load_agree {c : Core} {w : Width} {arg : Arg} {v : Word} (h : arg.load c w = .ok v) :
    OkOr (arg.load (c.withPerms R W) w) v := by
  cases arg with
  | reg r => cases h; rfl
  | mem ad => exact read?_agree (m := c.memory) h
  | imm x => cases h; rfl

theorem store_agree {before c c' : Core} {w : Width} {v : Word} {arg : Arg}
    (h : arg.store before w v c = .ok c') :
    OkOr (arg.store (before.withPerms R W) w v (c.withPerms R W)) (c'.withPerms R W) := by
  cases arg with
  | reg r => cases h; exact withPerms_writeReg c w r v
  | mem ad =>
    obtain ⟨m', hm, hc⟩ := bind_ok h
    cases hc
    exact OkOr.bind (write?_agree (m := c.memory) hm) rfl
  | imm x => cases h; rfl

theorem store_frame {before c c' : Core} {w : Width} {v : Word} {arg : Arg}
    (h : arg.store before w v c = .ok c') : Frame c c' := by
  cases arg with
  | reg r => cases h; exact Frame.of_memory (writeReg_memory c w r v)
  | mem ad =>
    obtain ⟨m', hm, hc⟩ := bind_ok h
    cases hc
    obtain ⟨hr, hw, hb⟩ := write?_frame hm
    exact ⟨hr, hw, hb⟩
  | imm x => cases h; exact Frame.refl c

theorem readSlots_agree {c : Core} :
    ∀ (slots : List Slot) (args : List Arg) {vs : List Word},
      readSlots c slots args = .ok vs → OkOr (readSlots (c.withPerms R W) slots args) vs
  | [], _, _, h => by cases h; rfl
  | _ :: _, [], _, h => by cases h; rfl
  | slot :: slots, arg :: args, vs, h => by
    unfold readSlots at h ⊢
    cases hr : slot.role <;> simp only [hr] at h ⊢
    · obtain ⟨v, hv, h⟩ := bind_ok h
      obtain ⟨vs', hvs, h⟩ := bind_ok h
      cases h
      exact OkOr.bind (load_agree hv) (OkOr.bind (readSlots_agree slots args hvs) rfl)
    · exact readSlots_agree slots args h
    · obtain ⟨v, hv, h⟩ := bind_ok h
      obtain ⟨vs', hvs, h⟩ := bind_ok h
      cases h
      exact OkOr.bind (load_agree hv) (OkOr.bind (readSlots_agree slots args hvs) rfl)
    · obtain ⟨vs', hvs, h⟩ := bind_ok h
      cases h
      exact OkOr.bind (readSlots_agree slots args hvs) rfl

theorem writeSlots_agree {before : Core} :
    ∀ (c : Core) (slots : List Slot) (args : List Arg) (results : List Word) {c' : Core},
      writeSlots before c slots args results = .ok c' →
      OkOr (writeSlots (before.withPerms R W) (c.withPerms R W) slots args results) (c'.withPerms R W)
  | _, [], _, _, _, h => by cases h; rfl
  | _, _ :: _, [], _, _, h => by cases h; rfl
  | c, slot :: slots, arg :: args, results, c', h => by
    unfold writeSlots at h ⊢
    cases hr : slot.role <;> simp only [hr] at h ⊢
    · exact writeSlots_agree c slots args results h
    · obtain ⟨c₁, h₁, h⟩ := bind_ok h
      exact OkOr.bind (store_agree h₁) (writeSlots_agree c₁ slots args results.tail h)
    · obtain ⟨c₁, h₁, h⟩ := bind_ok h
      exact OkOr.bind (store_agree h₁) (writeSlots_agree c₁ slots args results.tail h)
    · exact writeSlots_agree c slots args results h

theorem writeSlots_frame {before : Core} :
    ∀ (c : Core) (slots : List Slot) (args : List Arg) (results : List Word) {c' : Core},
      writeSlots before c slots args results = .ok c' → Frame c c'
  | c, [], _, _, _, h => by cases h; exact Frame.refl c
  | c, _ :: _, [], _, _, h => by cases h; exact Frame.refl c
  | c, slot :: slots, arg :: args, results, c', h => by
    unfold writeSlots at h
    cases hr : slot.role <;> simp only [hr] at h
    · exact writeSlots_frame c slots args results h
    · obtain ⟨c₁, h₁, h⟩ := bind_ok h
      exact (store_frame h₁).trans (writeSlots_frame c₁ slots args results.tail h)
    · obtain ⟨c₁, h₁, h⟩ := bind_ok h
      exact (store_frame h₁).trans (writeSlots_frame c₁ slots args results.tail h)
    · exact writeSlots_frame c slots args results h

theorem writeImplicits_withPerms :
    ∀ (c : Core) (is : List Implicit) (rs : List Word),
      writeImplicits (c.withPerms R W) is rs = (writeImplicits c is rs).withPerms R W
  | c, [], rs => by simp only [writeImplicits_nil]
  | c, i :: is, rs => by
    unfold writeImplicits
    split
    · rw [withPerms_writeReg]; exact writeImplicits_withPerms _ is rs.tail
    · exact writeImplicits_withPerms c is rs

theorem writeImplicits_memory :
    ∀ (c : Core) (is : List Implicit) (rs : List Word), (writeImplicits c is rs).memory = c.memory
  | c, [], rs => by simp only [writeImplicits_nil]
  | c, i :: is, rs => by
    unfold writeImplicits
    split
    · rw [writeImplicits_memory _ is rs.tail, writeReg_memory]
    · exact writeImplicits_memory c is rs

theorem readImplicits_withPerms (c : Core) (is : List Implicit) :
    readImplicits (c.withPerms R W) is = readImplicits c is := rfl

/-! ## Rows -/

theorem inputs_agree {o : Op} {args : List Arg} {c : Core} {vs : List Word} (h : o.inputs args c = .ok vs) :
    OkOr (o.inputs args (c.withPerms R W)) vs := by
  unfold Op.inputs at h ⊢
  obtain ⟨v₁, h₁, h⟩ := bind_ok h
  refine OkOr.bind (readSlots_agree _ _ h₁) ?_
  rw [readImplicits_withPerms]
  cases hs : (desc o).stack <;> simp only [hs] at h ⊢
  · cases h; rfl
  · cases h; rfl
  · obtain ⟨v, hv, h⟩ := bind_ok h
    cases h
    exact OkOr.bind (read?_agree (m := c.memory) hv) rfl

theorem stage_agree {o : Op} {c c' : Core} {out : SemOut} (h : o.stage c out = .ok c') :
    OkOr (o.stage (c.withPerms R W) out) (c'.withPerms R W) := by
  unfold Op.stage at h ⊢
  cases hs : (desc o).stack <;> simp only [hs] at h ⊢
  · cases h; rfl
  · obtain ⟨m, hm, h⟩ := bind_ok h
    cases h
    exact OkOr.bind (write?_agree (m := c.memory) hm) rfl
  · cases h; rfl

theorem stage_frame {o : Op} {c c' : Core} {out : SemOut} (h : o.stage c out = .ok c') : Frame c c' := by
  unfold Op.stage at h
  cases hs : (desc o).stack <;> simp only [hs] at h
  · cases h; exact Frame.refl c
  · obtain ⟨m, hm, h⟩ := bind_ok h
    cases h
    obtain ⟨hr, hw, hb⟩ := write?_frame hm
    exact ⟨hr, hw, hb⟩
  · cases h; exact Frame.of_memory rfl

theorem opRun_agree {o : Op} {args : List Arg} {c c' : Core} {obs : ByteEval.Flags} {out : SemOut}
    (h : o.run args c obs = .ok (c', out)) :
    OkOrE (o.run args (c.withPerms R W) obs) (c'.withPerms R W, out) := by
  unfold Op.run at h ⊢
  obtain ⟨ins, hi, h⟩ := bind_ok h
  obtain ⟨out', ho, h⟩ := bind_ok h
  obtain ⟨st, hs, h⟩ := bind_ok h
  obtain ⟨fin, hf, h⟩ := bind_ok h
  cases h
  refine OkOrE.bind (OkOr.mapError (inputs_agree (mapError_ok hi))) ?_
  rw [ho]
  refine OkOrE.bind (a := out) rfl ?_
  refine OkOrE.bind (OkOr.mapError (stage_agree (mapError_ok hs))) ?_
  refine OkOrE.bind (OkOr.mapError (writeSlots_agree _ _ _ _ (mapError_ok hf))) ?_
  show (writeImplicits (fin.withPerms R W) (desc o).implicit out.implicit, out) = _
  rw [writeImplicits_withPerms]

theorem opRun_frame {o : Op} {args : List Arg} {c c' : Core} {obs : ByteEval.Flags} {out : SemOut}
    (h : o.run args c obs = .ok (c', out)) : Frame c c' := by
  unfold Op.run at h
  obtain ⟨ins, hi, h⟩ := bind_ok h
  obtain ⟨out', ho, h⟩ := bind_ok h
  obtain ⟨st, hs, h⟩ := bind_ok h
  obtain ⟨fin, hf, h⟩ := bind_ok h
  cases h
  exact ((stage_frame (mapError_ok hs)).trans (writeSlots_frame _ _ _ _ (mapError_ok hf))).trans
    (Frame.of_memory (writeImplicits_memory _ _ _))

theorem exec_agree {o : Op} {args : List Arg} {c c' : Core} {f f' : ByteEval.Flags}
    (h : o.exec args c f = .ok (c', f')) :
    OkOrE (o.exec args (c.withPerms R W) f) (c'.withPerms R W, f') := by
  unfold Op.exec at h ⊢
  obtain ⟨⟨fin, out⟩, hr, h⟩ := bind_ok h
  cases h
  exact OkOrE.bind (opRun_agree hr) rfl

theorem exec_frame {o : Op} {args : List Arg} {c c' : Core} {f f' : ByteEval.Flags}
    (h : o.exec args c f = .ok (c', f')) : Frame c c' := by
  unfold Op.exec at h
  obtain ⟨⟨fin, out⟩, hr, h⟩ := bind_ok h
  cases h
  exact opRun_frame hr

/-! ## The byte machine -/

theorem execute_agree {d : Decode.Decoded} {s s' : ByteEval.State} (h : ByteEval.execute d s = .ok s') :
    OkOrF (ByteEval.execute d (s.withPerms R W)) (s'.withPerms R W) := by
  obtain ⟨⟨o, args⟩, len⟩ := d
  revert h
  unfold ByteEval.execute
  dsimp only
  split
  · intro h
    obtain ⟨m, hm, h⟩ := bind_ok h
    cases h
    exact OkOrF.bind (OkOr.mapErrorF (write?_agree (m := s.core.memory) (mapError_ok hm))) rfl
  · intro h
    cases h
    exact rfl
  · intro h
    obtain ⟨out, ho, h⟩ := bind_ok h
    cases h
    refine OkOrF.bind (a := out) ?_ rfl
    rw [show (s.withPerms R W).flags = s.flags from rfl, ho]
    exact rfl
  · intro h
    obtain ⟨t, ht, h⟩ := bind_ok h
    cases h
    exact OkOrF.bind (OkOr.mapErrorF (read?_agree (m := s.core.memory) (mapError_ok ht))) rfl
  · intro h
    obtain ⟨⟨c, f⟩, he, h⟩ := bind_ok h
    cases h
    exact OkOrF.bind (OkOrE.mapErrorF (exec_agree (mapError_ok he))) rfl

theorem execute_frame {d : Decode.Decoded} {s s' : ByteEval.State} (h : ByteEval.execute d s = .ok s') :
    Frame s.core s'.core := by
  obtain ⟨⟨o, args⟩, len⟩ := d
  revert h
  unfold ByteEval.execute
  dsimp only
  split
  · intro h
    obtain ⟨m, hm, h⟩ := bind_ok h
    cases h
    obtain ⟨hr, hw, hb⟩ := write?_frame (mapError_ok hm)
    exact ⟨hr, hw, hb⟩
  · intro h
    cases h
    exact Frame.refl _
  · intro h
    obtain ⟨out, ho, h⟩ := bind_ok h
    cases h
    exact Frame.refl _
  · intro h
    obtain ⟨t, ht, h⟩ := bind_ok h
    cases h
    exact Frame.of_memory rfl
  · intro h
    obtain ⟨⟨c, f⟩, he, h⟩ := bind_ok h
    cases h
    exact exec_frame (mapError_ok he)

/-- **Agreement or fault, one step.** -/
theorem step_agree {text : ByteArray} {base : Word} {s s' : ByteEval.State}
    (h : ByteEval.step text base s = .ok s') :
    OkOrF (ByteEval.step text base (s.withPerms R W)) (s'.withPerms R W) := by
  unfold ByteEval.step at h ⊢
  rw [show (s.withPerms R W).rip = s.rip from rfl]
  cases hd : Decode.decodeAt text (s.rip - base).toNat with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; exact execute_agree h

/-- **The frame, one step.** -/
theorem step_frame {text : ByteArray} {base : Word} {s s' : ByteEval.State}
    (h : ByteEval.step text base s = .ok s') : Frame s.core s'.core := by
  unfold ByteEval.step at h
  cases hd : Decode.decodeAt text (s.rip - base).toNat with
  | none => rw [hd] at h; cases h
  | some d => rw [hd] at h; exact execute_frame h

/-- **Agreement or fault, a run.** -/
theorem run_agree {text : ByteArray} {base : Word} :
    ∀ (n : Nat) {s s' : ByteEval.State}, ByteEval.run text base n s = .ok s' →
      OkOrF (ByteEval.run text base n (s.withPerms R W)) (s'.withPerms R W)
  | 0, s, s', h => by cases h; exact rfl
  | n + 1, s, s', h => by
    obtain ⟨s₁, h₁, h⟩ := bind_ok h
    exact OkOrF.bind (step_agree h₁) (run_agree n h)

/-- **The frame, a run.** -/
theorem run_frame {text : ByteArray} {base : Word} :
    ∀ (n : Nat) {s s' : ByteEval.State}, ByteEval.run text base n s = .ok s' → Frame s.core s'.core
  | 0, s, s', h => by cases h; exact Frame.refl _
  | n + 1, s, s', h => by
    obtain ⟨s₁, h₁, h⟩ := bind_ok h
    exact (step_frame h₁).trans (run_frame n h)

/-- What `OkOrF` says: the value, or a memory fault. -/
theorem OkOrF.cases {α : Type} {e : Except ByteEval.Fault α} {a : α} (h : OkOrF e a) :
    e = .ok a ∨ ∃ f, e = .error (.memory f) := by
  cases e with
  | ok x => exact .inl (congrArg _ h)
  | error f => cases f <;> first | exact .inr ⟨_, rfl⟩ | cases h

end ByteAgree

/-- **Agreement or fault** (`ByteAgree.step_agree`, stated on two memories):
where the byte machine steps on memory `m₁`, it steps alike on a memory `m₂`
with the same bytes and any permissions, or faults there on a memory access;
the bytes it writes are the same and `m₂` keeps its permissions. -/
theorem ByteEval.step_agree {text : ByteArray} {base : Word} {regs : Registers} {m₁ m₂ : Memory}
    {rip : Word} {flags : ByteEval.Flags} {s₁ : ByteEval.State} (hb : m₁.bytes = m₂.bytes)
    (h : ByteEval.step text base ⟨⟨regs, m₁⟩, rip, flags⟩ = .ok s₁) :
    (∃ fault, ByteEval.step text base ⟨⟨regs, m₂⟩, rip, flags⟩ = .error (.memory fault)) ∨
    ByteEval.step text base ⟨⟨regs, m₂⟩, rip, flags⟩ = .ok (s₁.withPerms m₂.readable m₂.writable) := by
  have he : (⟨⟨regs, m₂⟩, rip, flags⟩ : ByteEval.State) =
      (⟨⟨regs, m₁⟩, rip, flags⟩ : ByteEval.State).withPerms m₂.readable m₂.writable := by
    obtain ⟨b₂, r₂, w₂⟩ := m₂
    cases hb
    rfl
  rw [he]
  exact (ByteAgree.OkOrF.cases (ByteAgree.step_agree h)).symm

end IxCC.X86
