import IxCC.X86.Exe.Machine.Proof.Paths
import IxCC.Exe.Machine.Sound

/-!
# The shell's loop (X0-P, third part)

`from_loop`: from a state at the machine shell's `loop` block standing for a
session configuration (`AtLoop`), every trace of the process is a prefix of the
system calls of a trace the session model performs from that configuration, or
has passed those of a trace reaching a call the model shows stuck.

`AtLoop` says where the shell keeps the configuration: the state and the event
in its own words at `C` and `C + 8`, the argument cursor at `C + 16` and
`C + 24` over the argument block (`Cursor`), which lies outside the
zero-filled segments, and the file's bytes. Nothing is said of the registers,
the flags, the region or the call stack.

The proof is by strong induction on the steps of the trace (`TraceN`). One
iteration: the loop head (`head`), the two calls (`iteration_calls_at`, on the
session model's call at the configuration), then by the call's outcome:

- a timeout: the process runs more steps than the trace has;
- stuck: the trace is past a call the model shows stuck;
- a resource failure or a trap of either call: the status test, the failure
  dispatch and the report (`returned_fail`);
- a value: `decode` (an even word is not a `Nat`: the `notValue` report),
  `split`, the request's kind, then `arg` (the cursor's three cases), a
  one-byte write, the program's exit, or a request outside the interface
  (the `request` report); `arg` and the write go back to `loop` standing for
  the configuration the model reaches, and the induction hypothesis applies.

What an iteration keeps of memory (`Kept`): every call leaves the bytes
outside its mapping as they were (`Returned.frame`), and every store of the
shell lies inside the zero-filled segments, so the argument block and the
file are never written; the cursor's words change only in `arg`.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Sem (Result Obs Lang)
open IxCC.Exe.Machine (Event Config Performs Reaches Last objCallAtOf nextArg Request)
open SB

/-- The argument cursor `(slot, ptr)` stands for what is left of the block,
every word and byte of which lies where `apart` says: a null slot for no
argument left; a nonzero slot `p` with byte pointer `p + j` for `drop j a`
followed by what the next slot stands for. -/
inductive Cursor (m : Memory) (apart : Word → Prop) : Word → Word → List (List Nat) → Prop
  | done {slot ptr : Word} (h : m.read64 slot = 0) (hs : ∀ b < 8, apart (slot + UInt64.ofNat b)) :
      Cursor m apart slot ptr []
  | arg {slot : Word} {a : List Nat} {j : Nat} {more : List (List Nat)} (hp : m.read64 slot ≠ 0)
      (hs : ∀ b < 8, apart (slot + UInt64.ofNat b))
      (hj : j ≤ a.length)
      (hbytes : ∀ i < a.length, m.bytes (m.read64 slot + UInt64.ofNat i) = UInt8.ofNat a[i]!)
      (hnul : m.bytes (m.read64 slot + UInt64.ofNat a.length) = 0)
      (ha : ∀ i ≤ a.length, apart (m.read64 slot + UInt64.ofNat i))
      (hnext : Cursor m apart (slot + 8) (m.read64 (slot + 8)) more) :
      Cursor m apart slot (m.read64 slot + UInt64.ofNat j) (a.drop j :: more)

/-- **The shell at `loop`** stands for the session configuration `cfg`: the
state and the event in its own bytes at `C = callTop`, the cursor at `C + 16`
and `C + 24` over the argument block, which lies outside the zero-filled
segments, the file's bytes unchanged. Nothing is said of the registers, the
flags, the region or the call stack. -/
def AtLoop (L : Machine.Layout) {f : Frame} {object : ByteArray} (c : Checked f object) (loopAddr : Word)
    (cfg : Config) (s : ByteEval.State) : Prop :=
  let C : Word := UInt64.ofNat L.callTop
  s.rip = loopAddr ∧
  cfg.state < 2 ^ 64 ∧ s.core.memory.read64 C = UInt64.ofNat cfg.state ∧
  cfg.event < 2 ^ 64 ∧ s.core.memory.read64 (C + 8) = UInt64.ofNat cfg.event ∧
  (∀ a ∈ cfg.args, ∀ b ∈ a, 0 < b ∧ b < 256) ∧
  Cursor s.core.memory (OutsideSegments L.segments) (s.core.memory.read64 (C + 16)) (s.core.memory.read64 (C + 24))
    cfg.args ∧
  (∀ i < c.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = c.bytes[i]!)

/-- The loop's address in a machine executable. -/
def loopAddr (L : Machine.Layout) (step : String) {object : ByteArray} (c : Checked (Machine.frame L step) object) : Word :=
  UInt64.ofNat (shellAddr L step c Machine.B.loop 0)

/-- What `from_loop` concludes of a trace `σ` from a state standing for `cfg`. -/
def LoopGoal (call : SessionCall) (cfg : Config) (σ : List Sys) : Prop :=
  (∃ t ρ, Performs call cfg t ∧ DenotesAll t ρ ∧ σ <+: ρ) ∨
  (∃ t₀ c' ρ₀, Reaches call cfg t₀ c' ∧ call c'.state c'.event .stuck ∧ DenotesAll t₀ ρ₀ ∧ ρ₀ <+: σ)

section
variable {call : SessionCall} {cfg : Config}

theorem LoopGoal.nil : LoopGoal call cfg [] := .inl ⟨[], [], .inl ⟨cfg, .refl cfg⟩, .nil, List.nil_prefix⟩

theorem LoopGoal.stuck (h : call cfg.state cfg.event .stuck) {σ : List Sys} : LoopGoal call cfg σ :=
  .inr ⟨[], cfg, [], .refl cfg, h, .nil, List.nil_prefix⟩

theorem LoopGoal.last {ev : Event} {ρ σ : List Sys} (h : Last call cfg ev) (hd : Denotes ev ρ) (hp : σ <+: ρ) :
    LoopGoal call cfg σ := by
  have hd' := DenotesAll.cons hd .nil
  rw [List.append_nil] at hd'
  exact .inl ⟨[ev], ρ, Performs.last h, hd', hp⟩

theorem LoopGoal.fail {st : Nat} {σ : List Sys} (h : ∀ b, Last call cfg (.fail st b))
    (hr : ∃ b ρ, Report st (messageOf st) b ρ ∧ σ <+: ρ) : LoopGoal call cfg σ := by
  obtain ⟨b, ρ, hρ, hp⟩ := hr
  exact LoopGoal.last (h b) (.fail hρ) hp

theorem LoopGoal.arg {w : Nat} {σ : List Sys} (hc : call cfg.state cfg.event (.ok (some (.nat w))))
    (hq : Request.decode (IxCC.Exe.Machine.split w).2 = some .arg)
    (h : LoopGoal call ⟨(IxCC.Exe.Machine.split w).1, (nextArg cfg.args).1, (nextArg cfg.args).2⟩ σ) :
    LoopGoal call cfg σ := by
  rcases h with ⟨t, ρ, hp, hd, hpre⟩ | ⟨t₀, c', ρ₀, hr, hs, hd, hpre⟩
  · exact .inl ⟨_, ρ, Performs.cons (fun _ _ hr => .arg hc hq hr) hp, .cons (.arg _) hd, hpre⟩
  · exact .inr ⟨_, c', ρ₀, .arg hc hq hr, hs, .cons (.arg _) hd, hpre⟩

theorem LoopGoal.write {w fd b : Nat} {ok : Bool} {r : Word} {σ : List Sys}
    (hc : call cfg.state cfg.event (.ok (some (.nat w))))
    (hq : Request.decode (IxCC.Exe.Machine.split w).2 = some (.write fd b)) (hr : r = 1 ↔ ok = true)
    (h : LoopGoal call ⟨(IxCC.Exe.Machine.split w).1,
      if ok then IxCC.Exe.Machine.written else IxCC.Exe.Machine.notWritten, cfg.args⟩ σ) :
    LoopGoal call cfg (.write (UInt64.ofNat fd) [UInt8.ofNat b] r :: σ) := by
  rcases h with ⟨t, ρ, hp, hd, hpre⟩ | ⟨t₀, c', ρ₀, hrr, hs, hd, hpre⟩
  · exact .inl ⟨_, _, Performs.cons (fun _ _ hr' => .write (ok := ok) hc hq hr') hp, .cons (.write hr) hd,
      (List.prefix_cons_inj _).mpr hpre⟩
  · exact .inr ⟨_, c', _, .write (ok := ok) hc hq hrr, hs, .cons (.write hr) hd, (List.prefix_cons_inj _).mpr hpre⟩

end

/-! ## The cursor -/

theorem Cursor.slot_apart {m : Memory} {apart : Word → Prop} {slot ptr : Word} {args : List (List Nat)}
    (h : Cursor m apart slot ptr args) : ∀ b < 8, apart (slot + UInt64.ofNat b) := by
  cases h with
  | done _ hs => exact hs
  | arg _ hs _ _ _ _ _ => exact hs

/-- A cursor reads only the bytes `apart` allows: another memory that agrees with it there carries it. -/
theorem Cursor.congr {m m' : Memory} {apart : Word → Prop} (hm : ∀ a, apart a → m'.bytes a = m.bytes a)
    {slot ptr : Word} {args : List (List Nat)} (h : Cursor m apart slot ptr args) : Cursor m' apart slot ptr args := by
  induction h with
  | done h hs => exact .done (by rw [read64_congr hm hs]; exact h) hs
  | @arg slot a j more hp hs hj hbytes hnul ha hnext ih =>
    have e : m'.read64 slot = m.read64 slot := read64_congr hm hs
    have e2 : m'.read64 (slot + 8) = m.read64 (slot + 8) := read64_congr hm (Cursor.slot_apart hnext)
    rw [← e2] at ih
    have h' := Cursor.arg (m := m') (apart := apart) (slot := slot) (a := a) (j := j) (more := more)
      (by rw [e]; exact hp) hs hj (fun i hi => by rw [e, hm _ (ha i (Nat.le_of_lt hi))]; exact hbytes i hi)
      (by rw [e, hm _ (ha _ (Nat.le_refl _))]; exact hnul) (fun i hi => by rw [e]; exact ha i hi) ih
    rw [e] at h'
    exact h'

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)
include ce

/-- The file's bytes lie outside the zero-filled segments. -/
theorem file_outside {i : Nat} (hi : i < ce.checked.bytes.size) : OutsideSegments L.segments (UInt64.ofNat (fileBase + i)) := by
  have ff := Machine.fileFacts ce.checked
  have hsz := ff.size
  have hbl := ff.below
  have hfit := file_fit ce
  obtain ⟨-, -, -, h4, -, -, -, -, -, hd⟩ := numbers ce
  intro seg hseg
  simp only [Machine.Layout.segments, List.mem_cons, List.mem_nil_iff, or_false] at hseg
  rw [toNat_small (by omega)]
  rcases hseg with rfl | rfl
  · left; show fileBase + i < dataBase; omega
  · left; show fileBase + i < L.regionStart; omega

/-- The shell's words at `C` and `C + 8` after an iteration's store at `region + 16`. -/
theorem region_store_read (m : Memory) (v : Word) {k : Nat} (hk : k ≤ 248) :
    (m.write .w64 (UInt64.ofNat L.regionStart + UInt64.ofNat 16) v).read64 (cTop L + UInt64.ofNat k) =
      m.read64 (cTop L + UInt64.ofNat k) :=
  write_read64_apart (fun i hi j hj e => by
    have hj' : j < 8 := hj
    obtain ⟨-, h2, -, h4, -, -, -, -, -, hd⟩ := numbers ce
    have := congrArg UInt64.toNat e
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega), UInt64.add_assoc, ← UInt64.ofNat_add,
      region_add ce _ (by omega)] at this
    omega)

/-- **What an iteration keeps, across its two calls**: the bytes the iteration keeps are as they
were before the loop head stored the budget. -/
theorem kept_calls {s s₀ s' : ByteEval.State}
    (hmem0 : s₀.core.memory = s.core.memory.write .w64 (UInt64.ofNat L.regionStart + UInt64.ofNat 16)
      (UInt64.ofNat L.budget))
    (hinit : s₀.core.memory.bytes = (initDriverOf L ce s₀).initBytes) {D : Driver}
    (hD : D.mapped = (initDriverOf L ce s₀).mapped) {code : Word}
    (hret : Returned D (initDriverOf L ce s₀).initBytes code s') : Kept L s s'.core.memory := fun a ha => by
  rw [hret.frame a (by rw [hD]; exact kept_unmapped ce s₀ ha), ← hinit, hmem0]
  exact write_bytes_apart (fun j hj e => store_region ce j hj (e ▸ ha))

/-- **A failure after a return**: from a call's return with status `k + 1` (`k < 4`), through
the status test and the failure dispatch, every trace is a prefix of the failure's report. -/
theorem fail_report {b j b' : Nat} (hb : b < 46) (hb' : b' < 46)
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (mI .r11 L.callTop))
    (hsz : (blockAt (shellOf ce.checked) b).instructions.size = j + 1)
    (ht : (blockAt (shellOf ce.checked) b).terminator = cmpR .rsp .r11 .ne 42 b')
    (hblk : blockAt (shellOf ce.checked) b' = ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 (b' + 1)⟩)
    {s : ByteEval.State} (hrip : s.rip = addr ce b j) (hrsp : s.core.readReg .rsp = cTop L)
    {k : Nat} (hk : k < 4) (hax : s.core.readReg .rax = UInt64.ofNat (k + 1)) {f : Machine.Failure}
    (hf : Machine.B.message f = 38 + k)
    (hfile : ∀ i < ce.checked.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!)
    {n : Nat} {σ : List Sys} (htr : TraceN ce.checked.bytes n s σ) :
    ∃ b ρ, Report f.status (messageOf f.status) b ρ ∧ σ <+: ρ := by
  obtain ⟨fl1, e1⟩ := back ce hb hb' hi hsz ht hblk hrip hrsp
  let core1 := ((s.core.setReg .r11 (cTop L)).setReg .r11 (UInt64.ofNat L.shellTop)).setReg .rsp (UInt64.ofNat L.shellTop)
  have hax1 : core1.readReg .rax = UInt64.ofNat (k + 1) := hax
  have hne : core1.readReg .rax ≠ 0 := by
    rw [hax1]
    intro h
    have := congrArg UInt64.toNat h
    rw [toNat_small (by omega)] at this
    exact absurd this (by simp)
  obtain ⟨fl2, e2⟩ := back_nonzero ce hb' hblk (core := core1) (fl := fl1) hne
  obtain ⟨m3, fl3, e3⟩ := fail_dispatch ce (core := core1) (fl := fl2) k hk hax1
  rcases TraceN.through (run_comp e1 (run_comp e2 e3)) htr with rfl | ⟨-, ht'⟩
  · exact report_nil _ _
  · exact report ce f (s := ⟨core1, addr ce (38 + k) 0, fl3⟩) (by rw [hf]) hfile ht'

/-- **A failure after either call returns**: `cx_init`'s return (after `loop`) or the step's
(after `callStep`) with status `k + 1`, then the failure's report. -/
theorem returned_fail {s₀ s' : ByteEval.State} {code : Word}
    (hret : Returned (initDriverOf L ce s₀) (initDriverOf L ce s₀).initBytes code s' ∨
      Returned ((initDriverOf L ce s₀).withSite (stepSite L ce s₀)) (initDriverOf L ce s₀).initBytes code s')
    {k : Nat} (hk : k < 4) (hcode : code = UInt64.ofNat (k + 1)) {f : Machine.Failure}
    (hf : Machine.B.message f = 38 + k) {s : ByteEval.State}
    (hmem0 : s₀.core.memory = s.core.memory.write .w64 (UInt64.ofNat L.regionStart + UInt64.ofNat 16)
      (UInt64.ofNat L.budget))
    (hinit : s₀.core.memory.bytes = (initDriverOf L ce s₀).initBytes)
    (hfile : ∀ i < ce.checked.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!)
    {n : Nat} {σ : List Sys} (htr : TraceN ce.checked.bytes n s' σ) :
    ∃ b ρ, Report f.status (messageOf f.status) b ρ ∧ σ <+: ρ := by
  have hC := sp_add8 ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes
  rcases hret with hr | hr
  · have hkept := kept_calls ce hmem0 hinit rfl hr
    exact fail_report ce (b := 6) (j := 12) (b' := 7) (by decide) (by decide) (by rw [block_loop] <;> rfl)
      (by rw [block_loop] <;> rfl) (by rw [block_loop] <;> rfl) (block_initBack L step _) hr.rip (hr.rsp.trans hC) hk
      (hr.rax.trans hcode) hf (fun i hi => (hkept _ (.inl (file_outside ce hi))).trans (hfile i hi)) htr
  · have hkept := kept_calls ce (D := (initDriverOf L ce s₀).withSite (stepSite L ce s₀)) hmem0 hinit
      (Driver.withSite_mapped _ _) hr
    exact fail_report ce (b := 8) (j := 10) (b' := 9) (by decide) (by decide) (by rw [block_callStep] <;> rfl)
      (by rw [block_callStep] <;> rfl) (by rw [block_callStep] <;> rfl) (block_stepBack L step _) hr.rip (hr.rsp.trans hC)
      hk (hr.rax.trans hcode) hf (fun i hi => (hkept _ (.inl (file_outside ce hi))).trans (hfile i hi)) htr

/-- The model's calls of `from_loop`. -/
abbrev loopCall (object : ByteArray) (roots : List Linked.Root) (textSize : Nat) : SessionCall :=
  objCallAtOf (linkedOf object roots) textSize

/-- The induction hypothesis of `from_loop`: every trace of fewer than `n₀` steps from a state at `loop`. -/
def LoopIH (roots : List Linked.Root) (n₀ : Nat) : Prop :=
  ∀ m < n₀, ∀ {cfg : Config} {s : ByteEval.State} {σ : List Sys}, AtLoop L ce.checked (loopAddr L step ce.checked) cfg s →
    TraceN ce.checked.bytes m s σ → LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ

theorem atLoop_parts {cfg : Config} {s : ByteEval.State} (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) :
    s.rip = addr ce 6 0 ∧ cfg.state < 2 ^ 64 ∧ s.core.memory.read64 (cTop L) = UInt64.ofNat cfg.state ∧
    cfg.event < 2 ^ 64 ∧ s.core.memory.read64 (cTop L + UInt64.ofNat 8) = UInt64.ofNat cfg.event ∧
    (∀ a ∈ cfg.args, ∀ b ∈ a, 0 < b ∧ b < 256) ∧
    Cursor s.core.memory (OutsideSegments L.segments) (s.core.memory.read64 (cTop L + UInt64.ofNat 16))
      (s.core.memory.read64 (cTop L + UInt64.ofNat 24)) cfg.args ∧
    (∀ i < ce.checked.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!) := hat

/-- **Back at `loop`**: the configuration a state stands for, from the iteration's start. -/
theorem atLoop_next {cfg : Config} {s : ByteEval.State} (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s)
    {e : ByteEval.State} (hrip : e.rip = addr ce 6 0)
    (hout : ∀ a, OutsideSegments L.segments a → e.core.memory.bytes a = s.core.memory.bytes a)
    {cfg' : Config} (hst : cfg'.state < 2 ^ 64) (hsv : e.core.memory.read64 (cTop L) = UInt64.ofNat cfg'.state)
    (hev : cfg'.event < 2 ^ 64) (hevv : e.core.memory.read64 (cTop L + UInt64.ofNat 8) = UInt64.ofNat cfg'.event)
    (hargs : ∀ a ∈ cfg'.args, ∀ b ∈ a, 0 < b ∧ b < 256)
    (hcur : Cursor s.core.memory (OutsideSegments L.segments) (e.core.memory.read64 (cTop L + UInt64.ofNat 16))
      (e.core.memory.read64 (cTop L + UInt64.ofNat 24)) cfg'.args) :
    AtLoop L ce.checked (loopAddr L step ce.checked) cfg' e :=
  ⟨hrip, hst, hsv, hev, hevv, hargs, Cursor.congr hout hcur,
    fun i hi => (hout _ (file_outside ce hi)).trans ((atLoop_parts ce hat).2.2.2.2.2.2.2 i hi)⟩

theorem cword0_apart {m : Memory} {w : Width} {k' : Nat} (hk' : 8 ≤ k') (hk2 : k' + w.bytes ≤ 256) (v : Word) :
    (m.write w (cTop L + UInt64.ofNat k') v).read64 (cTop L) = m.read64 (cTop L) := by
  have h := cword_apart ce (m := m) (w := w) (k := 0) (k' := k') (by decide) hk2 (.inl hk') v
  rwa [add_zero'] at h

/-- A store to the cursor's words leaves every byte outside the segments. -/
theorem cursor_store_out {m : Memory} {k : Nat} (hk1 : 16 ≤ k) (hk2 : k ≤ 24) (v : Word) {a : Word}
    (ha : OutsideSegments L.segments a) : (m.write .w64 (cTop L + UInt64.ofNat k) v).bytes a = m.bytes a :=
  write_bytes_apart (fun j hj e => by
    have hj' : j < 8 := hj
    obtain ⟨h1, h2, -, -, -, -, -, -, -, hd⟩ := numbers ce
    have hn : (cTop L + UInt64.ofNat k + UInt64.ofNat j).toNat = L.callTop + k + j := by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add, cTop_add ce _ (by omega)]; omega
    exact inside_stack (L := L) (by rw [e, hn]; omega) (by rw [e, hn]; omega) ha)

/-- `exit`, as the model's last event. -/
theorem value_exit {roots : List Linked.Root} {cfg : Config} {N : Nat}
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event (.ok (some (.nat N))))
    (hk : N % 2048 % 8 = 3) {core : Core} {fl : ByteEval.Flags} (hpay : (core.readReg .rax).toNat = N % 2048 / 8)
    {n : Nat} {σ : List Sys} (htr : TraceN ce.checked.bytes n ⟨core, addr ce 26 0, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  have hq : Request.decode (IxCC.Exe.Machine.split N).2 = some (.exit (N % 2048 / 8)) := by
    show Request.decode (N % 2048) = _
    simp only [Request.decode, hk]
  have hrax : core.readReg .rax = UInt64.ofNat (N % 2048 / 8) :=
    UInt64.toNat_inj.mp (by rw [hpay, toNat_small (by omega)])
  have h := exitCode_path ce core fl htr
  rw [hrax] at h
  exact LoopGoal.last (Last.exit hc hq) (.exit _) h

/-- A request outside the interface, as the model's last event. -/
theorem value_request {roots : List Linked.Root} {cfg : Config} {N : Nat}
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event (.ok (some (.nat N))))
    (hq : Request.decode (IxCC.Exe.Machine.split N).2 = none) {core : Core} {fl : ByteEval.Flags}
    (hfile : ∀ i < ce.checked.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!)
    {n : Nat} {σ : List Sys} (htr : TraceN ce.checked.bytes n ⟨core, addr ce 44 0, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ :=
  LoopGoal.fail (fun _ => Last.request hc hq) (report ce .request (s := ⟨core, addr ce 44 0, fl⟩) rfl hfile htr)

/-- **A one-byte write**, then the loop from the configuration the model reaches. -/
theorem value_write {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event (.ok (some (.nat N))))
    (fd : Nat) (hfd : fd = 1 ∨ fd = 2) (hk : N % 2048 % 8 = fd) {core : Core} {fl : ByteEval.Flags}
    (hpay : (core.readReg .rax).toNat = N % 2048 / 8) (hkept : Kept L s core.memory)
    (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce (20 + fd) 0, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  obtain ⟨-, -, -, -, -, hargs, hcur, -⟩ := atLoop_parts ce hat
  have hq : Request.decode (IxCC.Exe.Machine.split N).2 = some (.write fd (N % 2048 / 8)) := by
    show Request.decode (N % 2048) = _
    rcases hfd with rfl | rfl <;> simp only [Request.decode, hk]
  rcases write_path ce fd hfd core fl htr with rfl | ⟨r, σ', rfl, hrest⟩
  · exact LoopGoal.nil
  rw [hpay]
  refine LoopGoal.write (ok := decide (r.toNat = 1)) hc hq ?_ ?_
  · rw [decide_eq_true_iff]
    exact ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.mp h⟩
  rcases hrest with rfl | ⟨s', n', hn', ht', hrip', hmem'⟩
  · exact LoopGoal.nil
  have hk2 : Kept L s s'.core.memory := by
    rw [hmem']
    exact (hkept.write (store_out ce)).write (store_low ce 8 (by decide))
  apply ih n' (by omega) _ ht'
  have hans : UInt64.ofNat (if r.toNat = 1 then 0 else 1) =
      UInt64.ofNat (if decide (r.toNat = 1) = true then IxCC.Exe.Machine.written else IxCC.Exe.Machine.notWritten) := by
    by_cases h : r.toNat = 1 <;> simp [h, IxCC.Exe.Machine.written, IxCC.Exe.Machine.notWritten]
  refine atLoop_next ce hat hrip' (fun a ha => hk2 a (.inl ha)) (by show N / 2048 < 2 ^ 64; omega) ?_ ?_ ?_ hargs ?_
  · rw [hmem', cword0_apart ce (by decide) (by decide), cword0_apart ce (by decide) (by decide), hstate]; rfl
  · show (if decide (r.toNat = 1) = true then IxCC.Exe.Machine.written else IxCC.Exe.Machine.notWritten) < 2 ^ 64
    split <;> decide
  · rw [hmem', write_read64_same, hans]
  · rw [hk2.read64 ce (k := 16) (by decide) (by decide), hk2.read64 ce (k := 24) (by decide) (by decide)]
    exact hcur

/-- `arg` with no argument left (`noMore`). -/
theorem arg_done {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    {core : Core} {fl : ByteEval.Flags} (hkept : Kept L s core.memory)
    (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    (h10 : core.readReg .r10 = cTop L) {slot : Word}
    (hslot : core.memory.read64 (cTop L + UInt64.ofNat 16) = slot) (h0 : s.core.memory.read64 slot = 0)
    (hs : ∀ b < 8, OutsideSegments L.segments (slot + UInt64.ofNat b)) (hrsi : core.readReg .rsi = core.memory.read64 slot)
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce 16 3, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) ⟨N / 2048, 257, []⟩ σ := by
  have hz : core.readReg .rsi = 0 := by rw [hrsi, read64_congr (fun a ha => hkept a (.inl ha)) hs, h0]
  obtain ⟨f1, e1⟩ := mrun_cmp ce (b := 16) (j := 3) (by decide) (by rw [block_arg] <;> rfl) (r := .rsi) (c := 0)
    (t := 17) (f := 18) (cond := .eq) (by decide) (by decide) (by rw [block_arg] <;> rfl) (core := core) fl
    (taken := true) (by rw [holds_eq _ (by decide), hz]; rfl)
  have e1 : ByteEval.run ce.checked.bytes fetchBase 2 ⟨core, addr ce 16 3, fl⟩ = .ok ⟨core, addr ce 17 0, f1⟩ := e1
  rcases TraceN.through e1 htr with rfl | ⟨hb1, ht1⟩
  · exact LoopGoal.nil
  rcases noMore_run ce core f1 h10 with hf | ⟨core2, e2, hm2⟩
  · rw [TraceN.nil_of_faults hf ht1]; exact LoopGoal.nil
  rcases TraceN.through e2 ht1 with rfl | ⟨hb2, ht2⟩
  · exact LoopGoal.nil
  have hk2 : Kept L s core2.memory := by rw [hm2]; exact hkept.write (store_low ce 8 (by decide))
  apply ih _ (by omega) _ ht2
  refine atLoop_next ce hat (e := ⟨core2, addr ce 6 0, f1⟩) (cfg' := ⟨N / 2048, 257, []⟩) rfl (fun a ha => hk2 a (.inl ha))
    (by show N / 2048 < 2 ^ 64; omega) ?_ (by show (257 : Nat) < 2 ^ 64; decide) ?_
    (by simp) ?_
  · show core2.memory.read64 (cTop L) = _
    rw [hm2, cword0_apart ce (by decide) (by decide), hstate]
  · show core2.memory.read64 _ = _
    rw [hm2, write_read64_same]
  · show Cursor _ _ (core2.memory.read64 _) (core2.memory.read64 _) []
    rw [hk2.read64 ce (k := 16) (by decide) (by decide), ← hkept.read64 ce (k := 16) (by decide) (by decide), hslot]
    exact .done h0 hs

/-- `arg` within an argument (`argNext`): the byte, the pointer moved on. -/
theorem arg_next {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    {core : Core} {fl : ByteEval.Flags} (hkept : Kept L s core.memory)
    (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    (h10 : core.readReg .r10 = cTop L) {slot : Word}
    (hslot : core.memory.read64 (cTop L + UInt64.ofNat 16) = slot)
    {a : List Nat} {j : Nat} {more : List (List Nat)} (hjlt : j < a.length)
    (hp : s.core.memory.read64 slot ≠ 0) (hs : ∀ b < 8, OutsideSegments L.segments (slot + UInt64.ofNat b))
    (hbytes : ∀ i < a.length, s.core.memory.bytes (s.core.memory.read64 slot + UInt64.ofNat i) = UInt8.ofNat a[i]!)
    (hnul : s.core.memory.bytes (s.core.memory.read64 slot + UInt64.ofNat a.length) = 0)
    (ha : ∀ i ≤ a.length, OutsideSegments L.segments (s.core.memory.read64 slot + UInt64.ofNat i))
    (hnext : Cursor s.core.memory (OutsideSegments L.segments) (slot + 8) (s.core.memory.read64 (slot + 8)) more)
    (hptr : core.memory.read64 (cTop L + UInt64.ofNat 24) = s.core.memory.read64 slot + UInt64.ofNat j)
    (hargs : ∀ x ∈ (a.drop j :: more), ∀ b ∈ x, 0 < b ∧ b < 256)
    (hrsi : core.readReg .rsi = core.memory.read64 slot)
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce 16 3, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) ⟨N / 2048, a[j], a.drop (j + 1) :: more⟩ σ := by
  have hout : ∀ x, OutsideSegments L.segments x → core.memory.bytes x = s.core.memory.bytes x :=
    fun x hx => hkept x (.inl hx)
  have hnz : (core.readReg .rsi).toNat ≠ 0 := by
    rw [hrsi, read64_congr hout hs]
    intro h
    exact hp (UInt64.toNat_inj.mp (by rw [h]; rfl))
  obtain ⟨f1, e1⟩ := mrun_cmp ce (b := 16) (j := 3) (by decide) (by rw [block_arg] <;> rfl) (r := .rsi) (c := 0)
    (t := 17) (f := 18) (cond := .eq) (by decide) (by decide) (by rw [block_arg] <;> rfl) (core := core) fl
    (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; exact hnz)
  have e1 : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce 16 3, fl⟩ = .ok ⟨core, addr ce 18 0, f1⟩ := e1
  rcases TraceN.through e1 htr with rfl | ⟨hb1, ht1⟩
  · exact LoopGoal.nil
  rcases argByte_run ce core f1 h10 with hf | ⟨core2, e2, hm2, h10', -, hsi2, hax2⟩
  · rw [TraceN.nil_of_faults hf ht1]; exact LoopGoal.nil
  rcases TraceN.through e2 ht1 with rfl | ⟨hb2, ht2⟩
  · exact LoopGoal.nil
  have hmem : a[j] ∈ a.drop j := by rw [List.drop_eq_getElem_cons hjlt]; exact List.mem_cons_self
  have hb := hargs (a.drop j) List.mem_cons_self a[j] hmem
  have hv : (core2.readReg .rax).toNat = a[j] := by
    rw [hax2, hptr, hout _ (ha j (Nat.le_of_lt hjlt)), hbytes j hjlt, getElem!_pos a j hjlt]
    show a[j] % 2 ^ 8 = a[j]
    omega
  obtain ⟨f3, e3⟩ := mrun_cmp ce (b := 18) (j := 2) (by decide) (by rw [block_argByte] <;> rfl) (r := .rax) (c := 0)
    (t := 20) (f := 19) (cond := .eq) (by decide) (by decide) (by rw [block_argByte] <;> rfl) (core := core2) f1
    (taken := false) (by rw [holds_eq _ (by decide), hv]; simp only [decide_eq_false_iff_not]; omega)
  have e3 : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core2, addr ce 18 2, f1⟩ = .ok ⟨core2, addr ce 19 0, f3⟩ := e3
  rcases TraceN.through e3 ht2 with rfl | ⟨hb3, ht3⟩
  · exact LoopGoal.nil
  rcases argNext_run ce core2 f3 h10' with hf | ⟨core4, f4, e4, hm4⟩
  · rw [TraceN.nil_of_faults hf ht3]; exact LoopGoal.nil
  rcases TraceN.through e4 ht3 with rfl | ⟨hb4, ht4⟩
  · exact LoopGoal.nil
  apply ih _ (by omega) _ ht4
  have hsi : core2.readReg .rsi = s.core.memory.read64 slot + UInt64.ofNat j := by rw [hsi2, hptr]
  refine atLoop_next ce hat (e := ⟨core4, addr ce 6 0, f4⟩) (cfg' := ⟨N / 2048, a[j], a.drop (j + 1) :: more⟩) rfl
    (fun x hx => by
      show core4.memory.bytes x = _
      rw [hm4, hm2, write_bytes_apart (fun i hi e => store_low ce 8 (by decide) i hi (e ▸ .inl hx)),
        cursor_store_out ce (by decide) (by decide) _ hx]
      exact hout x hx)
    (by show N / 2048 < 2 ^ 64; omega) ?_ (by show a[j] < 2 ^ 64; omega) ?_ ?_ ?_
  · show core4.memory.read64 (cTop L) = _
    rw [hm4, hm2, cword0_apart ce (by decide) (by decide), cword0_apart ce (by decide) (by decide), hstate]
  · show core4.memory.read64 _ = UInt64.ofNat a[j]
    rw [hm4, write_read64_same]
    exact UInt64.toNat_inj.mp (by rw [hv, toNat_small (by omega)])
  · intro x hx b hbx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hargs (a.drop j) List.mem_cons_self b (by
        rw [List.drop_eq_getElem_cons hjlt]; exact List.mem_cons_of_mem _ hbx)
    · exact hargs x (List.mem_cons_of_mem _ hx) b hbx
  · show Cursor _ _ (core4.memory.read64 _) (core4.memory.read64 _) _
    rw [hm4, hm2, cword_apart ce (k := 16) (k' := 8) (by decide) (by decide) (.inr (by decide)),
      cword_apart ce (k := 16) (k' := 24) (by decide) (by decide) (.inl (by decide)), hslot,
      cword_apart ce (k := 24) (k' := 8) (by decide) (by decide) (.inr (by decide)), write_read64_same, hsi,
      UInt64.add_assoc, ← UInt64.ofNat_add]
    exact .arg (j := j + 1) hp hs hjlt hbytes hnul ha hnext

/-- `arg` at an argument's end (`argEnd`): 256, the next slot. -/
theorem arg_end {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    {core : Core} {fl : ByteEval.Flags} (hkept : Kept L s core.memory)
    (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    (h10 : core.readReg .r10 = cTop L) {slot : Word} (h11 : core.readReg .r11 = slot)
    {a : List Nat} {more : List (List Nat)}
    (hp : s.core.memory.read64 slot ≠ 0) (hs : ∀ b < 8, OutsideSegments L.segments (slot + UInt64.ofNat b))
    (hnul : s.core.memory.bytes (s.core.memory.read64 slot + UInt64.ofNat a.length) = 0)
    (ha : ∀ i ≤ a.length, OutsideSegments L.segments (s.core.memory.read64 slot + UInt64.ofNat i))
    (hnext : Cursor s.core.memory (OutsideSegments L.segments) (slot + 8) (s.core.memory.read64 (slot + 8)) more)
    (hptr : core.memory.read64 (cTop L + UInt64.ofNat 24) = s.core.memory.read64 slot + UInt64.ofNat a.length)
    (hargs : ∀ x ∈ more, ∀ b ∈ x, 0 < b ∧ b < 256)
    (hrsi : core.readReg .rsi = core.memory.read64 slot)
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce 16 3, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) ⟨N / 2048, 256, more⟩ σ := by
  have hout : ∀ x, OutsideSegments L.segments x → core.memory.bytes x = s.core.memory.bytes x :=
    fun x hx => hkept x (.inl hx)
  have hnz : (core.readReg .rsi).toNat ≠ 0 := by
    rw [hrsi, read64_congr hout hs]
    intro h
    exact hp (UInt64.toNat_inj.mp (by rw [h]; rfl))
  obtain ⟨f1, e1⟩ := mrun_cmp ce (b := 16) (j := 3) (by decide) (by rw [block_arg] <;> rfl) (r := .rsi) (c := 0)
    (t := 17) (f := 18) (cond := .eq) (by decide) (by decide) (by rw [block_arg] <;> rfl) (core := core) fl
    (taken := false) (by rw [holds_eq _ (by decide)]; simp only [decide_eq_false_iff_not]; exact hnz)
  have e1 : ByteEval.run ce.checked.bytes fetchBase 3 ⟨core, addr ce 16 3, fl⟩ = .ok ⟨core, addr ce 18 0, f1⟩ := e1
  rcases TraceN.through e1 htr with rfl | ⟨hb1, ht1⟩
  · exact LoopGoal.nil
  rcases argByte_run ce core f1 h10 with hf | ⟨core2, e2, hm2, h10', h11', -, hax2⟩
  · rw [TraceN.nil_of_faults hf ht1]; exact LoopGoal.nil
  rcases TraceN.through e2 ht1 with rfl | ⟨hb2, ht2⟩
  · exact LoopGoal.nil
  have hv : (core2.readReg .rax).toNat = 0 := by
    rw [hax2, hptr, hout _ (ha a.length (Nat.le_refl _)), hnul]
    rfl
  obtain ⟨f3, e3⟩ := mrun_cmp ce (b := 18) (j := 2) (by decide) (by rw [block_argByte] <;> rfl) (r := .rax) (c := 0)
    (t := 20) (f := 19) (cond := .eq) (by decide) (by decide) (by rw [block_argByte] <;> rfl) (core := core2) f1
    (taken := true) (by rw [holds_eq _ (by decide), hv]; rfl)
  have e3 : ByteEval.run ce.checked.bytes fetchBase 2 ⟨core2, addr ce 18 2, f1⟩ = .ok ⟨core2, addr ce 20 0, f3⟩ := e3
  rcases TraceN.through e3 ht2 with rfl | ⟨hb3, ht3⟩
  · exact LoopGoal.nil
  rcases argEnd_run ce core2 f3 h10' with hf | ⟨core4, f4, e4, hm4⟩
  · rw [TraceN.nil_of_faults hf ht3]; exact LoopGoal.nil
  rcases TraceN.through e4 ht3 with rfl | ⟨hb4, ht4⟩
  · exact LoopGoal.nil
  apply ih _ (by omega) _ ht4
  rw [h11', h11, hm2] at hm4
  have hm2out : ∀ x, OutsideSegments L.segments x →
      ((core.memory.write .w64 (cTop L + UInt64.ofNat 8) (UInt64.ofNat 256)).write .w64 (cTop L + UInt64.ofNat 16)
        (slot + UInt64.ofNat 8)).bytes x = s.core.memory.bytes x := fun x hx => by
    rw [cursor_store_out ce (by decide) (by decide) _ hx,
      write_bytes_apart (fun i hi e => store_low ce 8 (by decide) i hi (e ▸ .inl hx))]
    exact hout x hx
  refine atLoop_next ce hat (e := ⟨core4, addr ce 6 0, f4⟩) (cfg' := ⟨N / 2048, 256, more⟩) rfl
    (fun x hx => by
      show core4.memory.bytes x = _
      rw [hm4, cursor_store_out ce (by decide) (by decide) _ hx]
      exact hm2out x hx)
    (by show N / 2048 < 2 ^ 64; omega) ?_ (by show (256 : Nat) < 2 ^ 64; decide) ?_ hargs ?_
  · show core4.memory.read64 (cTop L) = _
    rw [hm4, cword0_apart ce (by decide) (by decide), cword0_apart ce (by decide) (by decide),
      cword0_apart ce (by decide) (by decide), hstate]
  · show core4.memory.read64 _ = _
    rw [hm4, cword_apart ce (k := 8) (k' := 24) (by decide) (by decide) (.inl (by decide)),
      cword_apart ce (k := 8) (k' := 16) (by decide) (by decide) (.inl (by decide)), write_read64_same]
  · show Cursor _ _ (core4.memory.read64 _) (core4.memory.read64 _) _
    have hs8 : ∀ b < 8, OutsideSegments L.segments (slot + UInt64.ofNat 8 + UInt64.ofNat b) := Cursor.slot_apart hnext
    rw [hm4, cword_apart ce (k := 16) (k' := 24) (by decide) (by decide) (.inl (by decide)), write_read64_same,
      write_read64_same, read64_congr hm2out hs8]
    exact hnext

/-- `arg`: the argument block's next answer, by the cursor's three cases. -/
theorem value_arg {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event (.ok (some (.nat N))))
    (hq : Request.decode (IxCC.Exe.Machine.split N).2 = some .arg) {core : Core} {fl : ByteEval.Flags}
    (hkept : Kept L s core.memory) (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce 16 0, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  obtain ⟨-, -, -, -, -, hargs, hcur, -⟩ := atLoop_parts ce hat
  apply LoopGoal.arg hc hq
  rcases arg_head ce core fl with hf | ⟨core1, e1, hm1, h10, h11, hsi⟩
  · rw [TraceN.nil_of_faults hf htr]; exact LoopGoal.nil
  rcases TraceN.through e1 htr with rfl | ⟨hb1, ht1⟩
  · exact LoopGoal.nil
  have hkept1 : Kept L s core1.memory := by rw [hm1]; exact hkept
  have hstate1 : core1.memory.read64 (cTop L) = UInt64.ofNat (N / 2048) := by rw [hm1]; exact hstate
  have hslot : core1.memory.read64 (cTop L + UInt64.ofNat 16) = s.core.memory.read64 (cTop L + UInt64.ofNat 16) :=
    hkept1.read64 ce (k := 16) (by decide) (by decide)
  have hptr : core1.memory.read64 (cTop L + UInt64.ofNat 24) = s.core.memory.read64 (cTop L + UInt64.ofNat 24) :=
    hkept1.read64 ce (k := 24) (by decide) (by decide)
  have h11' : core1.readReg .r11 = s.core.memory.read64 (cTop L + UInt64.ofNat 16) := by
    rw [h11, ← hm1, hslot]
  have hsi' : core1.readReg .rsi = core1.memory.read64 (s.core.memory.read64 (cTop L + UInt64.ofNat 16)) := by
    rw [hsi, ← hm1, hslot]
  generalize s.core.memory.read64 (cTop L + UInt64.ofNat 16) = slot at hcur hslot h11' hsi'
  generalize s.core.memory.read64 (cTop L + UInt64.ofNat 24) = ptr at hcur hptr
  generalize cfg.args = args at hcur hargs ⊢
  cases hcur with
  | done h0 hs => exact arg_done ce ih hat hN hkept1 hstate1 h10 hslot h0 hs hsi' (by omega) ht1
  | @arg slot a j more hp hs hj hbytes hnul ha hnext =>
    rcases Nat.lt_or_ge j a.length with hjlt | hjge
    · rw [List.drop_eq_getElem_cons hjlt]
      exact arg_next ce ih hat hN hkept1 hstate1 h10 hslot hjlt hp hs hbytes hnul ha hnext hptr hargs hsi' (by omega) ht1
    · have hjeq : j = a.length := by omega
      subst hjeq
      rw [List.drop_length]
      exact arg_end ce ih hat hN hkept1 hstate1 h10 h11' hp hs hnul ha hnext hptr
        (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hsi' (by omega) ht1

omit ce in
theorem decode_none {q : Nat} (h : 4 ≤ q % 8) : Request.decode q = none := by
  unfold Request.decode
  split <;> first | rfl | (exfalso; omega)

/-- **After `split`**: the request's kind, then its block. -/
theorem after_split {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {N : Nat} (hN : N < 2 ^ 63)
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event (.ok (some (.nat N))))
    {core : Core} {fl : ByteEval.Flags} (hkind : (core.readReg .rcx).toNat = N % 2048 % 8)
    (hpay : (core.readReg .rax).toNat = N % 2048 / 8) (hkept : Kept L s core.memory)
    (hstate : core.memory.read64 (cTop L) = UInt64.ofNat (N / 2048))
    {n : Nat} {σ : List Sys} (hn : n ≤ n₀) (htr : TraceN ce.checked.bytes n ⟨core, addr ce 11 9, fl⟩ σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  have hfile : ∀ i < ce.checked.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]! :=
    fun i hi => (hkept _ (.inl (file_outside ce hi))).trans ((atLoop_parts ce hat).2.2.2.2.2.2.2 i hi)
  obtain ⟨m, fl', e⟩ := kinds ce core fl
  rw [hkind, hpay] at e
  rcases TraceN.through e htr with rfl | ⟨hm, ht'⟩
  · exact LoopGoal.nil
  have hq2 : (IxCC.Exe.Machine.split N).2 = N % 2048 := rfl
  by_cases h0 : N % 2048 % 8 = 0
  · by_cases hp : N % 2048 / 8 = 0
    · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 16 by unfold kindTarget; rw [ite_eq_left h0, ite_eq_left hp]] at ht'
      have hq : Request.decode (IxCC.Exe.Machine.split N).2 = some .arg := by
        rw [hq2]; unfold Request.decode; rw [h0]; exact ite_eq_left hp
      exact value_arg ce ih hat hN hc hq hkept hstate (by omega) ht'
    · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 44 by unfold kindTarget; rw [ite_eq_left h0, ite_eq_right hp]] at ht'
      have hq : Request.decode (IxCC.Exe.Machine.split N).2 = none := by
        rw [hq2]; unfold Request.decode; rw [h0]; exact ite_eq_right hp
      exact value_request ce hc hq hfile ht'
  by_cases h1 : N % 2048 % 8 = 1
  · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 21 by unfold kindTarget; rw [ite_eq_right h0, ite_eq_left h1]] at ht'
    exact value_write ce ih hat hN hc 1 (.inl rfl) h1 hpay hkept hstate (by omega) ht'
  by_cases h2 : N % 2048 % 8 = 2
  · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 22 by unfold kindTarget; rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]] at ht'
    exact value_write ce ih hat hN hc 2 (.inr rfl) h2 hpay hkept hstate (by omega) ht'
  by_cases h3 : N % 2048 % 8 = 3
  · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 26 by unfold kindTarget; rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]] at ht'
    exact value_exit ce hc h3 hpay ht'
  · rw [show kindTarget (N % 2048 % 8) (N % 2048 / 8) = 44 by
      unfold kindTarget; rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]] at ht'
    exact value_request ce hc (by rw [hq2]; exact decode_none (by omega)) hfile ht'

omit ce in
/-- The observation of the step's result word (`Linked.observe` at a `Nat` result). -/
theorem observe_value {roots : List Linked.Root} {sig : Rt.Sig} (D : Driver) (site : Driver.Site) (w : Word) (mem : Memory) :
    (linkedOf object roots D site).linked.observe { symbol := step, params := 2, ty := some (sig, .nat) } w mem =
      if w &&& 1 == 1 then some (.nat (w >>> 1).toNat) else none := by
  show Rt.readback sig _ _ .nat w = _
  simp only [Rt.readback]

/-- **The step's value**: its return, `stepBack`, `decode` (an even word: the `notValue` report),
`split`, then `after_split`. -/
theorem iter_value {roots : List Linked.Root} {n₀ : Nat} (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {s₀ : ByteEval.State}
    (hmem0 : s₀.core.memory = s.core.memory.write .w64 (UInt64.ofNat L.regionStart + UInt64.ofNat 16)
      (UInt64.ofNat L.budget))
    (hinit : s₀.core.memory.bytes = (initDriverOf L ce s₀).initBytes) {w : Word}
    (hc : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event
      (.ok (if w &&& 1 == 1 then some (.nat (w >>> 1).toNat) else none)))
    {s' : ByteEval.State}
    (hret : Returned ((initDriverOf L ce s₀).withSite (stepSite L ce s₀)) (initDriverOf L ce s₀).initBytes 0 s')
    (hw : s'.core.readReg .rdx = w) {n : Nat} {σ : List Sys} (hn : n ≤ n₀)
    (htr : TraceN ce.checked.bytes n s' σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  have hkept := kept_calls ce (D := (initDriverOf L ce s₀).withSite (stepSite L ce s₀)) hmem0 hinit
    (Driver.withSite_mapped _ _) hret
  have hC := sp_add8 ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes
  obtain ⟨fl1, e1⟩ := back ce (b := 8) (j := 10) (b' := 9) (by decide) (by decide) (by rw [block_callStep] <;> rfl)
    (by rw [block_callStep] <;> rfl) (by rw [block_callStep] <;> rfl) (block_stepBack L step _) hret.rip
    (hret.rsp.trans hC)
  let core1 := ((s'.core.setReg .r11 (cTop L)).setReg .r11 (UInt64.ofNat L.shellTop)).setReg .rsp (UInt64.ofNat L.shellTop)
  obtain ⟨fl2, e2⟩ := back_zero ce (b' := 9) (by decide) (by decide) (block_stepBack L step _) (core := core1) (fl := fl1)
    hret.rax
  obtain ⟨m3, core2, fl3, e3, hm2, hrdx2⟩ := decode_run ce core1 fl2
  have hw1 : core1.readReg .rdx = w := hw
  rw [hw1] at e3 hrdx2
  rcases TraceN.through (run_comp e1 (run_comp e2 e3)) htr with rfl | ⟨hb, ht'⟩
  · exact LoopGoal.nil
  have hk2 : Kept L s core2.memory := by rw [hm2]; exact hkept
  have hand : (w &&& 1).toNat = w.toNat % 2 := by
    rw [show (1 : Word) = UInt64.ofNat (2 ^ 1 - 1) from rfl, and_toNat w 1 (by decide)]
  by_cases hodd : w.toNat % 2 = 1
  · rw [ite_eq_left hodd] at ht'
    have hN : (w >>> 1).toNat = w.toNat / 2 := by
      rw [UInt64.toNat_shiftRight]
      show w.toNat >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow]
    have hbit : (w &&& 1 == 1) = true := by
      rw [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [hand, hodd]; rfl)
    rw [hbit, ite_eq_left rfl, hN] at hc
    have hlt : w.toNat / 2 < 2 ^ 63 := by have := w.toNat_lt; omega
    rcases split_run ce core2 fl3 with hf | ⟨core3, fl4, z, e4, hm3, hz, hk3, hp3⟩
    · rw [TraceN.nil_of_faults hf ht']; exact LoopGoal.nil
    rcases TraceN.through e4 ht' with rfl | ⟨hb4, ht4⟩
    · exact LoopGoal.nil
    rw [hrdx2] at hz hk3 hp3
    have hk3' : Kept L s core3.memory := by rw [hm3]; exact hk2.write (store_low ce 0 (by decide))
    have hst3 : core3.memory.read64 (cTop L) = UInt64.ofNat (w.toNat / 2 / 2048) := by
      rw [hm3, add_zero', write_read64_same]
      exact UInt64.toNat_inj.mp (by rw [hz, toNat_small (by omega)])
    exact after_split ce ih hat hlt hc hk3 hp3 hk3' hst3 (by omega) ht4
  · rw [ite_eq_right hodd] at ht'
    have hbit : (w &&& 1 == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg UInt64.toNat h
      rw [hand] at this
      exact hodd this
    rw [hbit, ite_eq_right (by decide)] at hc
    have hfile : ∀ i < ce.checked.bytes.size, core2.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]! :=
      fun i hi => (hk2 _ (.inl (file_outside ce hi))).trans ((atLoop_parts ce hat).2.2.2.2.2.2.2 i hi)
    exact LoopGoal.fail (fun _ => Last.notValue hc (fun _ h => by cases h))
      (report ce .notValue (s := ⟨core2, addr ce 43 0, fl3⟩) rfl hfile ht')

/-- **One iteration**: from `loop` standing for `cfg`, by the call's outcome (see the module note). -/
theorem iteration {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) }) {n₀ : Nat}
    (ih : LoopIH ce roots n₀) {cfg : Config} {s : ByteEval.State}
    (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s) {σ : List Sys}
    (ht : TraceN ce.checked.bytes n₀ s σ) :
    LoopGoal (loopCall object roots ce.checked.plan.placement.textSize) cfg σ := by
  obtain ⟨hrip, hst, hsv, hev, hevv, hargs, hcur, hfile⟩ := atLoop_parts ce hat
  rcases head ce hrip with hf | ⟨s₀, hrun, hmem0, hat0⟩
  · rw [TraceN.nil_of_faults hf ht]; exact LoopGoal.nil
  rcases TraceN.through hrun ht with rfl | ⟨h11, ht0⟩
  · exact LoopGoal.nil
  have hinit : s₀.core.memory.bytes = (initDriverOf L ce s₀).initBytes := hat0.bytes
  have hword : ∀ k, k ≤ 248 → wordOf (initDriverOf L ce s₀).initBytes (cTop L + UInt64.ofNat k) =
      s.core.memory.read64 (cTop L + UInt64.ofNat k) := by
    intro k hk
    rw [← hinit]
    show (⟨s₀.core.memory.bytes, fun _ => true, fun _ => true⟩ : Memory).read64 _ = _
    rw [show (⟨s₀.core.memory.bytes, fun _ => true, fun _ => true⟩ : Memory).read64 (cTop L + UInt64.ofNat k) =
      s₀.core.memory.read64 (cTop L + UInt64.ofNat k) from Memory.readLittle_congr _ _ _ _ (fun _ _ => rfl), hmem0]
    exact region_store_read ce _ _ hk
  have hst0 : wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop) = UInt64.ofNat cfg.state ∧
      wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + 8) = UInt64.ofNat cfg.event := by
    constructor
    · have h := hword 0 (by decide)
      rw [add_zero'] at h
      exact h.trans hsv
    · exact (hword 8 (by decide)).trans hevv
  have hcl := iteration_calls_at ce hroot hst hev hat0 hst0 n₀
  have hcall : loopCall object roots ce.checked.plan.placement.textSize cfg.state cfg.event
      (Lang.run (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀)) (0, [cfg.state, cfg.event]) n₀) :=
    ⟨_, _, n₀, initDriver_ok ce s₀, stepDriver_ok ce s₀, rfl⟩
  generalize Lang.run (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀)) (0, [cfg.state, cfg.event]) n₀ = res
    at hcl hcall
  cases res with
  | timeout =>
    rcases hcl with ⟨s', hr'⟩ | hf
    · rcases TraceN.through hr' ht0 with rfl | ⟨hle, -⟩
      · exact LoopGoal.nil
      · omega
    · rw [TraceN.nil_of_faults hf ht0]; exact LoopGoal.nil
  | stuck => exact LoopGoal.stuck hcall
  | resource f =>
    rcases hcl with ⟨m, s', -, hr', hret⟩ | hf
    · rcases TraceN.through hr' ht0 with rfl | ⟨-, ht'⟩
      · exact LoopGoal.nil
      cases f with
      | heap =>
        exact LoopGoal.fail (fun _ => Last.resource hcall)
          (returned_fail ce hret (k := 0) (by decide) rfl (f := .heap) rfl hmem0 hinit hfile ht')
      | stack =>
        exact LoopGoal.fail (fun _ => Last.resource hcall)
          (returned_fail ce hret (k := 1) (by decide) rfl (f := .stack) rfl hmem0 hinit hfile ht')
      | natOverflow =>
        exact LoopGoal.fail (fun _ => Last.resource hcall)
          (returned_fail ce hret (k := 2) (by decide) rfl (f := .natOverflow) rfl hmem0 hinit hfile ht')
    · rw [TraceN.nil_of_faults hf ht0]; exact LoopGoal.nil
  | trap =>
    rcases hcl with ⟨m, s', -, hr', hret⟩ | hf
    · rcases TraceN.through hr' ht0 with rfl | ⟨-, ht'⟩
      · exact LoopGoal.nil
      exact LoopGoal.fail (fun _ => Last.trap hcall)
        (returned_fail ce hret (k := 3) (by decide) rfl (f := .trap) rfl hmem0 hinit hfile ht')
    · rw [TraceN.nil_of_faults hf ht0]; exact LoopGoal.nil
  | ok o =>
    rcases hcl with ⟨m, s', w, mem, -, hr', hret, hw, -, ho⟩ | hf
    · rcases TraceN.through hr' ht0 with rfl | ⟨-, ht'⟩
      · exact LoopGoal.nil
      rw [← ho, observe_value] at hcall
      exact iter_value ce ih hat hmem0 hinit hcall hret hw (by omega) ht'
    · rw [TraceN.nil_of_faults hf ht0]; exact LoopGoal.nil

/-- **From `loop`**: every trace from a state at `loop` standing for `cfg` is a prefix of the
system calls of a trace the session model performs from `cfg`, or has passed those of a trace
reaching a call the model shows stuck. -/
theorem from_loop {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) })
    {cfg : Config} {s : ByteEval.State} (hat : AtLoop L ce.checked (loopAddr L step ce.checked) cfg s)
    {σ : List Sys} (hσ : Trace ce.checked.bytes s σ) :
    let call := objCallAtOf (linkedOf object roots)
      ce.checked.plan.placement.textSize
    (∃ t ρ, Performs call cfg t ∧ DenotesAll t ρ ∧ σ <+: ρ) ∨
    (∃ t₀ c' ρ₀, Reaches call cfg t₀ c' ∧ call c'.state c'.event .stuck ∧ DenotesAll t₀ ρ₀ ∧ ρ₀ <+: σ) := by
  obtain ⟨n, hn⟩ := Trace.toN hσ
  have all : ∀ n : Nat, LoopIH ce roots (n + 1) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro m hm cfg s σ hat ht
      exact iteration ce hroot (n₀ := m) (fun m' hm' => ih m' (by omega) m' (by omega)) hat ht
  exact all n n (Nat.lt_succ_self n) hat hn

end

end IxCC.X86.Exe.Process
