import Aiur.Execution.Encode

/-!
# `getTy` reads what `putTy` writes

`putTy t` appends `tyBytes t` (`putTy_writes`), and `getTy` started at those
bytes returns `t` and stops after them, whatever follows (`getTy_reads`). So
`putTy` is injective (`putTy_inj`): two types written from the same buffer to
the same bytes are equal. The pieces are the Ixon primitives: TagN `nat`
(`getNat_reads`), UTF-8 strings (`getString_reads`) and length-prefixed lists
(`getArray_reads`).
-/

namespace Aiur.Execution.Codec

open Aiur.Ixon

/-! ## Byte positions -/

/-- `bs` holds `enc` at `pos`. -/
def At (bs : ByteArray) (pos : Nat) (enc : List UInt8) : Prop :=
  pos ≤ bs.size ∧ ∃ suf, bs.data.toList.drop pos = enc ++ suf

theorem at_le {bs : ByteArray} {pos : Nat} {e : List UInt8} (h : At bs pos e) :
    pos + e.length ≤ bs.size := by
  obtain ⟨le, suf, h⟩ := h
  have := congrArg List.length h
  simp only [List.length_drop, Array.length_toList, List.length_append] at this
  rw [ByteArray.size] at le ⊢
  omega

theorem at_append {bs : ByteArray} {pos : Nat} {e₁ e₂ : List UInt8} :
    At bs pos (e₁ ++ e₂) → At bs pos e₁ ∧ At bs (pos + e₁.length) e₂ := by
  intro h
  have le := at_le h
  obtain ⟨_, suf, h⟩ := h
  simp only [List.length_append] at le
  refine ⟨⟨by omega, e₂ ++ suf, by simp [h]⟩, ⟨by omega, suf, ?_⟩⟩
  rw [← List.drop_drop, h]
  simp

theorem getElem?_bytes (bs : ByteArray) (i : Nat) : bs[i]? = bs.data[i]? := by
  by_cases h : i < bs.size
  · rw [getElem?_pos bs i h, getElem?_pos bs.data i h, ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg bs i h, getElem?_neg bs.data i h]

theorem at_head {bs : ByteArray} {pos : Nat} {x : UInt8} {e : List UInt8} (h : At bs pos (x :: e)) :
    bs[pos]? = some x := by
  obtain ⟨_, suf, h⟩ := h
  have := congrArg List.head? h
  rw [List.head?_drop] at this
  rw [getElem?_bytes]
  simpa using this

/-- `g`, started at `enc`, returns `x` and stops after `enc`. -/
def Reads {α : Type} (g : GetM α) (enc : List UInt8) (x : α) : Prop :=
  ∀ bs pos, At bs pos enc → g.run ⟨bs, pos⟩ = .ok x ⟨bs, pos + enc.length⟩

theorem reads_pure {α : Type} (x : α) : Reads (pure x : GetM α) [] x := by
  intro bs pos _
  rfl

theorem reads_bind {α β : Type} {g : GetM α} {f : α → GetM β} {e₁ e₂ : List UInt8} {x : α} {y : β}
    (hg : Reads g e₁ x) (hf : Reads (f x) e₂ y) : Reads (g >>= f) (e₁ ++ e₂) y := by
  intro bs pos h
  obtain ⟨h₁, h₂⟩ := at_append h
  have r₁ := hg bs pos h₁
  have r₂ := hf bs (pos + e₁.length) h₂
  simp only [EStateM.run] at r₁ r₂ ⊢
  show EStateM.bind g f ⟨bs, pos⟩ = _
  unfold EStateM.bind
  rw [r₁]
  simp only
  rw [r₂, List.length_append, Nat.add_assoc]

theorem reads_congr {α : Type} {g : GetM α} {e e' : List UInt8} {x : α} (h : Reads g e x) (he : e = e') :
    Reads g e' x := he ▸ h

/-! ## Primitives -/

theorem getU8_reads (x : UInt8) : Reads getU8 [x] x := by
  intro bs pos h
  have head := at_head h
  simp only [getU8, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    head, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure, List.length_singleton]

theorem getTag_reads (what : String) {count : Nat} {x : UInt8} (hx : x.toNat < count) :
    Reads (getTag what count) [x] x.toNat := by
  intro bs pos h
  have r := getU8_reads x bs pos h
  simp only [EStateM.run] at r ⊢
  simp only [getTag, bind, EStateM.bind, r, hx, not_true_eq_false, ↓reduceIte, pure, EStateM.pure]

/-! ## TagN -/

/-- `k` little-endian bytes of `x`. -/
def leB (x : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => (x % 256).toUInt8 :: leB (x / 256) k

/-- The TagN code of `n` (`tagN0`). -/
def tagBytes (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else if n < 16512 then [(128 + (n - 128) / 256).toUInt8, ((n - 128) % 256).toUInt8]
  else if n < 82048 then 192 :: leB (n - 16512) 2
  else if n < 16859264 then 193 :: leB (n - 82048) 3
  else if n < 4311826560 then 194 :: leB (n - 16859264) 4
  else 195 :: leB (n - 4311826560) 8

theorem push_append (out : ByteArray) (b : UInt8) (e : List UInt8) :
    out.push b ++ ⟨e.toArray⟩ = out ++ ⟨(b :: e).toArray⟩ := by
  apply ByteArray.ext
  simp [ByteArray.data_push, ByteArray.data_append]

/-- `tagN0.le`, restated. -/
def leOut (out : ByteArray) (x : Nat) : Nat → ByteArray
  | 0 => out
  | k + 1 => leOut (out.push (x % 256).toUInt8) (x / 256) k

theorem le_eq : ∀ (k : Nat) (out : ByteArray) (x : Nat), leOut out x k = out ++ ⟨(leB x k).toArray⟩
  | 0, out, x => by apply ByteArray.ext; simp [leOut, leB, ByteArray.data_append]
  | k + 1, out, x => by
      rw [leOut, le_eq k, push_append]
      rfl

theorem tagN0_eq (out : ByteArray) {n : Nat} (h : n < 2 ^ 64) :
    tagN0 out n.toUInt64 = out ++ ⟨(tagBytes n).toArray⟩ := by
  have hn : n.toUInt64.toNat = n := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]
  unfold tagN0
  simp only [hn, tagBytes]
  split
  · apply ByteArray.ext; apply Array.toList_inj.mp; simp [ByteArray.data_push, ByteArray.data_append]
  split
  · apply ByteArray.ext; apply Array.toList_inj.mp; simp [ByteArray.data_push, ByteArray.data_append]
  split
  · change leOut (out.push 192) (n - 16512) 2 = _
    rw [le_eq, push_append]
  split
  · change leOut (out.push 193) (n - 82048) 3 = _
    rw [le_eq, push_append]
  split
  · change leOut (out.push 194) (n - 16859264) 4 = _
    rw [le_eq, push_append]
  · change leOut (out.push 195) (n - 4311826560) 8 = _
    rw [le_eq, push_append]

theorem leB_length : ∀ (x k : Nat), (leB x k).length = k
  | _, 0 => rfl
  | x, k + 1 => by simp [leB, leB_length (x / 256) k]

theorem leB_foldr : ∀ (x k : Nat),
    (leB x k).foldr (fun b acc => acc * 256 + b.toNat) 0 = x % 256 ^ k
  | x, 0 => by simp [leB, Nat.mod_one]
  | x, k + 1 => by
      simp only [leB, List.foldr_cons, leB_foldr (x / 256) k]
      have hb : (x % 256).toUInt8.toNat = x % 256 := by
        simp [Nat.toUInt8, UInt8.toNat_ofNat_of_lt' (show x % 256 < UInt8.size by
          simp only [UInt8.size]; omega)]
      rw [hb, Nat.pow_succ', Nat.mod_mul]
      omega

theorem getRaw_reads (e : List UInt8) : Reads (getRaw e.length) e ⟨e.toArray⟩ := by
  intro bs pos h
  have le := at_le h
  obtain ⟨_, suf, hd⟩ := h
  have ext : bs.extract pos (pos + e.length) = ⟨e.toArray⟩ := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take, hd]
    simp
  simp only [getRaw, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    le, not_true_eq_false, ↓reduceIte, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure, ext]

/-- `getLE`, restated. -/
def getLE' (width : Nat) : GetM Nat := do
  let bytes ← getRaw width
  return bytes.data.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- `getNat`, restated over `getLE'`. -/
def getNat' : GetM Nat := do
  let head := (← getU8).toNat
  if head < 128 then return head
  if head < 192 then return 128 + (head - 128) * 256 + (← getU8).toNat
  let value ← match head - 192 with
    | 0 => pure (16512 + (← getLE' 2))
    | 1 => pure (82048 + (← getLE' 3))
    | 2 => pure (16859264 + (← getLE' 4))
    | 3 => pure (4311826560 + (← getLE' 8))
    | code => fail s!"invalid TagN code {code}"
  unless value < 2 ^ 64 do fail "TagN value exceeds UInt64"
  return value

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem getNat_eq : getNat = getNat' := by
  unfold getNat getNat'
  rfl

theorem getLE_reads (x k : Nat) (hx : x < 256 ^ k) : Reads (getLE' k) (leB x k) x := by
  have hv : (⟨(leB x k).toArray⟩ : ByteArray).data.foldr (fun b acc => acc * 256 + b.toNat) 0 = x := by
    rw [← Array.foldr_toList]
    simp only [List.toList_toArray]
    rw [leB_foldr, Nat.mod_eq_of_lt hx]
  have r : Reads (getRaw (leB x k).length >>= fun bytes : ByteArray =>
      (pure (bytes.data.foldr (fun b acc => acc * 256 + b.toNat) 0) : GetM Nat)) (leB x k ++ []) x :=
    reads_bind (getRaw_reads _) (by rw [hv]; exact reads_pure x)
  rw [leB_length, List.append_nil] at r
  exact r

theorem u8_toNat {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat_of_lt' (show n < UInt8.size by simp only [UInt8.size]; omega)]

theorem run_of_reads {α : Type} {g : GetM α} {e rest : List UInt8} {x : α} (hg : Reads g e x)
    {bs : ByteArray} {pos : Nat} (h : At bs pos (e ++ rest)) :
    g ⟨bs, pos⟩ = .ok x ⟨bs, pos + e.length⟩ :=
  hg bs pos (at_append h).1

theorem at_rest {bs : ByteArray} {pos : Nat} {e rest : List UInt8} (h : At bs pos (e ++ rest)) :
    At bs (pos + e.length) rest := (at_append h).2


/-- `getNat'` after a multi-byte head `192 + code`: the `code`-th rung reads
`k` little-endian bytes above `base`. -/
def RungStep (head : UInt8) (base k : Nat) : Prop :=
  ∀ s s1 s2 x, getU8 s = .ok head s1 → getLE' k s1 = .ok x s2 → base + x < 2 ^ 64 →
    getNat' s = .ok (base + x) s2

/-- A rung of TagN is read back once its head step is known. Stated over the
rung's constants, so that no literal case proof unfolds `leB` or the reader. -/
theorem rung_reads {n base k : Nat} {head : UInt8} (hb : base ≤ n) (hx : n - base < 256 ^ k)
    (step : RungStep head base k) (h : n < 2 ^ 64) :
    Reads getNat' (head :: leB (n - base) k) n := by
  intro bs pos hat
  have r0 := run_of_reads (getU8_reads head) (rest := leB (n - base) k) hat
  have r1 := run_of_reads (getLE_reads (n - base) k hx) (rest := [])
    (by rw [List.append_nil]; exact at_rest (e := [head]) (rest := leB _ _) hat)
  simp only [List.length_singleton] at r0 r1
  have := step _ _ _ _ r0 r1 (by omega)
  rw [show base + (n - base) = n by omega, leB_length] at this
  simp only [EStateM.run, List.length_cons, leB_length]
  rw [this, Nat.add_assoc, Nat.add_comm 1 k]

set_option maxRecDepth 100000 in
theorem rungStep_192 : RungStep 192 16512 2 := by
  intro s s1 s2 x h0 h1 hx
  unfold getNat'
  simp only [bind, EStateM.bind, h0, UInt8.reduceToNat]
  simp only [show ¬ (192 : Nat) < 128 by omega, show ¬ (192 : Nat) < 192 by omega, ↓reduceIte, pure]
  simp only [EStateM.bind, EStateM.pure, h1, hx, ↓reduceIte]

set_option maxRecDepth 100000 in
theorem rungStep_193 : RungStep 193 82048 3 := by
  intro s s1 s2 x h0 h1 hx
  unfold getNat'
  simp only [bind, EStateM.bind, h0, UInt8.reduceToNat]
  simp only [show ¬ (193 : Nat) < 128 by omega, show ¬ (193 : Nat) < 192 by omega, ↓reduceIte, pure]
  simp only [EStateM.bind, EStateM.pure, h1, hx, ↓reduceIte]

set_option maxRecDepth 100000 in
theorem rungStep_194 : RungStep 194 16859264 4 := by
  intro s s1 s2 x h0 h1 hx
  unfold getNat'
  simp only [bind, EStateM.bind, h0, UInt8.reduceToNat]
  simp only [show ¬ (194 : Nat) < 128 by omega, show ¬ (194 : Nat) < 192 by omega, ↓reduceIte, pure]
  simp only [EStateM.bind, EStateM.pure, h1, hx, ↓reduceIte]

set_option maxRecDepth 100000 in
theorem rungStep_195 : RungStep 195 4311826560 8 := by
  intro s s1 s2 x h0 h1 hx
  unfold getNat'
  simp only [bind, EStateM.bind, h0, UInt8.reduceToNat]
  simp only [show ¬ (195 : Nat) < 128 by omega, show ¬ (195 : Nat) < 192 by omega, ↓reduceIte, pure]
  simp only [EStateM.bind, EStateM.pure, h1, hx, ↓reduceIte]

set_option maxRecDepth 2000000 in
/-- Every TagN rung: `getNat` reads `tagBytes n` for every `n` that `nat`
accepts. -/
theorem getNat_reads {n : Nat} (h : n < 2 ^ 64) : Reads getNat (tagBytes n) n := by
  rw [getNat_eq]
  unfold tagBytes
  by_cases h1 : n < 128
  · simp only [if_pos h1]
    intro bs pos hat
    simp only [EStateM.run]
    unfold getNat'
    have r0 := run_of_reads (getU8_reads n.toUInt8) (rest := []) (by simpa using hat)
    simp only [bind, EStateM.bind, r0, u8_toNat (by omega : n < 256), h1, ↓reduceIte, pure, EStateM.pure,
      List.length_singleton]
  simp only [if_neg h1]
  by_cases h2 : n < 16512
  · simp only [if_pos h2]
    intro bs pos hat
    simp only [EStateM.run]
    unfold getNat'
    have b0 : (128 + (n - 128) / 256).toUInt8.toNat = 128 + (n - 128) / 256 := u8_toNat (by omega)
    have b1 : ((n - 128) % 256).toUInt8.toNat = (n - 128) % 256 := u8_toNat (by omega)
    have r0 := run_of_reads (getU8_reads (128 + (n - 128) / 256).toUInt8)
      (rest := [((n - 128) % 256).toUInt8]) (by simpa using hat)
    have r1 := run_of_reads (getU8_reads ((n - 128) % 256).toUInt8) (rest := [])
      (by simpa using at_rest (e := [(128 + (n - 128) / 256).toUInt8]) (by simpa using hat))
    simp only [List.length_singleton] at r0 r1
    simp only [bind, EStateM.bind, r0, r1, b0, b1, show ¬ 128 + (n - 128) / 256 < 128 by omega,
      show 128 + (n - 128) / 256 < 192 by omega, ↓reduceIte, pure, EStateM.pure, List.length_cons,
      List.length_singleton, List.length_nil]
    congr 2
    · omega
  simp only [if_neg h2]
  by_cases h3 : n < 82048
  · simp only [if_pos h3]
    exact rung_reads (by omega) (by omega) rungStep_192 h
  simp only [if_neg h3]
  by_cases h4 : n < 16859264
  · simp only [if_pos h4]
    exact rung_reads (by omega) (by omega) rungStep_193 h
  simp only [if_neg h4]
  by_cases h5 : n < 4311826560
  · simp only [if_pos h5]
    exact rung_reads (by omega) (by omega) rungStep_194 h
  simp only [if_neg h5]
  exact rung_reads (by omega) (by omega) rungStep_195 h

/-! ## Strings and lists -/

theorem reads_run {α : Type} {g : GetM α} {e : List UInt8} {x : α} (hg : Reads g e x)
    {bs : ByteArray} {pos : Nat} (h : At bs pos e) : g ⟨bs, pos⟩ = .ok x ⟨bs, pos + e.length⟩ :=
  hg bs pos h

set_option maxRecDepth 100000 in
theorem getString_reads (str : String) (hs : str.toUTF8.size < 2 ^ 64) :
    Reads getString (tagBytes str.toUTF8.size ++ str.toUTF8.data.toList) str := by
  intro bs pos h
  obtain ⟨h₁, h₂⟩ := at_append h
  have r₁ := reads_run (getNat_reads hs) h₁
  have r₂ := reads_run (getRaw_reads str.toUTF8.data.toList) h₂
  have len : str.toUTF8.data.toList.length = str.toUTF8.size := by rw [Array.length_toList]; rfl
  rw [len] at r₂
  have back : (⟨str.toUTF8.data.toList.toArray⟩ : ByteArray) = str.toUTF8 := by
    apply ByteArray.ext; simp
  rw [back] at r₂
  have valid : String.fromUTF8? str.toUTF8 = some str := by
    simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray, str.isValidUTF8, dite_true]
    rfl
  simp only [EStateM.run, getString, getBytes, bind, EStateM.bind, r₁, r₂, valid, pure, EStateM.pure,
    List.length_append, len, Nat.add_assoc]

/-- Reading `n` items with a `for` loop over `[0:n]` whose body `f` reads one item. -/
theorem loop_reads {α : Type} {f : Array α → GetM (ForInStep (Array α))} :
    ∀ (encs : List (List UInt8 × α)), (∀ r, ∀ p ∈ encs, Reads (f r) p.1 (.yield (r.push p.2))) →
    ∀ (start : Nat) (acc : Array α),
    Reads (forIn (List.range' start encs.length) acc (fun _ r => f r))
      (encs.flatMap Prod.fst) (acc ++ (encs.map Prod.snd).toArray)
  | [], _, start, acc => by
      simpa using (reads_pure acc : Reads (pure acc : GetM (Array α)) [] acc)
  | p :: encs, hall, start, acc => by
      have head := hall acc p (List.mem_cons_self ..)
      have tail := loop_reads encs (fun r q hq => hall r q (List.mem_cons_of_mem _ hq)) (start + 1)
        (acc.push p.2)
      simp only [List.length_cons, List.range'_succ, List.forIn_cons, List.flatMap_cons, List.map_cons]
      have hv : acc.push p.2 ++ (List.map Prod.snd encs).toArray =
          acc ++ (p.2 :: List.map Prod.snd encs).toArray := by
        apply Array.toList_inj.mp; simp
      rw [← hv]
      exact reads_bind (x := ForInStep.yield (acc.push p.2)) head tail

theorem length_le_flatMap {α : Type} : ∀ (encs : List (List UInt8 × α)), (∀ p ∈ encs, p.1 ≠ []) →
    encs.length ≤ (encs.flatMap Prod.fst).length
  | [], _ => by simp
  | p :: encs, h => by
      have := length_le_flatMap encs (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hp : p.1.length ≠ 0 := by simpa using h p (List.mem_cons_self ..)
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

set_option maxRecDepth 100000 in
theorem getArray_reads {α : Type} {item : GetM α} (encs : List (List UInt8 × α))
    (hall : ∀ p ∈ encs, Reads item p.1 p.2) (hne : ∀ p ∈ encs, p.1 ≠ [])
    (hs : encs.length < 2 ^ 64) :
    Reads (getArray item) (tagBytes encs.length ++ encs.flatMap Prod.fst) (encs.map Prod.snd).toArray := by
  intro bs pos h
  obtain ⟨h₁, h₂⟩ := at_append h
  have r₁ := reads_run (getNat_reads hs) h₁
  have body : ∀ (r : Array α), ∀ p ∈ encs, Reads ((fun r => (EStateM.bind item fun x =>
      (EStateM.pure PUnit.unit : GetM PUnit).bind fun _ =>
        (EStateM.pure (ForInStep.yield (r.push x)) : GetM (ForInStep (Array α)))) :
        Array α → GetM (ForInStep (Array α))) r) p.1 (.yield (r.push p.2)) := by
    intro r p hp
    exact reads_congr (reads_bind (hall p hp) (reads_bind (reads_pure PUnit.unit) (reads_pure _)))
      (by simp)
  have r₂ := reads_run (loop_reads encs body 0 (Array.mkEmpty encs.length)) h₂
  have room := at_le h₂
  have count := length_le_flatMap encs hne
  have fits : encs.length ≤ bs.size - (pos + (tagBytes encs.length).length) := by omega
  have empty : Array.mkEmpty encs.length ++ (encs.map Prod.snd).toArray = (encs.map Prod.snd).toArray := by
    apply Array.toList_inj.mp; simp
  rw [empty] at r₂
  simp only [EStateM.run, getArray, getCount, bind, EStateM.bind, r₁, remaining, get, getThe,
    MonadStateOf.get, EStateM.get, fits, not_true_eq_false, ↓reduceIte, pure, EStateM.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [r₂]
  simp [Nat.add_assoc]

/-! ## Types -/

/-- The bytes `putTy` writes. -/
def tyBytes : Ty → List UInt8
  | .field => [0]
  | .tuple items => 1 :: (tagBytes items.length ++ items.attach.flatMap fun ⟨t, _⟩ => tyBytes t)
  | .ptr t => 2 :: tyBytes t
  | .enum name => 3 :: (tagBytes name.toUTF8.size ++ name.toUTF8.data.toList)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-- Every list length and name size fits a TagN integer (below `2 ^ 64`). -/
def TyShort : Ty → Prop
  | .field => True
  | .tuple items => items.length < 2 ^ 64 ∧ ∀ t ∈ items.attach, TyShort t.1
  | .ptr t => TyShort t
  | .enum name => name.toUTF8.size < 2 ^ 64
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem t.2; omega)

theorem tyBytes_ne_nil (t : Ty) : tyBytes t ≠ [] := by
  cases t <;> simp [tyBytes]

theorem le_sum_of_mem' : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := le_sum_of_mem' h; simp; omega

theorem attach_flatMap_length {items : List Ty} {t : Ty} (h : t ∈ items) :
    (tyBytes t).length ≤ (items.attach.flatMap fun x => tyBytes x.1).length := by
  rw [List.length_flatMap]
  exact le_sum_of_mem' (List.mem_map.mpr ⟨⟨t, h⟩, List.mem_attach _ _, rfl⟩)

set_option maxRecDepth 100000 in
theorem getTyAux_reads : ∀ (t : Ty), TyShort t → ∀ fuel, (tyBytes t).length < fuel →
    Reads (getTyAux fuel) (tyBytes t) t
  | .field, _, fuel + 1, _ => by
      rw [tyBytes]
      refine reads_congr (reads_bind (e₂ := []) (getTag_reads "type" (x := 0) (by decide)) ?_) rfl
      exact reads_pure _
  | .ptr t, short, fuel + 1, lt => by
      rw [tyBytes] at lt ⊢
      rw [TyShort] at short
      have inner := getTyAux_reads t short fuel (by simp at lt; omega)
      refine reads_bind (getTag_reads "type" (x := 2) (by decide)) ?_
      exact reads_congr (reads_bind inner (reads_pure _)) (List.append_nil _)
  | .enum name, short, fuel + 1, _ => by
      rw [tyBytes]
      rw [TyShort] at short
      refine reads_bind (getTag_reads "type" (x := 3) (by decide)) ?_
      exact reads_congr (reads_bind (getString_reads name short) (reads_pure _)) (List.append_nil _)
  | .tuple items, short, fuel + 1, lt => by
      rw [tyBytes] at lt ⊢
      rw [TyShort] at short
      let encs := items.attach.map fun x => (tyBytes x.1, x.1)
      have hall : ∀ p ∈ encs, Reads (getTyAux fuel) p.1 p.2 := by
        intro p hp
        obtain ⟨⟨t, ht⟩, hmem, rfl⟩ := List.mem_map.mp hp
        have := attach_flatMap_length ht
        have := List.sizeOf_lt_of_mem ht
        simp only [List.length_cons, List.length_append] at lt
        exact getTyAux_reads t (short.2 ⟨t, ht⟩ hmem) fuel (by omega)
      have hne : ∀ p ∈ encs, p.1 ≠ [] := by
        intro p hp
        obtain ⟨⟨t, _⟩, _, rfl⟩ := List.mem_map.mp hp
        exact tyBytes_ne_nil t
      have len : encs.length = items.length := by simp [encs]
      have arr := getArray_reads encs hall hne (by rw [len]; exact short.1)
      have flat : encs.flatMap Prod.fst = items.attach.flatMap fun x => tyBytes x.1 := by
        simp [encs, List.flatMap_map]
      have vals : (encs.map Prod.snd).toArray.toList = items := by
        simp [encs, List.map_map, Function.comp_def]
      rw [len, flat] at arr
      refine reads_bind (getTag_reads "type" (x := 1) (by decide)) ?_
      refine reads_congr (reads_bind arr ?_) (List.append_nil _)
      rw [vals]
      exact reads_pure _
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)

theorem getTy_reads (t : Ty) (short : TyShort t) : Reads getTy (tyBytes t) t := by
  intro bs pos h
  have room := at_le h
  have r := getTyAux_reads t short (bs.size - pos + 1) (by omega) bs pos h
  simp only [EStateM.run] at r ⊢
  simp only [getTy, bind, EStateM.bind, remaining, get, getThe, MonadStateOf.get, EStateM.get, pure,
    EStateM.pure]
  exact r

/-! ## Writing -/

/-- A successful run of `p` appends `e`. -/
def Writes (p : PutM Unit) (e : List UInt8) : Prop :=
  ∀ b b', p b = .ok () b' → b' = b ++ ⟨e.toArray⟩

theorem append_assoc' (b : ByteArray) (e₁ e₂ : List UInt8) :
    b ++ ⟨e₁.toArray⟩ ++ ⟨e₂.toArray⟩ = b ++ ⟨(e₁ ++ e₂).toArray⟩ := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem writes_bind {p q : PutM Unit} {e₁ e₂ : List UInt8} (hp : Writes p e₁) (hq : Writes q e₂) :
    Writes (p >>= fun _ => q) (e₁ ++ e₂) := by
  intro b b' h
  change EStateM.bind p (fun _ => q) b = _ at h
  simp only [EStateM.bind] at h
  split at h
  · rename_i u b₁ hb
    rw [hq _ _ h, hp _ _ hb, append_assoc']
  · cases h

theorem writes_congr {p : PutM Unit} {e e' : List UInt8} (h : Writes p e) (he : e = e') : Writes p e' :=
  he ▸ h

theorem u8_writes (x : UInt8) : Writes (u8 x) [x] := by
  intro b b' h
  simp only [u8, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, Prod.mk.injEq] at h
  cases h
  apply ByteArray.ext; simp [ByteArray.data_push, ByteArray.data_append]

theorem nat_writes (n : Nat) : Writes (nat n) (tagBytes n) := by
  intro b b' h
  by_cases hn : n < 2 ^ 64
  · simp only [Aiur.Ixon.nat, hn, not_true_eq_false, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at h
    cases h
    exact tagN0_eq b hn
  · have hn' : ¬ n < 18446744073709551616 := hn
    simp [Aiur.Ixon.nat, hn', bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

theorem raw_writes (bs : ByteArray) : Writes (raw bs) bs.data.toList := by
  intro b b' h
  simp only [raw, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at h
  cases h
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem pure_writes : Writes (pure ()) [] := by
  intro b b' h
  cases h
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem str_writes (name : String) :
    Writes (str name) (tagBytes name.toUTF8.size ++ name.toUTF8.data.toList) :=
  writes_bind (nat_writes _) (raw_writes _)

/-- A `for` loop whose body appends `enc x` for each `x` and always continues. -/
theorem forIn_writes {α : Type} {f : α → PUnit → PutM (ForInStep PUnit)} {enc : α → List UInt8} :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ b b' s, f x () b = .ok s b' → s = .yield () ∧ b' = b ++ ⟨(enc x).toArray⟩) →
    Writes (forIn xs () f) (xs.flatMap enc)
  | [], _ => by
      intro b b' h
      simp only [List.forIn_nil, pure, EStateM.pure] at h
      cases h
      apply ByteArray.ext; simp [ByteArray.data_append]
  | x :: xs, hf => by
      intro b b' h
      simp only [List.forIn_cons, bind, EStateM.bind] at h
      split at h
      · rename_i s b₁ hb
        obtain ⟨rfl, rfl⟩ := hf x (List.mem_cons_self ..) _ _ _ hb
        have := forIn_writes xs (fun y hy => hf y (List.mem_cons_of_mem _ hy)) _ _ h
        rw [this, List.flatMap_cons, append_assoc']
      · cases h

theorem list_writes {α : Type} (xs : List α) (item : α → PutM Unit) (enc : α → List UInt8)
    (h : ∀ x ∈ xs, Writes (item x) (enc x)) :
    Writes (list xs item) (tagBytes xs.length ++ xs.flatMap enc) := by
  refine writes_bind (nat_writes _) (writes_congr (writes_bind (forIn_writes xs ?_) pure_writes)
    (List.append_nil _))
  intro x hx b b' s hrun
  simp only [bind, EStateM.bind] at hrun
  split at hrun
  · rename_i u b₁ hb
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, h x hx _ _ hb⟩
  · cases hrun

theorem putTy_writes : ∀ (t : Ty), Writes (putTy t) (tyBytes t)
  | .field => by rw [putTy, tyBytes]; exact u8_writes 0
  | .ptr t => by
      rw [putTy, tyBytes]
      exact writes_congr (writes_bind (u8_writes 2) (putTy_writes t)) rfl
  | .enum name => by
      rw [putTy, tyBytes]
      exact writes_congr (writes_bind (u8_writes 3) (str_writes name)) rfl
  | .tuple items => by
      rw [putTy, tyBytes]
      refine writes_congr (writes_bind (u8_writes 1) (list_writes items.attach _ (fun x => tyBytes x.1) ?_))
        (by simp)
      intro ⟨t, ht⟩ _
      have := List.sizeOf_lt_of_mem ht
      exact putTy_writes t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-! ## Injectivity -/

theorem at_written (b : ByteArray) (e : List UInt8) : At (b ++ ⟨e.toArray⟩) b.size e := by
  refine ⟨by rw [ByteArray.size_append]; omega, [], ?_⟩
  rw [ByteArray.data_append, Array.toList_append, List.append_nil]
  exact List.drop_left' (by rw [Array.length_toList]; rfl)

/-- `getTy` reads back what `putTy` wrote. -/
theorem getTy_putTy {t : Ty} (short : TyShort t) {b b' : ByteArray} (h : putTy t b = .ok () b') :
    getTy ⟨b', b.size⟩ = .ok t ⟨b', b'.size⟩ := by
  have hw := putTy_writes t b b' h
  subst hw
  have r := getTy_reads t short _ _ (at_written b (tyBytes t))
  simp only [EStateM.run] at r
  rw [r, ByteArray.size_append]
  simp only [ByteArray.size, List.size_toArray]

/-- `putTy` is injective on the types whose lengths fit TagN. -/
theorem putTy_inj {t₁ t₂ : Ty} (s₁ : TyShort t₁) (s₂ : TyShort t₂) {b b' : ByteArray}
    (h₁ : putTy t₁ b = .ok () b') (h₂ : putTy t₂ b = .ok () b') : t₁ = t₂ := by
  have r₁ := getTy_putTy s₁ h₁
  have r₂ := getTy_putTy s₂ h₂
  rw [r₁] at r₂
  cases r₂
  rfl

end Aiur.Execution.Codec
