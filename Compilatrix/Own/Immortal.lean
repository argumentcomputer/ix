import Compilatrix.Own.Syntax

/-! # The Phase 1 Own fragment

Design note 03 §4.4 (phase1 M0.3): Phase 1 compiles under the immortal
allocation policy, where the Own layer is an embedding of Fir.

* `Own.immortal : Fir.Program → Own.Program` (style P, re-run on the
  recheck path, 03 §4.5): `ctor` ↦ `alloc … shared`, `proj` ↦ Own's
  borrowed `proj`, every other right-hand side ↦ `fir`; parameters owned
  and shared with their Fir representation, join parameters owned, shared
  and `tobj`, every `φ` empty; no clone, no region frame. No RC form is
  emitted (the syntax has none yet).
* `Own.erase : Own.Program → Fir.Program` (03 §3.1): `alloc` ↦ `ctor`,
  annotations dropped.
* `Own.checkImmortal q` accepts exactly the fragment: it holds iff
  `Own.immortal (Own.erase q) = q` (`checkImmortal_iff`), and
  `Own.erase (Own.immortal p) = p` (`erase_immortal`).

Structural recursion throughout (kernel-evaluable, D17). -/

namespace Compilatrix.Own

/-! ## The embedding -/

def immRhs : Fir.Rhs → Rhs
  | .ctor c as => .alloc c as .shared
  | .proj x c i => .proj x c i
  | r => .fir r

mutual

def immCode : Fir.Code → Code
  | .bind x r k => .bind x (immRhs r) (immCode k)
  | .jp j ps r b k => .jp j (ps.map (·, PSig.plain .tobj)) [] r (immCode b) (immCode k)
  | .jmp j as => .jmp j as
  | .case x alts d => .case x (immAlts alts) (immOpt d)
  | .ret a => .ret a
  | .tcall f as => .tcall f as
  | .trap => .trap

def immAlts : List Fir.Alt → List Alt
  | [] => []
  | .mk k b :: as => .mk k (immCode b) :: immAlts as

def immOpt : Option Fir.Code → Option Code
  | none => none
  | some c => some (immCode c)

end

def immFun (fd : Fir.Fun) : Fun :=
  { key := fd.key
    sig := { params := fd.params.map (PSig.plain ·.2), result := .shared }
    params := fd.params.map (·.1)
    body := immCode fd.body
    result := fd.result, contracts := fd.contracts, letContracts := fd.letContracts
    vars := fd.vars, joins := fd.joins }

/-- The Phase 1 embedding of Fir into Own (03 §4.4). -/
def immortal (p : Fir.Program) : Program :=
  { funs := p.funs.map immFun, size := p.size, exports := p.exports, ctors := p.ctors
    known := p.known }

/-! ## Erasure -/

def eraseRhs : Rhs → Fir.Rhs
  | .fir r => r
  | .alloc c as _ => .ctor c as
  | .proj x c i => .proj x c i

mutual

def eraseCode : Code → Fir.Code
  | .bind x r k => .bind x (eraseRhs r) (eraseCode k)
  | .jp j ps _ r b k => .jp j (ps.map (·.1)) r (eraseCode b) (eraseCode k)
  | .jmp j as => .jmp j as
  | .case x alts d => .case x (eraseAlts alts) (eraseOpt d)
  | .ret a => .ret a
  | .tcall f as => .tcall f as
  | .trap => .trap

def eraseAlts : List Alt → List Fir.Alt
  | [] => []
  | .mk k b :: as => .mk k (eraseCode b) :: eraseAlts as

def eraseOpt : Option Code → Option Fir.Code
  | none => none
  | some c => some (eraseCode c)

end

def eraseFun (fd : Fun) : Fir.Fun :=
  { key := fd.key
    params := fd.params.zip (fd.sig.params.map (·.rep))
    body := eraseCode fd.body
    result := fd.result, contracts := fd.contracts, letContracts := fd.letContracts
    vars := fd.vars, joins := fd.joins }

/-- Erasure to Fir (03 §3.1): allocations become constructors, annotations
go. (Clones are empty in Phase 1; `checkImmortal` requires it.) -/
def erase (q : Program) : Fir.Program :=
  { funs := q.funs.map eraseFun, size := q.size, exports := q.exports, ctors := q.ctors
    known := q.known }

/-! ## The checker -/

/-- Every entry of a map satisfies `p`. -/
def mapAll {α : Type} (p : α → Bool) : Src.NatMap α → Bool
  | .leaf => true
  | .node v z o => (match v with | some x => p x | none => true) && mapAll p z && mapAll p o

def okRhs : Rhs → Bool
  | .fir (.ctor ..) | .fir (.proj ..) => false
  | .fir _ => true
  | .alloc _ _ κ => κ == .shared
  | .proj .. => true

mutual

def okCode : Code → Bool
  | .bind _ r k => okRhs r && okCode k
  | .jp _ ps φ _ b k => ps.all (·.2 == PSig.plain .tobj) && φ.isEmpty && okCode b && okCode k
  | .case _ alts d => okAlts alts && okOpt d
  | .jmp .. | .ret _ | .tcall .. | .trap => true

def okAlts : List Alt → Bool
  | [] => true
  | .mk _ b :: as => okCode b && okAlts as

def okOpt : Option Code → Bool
  | none => true
  | some c => okCode c

end

def okFun (fd : Fun) : Bool :=
  !fd.regionFrame && fd.sig.result == .shared && fd.sig.params.length == fd.params.length &&
  fd.sig.params.all (fun s => s.mode == .owned && s.kind == .shared) && okCode fd.body

/-- The Phase 1 checker (03 §4.4): the program is in the immortal
fragment. -/
def checkImmortal (q : Program) : Bool := q.clones.isEmpty && mapAll okFun q.funs

/-! ## Characterisation -/

theorem map_map_of_all {α β : Type} (p : α → Bool) (g : α → β) (f : β → α)
    (h : ∀ x, p x = true → f (g x) = x) :
    ∀ m : Src.NatMap α, mapAll p m = true → (m.map g).map f = m
  | .leaf, _ => rfl
  | .node v z o, hm => by
    simp only [mapAll, Bool.and_eq_true] at hm
    obtain ⟨⟨hv, hz⟩, ho⟩ := hm
    simp only [Src.NatMap.map, map_map_of_all p g f h z hz, map_map_of_all p g f h o ho]
    cases v with
    | none => rfl
    | some x => simp only [Option.map_some, h x hv]

theorem mapAll_map {α β : Type} (p : β → Bool) (g : α → β) (h : ∀ x, p (g x) = true) :
    ∀ m : Src.NatMap α, mapAll p (m.map g) = true
  | .leaf => rfl
  | .node v z o => by
    simp only [Src.NatMap.map, mapAll, mapAll_map p g h z, mapAll_map p g h o, Bool.and_true]
    cases v with
    | none => rfl
    | some x => exact h x

theorem eraseRhs_immRhs (r : Fir.Rhs) : eraseRhs (immRhs r) = r := by
  cases r <;> rfl

mutual

theorem eraseCode_immCode : ∀ c : Fir.Code, eraseCode (immCode c) = c
  | .bind x r k => by simp only [immCode, eraseCode, eraseRhs_immRhs, eraseCode_immCode k]
  | .jp j ps r b k => by
    simp only [immCode, eraseCode, List.map_map, eraseCode_immCode b, eraseCode_immCode k]
    have : ((·.1) ∘ fun (x : Fir.Var) => (x, PSig.plain .tobj)) = id := rfl
    rw [this, List.map_id]
  | .jmp _ _ | .ret _ | .tcall _ _ | .trap => rfl
  | .case x alts d => by
    simp only [immCode, eraseCode, eraseAlts_immAlts alts, eraseOpt_immOpt d]

theorem eraseAlts_immAlts : ∀ as : List Fir.Alt, eraseAlts (immAlts as) = as
  | [] => rfl
  | .mk k b :: as => by simp only [immAlts, eraseAlts, eraseCode_immCode b, eraseAlts_immAlts as]

theorem eraseOpt_immOpt : ∀ d : Option Fir.Code, eraseOpt (immOpt d) = d
  | none => rfl
  | some c => by simp only [immOpt, eraseOpt, eraseCode_immCode c]

end

theorem zip_map_fst_snd {α β γ : Type} (xs : List (α × β)) (f : β → γ) (g : γ → β)
    (h : ∀ b, g (f b) = b) : (xs.map (·.1)).zip ((xs.map (f ·.2)).map g) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zip_cons_cons, h, ih]

theorem eraseFun_immFun (fd : Fir.Fun) : eraseFun (immFun fd) = fd := by
  simp only [eraseFun, immFun, eraseCode_immCode]
  rw [zip_map_fst_snd fd.params (PSig.plain ·) (·.rep) (fun _ => rfl)]

theorem mapAll_true {α : Type} : ∀ m : Src.NatMap α, mapAll (fun _ => true) m = true
  | .leaf => rfl
  | .node v z o => by
    simp only [mapAll, mapAll_true z, mapAll_true o, Bool.and_true]
    cases v <;> rfl

/-- Erasure inverts the embedding. -/
theorem erase_immortal (p : Fir.Program) : erase (immortal p) = p := by
  simp only [erase, immortal]
  rw [map_map_of_all (fun _ => true) immFun eraseFun (fun x _ => eraseFun_immFun x) p.funs
    (mapAll_true p.funs)]

theorem map_pair_snd {α β : Type} (b : β) :
    ∀ ps : List (α × β), (∀ p ∈ ps, p.2 = b) → ps.map (fun p => (p.1, b)) = ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [List.map_cons, map_pair_snd b ps h.2, ← h.1]

theorem okRhs_immRhs (r : Fir.Rhs) : okRhs (immRhs r) = true := by
  cases r <;> rfl

mutual

theorem okCode_immCode : ∀ c : Fir.Code, okCode (immCode c) = true
  | .bind _ r k => by simp only [immCode, okCode, okRhs_immRhs, okCode_immCode k, Bool.and_self]
  | .jp _ ps _ b k => by
    simp only [immCode, okCode, okCode_immCode b, okCode_immCode k, List.isEmpty_nil,
      Bool.and_true, List.all_map, List.all_eq_true]
    intro _ _
    simp
  | .jmp _ _ | .ret _ | .tcall _ _ | .trap => rfl
  | .case _ alts d => by simp only [immCode, okCode, okAlts_immAlts alts, okOpt_immOpt d,
      Bool.and_self]

theorem okAlts_immAlts : ∀ as : List Fir.Alt, okAlts (immAlts as) = true
  | [] => rfl
  | .mk _ b :: as => by simp only [immAlts, okAlts, okCode_immCode b, okAlts_immAlts as,
      Bool.and_self]

theorem okOpt_immOpt : ∀ d : Option Fir.Code, okOpt (immOpt d) = true
  | none => rfl
  | some c => okCode_immCode c

end

theorem okFun_immFun (fd : Fir.Fun) : okFun (immFun fd) = true := by
  simp [okFun, immFun, okCode_immCode, PSig.plain]

/-- The embedding lands in the fragment. -/
theorem checkImmortal_immortal (p : Fir.Program) : checkImmortal (immortal p) = true := by
  simp only [checkImmortal, immortal, List.isEmpty_nil, Bool.true_and]
  exact mapAll_map okFun immFun okFun_immFun p.funs

theorem immRhs_eraseRhs : ∀ r : Rhs, okRhs r = true → immRhs (eraseRhs r) = r
  | .fir (.arg _), _ | .fir (.prim ..), _ | .fir (.call ..), _ => rfl
  | .fir (.ctor ..), h | .fir (.proj ..), h => by simp [okRhs] at h
  | .alloc c as κ, h => by
    simp only [okRhs, beq_iff_eq] at h
    subst h
    rfl
  | .proj .., _ => rfl

mutual

theorem immCode_eraseCode : ∀ c : Code, okCode c = true → immCode (eraseCode c) = c
  | .bind x r k, h => by
    simp only [okCode, Bool.and_eq_true] at h
    simp only [eraseCode, immCode, immRhs_eraseRhs r h.1, immCode_eraseCode k h.2]
  | .jp j ps φ r b k, h => by
    simp only [okCode, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hps, hφ⟩, hb⟩, hk⟩ := h
    subst hφ
    simp only [eraseCode, immCode, immCode_eraseCode b hb, immCode_eraseCode k hk, List.map_map]
    simp only [List.all_eq_true, beq_iff_eq] at hps
    have := map_pair_snd (PSig.plain .tobj) ps hps
    simp only [Function.comp_def]
    rw [this]
  | .jmp _ _, _ | .ret _, _ | .tcall _ _, _ | .trap, _ => rfl
  | .case x alts d, h => by
    simp only [okCode, Bool.and_eq_true] at h
    simp only [eraseCode, immCode, immAlts_eraseAlts alts h.1, immOpt_eraseOpt d h.2]

theorem immAlts_eraseAlts : ∀ as : List Alt, okAlts as = true → immAlts (eraseAlts as) = as
  | [], _ => rfl
  | .mk k b :: as, h => by
    simp only [okAlts, Bool.and_eq_true] at h
    simp only [eraseAlts, immAlts, immCode_eraseCode b h.1, immAlts_eraseAlts as h.2]

theorem immOpt_eraseOpt : ∀ d : Option Code, okOpt d = true → immOpt (eraseOpt d) = d
  | none, _ => rfl
  | some c, h => by simp only [eraseOpt, immOpt, immCode_eraseCode c h]

end

theorem map_fst_zip {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length → (xs.zip ys).map (·.1) = xs
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.map_cons, map_fst_zip xs ys h]

theorem map_plain_zip {α : Type} :
    ∀ (xs : List α) (ys : List PSig), xs.length = ys.length →
      (∀ s ∈ ys, s.mode = .owned ∧ s.kind = .shared) →
      (xs.zip (ys.map (·.rep))).map (PSig.plain ·.2) = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, h, hy => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.mem_cons, forall_eq_or_imp] at hy
    simp only [List.map_cons, List.zip_cons_cons, map_plain_zip xs ys h hy.2]
    obtain ⟨⟨hm, hk⟩, _⟩ := hy
    cases y
    simp only at hm hk
    simp only [PSig.plain, hm, hk]

theorem immFun_eraseFun (fd : Fun) (h : okFun fd = true) : immFun (eraseFun fd) = fd := by
  simp only [okFun, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hr, hres⟩, hlen⟩, hps⟩, hb⟩ := h
  have hlen' : fd.params.length = (fd.sig.params.map (·.rep)).length := by simp [hlen]
  cases fd with
  | mk key sig params body regionFrame result contracts letContracts vars joins =>
    cases sig with
    | mk sps sres =>
      simp only at hr hres hlen hps hb hlen'
      subst hr hres
      simp only [immFun, eraseFun, immCode_eraseCode body hb, map_fst_zip params _ hlen',
        map_plain_zip params sps hlen.symm hps]

/-- The checker accepts exactly the image of the embedding (03 §4.4). -/
theorem immortal_erase (q : Program) (h : checkImmortal q = true) : immortal (erase q) = q := by
  simp only [checkImmortal, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨hc, hf⟩ := h
  cases q with
  | mk funs size clones exports ctors known =>
    simp only at hc hf
    subst hc
    simp only [immortal, erase, map_map_of_all okFun eraseFun immFun immFun_eraseFun funs hf]

theorem checkImmortal_iff (q : Program) : checkImmortal q = true ↔ immortal (erase q) = q :=
  ⟨immortal_erase q, fun h => h ▸ checkImmortal_immortal (erase q)⟩

end Compilatrix.Own
