import IxCCCorrect.Shape1

/-!
# The decision for milestone M1 (`IxCCCorrect.Shape1Check`)

`IxCCCorrect.Shape1`'s judgments, decided from an untrusted certificate
(`Cert`): the instances `(constant, levels, shape)` the program uses, and the
constructor list of each enumeration.

* `synth`: the shapes a term can have in a context, as a list (a constant may have
  several instances); a λ needs the expected shape. `synth_sound`: each is a
  derivation.
* `entryOk`: one instance resolves in the program as its shape says, by kind of
  constant (primitive, equation hint, `csimp`, `case` entry, definition, constructor,
  recursor). `entryOk_sound`: `ConstOk`.
* `certOk`: every instance and every enumeration. `sigOk_of_cert`: `SigOk`.
* `neverWrong_of_cert_nat`, `neverWrong_of_cert_enum`: `NeverWrong` from the
  decision, at a root that returns a `Nat` or a value of an enumeration.

The checks read a shape apart with total, unproved helpers (`argAt`, `resAfter`,
`unarrowD`) and then compare the shape with the one the rule builds (`decide`), so
soundness rests on the comparison only.
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape1

open IxCC.Src
open IxCC.Sem (Result Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- The certificate: the instances, and each enumeration's constructors in index
order. -/
structure Cert where
  insts : List (CId × Levels × Shape)
  enums : List (CId × List CId)

/-- The constructors a certificate lists for an enumeration: its first entry's. -/
def lookupEnum : List (CId × List CId) → CId → Option (List CId)
  | [], _ => none
  | (I', cs) :: l, I => if I = I' then some cs else lookupEnum l I

theorem mem_of_lookupEnum : ∀ (l : List (CId × List CId)) (I : CId) (cs : List CId),
    lookupEnum l I = some cs → (I, cs) ∈ l
  | [], I, cs, h => by simp [lookupEnum] at h
  | (I', cs') :: l, I, cs, h => by
    simp only [lookupEnum] at h
    split at h
    · rename_i hI
      simp only [Option.some.injEq] at h
      subst hI
      subst h
      exact List.mem_cons.2 (.inl rfl)
    · exact List.mem_cons.2 (.inr (mem_of_lookupEnum l I cs h))

/-- The signature a certificate states. -/
def Cert.sig (cert : Cert) : Sig where
  inst c ls σ := (c, ls, σ) ∈ cert.insts
  enums := lookupEnum cert.enums

/-- The shapes the certificate lists for a constant at given levels. -/
def instsOf : List (CId × Levels × Shape) → CId → Levels → List Shape
  | [], _, _ => []
  | (c', ls', σ) :: l, c, ls =>
    if c' = c ∧ ls' = ls then σ :: instsOf l c ls else instsOf l c ls

theorem mem_instsOf : ∀ (l : List (CId × Levels × Shape)) (c : CId) (ls : Levels) (σ : Shape),
    σ ∈ instsOf l c ls → (c, ls, σ) ∈ l
  | [], _, _, _, h => by simp [instsOf] at h
  | (c', ls', σ') :: l, c, ls, σ, h => by
    simp only [instsOf] at h
    split at h
    · rename_i hcond
      obtain ⟨h1, h2⟩ := hcond
      subst h1
      subst h2
      rcases List.mem_cons.1 h with h' | h'
      · subst h'
        exact List.mem_cons.2 (.inl rfl)
      · exact List.mem_cons.2 (.inr (mem_instsOf l _ _ σ h'))
    · exact List.mem_cons.2 (.inr (mem_instsOf l c ls σ h))

/-! ## Shape synthesis -/

/-- What an application returns, per shape of the function: at an irrelevant argument
the domain must be `irr`; at a relevant one the argument must check against it. -/
def appRes (irrArg : Bool) (argOk : Shape → Bool) : Shape → List Shape
  | .fn σ τ => if irrArg then (if σ = .irr then [τ] else []) else (if argOk σ then [τ] else [])
  | _ => []

theorem mem_appRes {irrArg : Bool} {argOk : Shape → Bool} {s τ : Shape}
    (h : τ ∈ appRes irrArg argOk s) :
    ∃ σ, s = .fn σ τ ∧ ((irrArg = true ∧ σ = .irr) ∨ (irrArg = false ∧ argOk σ = true)) := by
  cases s with
  | fn σ τ' =>
    cases irrArg with
    | true =>
      by_cases hσ : σ = .irr
      · simp [appRes, hσ] at h
        exact ⟨σ, by rw [h], .inl ⟨rfl, hσ⟩⟩
      · simp [appRes, hσ] at h
    | false =>
      by_cases ha : argOk σ = true
      · simp [appRes, ha] at h
        exact ⟨σ, by rw [h], .inr ⟨rfl, ha⟩⟩
      · simp [appRes, ha] at h
  | nat => simp [appRes] at h
  | enum _ => simp [appRes] at h
  | irr => simp [appRes] at h

/-- **Shape synthesis at levels `ls`**: the shapes of a term in a context. `e` is the
shape expected, which a λ needs and nothing else reads. -/
def synth (insts : List (CId × Levels × Shape)) (ls : Levels) :
    List Shape → Term → Option Shape → List Shape
  | Γ, .var i, _ => (Γ[i]?).toList
  | _, .natLit _, _ => [.nat]
  | _, .sort _, _ => [.irr]
  | _, .pi _ _ _, _ => [.irr]
  | _, .const c us, _ => instsOf insts c (us.map (evalUniv ls))
  | Γ, .app f a _ r, _ =>
    (synth insts ls Γ f none).flatMap fun s =>
      appRes (r.irrAt ls) (fun σ => decide (σ ∈ synth insts ls Γ a (some σ))) s
  | Γ, .lam b _ body, e =>
    match e with
    | some (.fn σ τ) =>
      if b.propWhen.allowsBeta ls then
        if τ ∈ synth insts ls (σ :: Γ) body (some τ) then [.fn σ τ] else []
      else []
    | _ => []
  | Γ, .letE _ _ r _ v body, e =>
    if r.irrAt ls then synth insts ls (.irr :: Γ) body e
    else (synth insts ls Γ v none).flatMap fun σ => synth insts ls (σ :: Γ) body e
  | _, _, _ => []

/-- A synthesized shape is a derivation. -/
theorem synth_sound (cert : Cert) (ls : Levels) : ∀ (t : Term) (Γ : List Shape)
    (e : Option Shape) (σ : Shape), σ ∈ synth cert.insts ls Γ t e → HasShape cert.sig ls Γ t σ := by
  intro t
  induction t with
  | var i =>
    intro Γ e σ h
    simp [synth] at h
    exact .var h
  | sort u =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .sort
  | const c us =>
    intro Γ e σ h
    simp only [synth] at h
    exact .const (mem_instsOf _ _ _ _ h)
  | app f a m r ihf iha =>
    intro Γ e σ h
    simp only [synth] at h
    obtain ⟨s, hs, hτ⟩ := List.mem_flatMap.1 h
    obtain ⟨σ', rfl, hc⟩ := mem_appRes hτ
    rcases hc with ⟨hr, rfl⟩ | ⟨hr, ha⟩
    · exact .appIrr hr (ihf _ _ _ hs)
    · exact .app hr (ihf _ _ _ hs) (iha _ _ _ (of_decide_eq_true ha))
  | lam b d body _ ihb =>
    intro Γ e σ h
    cases e with
    | none => simp [synth] at h
    | some s =>
      cases s with
      | fn σ' τ' =>
        simp only [synth] at h
        split at h
        · rename_i hb
          split at h
          · rename_i hbody
            simp only [List.mem_singleton] at h
            subst h
            exact .lam hb (ihb _ _ _ hbody)
          · simp at h
        · simp at h
      | nat => simp [synth] at h
      | enum _ => simp [synth] at h
      | irr => simp [synth] at h
  | pi b d c _ _ =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .pi
  | letE nonDep lm r ty v body _ ihv ihb =>
    intro Γ e σ h
    simp only [synth] at h
    split at h
    · rename_i hr
      exact .letIrr hr (ihb _ _ _ h)
    · rename_i hr
      obtain ⟨σ', hv, hb⟩ := List.mem_flatMap.1 h
      exact .letE (by simpa using hr) (ihv _ _ _ hv) (ihb _ _ _ hb)
  | proj s i e' _ =>
    intro Γ e σ h
    simp [synth] at h
  | natLit n =>
    intro Γ e σ h
    simp [synth] at h
    subst h
    exact .natLit
  | strLit s =>
    intro Γ e σ h
    simp [synth] at h

/-! ## Reading a shape apart (unproved helpers; the checks compare afterwards) -/

/-- The `n`-th argument shape, or `irr`. -/
def argAt : Nat → Shape → Shape
  | 0, .fn a _ => a
  | n + 1, .fn _ b => argAt n b
  | _, _ => .irr

/-- What is left after `n` arrows. -/
def resAfter : Nat → Shape → Shape
  | n + 1, .fn _ b => resAfter n b
  | _, τ => τ

/-- The first `n` argument shapes. -/
def argsUpTo : Nat → Shape → List Shape
  | n + 1, .fn a b => a :: argsUpTo n b
  | _, _ => []

/-! ## Special heads -/

/-- The field shapes of the constructors of what a recursor of `ind` scrutinises at
shape `σ`. -/
def fldsOf (p : Program) (enums : CId → Option (List CId)) (ind : CId) :
    Shape → Option (List (List Shape))
  | .nat => if (some ind == p.known.nat) then some [[], [.nat]] else none
  | .enum I => if I = ind then (enums I).map fun cs => cs.map fun _ => [] else none
  | _ => none

theorem fldsOf_sound {p : Program} {sig : Sig} {ind : CId} {σ : Shape}
    {flds : List (List Shape)} (h : fldsOf p sig.enums ind σ = some flds) :
    ScrutOk p sig σ ind flds := by
  cases σ with
  | nat =>
    simp only [fldsOf] at h
    split at h
    · rename_i hN
      cases h
      exact .nat hN
    · cases h
  | enum I =>
    simp only [fldsOf] at h
    split at h
    · rename_i hI
      subst hI
      cases he : sig.enums I with
      | none =>
        rw [he] at h
        cases h
      | some cs =>
        rw [he] at h
        cases h
        exact .enum he
    · cases h
  | irr => simp [fldsOf] at h
  | fn _ _ => simp [fldsOf] at h

def isOrdinary : Option RecKind → Bool
  | some .ordinary => true
  | _ => false

theorem isOrdinary_sound {k : Option RecKind} (h : isOrdinary k = true) : k = some .ordinary := by
  cases k with
  | none => simp [isOrdinary] at h
  | some kind =>
    cases kind with
    | ordinary => rfl
    | subsingleton _ _ => simp [isOrdinary] at h
    | empty => simp [isOrdinary] at h

/-- A `Bool`-valued primitive: its result is an enumeration of the certificate that
lists both pinned `Bool` constructors. -/
def predOk (p : Program) (cert : Cert) (op : PrimOp) (σ : Shape) : Bool :=
  cert.enums.any fun e =>
    decide (lookupEnum cert.enums e.1 = some e.2) &&
      decide (σ = arrows (List.replicate op.arity .nat) (.enum e.1)) &&
      decide (p.known.boolTrue ∈ e.2.map some) && decide (p.known.boolFalse ∈ e.2.map some)

theorem predOk_sound {p : Program} {cert : Cert} {op : PrimOp} {σ : Shape} {ls : Levels}
    (hp : op.isPredicate = true) (h : predOk p cert op σ = true) :
    ∃ σs τ, HeadOk p cert.sig (.prim op) ls σs τ ∧ σ = arrows σs τ := by
  obtain ⟨⟨B, cs⟩, -, he⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨hB, hσ⟩, ht⟩, hf⟩ := he
  obtain ⟨t, htm, ht'⟩ := List.mem_map.1 ht
  obtain ⟨f, hfm, hf'⟩ := List.mem_map.1 hf
  exact ⟨_, _, .pred op ls B t f cs hp ht'.symm hf'.symm hB htm hfm, hσ⟩

/-- A `case` entry at an instance `irr → σ₁ → minors → τ`. -/
def casesOk (p : Program) (cert : Cert) (σ : Shape) (ind : CId) (np nmin ni : Nat) : Bool :=
  match fldsOf p (lookupEnum cert.enums) ind (argAt 1 σ) with
  | some flds =>
    decide (np = 0) && decide (ni = 0) && decide (nmin = flds.length) &&
      decide (σ = arrows (.irr :: argAt 1 σ :: flds.map fun fl =>
        arrows fl (resAfter (2 + flds.length) σ)) (resAfter (2 + flds.length) σ))
  | none => false

theorem casesOk_sound {p : Program} {cert : Cert} {ls : Levels} {σ : Shape} {c r : CId}
    {s kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hres : p.table.resolveOf c = some (.case r))
    (hdecl : p.decl? r = some (.recr s kk lv np nmot nmin ni ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary)
    (h : casesOk p cert σ ind np nmin ni = true) :
    ∃ σs τ, HeadOk p cert.sig (.cases c) ls σs τ ∧ σ = arrows σs τ := by
  unfold casesOk at h
  cases hf : fldsOf p (lookupEnum cert.enums) ind (argAt 1 σ) with
  | none => simp [hf] at h
  | some flds =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hnp, hni⟩, hnm⟩, hσ⟩ := h
    rw [hnp, hni, hnm] at hdecl
    exact ⟨_, _, .cases c r ls _ ind flds _ s kk lv nmot rules ty hres hdecl hkind
      (fldsOf_sound (sig := cert.sig) hf), hσ⟩

/-- Each rule of a recursor peels its λs and its body has the result shape in the
environment F2 builds, from rule `j` on. -/
def rulesOk (insts : List (CId × Levels × Shape)) (ls : Levels) (rules : List Rule)
    (ms : List Shape) (τ : Shape) : Nat → List (List Shape) → Bool
  | _, [] => true
  | j, fl :: rest =>
    (match rules[j]? with
      | some rule =>
        match peelLams (1 + ms.length + fl.length) rule.rhs with
        | some body =>
          decide (τ ∈ synth insts ls (fl.reverse ++ (ms.reverse ++ [.irr])) body (some τ))
        | none => false
      | none => false) && rulesOk insts ls rules ms τ (j + 1) rest

theorem rulesOk_sound {cert : Cert} {ls : Levels} {rules : List Rule} {ms : List Shape}
    {τ : Shape} : ∀ (flds : List (List Shape)) (j0 : Nat),
    rulesOk cert.insts ls rules ms τ j0 flds = true →
    ∀ (i : Nat) (fl : List Shape), flds[i]? = some fl → ∃ (rule : Rule) (body : Term),
      rules[j0 + i]? = some rule ∧ peelLams (1 + ms.length + fl.length) rule.rhs = some body ∧
      HasShape cert.sig ls (fl.reverse ++ (ms.reverse ++ [.irr])) body τ
  | [], _, _, i, fl, hi => by simp at hi
  | fl0 :: rest, j0, h, i, fl, hi => by
    simp only [rulesOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      cases hr : rules[j0]? with
      | none => simp [hr] at h1
      | some rule =>
        cases hp : peelLams (1 + ms.length + fl0.length) rule.rhs with
        | none => simp [hr, hp] at h1
        | some body =>
          simp only [hr, hp, decide_eq_true_eq] at h1
          exact ⟨rule, body, rfl, hp, synth_sound cert ls _ _ _ _ h1⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨rule, body, hr, hp, hb⟩ := rulesOk_sound rest (j0 + 1) h2 i fl hi
      have e : j0 + (i + 1) = j0 + 1 + i := by omega
      rw [e]
      exact ⟨rule, body, hr, hp, hb⟩

/-- A recursor at an instance `irr → minors → σ₁ → τ`. -/
def recrOk (p : Program) (cert : Cert) (ls : Levels) (σ : Shape) (ind : CId)
    (np nmot nmin ni : Nat) (rules : List Rule) : Bool :=
  match fldsOf p (lookupEnum cert.enums) ind (argAt (1 + nmin) σ) with
  | some flds =>
    decide (np = 0) && decide (nmot = 1) && decide (ni = 0) &&
      decide ((argsUpTo nmin (resAfter 1 σ)).length = nmin) &&
      decide (σ = arrows (.irr :: (argsUpTo nmin (resAfter 1 σ) ++ [argAt (1 + nmin) σ]))
        (resAfter (2 + nmin) σ)) &&
      rulesOk cert.insts ls rules (argsUpTo nmin (resAfter 1 σ)) (resAfter (2 + nmin) σ) 0 flds
  | none => false

theorem recrOk_sound {p : Program} {cert : Cert} {ls : Levels} {σ : Shape} {r : CId}
    {s kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hdecl : p.decl? r = some (.recr s kk lv np nmot nmin ni ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary)
    (h : recrOk p cert ls σ ind np nmot nmin ni rules = true) :
    ∃ σs τ, HeadOk p cert.sig (.recr r) ls σs τ ∧ σ = arrows σs τ := by
  unfold recrOk at h
  cases hf : fldsOf p (lookupEnum cert.enums) ind (argAt (1 + nmin) σ) with
  | none => simp [hf] at h
  | some flds =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hnp, hnm⟩, hni⟩, hlen⟩, hσ⟩, hrules⟩ := h
    rw [hnp, hnm, hni, ← hlen] at hdecl
    refine ⟨_, _, .recr r ls _ ind flds (argsUpTo nmin (resAfter 1 σ)) _ s kk lv rules ty hdecl
      hkind (fldsOf_sound (sig := cert.sig) hf) ?_, hσ⟩
    intro j fl hfl
    obtain ⟨rule, body, hr, hp, hb⟩ := rulesOk_sound flds 0 hrules j fl hfl
    rw [Nat.zero_add] at hr
    exact ⟨rule, body, hr, hp, hb⟩

/-! ## Constructors -/

def zeroOk (p : Program) (c : CId) (np nf : Nat) (σ : Shape) : Bool :=
  decide (np = 0) && decide (nf = 0) && (some c == p.known.natZero) && decide (σ = .nat)

def succOk (p : Program) (c : CId) (np nf : Nat) (σ : Shape) : Bool :=
  decide (np = 0) && decide (nf = 1) && (some c == p.known.natSucc) &&
    !(some c == p.known.natZero) && decide (σ = .fn .nat .nat)

def enumCtorOk (cert : Cert) (c : CId) (σ : Shape) : Bool :=
  cert.enums.any fun e =>
    decide (lookupEnum cert.enums e.1 = some e.2) && decide (c ∈ e.2) && decide (σ = .enum e.1)

/-- An enumeration's listed constructors are its constructors, from index `i` on. -/
def enumOk (p : Program) (I : CId) : Nat → List CId → Bool
  | _, [] => true
  | i, c :: cs =>
    (match p.decl? c with
      | some (.ctor _ _ ind cidx np nf _) =>
        decide (ind = I) && decide (cidx = i) && decide (np = 0) && decide (nf = 0) &&
          !(some c == p.known.natZero) && !(some c == p.known.natSucc)
      | _ => false) && enumOk p I (i + 1) cs

theorem enumOk_sound {p : Program} {I : CId} : ∀ (cs : List CId) (i0 : Nat),
    enumOk p I i0 cs = true → ∀ (i : Nat) (c : CId), cs[i]? = some c →
    ∃ s lv ty, p.decl? c = some (.ctor s lv I (i0 + i) 0 0 ty) ∧
      (some c == p.known.natZero) = false ∧ (some c == p.known.natSucc) = false
  | [], _, _, i, c, hi => by simp at hi
  | c0 :: cs, i0, h, i, c, hi => by
    simp only [enumOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      cases hd : p.decl? c0 with
      | none => simp [hd] at h1
      | some d =>
        cases d with
        | ctor s lv ind cidx np nf ty =>
          simp only [hd, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
          obtain ⟨⟨⟨⟨⟨h1a, h1b⟩, h1c⟩, h1d⟩, hz⟩, hs⟩ := h1
          exact ⟨s, lv, ty, by rw [h1a, h1b, h1c, h1d, Nat.add_zero], hz, hs⟩
        | _ => simp [hd] at h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨s, lv, ty, hd, hz, hs⟩ := enumOk_sound cs (i0 + 1) h2 i c hi
      have e : i0 + 1 + i = i0 + (i + 1) := by omega
      rw [e] at hd
      exact ⟨s, lv, ty, hd, hz, hs⟩

/-! ## One instance, and the certificate -/

/-- **One instance resolves in the program as its shape says** (`ConstOk`, decided). -/
def entryOk (p : Program) (cert : Cert) (c : CId) (ls : Levels) (σ : Shape) : Bool :=
  match p.table.resolveOf c with
  | some (.prim op) =>
    if op.isPredicate then predOk p cert op σ
    else decide (σ = arrows (List.replicate op.arity .nat) .nat)
  | some (.eqn _ body) => decide (σ ∈ synth cert.insts ls [] body (some σ))
  | some (.csimp g us _) => decide ((g, us.map (evalUniv ls), σ) ∈ cert.insts)
  | some (.case r) =>
    match p.decl? r with
    | some (.recr _ _ _ np _ nmin ni ind _ _) =>
      isOrdinary (p.table.recKindOf r) && casesOk p cert σ ind np nmin ni
    | _ => false
  | some (.word _ _ _) => false
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => decide (σ ∈ synth cert.insts ls [] v (some σ))
    | some (.ctor _ _ _ _ np nf _) => zeroOk p c np nf σ || succOk p c np nf σ || enumCtorOk cert c σ
    | some (.recr _ _ _ np nmot nmin ni ind rules _) =>
      isOrdinary (p.table.recKindOf c) && recrOk p cert ls σ ind np nmot nmin ni rules
    | _ => false

theorem entryOk_sound {p : Program} {cert : Cert} {c : CId} {ls : Levels} {σ : Shape}
    (h : entryOk p cert c ls σ = true) : ConstOk p cert.sig c ls σ := by
  unfold entryOk at h
  cases hres : p.table.resolveOf c with
  | some res =>
    cases res with
    | prim op =>
      simp only [hres] at h
      by_cases hp : op.isPredicate = true
      · simp only [hp, ↓reduceIte] at h
        obtain ⟨σs, τ, hh, rfl⟩ := predOk_sound (ls := ls) hp h
        exact .head (.prim hres) hh
      · have hp' : op.isPredicate = false := by simpa using hp
        simp only [hp', Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h
        subst h
        exact .head (.prim hres) (.prim op ls hp')
    | csimp g us thm =>
      simp only [hres, decide_eq_true_eq] at h
      exact .body (.csimp hres) (.const h)
    | eqn thm body =>
      simp only [hres, decide_eq_true_eq] at h
      exact .body (.eqn hres) (synth_sound cert ls _ _ _ _ h)
    | case r =>
      simp only [hres] at h
      cases hd : p.decl? r with
      | none => simp [hd] at h
      | some d =>
        cases d with
        | recr s kk lv np nmot nmin ni ind rules ty =>
          simp only [hd, Bool.and_eq_true] at h
          obtain ⟨hk, hc⟩ := h
          obtain ⟨σs, τ, hh, rfl⟩ :=
            casesOk_sound (ls := ls) hres hd (isOrdinary_sound hk) hc
          exact .head (.cases hres) hh
        | _ => simp [hd] at h
    | word w op thm => simp [hres] at h
  | none =>
    simp only [hres] at h
    cases hd : p.decl? c with
    | none => simp [hd] at h
    | some d =>
      cases d with
      | defn kind safety lvls ty v =>
        cases kind <;> cases safety <;>
          simp only [hd, Bool.false_eq_true, decide_eq_true_eq] at h
        exact .body (.defn hres hd) (synth_sound cert ls _ _ _ _ h)
      | ctor s lv ind cidx np nf ty =>
        simp only [hd, Bool.or_eq_true] at h
        rcases h with (hz | hs) | he
        · simp only [zeroOk, Bool.and_eq_true, decide_eq_true_eq] at hz
          obtain ⟨⟨⟨h1, h2⟩, hz'⟩, h3⟩ := hz
          rw [h1, h2] at hd
          subst h3
          exact .zero hres hd hz'
        · simp only [succOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
          obtain ⟨⟨⟨⟨h1, h2⟩, hs'⟩, hz'⟩, h3⟩ := hs
          rw [h1, h2] at hd
          subst h3
          exact .head (.ctor hres hd) (.succ c ls s lv ind cidx ty hd hz' hs')
        · obtain ⟨⟨I, cs⟩, -, he'⟩ := List.any_eq_true.1 he
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he'
          obtain ⟨⟨hI, hc⟩, h3⟩ := he'
          subst h3
          exact .enumCtor hres hI hc
      | recr s kk lv np nmot nmin ni ind rules ty =>
        simp only [hd, Bool.and_eq_true] at h
        obtain ⟨hk, hr⟩ := h
        obtain ⟨σs, τ, hh, rfl⟩ := recrOk_sound (ls := ls) hd (isOrdinary_sound hk) hr
        exact .head (.recr hres hd) hh
      | _ => simp [hd] at h

/-- **The check**: every instance resolves as its shape says, and every enumeration's
constructors are as listed. -/
def certOk (p : Program) (cert : Cert) : Bool :=
  (cert.insts.all fun e => entryOk p cert e.1 e.2.1 e.2.2) &&
    (cert.enums.all fun e => enumOk p e.1 0 e.2)

theorem sigOk_of_cert {p : Program} {cert : Cert} (h : certOk p cert = true) :
    SigOk p cert.sig := by
  unfold certOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hi, he⟩ := h
  refine ⟨fun c ls σ hc => entryOk_sound (List.all_eq_true.1 hi (c, ls, σ) hc),
    fun I cs hI i c hic => ?_⟩
  have hmem := mem_of_lookupEnum _ _ _ hI
  obtain ⟨s, lv, ty, hd, hz, hs⟩ :=
    enumOk_sound cs 0 (List.all_eq_true.1 he (I, cs) hmem) i c hic
  rw [Nat.zero_add] at hd
  exact ⟨s, lv, ty, hd, hz, hs⟩

/-! ## The discharge, from the decision -/

/-- **M1 as a decision, at a `Nat` root.** A certificate that passes `certOk` on the
checked source and lists the instance `Nat → … → Nat → Nat` for root `r`'s constant,
at a root read back as `Nat` (or not read back): the viewed source goes wrong at no
clock on the root's inputs. -/
theorem neverWrong_of_cert_nat {f : Recheck.Front} {cert : Cert}
    (h : certOk f.src cert = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat)
    (hc : (c, ([] : Levels), arrows (List.replicate ns.length .nat) .nat) ∈ cert.insts)
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) :
    NeverWrong f.source (r, ns) :=
  neverWrong_of_shape (sig := cert.sig) (ρ := .nat) (sigOk_of_cert h) hroot ns hc (view_nat_ok hty)

/-- **M1 as a decision, at an enumeration root.** As `neverWrong_of_cert_nat`, with
the root's result an enumeration of the certificate each of whose constructors the
root's view reads back (finitely many evaluations of the view). -/
theorem neverWrong_of_cert_enum {f : Recheck.Front} {cert : Cert}
    (h : certOk f.src cert = true) {r : Nat} {addr : Ixon.Address} {c : CId}
    (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat) {B : CId} {cs : List CId}
    (hc : (c, ([] : Levels), arrows (List.replicate ns.length .nat) (.enum B)) ∈ cert.insts)
    (hB : lookupEnum cert.enums B = some cs)
    (hcs : ∀ c', c' ∈ cs → (IxCC.Lam.Erase.Input.ofProgram f.src f.checked).lvls c' = 0 ∧
      f.view r (Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c' [] [] []) :
          Lang.Val CheckedProgram)) ≠ none) :
    NeverWrong f.source (r, ns) :=
  neverWrong_of_shape (sig := cert.sig) (ρ := .enum B) (sigOk_of_cert h) hroot ns hc
    (view_enum_ok (sig := cert.sig) hB hcs)

end IxCC.Correct.Shape1
