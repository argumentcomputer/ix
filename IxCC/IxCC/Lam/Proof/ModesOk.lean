import IxCC.Lam.ModesOk
import IxCC.Src.Proof.NatMap
import IxCC.Lam.Proof.Program

/-! # `ModesOk` as a proposition

`Lam.ModesOk P` is decided by a checker on fuel (`ModesOk.run`). This module
states what the checker establishes as inductive propositions without fuel
(`ModesOk.TermOk`, `ArgsOk`, `NameArgOk`, and `Lam.ModesOkSpec` for a
program) and proves the checker sound against them (`ModesOk.run_sound`,
`modesOk_sound`): a `name` binder's dispatch signature is the one modes list
of every spine it heads; a spine headed by a global or a `name` variable
passes each argument with its binder's mode and covers every `name` binder;
a `name` argument whose binder's signature has a `name` is a forwarded minor
with that signature or a λ-telescope whose leading modes are the signature;
every other λ and application is strict (M2.2). -/

set_option autoImplicit false

namespace IxCC.Lam

namespace ModesOk

open IxCC.Src (NatMap)

/-! ## The propositions -/

/-- `sig` is the dispatch signature of the binder at level `lvl` of a body
under `d` binders: every spine it heads passes `sig` (none: `[]`). -/
def SigSpec (lvl d : Nat) (body : Term) (sig : List Mode) : Prop :=
  match body.dispatches lvl d false with
  | [] => sig = []
  | s :: rest => s = sig ∧ ∀ x ∈ rest, x = sig

/-- The kinds of a telescope's binders (outermost first) over depth `d`: a
`strict` binder holds a value, a `name` binder a thunk with its dispatch
signature. -/
def KindsSpec (ms : List Mode) (d : Nat) (body : Term) (kinds : List Kind) : Prop :=
  kinds.length = ms.length ∧ ∀ i m, ms[i]? = some m →
    (m = .strict → kinds[i]? = some .strict) ∧
    (m = .name → ∃ sig, kinds[i]? = some (.name sig) ∧ SigSpec (d + i) (d + ms.length) body sig)

/-- The signature list of a telescope's kinds. -/
def sigsOf (kinds : List Kind) : List (List Mode) :=
  kinds.map fun
    | .strict => []
    | .name s => s

mutual

/-- A term in a plain position under variable kinds `env` (innermost first),
with the globals' telescopes `G`. -/
inductive TermOk (G : NatMap GInfo) : List Kind → Term → Prop
  | varStrict {env : List Kind} {i : Nat} : env[i]? = some .strict → TermOk G env (.var i)
  | varName {env : List Kind} {i : Nat} {sig : List Mode} :
      env[i]? = some (.name sig) → hasName sig = false → TermOk G env (.var i)
  | glob {env : List Kind} {g : GlobalId} :
      hasName (((G.get? g).map (·.tele)).getD []) = false → TermOk G env (.glob g)
  | lam {env : List Kind} {m : Mode} {c : Ixon.V3.BinderContract} {b : Term} :
      m = .strict → TermOk G (.strict :: env) b → TermOk G env (.lam m c b)
  /-- A spine headed by a global: its telescope's modes and signatures. -/
  | appGlob {env : List Kind} {f a : Term} {m : Mode} {g : GlobalId}
      {args : List (Term × Mode)} :
      (Term.app f a m).spine = (.glob g, args) →
      covered ((G.get? g).getD {}).tele args.length = true →
      ArgsOk G env ((G.get? g).getD {}).tele ((G.get? g).getD {}).sigs 0 args →
      TermOk G env (.app f a m)
  /-- A spine headed by a `name` variable: its signature. -/
  | appName {env : List Kind} {f a : Term} {m : Mode} {i : Nat} {sig : List Mode}
      {args : List (Term × Mode)} :
      (Term.app f a m).spine = (.var i, args) → env[i]? = some (.name sig) →
      covered sig args.length = true → ArgsOk G env sig [] 0 args → TermOk G env (.app f a m)
  | appStrict {env : List Kind} {f a : Term} {m : Mode} {i : Nat} {args : List (Term × Mode)} :
      (Term.app f a m).spine = (.var i, args) → env[i]? = some .strict →
      ArgsOk G env [] [] 0 args → TermOk G env (.app f a m)
  /-- Any other head, applied strictly. -/
  | appOther {env : List Kind} {f a : Term} {m : Mode} {h : Term} {args : List (Term × Mode)} :
      (Term.app f a m).spine = (h, args) → (∀ g, h ≠ .glob g) → (∀ i, h ≠ .var i) →
      TermOk G env h → ArgsOk G env [] [] 0 args → TermOk G env (.app f a m)
  | letE {env : List Kind} {c : Ixon.V3.LetContract} {v b : Term} :
      TermOk G env v → TermOk G (.strict :: env) b → TermOk G env (.letE c v b)
  | con {env : List Kind} {k : Key.CtorKey} {fs : List Term} :
      (∀ t ∈ fs, TermOk G env t) → TermOk G env (.con k fs)
  | prim {env : List Kind} {p : Prim} {fs : List Term} :
      (∀ t ∈ fs, TermOk G env t) → TermOk G env (.prim p fs)
  | case {env : List Kind} {s : Term} {alts : List Alt} {dflt : Option Term} :
      TermOk G env s → (∀ a ∈ alts, TermOk G (List.replicate a.arity .strict ++ env) a.body) →
      (∀ t ∈ dflt, TermOk G env t) → TermOk G env (.case s alts dflt)
  | proj {env : List Kind} {k : Key.CtorKey} {i : Nat} {s : Term} :
      TermOk G env s → TermOk G env (.proj k i s)
  | tick {env : List Kind} {t : Term} : TermOk G env t → TermOk G env (.tick t)
  | lit {env : List Kind} {l : Lit} : TermOk G env (.lit l)
  | box {env : List Kind} : TermOk G env .box
  | trap {env : List Kind} : TermOk G env .trap

/-- A spine's arguments from position `i`, for a head whose binders have
modes `tele` and signatures `sigs`. -/
inductive ArgsOk (G : NatMap GInfo) :
    List Kind → List Mode → List (List Mode) → Nat → List (Term × Mode) → Prop
  | nil {env : List Kind} {tele : List Mode} {sigs : List (List Mode)} {i : Nat} :
      ArgsOk G env tele sigs i []
  | strict {env : List Kind} {tele : List Mode} {sigs : List (List Mode)} {i : Nat} {a : Term}
      {rest : List (Term × Mode)} :
      (expected tele sigs i).1 = .strict → TermOk G env a → ArgsOk G env tele sigs (i + 1) rest →
      ArgsOk G env tele sigs i ((a, .strict) :: rest)
  | name {env : List Kind} {tele : List Mode} {sigs : List (List Mode)} {i : Nat} {a : Term}
      {rest : List (Term × Mode)} :
      (expected tele sigs i).1 = .name → NameArgOk G env (expected tele sigs i).2 a →
      ArgsOk G env tele sigs (i + 1) rest → ArgsOk G env tele sigs i ((a, .name) :: rest)

/-- A `name` argument for a binder with dispatch signature `sig`. -/
inductive NameArgOk (G : NatMap GInfo) : List Kind → List Mode → Term → Prop
  | plain {env : List Kind} {sig : List Mode} {a : Term} :
      hasName sig = false → TermOk G env a → NameArgOk G env sig a
  /-- A forwarded minor binder with the same signature. -/
  | fwd {env : List Kind} {sig : List Mode} {i : Nat} :
      hasName sig = true → env[i]? = some (.name sig) → NameArgOk G env sig (.var i)
  /-- A minor λ-telescope: leading modes the signature, then strict ones; its
  own `name` binders (IH binders) are not dispatched by name. -/
  | tele {env : List Kind} {sig : List Mode} {m : Mode} {c : Ixon.V3.BinderContract} {b : Term}
      {kinds : List Kind} :
      hasName sig = true →
      (Term.lam m c b).telescope.1.take sig.length = sig →
      Mode.name ∉ (Term.lam m c b).telescope.1.drop sig.length →
      KindsSpec (Term.lam m c b).telescope.1 env.length (Term.lam m c b).telescope.2 kinds →
      (∀ s, Kind.name s ∈ kinds → hasName s = false) →
      TermOk G (kinds.reverse ++ env) (Term.lam m c b).telescope.2 →
      NameArgOk G env sig (.lam m c b)

end

/-- A global's telescope and its kinds. -/
def InfoSpec (body : Term) (gi : GInfo) (kinds : List Kind) : Prop :=
  gi.tele = body.telescope.1 ∧ KindsSpec gi.tele 0 body.telescope.2 kinds ∧ gi.sigs = sigsOf kinds

end ModesOk

open ModesOk in
/-- **`ModesOk` as a proposition**: with some table `G` of the globals'
telescopes, every global's telescope has its kinds (a `name` binder only in
a `byName` or `r⋆` global), and its body under the telescope is `TermOk`. -/
def ModesOkSpec (P : Program) : Prop :=
  ∃ G : Src.NatMap GInfo, ∀ g gl, P.global? g = some gl → g < P.size →
    ∃ gi kinds, G.get? g = some gi ∧ InfoSpec gl.body gi kinds ∧
      (hasName gi.tele = true → (∃ c q, gl.key = .byName c q) ∨ ∃ r q, gl.key = .recStar r q) ∧
      TermOk G kinds.reverse gl.body.telescope.2

namespace ModesOk

open IxCC.Src (NatMap)

/-! ## Soundness of the checker -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapError_ok {ε ε' α : Type} {x : Except ε α} {f : ε → ε'} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => cases h; rfl

theorem sigOf_sound {lvl d : Nat} {body : Term} {sig : List Mode}
    (h : sigOf lvl d body = .ok sig) : SigSpec lvl d body sig := by
  unfold sigOf at h
  unfold SigSpec
  split at h
  · next e => rw [e]; cases h; rfl
  · next s rest e =>
    rw [e]
    split at h
    · next hall =>
      cases h
      refine ⟨rfl, fun x hx => ?_⟩
      have := List.all_eq_true.1 hall x hx
      exact (beq_iff_eq.1 this)
    · cases h

theorem mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ (i : Nat) x, xs[i]? = some x → ∃ y, ys[i]? = some y ∧ f x = .ok y
  | [], ys, h => by
    rw [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun _ _ h => by simp at h⟩
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h'⟩ := bind_ok h
    obtain ⟨ys', hys, h''⟩ := bind_ok h'
    cases h''
    obtain ⟨hl, hi⟩ := mapM_ok hys
    refine ⟨by simp [hl], fun i z hz => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
      subst hz
      exact ⟨y, rfl, hy⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hz ⊢
      exact hi i z hz

theorem teleKinds_sound {ms : List Mode} {d : Nat} {body : Term} {kinds : List Kind}
    (h : teleKinds ms d body = .ok kinds) : KindsSpec ms d body kinds := by
  unfold teleKinds at h
  obtain ⟨hl, hk⟩ := mapM_ok h
  refine ⟨by simpa using hl, fun i m hm => ?_⟩
  have hz : (ms.zipIdx)[i]? = some (m, i) := by
    rw [List.getElem?_zipIdx, hm]
    simp
  obtain ⟨y, hy, hf⟩ := hk i _ hz
  dsimp only at hf
  cases m with
  | strict =>
    cases hf
    exact ⟨fun _ => hy, fun h => Mode.noConfusion h⟩
  | name =>
    obtain ⟨sig, hs, e⟩ := bind_ok hf
    cases e
    refine ⟨fun h => Mode.noConfusion h, fun _ => ⟨sig, hy, ?_⟩⟩
    simpa using sigOf_sound hs

theorem info_sound {t : Term} {gi : GInfo} {kinds : List Kind} (h : info t = .ok (gi, kinds)) :
    InfoSpec t gi kinds := by
  unfold info at h
  generalize ht : t.telescope = tb at h
  obtain ⟨ms, body⟩ := tb
  dsimp only at h
  obtain ⟨k, hk, e⟩ := bind_ok h
  cases e
  refine ⟨by rw [ht], ?_, rfl⟩
  rw [ht]
  exact teleKinds_sound hk

variable (G : NatMap GInfo)

theorem ite_ok {c : Bool} {m : String} {x : Except String Unit}
    (h : (if c = true then Except.error m else x) = .ok ()) : c = false ∧ x = .ok () := by
  cases c with
  | true => cases h
  | false => exact ⟨rfl, h⟩

mutual

theorem check_sound : ∀ (fuel : Nat) (env : List Kind) (t : Term),
    check G fuel env t = .ok () → TermOk G env t
  | 0, _, _, h => by simp [check] at h
  | fuel + 1, env, .var i, h => by
    simp only [check] at h
    split at h
    · next sig hs =>
      exact .varName hs (ite_ok h).1
    · next hs => exact .varStrict hs
    · cases h
  | fuel + 1, env, .glob g, h => by
    simp only [check] at h
    exact .glob (ite_ok h).1
  | fuel + 1, env, .lam m c b, h => by
    simp only [check] at h
    cases m with
    | name => cases h
    | strict => exact .lam rfl (check_sound fuel _ b h)
  | fuel + 1, env, .app f a m, h => by
    simp only [check] at h
    generalize hs : (Term.app f a m).spine = sp at h
    obtain ⟨hd, args⟩ := sp
    dsimp only at h
    cases hd with
    | glob g =>
      dsimp only at h
      obtain ⟨hc, h'⟩ := ite_ok (c := !covered _ _) h
      exact .appGlob hs (by simpa using hc) (checkArgs_sound fuel env _ _ 0 args h')
    | var i =>
      dsimp only at h
      split at h
      · next sig he =>
        obtain ⟨hc, h'⟩ := ite_ok (c := !covered _ _) h
        exact .appName hs he (by simpa using hc) (checkArgs_sound fuel env _ _ 0 args h')
      · next he => exact .appStrict hs he (checkArgs_sound fuel env _ _ 0 args h)
      · cases h
    | _ =>
      dsimp only at h
      obtain ⟨_, h₁, h₂⟩ := bind_ok h
      exact .appOther hs (fun _ e => Term.noConfusion e) (fun _ e => Term.noConfusion e)
        (check_sound fuel env _ h₁) (checkArgs_sound fuel env _ _ 0 args h₂)
  | fuel + 1, env, .letE c v b, h => by
    simp only [check] at h
    obtain ⟨_, h₁, h₂⟩ := bind_ok h
    exact .letE (check_sound fuel env v h₁) (check_sound fuel _ b h₂)
  | fuel + 1, env, .con k fs, h => by
    simp only [check] at h
    exact .con (checkList_sound fuel env fs h)
  | fuel + 1, env, .prim p fs, h => by
    simp only [check] at h
    exact .prim (checkList_sound fuel env fs h)
  | fuel + 1, env, .case s alts dflt, h => by
    simp only [check] at h
    obtain ⟨_, h₁, h₂⟩ := bind_ok h
    obtain ⟨_, h₃, h₄⟩ := bind_ok h₂
    refine .case (check_sound fuel env s h₁) (checkAlts_sound fuel env alts h₃) fun t ht => ?_
    cases dflt with
    | none => cases ht
    | some d =>
      cases ht
      exact check_sound fuel env _ h₄
  | fuel + 1, env, .proj k i s, h => by
    simp only [check] at h
    exact .proj (check_sound fuel env s h)
  | fuel + 1, env, .tick t, h => by
    simp only [check] at h
    exact .tick (check_sound fuel env t h)
  | fuel + 1, env, .lit l, _ => .lit
  | fuel + 1, env, .box, _ => .box
  | fuel + 1, env, .trap, _ => .trap

theorem checkList_sound : ∀ (fuel : Nat) (env : List Kind) (ts : List Term),
    checkList G fuel env ts = .ok () → ∀ t ∈ ts, TermOk G env t
  | 0, _, _, h => by simp [checkList] at h
  | fuel + 1, _, [], _ => fun _ h => by cases h
  | fuel + 1, env, t :: ts, h => by
    simp only [checkList] at h
    obtain ⟨_, h₁, h₂⟩ := bind_ok h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact check_sound fuel env x h₁
    · exact checkList_sound fuel env ts h₂ x hx

theorem checkAlts_sound : ∀ (fuel : Nat) (env : List Kind) (alts : List Alt),
    checkAlts G fuel env alts = .ok () →
      ∀ a ∈ alts, TermOk G (List.replicate a.arity .strict ++ env) a.body
  | 0, _, _, h => by simp [checkAlts] at h
  | fuel + 1, _, [], _ => fun _ h => by cases h
  | fuel + 1, env, .mk k n b :: as, h => by
    simp only [checkAlts] at h
    obtain ⟨_, h₁, h₂⟩ := bind_ok h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact check_sound fuel _ b h₁
    · exact checkAlts_sound fuel env as h₂ x hx

theorem checkArgs_sound : ∀ (fuel : Nat) (env : List Kind) (tele : List Mode)
    (sigs : List (List Mode)) (i : Nat) (args : List (Term × Mode)),
    checkArgs G fuel env tele sigs i args = .ok () → ArgsOk G env tele sigs i args
  | 0, _, _, _, _, _, h => by simp [checkArgs] at h
  | fuel + 1, _, _, _, _, [], _ => .nil
  | fuel + 1, env, tele, sigs, i, (a, m) :: rest, h => by
    simp only [checkArgs] at h
    generalize he : expected tele sigs i = e at h
    obtain ⟨want, sig⟩ := e
    dsimp only at h
    split at h
    · cases h
    · next hw =>
      have hm : m = want := by simpa using hw
      subst hm
      cases m with
      | strict =>
        split at h
        · next hc => exact absurd hc (by decide)
        · obtain ⟨_, h₃, h₄⟩ := bind_ok h
          exact .strict (by rw [he]) (check_sound fuel env a h₃)
            (checkArgs_sound fuel env tele sigs (i + 1) rest h₄)
      | name =>
        split at h
        · obtain ⟨_, h₃, h₄⟩ := bind_ok h
          exact .name (by rw [he]) (by rw [he]; exact checkNameArg_sound fuel env sig a h₃)
            (checkArgs_sound fuel env tele sigs (i + 1) rest h₄)
        · next hc => exact absurd rfl hc

theorem checkNameArg_sound : ∀ (fuel : Nat) (env : List Kind) (sig : List Mode) (a : Term),
    checkNameArg G fuel env sig a = .ok () → NameArgOk G env sig a
  | 0, _, _, _, h => by simp [checkNameArg] at h
  | fuel + 1, env, sig, a, h => by
    simp only [checkNameArg] at h
    cases hn : hasName sig with
    | false =>
      rw [hn] at h
      exact .plain hn (check_sound fuel env a h)
    | true =>
      simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases a with
      | var i =>
        dsimp only at h
        split at h
        · next sig' he =>
          split at h
          · next hs =>
            have : sig' = sig := by simpa using hs
            subst this
            exact .fwd hn he
          · cases h
        · cases h
      | lam m c b =>
        dsimp only at h
        generalize ht : (Term.lam m c b).telescope = tb at h
        obtain ⟨ms, body⟩ := tb
        dsimp only at h
        split at h
        · cases h
        · next hc =>
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
            List.any_eq_true, beq_iff_eq, not_exists, not_and] at hc
          split at h
          · cases h
          · next kinds hk =>
            split at h
            · cases h
            · next hany =>
              refine .tele hn (by rw [ht]; exact hc.1) (by rw [ht]; exact fun hm => hc.2 _ hm rfl)
                (by rw [ht]; exact teleKinds_sound hk) (fun s hs => ?_)
                (by rw [ht]; exact check_sound fuel _ body h)
              simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
              exact hany _ hs
      | _ => cases h

end

theorem forIn_facts {ε α : Type} {f : α → Unit → Except ε (ForInStep Unit)} {Q : α → Prop}
    (hf : ∀ x r, f x () = .ok r → r = .yield () ∧ Q x) :
    ∀ {xs : List α}, forIn xs () f = .ok () → ∀ x ∈ xs, Q x
  | [], _ => fun _ h => by cases h
  | x :: xs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h'⟩ := bind_ok h
    obtain ⟨rfl, hq⟩ := hf x r hr
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hq
    · exact forIn_facts hf h' y hy

theorem run_sound {P : Program} (h : run P = .ok ()) : ModesOkSpec P := by
  unfold run at h
  obtain ⟨infos, hinfos, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, hfor, -⟩ := bind_ok h
  have hfacts := forIn_facts (Q := fun x => ∃ gi kinds, info x.2.body = .ok (gi, kinds) ∧
      (hasName gi.tele = true → (∃ c q, x.2.key = .byName c q) ∨ ∃ r q, x.2.key = .recStar r q) ∧
      check (Src.NatMap.ofList infos) fuel kinds.reverse x.2.body.telescope.2 = .ok ())
    (fun x r hr => by
      obtain ⟨⟨gi, kinds⟩, hinfo, hr⟩ := bind_ok hr
      have hinfo := mapError_ok hinfo
      split at hr
      · next c q hk =>
        obtain ⟨_, hc, hr⟩ := bind_ok hr
        cases hr
        exact ⟨rfl, gi, kinds, hinfo, fun _ => .inl ⟨c, q, hk⟩, mapError_ok hc⟩
      · next r q hk =>
        obtain ⟨_, hc, hr⟩ := bind_ok hr
        cases hr
        exact ⟨rfl, gi, kinds, hinfo, fun _ => .inr ⟨r, q, hk⟩, mapError_ok hc⟩
      · next hb hr' =>
        split at hr
        · obtain ⟨_, ht, _⟩ := bind_ok hr
          cases ht
        · next hn =>
          obtain ⟨_, hc, hr⟩ := bind_ok hr
          cases hr
          exact ⟨rfl, gi, kinds, hinfo, fun e => absurd e hn, mapError_ok hc⟩) hfor
  obtain ⟨hlen, hidx⟩ := mapM_ok hinfos
  have hkeys : infos.map (·.1) = P.globalList.map (·.1) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map]
    cases hx : P.globalList[i]? with
    | none =>
      have : infos[i]? = none := by
        rw [List.getElem?_eq_none_iff] at hx ⊢
        omega
      rw [this]
      rfl
    | some x =>
      obtain ⟨y, hy, hf⟩ := hidx i x hx
      rw [hy]
      obtain ⟨g, gl⟩ := x
      obtain ⟨⟨gi, k⟩, _, hf⟩ := bind_ok hf
      cases hf
      rfl
  refine ⟨Src.NatMap.ofList infos, fun g gl hg hlt => ?_⟩
  have hmem : (g, gl) ∈ P.globalList := Program.mem_globalList.2 ⟨hlt, hg⟩
  obtain ⟨gi, kinds, hinfo, hkey, hcheck⟩ := hfacts _ hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  obtain ⟨y, hy, hf⟩ := hidx i _ hi
  obtain ⟨⟨gi', k'⟩, hinfo', hf⟩ := bind_ok hf
  cases hf
  rw [mapError_ok hinfo'] at hinfo
  cases hinfo
  have hin : (g, gi) ∈ infos := List.mem_of_getElem? hy
  refine ⟨gi, kinds, Src.NatMap.get?_ofList (by rw [hkeys]; exact Program.globalList_keys_nodup P)
    hin, info_sound (mapError_ok hinfo'), hkey, check_sound _ fuel _ _ hcheck⟩

end ModesOk

/-- **The checker is sound**: a program `modesOk` accepts meets `ModesOkSpec`. -/
theorem modesOk_sound {P : Program} (h : ModesOk P) : ModesOkSpec P := by
  unfold ModesOk modesOk at h
  cases hr : ModesOk.run P with
  | error e => rw [hr] at h; cases h
  | ok u => exact ModesOk.run_sound hr

namespace ModesOk

end ModesOk

end IxCC.Lam
