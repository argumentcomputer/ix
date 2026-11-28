import Ix.Cert.Aggr.MonolithicRom
import Ix.Cert.Compression.StarkShrinker
import Ix.Cert.Compression.StarkShrinkerZk

/-! # Monolithic ROM & Native `Fp^3` STARK Shrinker (`v6` + `v6-zk`) Audit Surface

Pins all 58 headline theorem signatures and axiom dependencies across:
- `Ix.Cert.Aggr.MonolithicRom` (straight-line single-oracle multi-node extraction,
  eliminating the `-log₂ M` union-bound penalty),
- `Ix.Cert.Compression.StarkShrinker` (Endpoint 1a: Native `Fp^3` `v6` transparent STARK Shrinker),
- `Ix.Cert.Compression.StarkShrinkerZk` (Endpoint 1b: Native `Fp^3` `v6-zk` hiding STARK Shrinker).

Every theorem is verified by `#guard_msgs` to depend strictly on standard Lean axioms
(`⊆ [propext, Classical.choice, Quot.sound]`), with ZERO `sorry`, ZERO custom `axiom`,
ZERO `native_decide`, ZERO `bv_decide`, and ZERO curve/SRS/pairing assumptions.
-/


-- Section 1: MonolithicRom
/--
info: @Ix.Cert.Aggr.MonolithicRom.monolithic_doomed_of_supports : ∀ {Inst Msg : Type u_1} {Chal : ℕ → Type u_2}
  {X' : Type u_3} {Y' : X' → Type u_2} {r : Inst → ℕ}
  {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop}
  {l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')},
  ¬CertiFri.Oracle.HasBad (fun x => Ix.Cert.Aggr.MonolithicRom.GlobalFlip r doomed) l →
    ∀ (inst : Inst),
      doomed inst 0 CertiFri.Oracle.Transcript.nil →
        ∀ {i : ℕ},
          i ≤ r inst →
            ∀ (t : CertiFri.Oracle.Transcript Msg Chal i),
              Ix.Cert.Aggr.MonolithicRom.MultiSupports inst t l → doomed inst i t
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_doomed_of_supports
/--
info: @Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound : ∀ {Inst Msg : Type u_1} {Chal : ℕ → Type u_2}
  {X' : Type u_3} {Y' : X' → Type u_2} [inst : DecidableEq Inst] [inst_1 : DecidableEq Msg]
  [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X'] [inst_4 : (i : ℕ) → Fintype (Chal i)]
  [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)] [∀ (x : X'), Nonempty (Y' x)] {D : Type u_4}
  [inst_8 : Fintype D] [Nonempty D] {r : Inst → ℕ}
  {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ} {εmax c : ℝ},
  Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
    (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
      0 ≤ εmax →
        0 ≤ c →
          ∀
            (hashBad :
              CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                  Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
            (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                List.dlookup x l = none →
                  CertiFri.Oracle.FractionLE (hashBad l x) (2 * c * ↑(List.length l) / ↑(Fintype.card D))) →
              ∀ {A : Type u_5} {B : Type u_6} {M : ℕ}
                (adv : CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A) {Q M_verif : ℕ},
                adv.QueryBound Q →
                  ∀ (verifyAll : A → CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') B),
                    (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                      ∀
                        (NodeForges :
                          B → Fin M → CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') → Prop),
                        (∀ (b : B) (l' : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')),
                            (adv.bind verifyAll).Outcome [] b l' →
                              (∃ k, NodeForges b k l') →
                                ¬CertiFri.Oracle.HasBad hashBad l' →
                                  ∃ inst t,
                                    doomed inst 0 CertiFri.Oracle.Transcript.nil ∧
                                      Ix.Cert.Aggr.MonolithicRom.MultiSupports inst t l' ∧ ¬doomed inst (r inst) t) →
                          CertiFri.Oracle.OracleComp.prob (fun b l' => ∃ k, NodeForges b k l') (adv.bind verifyAll) [] ≤
                            ↑(Q + M_verif) * εmax + c * ↑(Q + M_verif) ^ 2 / ↑(Fintype.card D)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound
/--
info: @Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound_collision : ∀ {Inst Msg : Type u_1} {Chal : ℕ → Type u_2}
  {X' : Type u_3} {Y' : X' → Type u_2} [inst : DecidableEq Inst] [inst_1 : DecidableEq Msg]
  [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X'] [inst_4 : (i : ℕ) → Fintype (Chal i)]
  [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)] [∀ (x : X'), Nonempty (Y' x)] {D : Type u_4}
  [inst_8 : Fintype D] [Nonempty D] {r : Inst → ℕ}
  {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ} {εmax : ℝ},
  Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
    (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
      0 ≤ εmax →
        ∀ (obs : (x : X') → Y' x → Option D),
          (∀ (x : X') (z : D), CertiFri.Oracle.FractionLE (fun y => obs x y = some z) (1 / ↑(Fintype.card D))) →
            ∀ {A : Type u_5} {B : Type u_6} {M : ℕ}
              (adv : CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A) {Q M_verif : ℕ},
              adv.QueryBound Q →
                ∀ (verifyAll : A → CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') B),
                  (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                    ∀
                      (NodeForges :
                        B → Fin M → CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') → Prop),
                      (∀ (b : B) (l' : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')),
                          (adv.bind verifyAll).Outcome [] b l' →
                            (∃ k, NodeForges b k l') →
                              ¬CertiFri.Oracle.LogCollision (Ix.Cert.Aggr.MonolithicRom.liftMultiObs obs) l' →
                                ∃ inst t,
                                  doomed inst 0 CertiFri.Oracle.Transcript.nil ∧
                                    Ix.Cert.Aggr.MonolithicRom.MultiSupports inst t l' ∧ ¬doomed inst (r inst) t) →
                        CertiFri.Oracle.OracleComp.prob (fun b l' => ∃ k, NodeForges b k l') (adv.bind verifyAll) [] ≤
                          ↑(Q + M_verif) * εmax + 1 / 2 * ↑(Q + M_verif) ^ 2 / ↑(Fintype.card D)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound_collision
/--
info: @Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {rootStmt :
    Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt) {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type}
  {Y' : X' → Type} [inst : DecidableEq Inst] [inst_1 : DecidableEq Msg] [inst_2 : (i : ℕ) → DecidableEq (Chal i)]
  [inst_3 : DecidableEq X'] [inst_4 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)]
  [inst_6 : (x : X') → Fintype (Y' x)] [∀ (x : X'), Nonempty (Y' x)] {D : Type} [inst_8 : Fintype D] [Nonempty D]
  {r : Inst → ℕ} {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ}
  {εmax c : ℝ},
  Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
    (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
      0 ≤ εmax →
        0 ≤ c →
          ∀
            (hashBad :
              CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                  Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
            (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                List.dlookup x l = none →
                  CertiFri.Oracle.FractionLE (hashBad l x) (2 * c * ↑(List.length l) / ↑(Fintype.card D))) →
              ∀ {A B : Type} (adv : CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A)
                {Q M_verif : ℕ},
                adv.QueryBound Q →
                  ∀ (verifyAll : A → CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') B),
                    (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                      ∀
                        (NodeForges :
                          B →
                            Fin t.verificationCount →
                              CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') → Prop),
                        (∀ (b : B) (l' : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')),
                            (adv.bind verifyAll).Outcome [] b l' →
                              (∃ k, NodeForges b k l') →
                                ¬CertiFri.Oracle.HasBad hashBad l' →
                                  ∃ inst tr,
                                    doomed inst 0 CertiFri.Oracle.Transcript.nil ∧
                                      Ix.Cert.Aggr.MonolithicRom.MultiSupports inst tr l' ∧ ¬doomed inst (r inst) tr) →
                          CertiFri.Oracle.OracleComp.prob (fun b l' => ∃ k, NodeForges b k l') (adv.bind verifyAll) [] ≤
                              ↑(Q + M_verif) * εmax + c * ↑(Q + M_verif) ^ 2 / ↑(Fintype.card D) ∧
                            Aggr.AggrNodeHolds sem rootStmt ∧
                              (t.HasTreeCollision ∨
                                ∀ vp ∈ t.childProofs,
                                  ∃ proofBytes,
                                    Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound
/--
info: Ix.Cert.Aggr.MonolithicRom.goldilocksExt3_card_ge_two_pow_191 : 2 ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ 3
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.goldilocksExt3_card_ge_two_pow_191
/--
info: Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_rate_128 : ∀ (Q M_verif : ℕ),
  M_verif ≤ 2 ^ 20 →
    Q + M_verif ≤ 2 ^ 128 →
      ∀ {εmax : ℝ},
        εmax ≤ 1 / 2 / 2 ^ 128 →
          Ix.Cert.Aggr.MonolithicRom.monolithicRomBound Q M_verif εmax (3 / 2) (2 ^ 512) ≤ ↑(Q + M_verif) / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_rate_128
/--
info: Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_concrete_prob_128 : ∀ (Q M_verif : ℕ),
  M_verif ≤ 2 ^ 20 →
    Q + M_verif ≤ 2 ^ 127 →
      ∀ {εmax : ℝ},
        ↑(Q + M_verif) * εmax ≤ 1 / 2 / 2 ^ 128 →
          Ix.Cert.Aggr.MonolithicRom.monolithicRomBound Q M_verif εmax (3 / 2) (2 ^ 512) ≤ 1 / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_concrete_prob_128
/--
info: Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_field_128 : ∀ (Q M_verif : ℕ),
  Q ≤ 2 ^ 61 →
    M_verif ≤ 2 ^ 20 →
      Ix.Cert.Aggr.MonolithicRom.monolithicRomBound Q M_verif (1 / ↑CertiFri.P3.Goldilocks.order ^ 3) (3 / 2)
          (2 ^ 512) ≤
        1 / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_field_128
/--
info: Ix.Cert.Aggr.MonolithicRom.monolithic_strictly_tighter_than_union_bound : ∀ (M Q M_verif : ℕ),
  2 ≤ M → M_verif < (M - 1) * Q → ∀ {εmax : ℝ}, 0 < εmax → ↑(Q + M_verif) * εmax < ↑M * ↑Q * εmax
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_strictly_tighter_than_union_bound
/--
info: Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20 : ↑(2 ^ 20) * ↑(2 ^ 108) * (1 / 2 ^ 128) = 1 ∧
  Ix.Cert.Aggr.MonolithicRom.monolithicRomBound (2 ^ 108) (2 ^ 20) (1 / 2 ^ 128) (3 / 2) (2 ^ 512) < 1 / 2 ^ 19
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20
/--
info: Ix.Cert.Aggr.MonolithicRom.negControl_fp2_below_128 : CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128 ∧
  1 / 2 ^ 128 < 1 / ↑CertiFri.P3.Goldilocks.order ^ 2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.negControl_fp2_below_128
/--
info: Ix.Cert.Aggr.MonolithicRom.negControl_digest32_saturates_at_2_128 : 3 / 2 * (2 ^ 128) ^ 2 / 2 ^ 256 = 3 / 2 ∧
  1 < 3 / 2 * (2 ^ 128) ^ 2 / 2 ^ 256 ∧ 1 / 2 * (2 ^ 128) ^ 2 / 2 ^ 256 = 1 / 2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.negControl_digest32_saturates_at_2_128

-- Section 2: StarkShrinker (Endpoint 1a: v6)
/--
info: Ix.Cert.Compression.StarkShrinker.Blake3Domain.keyWords_injective : Function.Injective
  Ix.Cert.Compression.StarkShrinker.Blake3Domain.keyWords
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.Blake3Domain.keyWords_injective
/--
info: Ix.Cert.Compression.StarkShrinker.Blake3Domain.context_injective : Function.Injective
  Ix.Cert.Compression.StarkShrinker.Blake3Domain.context
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.Blake3Domain.context_injective
/--
info: @Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6_keyWords_ne_nonV6 : ∀
  {d₁ d₂ : Ix.Cert.Compression.StarkShrinker.Blake3Domain}, d₁.isV6 = true → d₂.isV6 = false → d₁.keyWords ≠ d₂.keyWords
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6_keyWords_ne_nonV6
/--
info: @Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6Zk_keyWords_ne_nonZk : ∀
  {d₁ d₂ : Ix.Cert.Compression.StarkShrinker.Blake3Domain}, d₁.isZk = true → d₂.isZk = false → d₁.keyWords ≠ d₂.keyWords
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6Zk_keyWords_ne_nonZk
/--
info: @Ix.Cert.Compression.StarkShrinker.starkShrinker_query_soundness_128 : ∀
  {regime : Ix.Cert.Compression.StarkShrinker.SoundnessRegime} {logBlowup numQueries queryPowBits : ℕ},
  Ix.Cert.Compression.StarkShrinker.v6QueryFloorOk regime logBlowup numQueries queryPowBits →
    Ix.Cert.Compression.StarkShrinker.shrinkerProximityTheta regime logBlowup ^ numQueries / 2 ^ queryPowBits ≤
      1 / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.starkShrinker_query_soundness_128
/--
info: Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128_ok : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
  Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128_ok
/--
info: Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2_ok : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
  Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2_ok
/--
info: Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb3_ok : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
  Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb3
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb3_ok
/--
info: Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb4_ok : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
  Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb4
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb4_ok
/--
info: @Ix.Cert.Compression.StarkShrinker.starkShrinker_publicBinding_injective : ∀
  {cfg : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6Config}
  {stmt : Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicStatement}
  {friPub₁ friPub₂ : List Ix.Cert.Compression.Foreign.GoldilocksF} {dig₁ dig₂ : Fin 8 → Ix.Cert.MultiStark.Fp},
  Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicBinding cfg stmt friPub₁ dig₁ →
    Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicBinding cfg stmt friPub₂ dig₂ →
      (∀ (i : Fin 8), friPub₁[↑i]? = friPub₂[↑i]?) ∧ dig₁ = dig₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.starkShrinker_publicBinding_injective
/--
info: Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128 : ∀
  (cfg : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6Config),
  Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk cfg →
    ∀ {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type} [inst : DecidableEq Inst]
      [inst_1 : DecidableEq Msg] [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X']
      [inst_4 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)]
      [∀ (x : X'), Nonempty (Y' x)] {D : Type} [inst_8 : Fintype D] [Nonempty D],
      Fintype.card D = 2 ^ (8 * cfg.digestBytes) →
        ∀ {r : Inst → ℕ} {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ}
          {εmax : ℝ},
          Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
            (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
              0 ≤ εmax →
                εmax ≤ 1 / 2 / 2 ^ 128 →
                  ∀
                    (hashBad :
                      CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                        (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                          Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
                    (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                        (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                        List.dlookup x l = none →
                          CertiFri.Oracle.FractionLE (hashBad l x)
                            (2 * (3 / 2) * ↑(List.length l) / ↑(Fintype.card D))) →
                      ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
                        (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
                        (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
                          ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
                            (wFri : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.GoldilocksF),
                            (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout).Satisfies friPub
                                wFri →
                              ∀
                                {sem :
                                  Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address
                                    Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
                                    Ix.DynamicLink.LinkedCircuitEntry}
                                {batchClaim :
                                  ℕ →
                                    Aggr.ValidatorMode Address →
                                      (Address → Prop) →
                                        (Address → Prop) →
                                          (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
                                {rootStmt :
                                  Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address
                                    Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
                                    Ix.DynamicLink.LinkedCircuitEntry}
                                (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
                                (stmt : Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicStatement)
                                (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp),
                                Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicBinding cfg stmt friPub
                                    outClaimDig →
                                  ∀ {A B : Type}
                                    (adv :
                                      CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A)
                                    {Q M_verif : ℕ},
                                    adv.QueryBound Q →
                                      ∀
                                        (verifyAll :
                                          A →
                                            CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')
                                              B),
                                        (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                                          M_verif ≤ 2 ^ 20 →
                                            Q + M_verif ≤ 2 ^ 128 →
                                              ∀
                                                (NodeForges :
                                                  B →
                                                    Fin (1 + t.verificationCount) →
                                                      CertiFri.Oracle.Log
                                                          (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                                                        Prop),
                                                ⋯ → ⋯
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128
/--
info: Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128 : ∀
  (cfg : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6Config),
  Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk cfg →
    ∀ {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type} [inst : DecidableEq Inst]
      [inst_1 : DecidableEq Msg] [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X']
      [inst_4 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)]
      [∀ (x : X'), Nonempty (Y' x)] {D : Type} [inst_8 : Fintype D] [Nonempty D],
      Fintype.card D = 2 ^ (8 * cfg.digestBytes) →
        ∀ {r : Inst → ℕ} {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ}
          {εmax : ℝ},
          Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
            (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
              0 ≤ εmax →
                ∀
                  (hashBad :
                    CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                      (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                        Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
                  (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                      (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                      List.dlookup x l = none →
                        CertiFri.Oracle.FractionLE (hashBad l x) (2 * (3 / 2) * ↑(List.length l) / ↑(Fintype.card D))) →
                    ∀ {A B : Type} {M : ℕ}
                      (adv : CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A)
                      {Q M_verif : ℕ},
                      adv.QueryBound Q →
                        ∀
                          (verifyAll :
                            A → CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') B),
                          (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                            M_verif ≤ 2 ^ 20 →
                              Q + M_verif ≤ 2 ^ 127 →
                                ↑(Q + M_verif) * εmax ≤ 1 / 2 / 2 ^ 128 →
                                  ∀
                                    (NodeForges :
                                      B →
                                        Fin M →
                                          CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') → Prop),
                                    (∀ (b : B)
                                        (l' : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')),
                                        (adv.bind verifyAll).Outcome [] b l' →
                                          (∃ k, NodeForges b k l') →
                                            ¬CertiFri.Oracle.HasBad hashBad l' →
                                              ∃ inst tr,
                                                doomed inst 0 CertiFri.Oracle.Transcript.nil ∧
                                                  Ix.Cert.Aggr.MonolithicRom.MultiSupports inst tr l' ∧
                                                    ¬doomed inst (r inst) tr) →
                                      CertiFri.Oracle.OracleComp.prob (fun b l' => ∃ k, NodeForges b k l')
                                          (adv.bind verifyAll) [] ≤
                                        1 / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128
/--
info: Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_v5 : ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
      (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
      { version := Ix.Cert.Compression.StarkShrinker.ProtocolVersion.v5, extDegree := __src.extDegree,
        digestBytes := __src.digestBytes, batching := __src.batching, regime := __src.regime,
        logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
        numCircuits := __src.numCircuits, leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
      (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
        batching := __src.batching, regime := __src.regime, logBlowup := __src.logBlowup,
        numQueries := __src.numQueries, queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits,
        leafDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.plain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest })
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_v5
/--
info: Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_fp2 : ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
      (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
      { version := __src.version, extDegree := 2, digestBytes := __src.digestBytes, batching := __src.batching,
        regime := __src.regime, logBlowup := __src.logBlowup, numQueries := __src.numQueries,
        queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
        compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_fp2
/--
info: Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_weak_params : ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
      (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := 32, batching := __src.batching,
        regime := __src.regime, logBlowup := __src.logBlowup, numQueries := __src.numQueries,
        queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
        compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
        (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
        { version := __src.version, extDegree := __src.extDegree, digestBytes := 48, batching := __src.batching,
          regime := __src.regime, logBlowup := __src.logBlowup, numQueries := __src.numQueries,
          queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
          compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
          pinnedVkDigest := __src.pinnedVkDigest }) ∧
    ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
          (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
          { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
            batching := Ix.Cert.Compression.StarkShrinker.FriBatchingMode.powers, regime := __src.regime,
            logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
            numCircuits := __src.numCircuits, leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
            transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
            pinnedVkDigest := __src.pinnedVkDigest }) ∧
      ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
            (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
            { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
              batching := __src.batching, regime := __src.regime, logBlowup := __src.logBlowup, numQueries := 159,
              queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
              compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain,
              vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest }) ∧
        ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
            (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2;
            { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
              batching := __src.batching, regime := __src.regime, logBlowup := __src.logBlowup, numQueries := 117,
              queryPowBits := __src.queryPowBits, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
              compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain,
              vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest })
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_weak_params
/--
info: Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_vk_mismatch : ∀
  (cfg : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6Config) (badVk : List UInt8),
  badVk ≠ cfg.pinnedVkDigest →
    ∀ (claim : Fin 8 → Ix.Cert.Compression.Foreign.GoldilocksF) (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
      (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp),
      ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicBinding cfg { vkDigest := badVk, claimDigest := claim }
          friPub outClaimDig
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_vk_mismatch
/--
info: Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_claim_mismatch : ∀
  (cfg : Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6Config)
  (stmt : Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicStatement)
  (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF) (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp) (i : Fin 8),
  Ix.Cert.Compression.Foreign.GoldilocksF.ofNat (ZMod.val (outClaimDig i)) ≠ stmt.claimDigest i →
    ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicBinding cfg stmt friPub outClaimDig
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_claim_mismatch

-- Section 3: StarkShrinkerZk (Endpoint 1b: v6-zk)
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.salted_merkle_binding_of_no_collision : ∀ {Row Salt D : Type}
  (hashLeaf : Row × Salt → D) (compress : D → D → D),
  Function.Injective hashLeaf →
    (∀ (l₁ r₁ l₂ r₂ : D), compress l₁ r₁ = compress l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂) →
      ∀ {idx : ℕ} {row₁ row₂ : Row} {salt₁ salt₂ : Salt} {path₁ path₂ : List D},
        path₁.length = path₂.length →
          Ix.Cert.Compression.StarkShrinkerZk.evalMerklePath compress idx (hashLeaf (row₁, salt₁)) path₁ =
              Ix.Cert.Compression.StarkShrinkerZk.evalMerklePath compress idx (hashLeaf (row₂, salt₂)) path₂ →
            row₁ = row₂ ∧ salt₁ = salt₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.salted_merkle_binding_of_no_collision
/--
info: Ix.Cert.Compression.StarkShrinkerZk.v6Zk_preprocessed_salt_context_distinct : ∀
  (d : Ix.Cert.Compression.StarkShrinker.Blake3Domain),
  some Ix.Cert.Compression.StarkShrinkerZk.PREPROCESSED_SALT_CONTEXT ≠ d.context
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.v6Zk_preprocessed_salt_context_distinct
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.v6Zk_domains_disjoint_from_v6_and_plain : ∀
  {dZk dOther : Ix.Cert.Compression.StarkShrinker.Blake3Domain},
  dZk.isZk = true → dOther.isZk = false → dZk.keyWords ≠ dOther.keyWords ∧ dZk.context ≠ dOther.context
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.v6Zk_domains_disjoint_from_v6_and_plain
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_agrees_on_trace : ∀ {K : Type u_1} [inst : Field K] (N : ℕ)
  (T₀ b : Polynomial K) (x : K), x ^ N = 1 → Polynomial.eval x (T₀ + (Polynomial.X ^ N - 1) * b) = Polynomial.eval x T₀
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_agrees_on_trace
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_natDegree_lt : ∀ {K : Type u_1} [inst : Field K] {N : ℕ},
  0 < N →
    ∀ {T₀ b : Polynomial K}, T₀.natDegree < N → b.natDegree < N → (T₀ + (Polynomial.X ^ N - 1) * b).natDegree < 2 * N
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_natDegree_lt
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_telescoping_sum : ∀ {K : Type u_1} [inst : Field K] (N q : ℕ),
  1 ≤ q →
    ∀ (c : Fin (2 * q) → Polynomial K) (ρ : Fin (2 * q - 1) → Polynomial K),
      ∑ k, Polynomial.X ^ (↑k * N) * Ix.Cert.Compression.StarkShrinkerZk.zkBlindedSlice N q c ρ k =
        ∑ k, Polynomial.X ^ (↑k * N) * c k
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_telescoping_sum
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zk_blindedSlice_natDegree_lt : ∀ {K : Type u_1} [inst : Field K] {N q : ℕ},
  0 < N →
    ∀ {c : Fin (2 * q) → Polynomial K} {ρ : Fin (2 * q - 1) → Polynomial K},
      (∀ (k : Fin (2 * q)), (c k).natDegree < N) →
        (∀ (j : Fin (2 * q - 1)), (ρ j).natDegree < N) →
          ∀ (k : Fin (2 * q)), (Ix.Cert.Compression.StarkShrinkerZk.zkBlindedSlice N q c ρ k).natDegree < 2 * N
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zk_blindedSlice_natDegree_lt
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_degree_lt : ∀ {d N : ℕ},
  1 ≤ d → 1 ≤ N → (2 * d - 1) * N < 2 * N * Ix.Cert.Compression.StarkShrinkerZk.zkQuotientDegree d
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_degree_lt
/--
info: Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.card_fp3Model : Fintype.card Ix.Cert.Compression.StarkShrinkerZk.Fp3Model =
  CertiFri.P3.Goldilocks.order ^ 3
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.card_fp3Model
/--
info: Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.mul_adjugate : ∀ (a : Ix.Cert.Compression.StarkShrinkerZk.Fp3Model),
  a * a.adjugate = Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.embed a.norm
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.mul_adjugate
/--
info: Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.cubicTrinomial_no_root : ∀ (r : Ix.Cert.Compression.Foreign.GoldilocksF),
  r ^ 3 - r - 1 ≠ 0
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.cubicTrinomial_no_root
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_spans_of_not_base : ∀
  {r₀ r₁ : Ix.Cert.Compression.StarkShrinkerZk.Fp3Model},
  r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0 → r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0 → Ix.Cert.Compression.StarkShrinkerZk.FpSpan3 ![1, r₀, r₁, r₀ * r₁]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_spans_of_not_base
/--
info: Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_prob_le : ↑(Nat.card
        { p // ¬Ix.Cert.Compression.StarkShrinkerZk.FpSpan3 ![1, p.1, p.2, p.1 * p.2] }) /
    ↑(Nat.card (Ix.Cert.Compression.StarkShrinkerZk.Fp3Model × Ix.Cert.Compression.StarkShrinkerZk.Fp3Model)) ≤
  2 / ↑CertiFri.P3.Goldilocks.order ^ 2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_prob_le
/--
info: Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_lt_two_neg_126 : 2 / ↑CertiFri.P3.Goldilocks.order ^ 2 <
  1 / 2 ^ 126
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_lt_two_neg_126
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_fp3_tensor3_span_failure_ge : 1 / ↑CertiFri.P3.Goldilocks.order ≤
    ↑(Nat.card { p // ¬Ix.Cert.Compression.StarkShrinkerZk.FpSpan3 ![1, p.1, p.2] }) /
      ↑(Nat.card (Ix.Cert.Compression.StarkShrinkerZk.Fp3Model × Ix.Cert.Compression.StarkShrinkerZk.Fp3Model)) ∧
  1 / 2 ^ 64 < 1 / ↑CertiFri.P3.Goldilocks.order
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_fp3_tensor3_span_failure_ge
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_trace_height_ge : ∀
  {cfg : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkConfig},
  Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk cfg →
    2 * cfg.numQueries + 2 * cfg.extDegree ≤ 2 ^ cfg.logTraceHeight
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_trace_height_ge
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_constraintDegree_le_blowup : ∀
  {cfg : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkConfig},
  Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk cfg → cfg.maxConstraintDegree ≤ 2 ^ cfg.logBlowup
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_constraintDegree_le_blowup
/--
info: @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_domains_disjoint_from_nonZk : ∀
  {cfg : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkConfig},
  Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk cfg →
    ∀ {dNonZk : Ix.Cert.Compression.StarkShrinker.Blake3Domain},
      dNonZk.isZk = false →
        cfg.leafDomain.keyWords ≠ dNonZk.keyWords ∧
          cfg.compressDomain.keyWords ≠ dNonZk.keyWords ∧
            cfg.transcriptDomain.keyWords ≠ dNonZk.keyWords ∧ cfg.vkDomain.keyWords ≠ dNonZk.keyWords
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_domains_disjoint_from_nonZk
/--
info: Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128_ok : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
  Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128_ok
/--
info: Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb2_ok : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
  Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb2_ok
/--
info: Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb3_ok : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
  Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb3
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb3_ok
/--
info: Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb4_ok : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
  Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb4
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb4_ok
/--
info: Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128 : ∀
  (cfg : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkConfig),
  Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk cfg →
    ∀ {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type} [inst : DecidableEq Inst]
      [inst_1 : DecidableEq Msg] [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X']
      [inst_4 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)]
      [∀ (x : X'), Nonempty (Y' x)] {D : Type} [inst_8 : Fintype D] [Nonempty D],
      Fintype.card D = 2 ^ (8 * cfg.digestBytes) →
        ∀ {r : Inst → ℕ} {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ}
          {εmax : ℝ},
          Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
            (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
              0 ≤ εmax →
                εmax ≤ 1 / 2 / 2 ^ 128 →
                  ∀
                    (hashBad :
                      CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                        (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                          Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
                    (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                        (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                        List.dlookup x l = none →
                          CertiFri.Oracle.FractionLE (hashBad l x)
                            (2 * (3 / 2) * ↑(List.length l) / ↑(Fintype.card D))) →
                      ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
                        (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
                        (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
                          ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
                            (wFri : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.GoldilocksF),
                            (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout).Satisfies friPub
                                wFri →
                              ∀
                                {sem :
                                  Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address
                                    Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
                                    Ix.DynamicLink.LinkedCircuitEntry}
                                {batchClaim :
                                  ℕ →
                                    Aggr.ValidatorMode Address →
                                      (Address → Prop) →
                                        (Address → Prop) →
                                          (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
                                {rootStmt :
                                  Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address
                                    Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
                                    Ix.DynamicLink.LinkedCircuitEntry}
                                (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
                                (stmt : Ix.Cert.Compression.StarkShrinker.StarkShrinkerPublicStatement)
                                (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp),
                                Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkPublicBinding cfg stmt friPub
                                    outClaimDig →
                                  ∀ {A B : Type}
                                    (adv :
                                      CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A)
                                    {Q M_verif : ℕ},
                                    adv.QueryBound Q →
                                      ∀
                                        (verifyAll :
                                          A →
                                            CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')
                                              B),
                                        (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                                          M_verif ≤ 2 ^ 20 →
                                            Q + M_verif ≤ 2 ^ 128 →
                                              ∀
                                                (NodeForges :
                                                  B →
                                                    Fin (1 + t.verificationCount) →
                                                      CertiFri.Oracle.Log
                                                          (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                                                        Prop),
                                                ⋯ → ⋯
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128
/--
info: Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_concrete_prob_128 : ∀
  (cfg : Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkConfig),
  Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk cfg →
    ∀ {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type} [inst : DecidableEq Inst]
      [inst_1 : DecidableEq Msg] [inst_2 : (i : ℕ) → DecidableEq (Chal i)] [inst_3 : DecidableEq X']
      [inst_4 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)] [inst_6 : (x : X') → Fintype (Y' x)]
      [∀ (x : X'), Nonempty (Y' x)] {D : Type} [inst_8 : Fintype D] [Nonempty D],
      Fintype.card D = 2 ^ (8 * cfg.digestBytes) →
        ∀ {r : Inst → ℕ} {doomed : Inst → (i : ℕ) → CertiFri.Oracle.Transcript Msg Chal i → Prop} {ε : Inst → ℕ → ℝ}
          {εmax : ℝ},
          Ix.Cert.Aggr.MonolithicRom.MultiRbrSound r doomed ε →
            (∀ (inst : Inst), ∀ i < r inst, ε inst i ≤ εmax) →
              0 ≤ εmax →
                ∀
                  (hashBad :
                    CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') →
                      (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X') →
                        Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y' x → Prop),
                  (∀ (l : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y'))
                      (x : Ix.Cert.Aggr.MonolithicRom.MultiQuery Inst Msg Chal X'),
                      List.dlookup x l = none →
                        CertiFri.Oracle.FractionLE (hashBad l x) (2 * (3 / 2) * ↑(List.length l) / ↑(Fintype.card D))) →
                    ∀ {A B : Type} {M : ℕ}
                      (adv : CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') A)
                      {Q M_verif : ℕ},
                      adv.QueryBound Q →
                        ∀
                          (verifyAll :
                            A → CertiFri.Oracle.OracleComp (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') B),
                          (∀ (a : A), (verifyAll a).QueryBound M_verif) →
                            M_verif ≤ 2 ^ 20 →
                              Q + M_verif ≤ 2 ^ 127 →
                                ↑(Q + M_verif) * εmax ≤ 1 / 2 / 2 ^ 128 →
                                  ∀
                                    (NodeForges :
                                      B →
                                        Fin M →
                                          CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y') → Prop),
                                    (∀ (b : B)
                                        (l' : CertiFri.Oracle.Log (Ix.Cert.Aggr.MonolithicRom.MultiAnswer Chal Y')),
                                        (adv.bind verifyAll).Outcome [] b l' →
                                          (∃ k, NodeForges b k l') →
                                            ¬CertiFri.Oracle.HasBad hashBad l' →
                                              ∃ inst tr,
                                                doomed inst 0 CertiFri.Oracle.Transcript.nil ∧
                                                  Ix.Cert.Aggr.MonolithicRom.MultiSupports inst tr l' ∧
                                                    ¬doomed inst (r inst) tr) →
                                      CertiFri.Oracle.OracleComp.prob (fun b l' => ∃ k, NodeForges b k l')
                                          (adv.bind verifyAll) [] ≤
                                        1 / 2 ^ 128
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_concrete_prob_128
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_wr3 : ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
      (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
        batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
        logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
        randomizerWidth := 3, maxConstraintDegree := __src.maxConstraintDegree, leafSaltBytes := __src.leafSaltBytes,
        oddCosetBlinding := __src.oddCosetBlinding, interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded,
        numCircuits := __src.numCircuits, leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  1 / ↑CertiFri.P3.Goldilocks.order ≤
      ↑(Nat.card { p // ¬Ix.Cert.Compression.StarkShrinkerZk.FpSpan3 ![1, p.1, p.2] }) /
        ↑(Nat.card (Ix.Cert.Compression.StarkShrinkerZk.Fp3Model × Ix.Cert.Compression.StarkShrinkerZk.Fp3Model)) ∧
    1 / 2 ^ 64 < 1 / ↑CertiFri.P3.Goldilocks.order
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_wr3
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_small_trace : ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
      (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
        batching := __src.batching, regime := __src.regime, logTraceHeight := 8, logBlowup := __src.logBlowup,
        numQueries := __src.numQueries, queryPowBits := __src.queryPowBits, randomizerWidth := __src.randomizerWidth,
        maxConstraintDegree := __src.maxConstraintDegree, leafSaltBytes := __src.leafSaltBytes,
        oddCosetBlinding := __src.oddCosetBlinding, interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded,
        numCircuits := __src.numCircuits, leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  2 ^ 8 <
    2 * Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128.numQueries +
      2 * Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128.extDegree
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_small_trace
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_degree5_lb2 : ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
      (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
        batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight, logBlowup := 2,
        numQueries := __src.numQueries, queryPowBits := __src.queryPowBits, randomizerWidth := __src.randomizerWidth,
        maxConstraintDegree := 5, leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
        interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
        leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  Ix.Cert.Compression.StarkShrinkerZk.nonZkQuotientDegree 5 = 4 ∧
    Ix.Cert.Compression.StarkShrinkerZk.zkQuotientDegree 5 = 8
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_degree5_lb2
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_cross_mode_replay : ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
      (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
      { version := Ix.Cert.Compression.StarkShrinker.ProtocolVersion.v6, extDegree := __src.extDegree,
        digestBytes := __src.digestBytes, batching := __src.batching, regime := __src.regime,
        logTraceHeight := __src.logTraceHeight, logBlowup := __src.logBlowup, numQueries := __src.numQueries,
        queryPowBits := __src.queryPowBits, randomizerWidth := __src.randomizerWidth,
        maxConstraintDegree := __src.maxConstraintDegree, leafSaltBytes := __src.leafSaltBytes,
        oddCosetBlinding := __src.oddCosetBlinding, interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded,
        numCircuits := __src.numCircuits, leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
        transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
        (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
        { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
          batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
          logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
          randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
          leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
          interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
          leafDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.merkleLeaf,
          compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain,
          vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest }) ∧
    ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
          (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
          { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
            batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
            logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
            randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
            leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
            interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
            leafDomain := __src.leafDomain,
            compressDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.merkleCompress,
            transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
            pinnedVkDigest := __src.pinnedVkDigest }) ∧
      ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
            (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
            { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
              batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
              logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
              randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
              leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
              interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
              leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
              transcriptDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.transcriptSingle,
              vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest }) ∧
        ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
              (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
              { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
                batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
                logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
                randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
                leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
                interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
                leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
                transcriptDomain := __src.transcriptDomain,
                vkDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.verifyingKey,
                pinnedVkDigest := __src.pinnedVkDigest }) ∧
          ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
                (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
                { version := Ix.Cert.Compression.StarkShrinker.ProtocolVersion.v6Zk, extDegree := __src.extDegree,
                  digestBytes := __src.digestBytes, batching := __src.batching, regime := __src.regime,
                  logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
                  numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
                  compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain,
                  vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest }) ∧
            ¬Ix.Cert.Compression.StarkShrinker.StarkShrinkerV6ProfileOk
                  (have __src := Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128;
                  { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
                    batching := __src.batching, regime := __src.regime, logBlowup := __src.logBlowup,
                    numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
                    numCircuits := __src.numCircuits,
                    leafDomain := Ix.Cert.Compression.StarkShrinker.Blake3Domain.zkMerkleLeaf,
                    compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain,
                    vkDomain := __src.vkDomain, pinnedVkDigest := __src.pinnedVkDigest }) ∧
              ∀ (dV6 dZk : Ix.Cert.Compression.StarkShrinker.Blake3Domain),
                dV6.isV6 = true → dZk.isZk = true → dV6.keyWords ≠ dZk.keyWords
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_cross_mode_replay
/--
info: Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_unblinded_accumulators : ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
      (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
      { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
        batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
        logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
        randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
        leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
        interiorAccumulatorsBlinded := false, numCircuits := __src.numCircuits, leafDomain := __src.leafDomain,
        compressDomain := __src.compressDomain, transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
        pinnedVkDigest := __src.pinnedVkDigest }) ∧
  ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
        (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
        { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
          batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
          logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
          randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
          leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := false,
          interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
          leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
          transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
          pinnedVkDigest := __src.pinnedVkDigest }) ∧
    ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
          (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
          { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
            batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
            logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
            randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
            leafSaltBytes := 0, oddCosetBlinding := __src.oddCosetBlinding,
            interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := __src.numCircuits,
            leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
            transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
            pinnedVkDigest := __src.pinnedVkDigest }) ∧
      ¬Ix.Cert.Compression.StarkShrinkerZk.StarkShrinkerZkGuardrailsOk
          (have __src := Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128;
          { version := __src.version, extDegree := __src.extDegree, digestBytes := __src.digestBytes,
            batching := __src.batching, regime := __src.regime, logTraceHeight := __src.logTraceHeight,
            logBlowup := __src.logBlowup, numQueries := __src.numQueries, queryPowBits := __src.queryPowBits,
            randomizerWidth := __src.randomizerWidth, maxConstraintDegree := __src.maxConstraintDegree,
            leafSaltBytes := __src.leafSaltBytes, oddCosetBlinding := __src.oddCosetBlinding,
            interiorAccumulatorsBlinded := __src.interiorAccumulatorsBlinded, numCircuits := 2,
            leafDomain := __src.leafDomain, compressDomain := __src.compressDomain,
            transcriptDomain := __src.transcriptDomain, vkDomain := __src.vkDomain,
            pinnedVkDigest := __src.pinnedVkDigest })
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_unblinded_accumulators

-- Axioms
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_doomed_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_doomed_of_supports
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound_collision
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound
/--
info: 'Ix.Cert.Aggr.MonolithicRom.goldilocksExt3_card_ge_two_pow_191' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.goldilocksExt3_card_ge_two_pow_191
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_rate_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_rate_128
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_concrete_prob_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_concrete_prob_128
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_field_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_field_128
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_strictly_tighter_than_union_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_strictly_tighter_than_union_bound
/--
info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20
/--
info: 'Ix.Cert.Aggr.MonolithicRom.negControl_fp2_below_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.negControl_fp2_below_128
/--
info: 'Ix.Cert.Aggr.MonolithicRom.negControl_digest32_saturates_at_2_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.negControl_digest32_saturates_at_2_128
/--
info: 'Ix.Cert.Compression.StarkShrinker.Blake3Domain.keyWords_injective' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.Blake3Domain.keyWords_injective
/--
info: 'Ix.Cert.Compression.StarkShrinker.Blake3Domain.context_injective' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.Blake3Domain.context_injective
/--
info: 'Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6_keyWords_ne_nonV6' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6_keyWords_ne_nonV6
/--
info: 'Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6Zk_keyWords_ne_nonZk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.Blake3Domain.v6Zk_keyWords_ne_nonZk
/--
info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_query_soundness_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_query_soundness_128
/--
info: 'Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.v6ShrinkerUd128_ok
/--
info: 'Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb2_ok
/--
info: 'Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb3_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb3_ok
/--
info: 'Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb4_ok' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.v6ShrinkerJohnsonLb4_ok
/--
info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_publicBinding_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_publicBinding_injective
/--
info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128
/--
info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128
/--
info: 'Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_v5' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_v5
/--
info: 'Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_fp2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_fp2
/--
info: 'Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_weak_params' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_weak_params
/--
info: 'Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_vk_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_vk_mismatch
/--
info: 'Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_claim_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.negControl_shrinker_v6_rejects_claim_mismatch
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.salted_merkle_binding_of_no_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.salted_merkle_binding_of_no_collision
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.v6Zk_preprocessed_salt_context_distinct' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.v6Zk_preprocessed_salt_context_distinct
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.v6Zk_domains_disjoint_from_v6_and_plain' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.v6Zk_domains_disjoint_from_v6_and_plain
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_agrees_on_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_agrees_on_trace
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_natDegree_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zk_oddCoset_blinding_natDegree_lt
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_telescoping_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_telescoping_sum
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zk_blindedSlice_natDegree_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zk_blindedSlice_natDegree_lt
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_degree_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zk_quotient_degree_lt
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.card_fp3Model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.card_fp3Model
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.mul_adjugate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.mul_adjugate
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.cubicTrinomial_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.cubicTrinomial_no_root
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_spans_of_not_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_spans_of_not_base
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_prob_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_prob_le
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_lt_two_neg_126' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.fp3_tensor4_span_failure_lt_two_neg_126
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_fp3_tensor3_span_failure_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_fp3_tensor3_span_failure_ge
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_trace_height_ge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_trace_height_ge
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_constraintDegree_le_blowup' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_constraintDegree_le_blowup
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_domains_disjoint_from_nonZk' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerGuardrails_domains_disjoint_from_nonZk
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerUd128_ok
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb2_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb2_ok
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb3_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb3_ok
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb4_ok' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.zkShrinkerJohnsonLb4_ok
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_concrete_prob_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_concrete_prob_128
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_wr3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_wr3
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_small_trace' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_small_trace
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_degree5_lb2' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_degree5_lb2
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_cross_mode_replay' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_cross_mode_replay
/--
info: 'Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_unblinded_accumulators' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.negControl_zkShrinker_rejects_unblinded_accumulators
