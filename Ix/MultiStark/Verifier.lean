module
public import Ix.Aiur.Meta

/-!
# Multi-STARK verifier (Aiur)

Reimplementation of `multi-stark/src/verifier.rs` (`System::verify_multiple_claims`)
over the deserialized `Proof` (`Ix/MultiStark/Deserialize.lean`).

The Rust verifier runs these steps:

1. **Shape check** — proof array dimensions match the system's circuit count and
   column widths.
2. **Accumulator balance** — the last intermediate accumulator is zero (all
   lookup pushes/pulls cancel).
3. **Fiat-Shamir replay** — reconstruct the challenger: observe
   commitments / trace heights / claims, sample (lookup, fingerprint, α, ζ).
4. **PCS verification** — FRI opening proofs (see `Ix/MultiStark/Pcs.lean`).
5. **OOD evaluation** — recompute the composition polynomial at ζ and check
   `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.

### Implemented here
* Step 1 (the system-independent part): the proof is internally consistent —
  `stage_1`, `stage_2` and `intermediate_accumulators` all have the same length
  (the circuit count) and it is non-zero.
* Step 2: accumulator balance — the last `intermediate_accumulator` is the zero
  extension element.
* Step 3: the Fiat-Shamir challenger replay (`fiat_shamir`). Prover-faithful:
  starts from the parameter-seeded challenger (`b"multi-stark/v0"` + the 7
  protocol parameters), observes the system shape, the verifying key's
  preprocessed commitment, the stage_1 commitment, the trace heights, and the
  length-prefixed public claims (in that order), then samples and re-observes
  the lookup/fingerprint challenges, observes stage_2 and the intermediate
  accumulators, samples α, observes the quotient commitment, and samples ζ —
  matching `verify_multiple_claims` byte-for-byte.
* Step 5: the out-of-domain composition/quotient check (`ood_verify`). For each
  circuit it recomputes `composition(ζ)` by replaying the AIR constraint folder
  (`VerifierConstraintFolder` + `LookupAir::eval`) over the deserialized
  symbolic system and the opened values, recomputes `quotient(ζ)` from the
  opened quotient coefficient slices (the power series
  `Q(ζ) = Σᵢ ζ^(i·n)·cᵢ(ζ)`), and asserts
  `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.
  Validated end-to-end against a real factorial proof (the `recursive-verifier`
  test runner, `Tests/MultiStark.lean`): the verifier accepts the honest proof
  and rejects a tampered claim.

* Step 4: the PCS/FRI opening proof (`pcs_fri_verify`, `Ix/MultiStark/Pcs.lean`)
  — Merkle `verify_batch`, the challenger continuation, the FRI fold chain, and
  the final-polynomial check.

### Notes
* Base-field samples are rejection-sampled (`ch_sample_field`): a raw 8-byte
  limb in the band `[p, 2⁶⁴)` (probability ≈ 2⁻³²) is discarded and redrawn,
  consuming challenger bytes exactly as `SerializingChallenger64::sample` does.
-/

public section

namespace MultiStark

def verifier := ⟦
  -- An extension element `[c0, c1]` (`= c0 + c1·X`) is zero iff both Goldilocks
  -- coefficients are zero. (`read_ext` already reduced the limbs mod p.)
  fn ext_is_zero(e: Ext) -> G {
    @val_is_zero(e[0]) * @val_is_zero(e[1])
  }

  -- 1 iff the LAST element of the accumulator list is the zero extension
  -- element (Rust: `intermediate_accumulators.last() == Some(ExtVal::ZERO)`).
  -- The empty list returns 0 (there is no last element to balance).
  fn last_acc_is_zero(accs: List‹Ext›) -> G {
    match load(accs) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match load(rest) {
          ListNode.Nil => @ext_is_zero(e),
          _ => last_acc_is_zero(rest),
        },
    }
  }

  -- The preprocessed commitment cap from the verifying key, or an empty cap
  -- (observes nothing) when there is none.
  fn opt_commit_cap(commit: OptCommit) -> MerkleCap {
    match commit {
      OptCommit.NoCommit => store(ListNode.Nil),
      OptCommit.SomeCommit(c) => c,
    }
  }

  -- Replay the verifier transcript and derive the four challenges
  -- `(lookup, fingerprint, alpha, zeta)`. Mirrors `verify_multiple_claims`'s
  -- challenger sequence exactly:
  --   seed = tag + protocol parameters; observe_shape (circuit count + 6
  --   metadata words per circuit) → preprocessed_commit (if any) → stage_1 →
  --   log_degrees → length-prefixed claims;
  --   sample lookup, observe it; sample fingerprint, observe it;
  --   observe stage_2; observe the intermediate accumulators; sample α;
  --   observe quotient; sample ζ.
  -- `observe` clears the challenger's output buffer, and every sample here is
  -- preceded by an observe, so each `ch_sample_ext` re-flushes from an empty
  -- output (hence the `store(ListNode.Nil)` output argument each time).
  -- Every sample is rejection-sampled (`ch_sample_field` inside
  -- `ch_sample_ext`), so a limb in the band `[p, 2⁶⁴)` is redrawn exactly as in
  -- the reference challenger, and the limbs observed back are canonical.
  -- Also returns the post-ζ challenger `input` buffer, which the PCS phase
  -- (Phase 4+) continues observing into. The leftover `output` after the ζ
  -- sample is discarded — the next challenger op is an observe (of the opened
  -- values), which clears `output` anyway.
  -- Each activation bit as an observed `Val` (8 LE bytes, 0 or 1).
  fn active_onto(active: List‹G›, tail: ByteStream) -> ByteStream {
    match load(active) {
      ListNode.Nil => tail,
      ListNode.Cons(b, rest) =>
        b8_onto([u8_from_field_unsafe(b), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                active_onto(rest, tail)),
    }
  }

  fn fiat_shamir(tlimbs: List‹U64›, active: List‹G›, prep: MerkleCap, s1: MerkleCap, s2: MerkleCap,
      q: MerkleCap, lds: List‹U8›, cbytes: ByteStream, accs: List‹Ext›)
      -> (Ext, Ext, Ext, Ext, ByteStream) {
    -- Initial transcript, front-to-back: seed tag, parameter + shape words
    -- (`tlimbs`, from the verifying key), the activation bitmap, prep,
    -- stage_1, log_degrees, claims. Built inner-to-outer with the prepend
    -- helpers so the result is in forward (observation) order. The claims
    -- segment is `cbytes` VERBATIM: the wire format (u64 count, per-claim
    -- u64 len + raw u64 vals, all 8 LE bytes) is exactly the transcript
    -- encoding `verify_multiple_claims` observes, and the entrypoint
    -- asserts the stream fully consumed — so no re-serialization walk.
    let input = log_degrees_onto(lds, cbytes);
    let input = cap_onto(s1, input);
    let input = cap_onto(prep, input);
    let input = active_onto(active, input);
    let input = limbs_onto(tlimbs, input);
    let input = @seed_tag_onto(input);
    -- sample lookup challenge, then observe it back (append; one concat of
    -- the 16-byte segment instead of two full-buffer snoc walks)
    let (l0, l1, input, _ol) = ch_sample_ext(input, store(ListNode.Nil));
    let input = list_concat(input, b8_onto(l0, b8_onto(l1, store(ListNode.Nil))));
    -- sample fingerprint challenge, then observe it back
    let (f0, f1, input, _of) = ch_sample_ext(input, store(ListNode.Nil));
    let input = list_concat(input, b8_onto(f0, b8_onto(f1, store(ListNode.Nil))));
    -- observe stage_2 commitment
    let input = snoc_cap(input, s2);
    -- observe the intermediate accumulators (public values entering the
    -- constraints; α and ζ must depend on them directly)
    let input = list_concat(input, accs_onto(accs, store(ListNode.Nil)));
    -- sample constraint challenge α (not observed)
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    -- observe quotient commitment
    let input = snoc_cap(input, q);
    -- sample out-of-domain point ζ; keep the resulting `input` for the PCS phase
    let (z0, z1, zinput, _oz) = ch_sample_ext(input, store(ListNode.Nil));
    ([@val_from_bytes(l0), @val_from_bytes(l1)],
     [@val_from_bytes(f0), @val_from_bytes(f1)],
     [@val_from_bytes(a0), @val_from_bytes(a1)],
     [@val_from_bytes(z0), @val_from_bytes(z1)],
     zinput)
  }

  -- Structural + accumulator + PCS checks of a deserialized proof (steps 1, 2,
  -- 4). Fiat-Shamir (step 3) and the OOD check (step 5) live in `ood_verify`,
  -- which needs the verifying key and the claims.
  --
  -- Returns 1 on success; `assert_eq!` aborts the (proof) execution on any
  -- failed check, exactly as the Rust verifier returns `Err`.
  fn verify(proof: Proof) -> G {
    -- Single-constructor destructure (not a match): keeps the body — and the
    -- entrypoint it splices into — single-path, so its lookups group 2 per
    -- stage-2 slot.
    let Proof.Mk(_active, _commitments, accs, _log_degrees, _opening,
                 quotient, _preprocessed, stage_1, stage_2) = proof;
    -- Step 1 (shape, system-independent): the per-round opened-value lists
    -- and the accumulator list all have the same length = the circuit count.
    let num_circuits = list_length(accs);
    -- there must be at least one circuit (Rust: InvalidSystem)
    assert_eq!(eq_zero(num_circuits), 0);
    assert_eq!(list_length(stage_1), num_circuits);
    assert_eq!(list_length(stage_2), num_circuits);
    -- one wide quotient matrix per active circuit
    assert_eq!(list_length(quotient), num_circuits);

    -- Step 2: accumulator balance — the last accumulator must be zero.
    assert_eq!(last_acc_is_zero(accs), 1);
    -- Step 4 (PCS/FRI) now runs inside `ood_verify`, which has the verifying
    -- key, the challenger continuation, and the opened values it needs.
    1
  }

  -- ==========================================================================
  -- Step 5: out-of-domain (OOD) evaluation.
  --
  -- Mirrors the per-circuit loop in `verifier.rs::verify_multiple_claims`.
  -- For each circuit it recomputes the composition polynomial
  -- `composition(ζ)` from the opened values by replaying the AIR constraint
  -- folder (`VerifierConstraintFolder` + `LookupAir::eval`), recomputes the
  -- quotient `quotient(ζ)` from the opened coefficient slices via the power
  -- series `Q(ζ) = Σᵢ ζ^(i·n)·cᵢ(ζ)`, and asserts
  --   composition(ζ) · inv_vanishing(ζ) == quotient(ζ).
  --
  -- The challenges (lookup, fingerprint, α, ζ) come from `fiat_shamir` above.
  -- The running lookup accumulator starts from the public claims
  -- (`claims_acc`; ExtVal::ZERO when there are none).
  -- ==========================================================================

  -- One Horner fold step of the constraint folder: `acc := acc·α + x`
  -- (`VerifierConstraintFolder::assert_zero` / `assert_zero_ext`).
  fn ood_fold(acc: Ext, alpha: Ext, x: Ext) -> Ext {
    @ext_add(@ext_mul(acc, alpha), x)
  }

  -- Reconstruct an extension element from its two opened base coordinates,
  -- `from_ext_basis([c0, c1]) = c0 + c1·X` (the ExtVal basis is `[1, X]`).
  fn from_ext_basis(c0: Ext, c1: Ext) -> Ext {
    @ext_add(c0, @ext_mul(c1, [@val_zero(), @val_one()]))
  }

  -- A stage-2 / quotient opened row arrives as `stage_2_width·2` extension
  -- coordinates; fold consecutive pairs back into `stage_2_width` extension
  -- elements (Rust: `chunks_exact(2).map(from_ext_basis)`).
  fn reconstruct_ext_row(raw: List‹Ext›) -> List‹Ext› {
    match load(raw) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c0, t1) =>
        let ListNode.Cons(c1, t2) = load(t1);
        store(ListNode.Cons(from_ext_basis(c0, c1), reconstruct_ext_row(t2))),
    }
  }

  -- ==========================================================================
  -- Compiled node-graph evaluation (replaces the symbolic AIR folder).
  --
  -- The composition polynomial at ζ is `Σᵢ α^(k-1-i)·zeroᵢ`, where each `zeroᵢ`
  -- is the value of a constraint-root node. The nodes form a flat,
  -- topologically ordered DAG (children by NodeId, children precede parents).
  -- Instead of the Rust prover's dense forward sweep (which would build an
  -- O(n²) temporary value-buffer list here), `eval_at` interprets the graph
  -- directly by recursing into children. Aiur memoizes calls by argument
  -- pointers, so each node is evaluated at most once per opening context and
  -- every further reference — DAG sharing, later constraint roots — is a
  -- cache hit; node fetches share `list_drop`'s cached drop-chain over the
  -- one `nodes` list. The lookup-argument constraints are already compiled
  -- into `zeros`, so nothing special is done for them (Rust `verifier.rs`
  -- evaluates one node graph and Horner-folds the roots).
  -- ==========================================================================

  -- Evaluate node `i` of the graph into an ExtVal, given the leaf context.
  -- Stage-2 columns are the OPENED BASE columns used directly (no
  -- `from_ext_basis` reassembly).
  fn eval_at(nodes: List‹SysNode›, i: G,
      main: List‹Ext›, main_next: List‹Ext›, prep: List‹Ext›, prep_next: List‹Ext›,
      s2: List‹Ext›, s2next: List‹Ext›, publics: List‹Ext›,
      isf: Ext, isl: Ext, ist: Ext) -> Ext {
    let nd = list_lookup(nodes, i);
    match nd {
      SysNode.Const(c) => [c, @val_zero()],
      SysNode.Var(src, off, idx) =>
        -- flatten (source, offset) into one selector: 2·source + offset,
        -- with source 0 Preprocessed / 1 Main / 2 Stage2, offset 0 cur / 1 next.
        let sel = src + src + off;
        match sel {
          0 => list_lookup(prep, idx),
          1 => list_lookup(prep_next, idx),
          2 => list_lookup(main, idx),
          3 => list_lookup(main_next, idx),
          4 => list_lookup(s2, idx),
          _ => list_lookup(s2next, idx),
        },
      SysNode.Public(idx) => list_lookup(publics, idx),
      SysNode.IsFirstRow => isf,
      SysNode.IsLastRow => isl,
      SysNode.IsTransition => ist,
      SysNode.Add(a, b) =>
        @ext_add(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
               eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)),
      SysNode.Sub(a, b) =>
        @ext_sub(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
               eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)),
      SysNode.Mul(a, b) =>
        @ext_mul(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
               eval_at(nodes, b, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)),
      SysNode.Neg(a) =>
        @ext_neg(eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist)),
    }
  }

  -- Horner-fold the constraint roots with α: `acc := acc·α + eval_at(z)` for
  -- each root NodeId `z`, in `zeros` order (the canonical compiled order the
  -- prover folded in). Roots share subgraphs, so their evaluations hit the
  -- `eval_at` cache.
  fn fold_roots(acc: Ext, alpha: Ext, zeros: List‹G›, nodes: List‹SysNode›,
      main: List‹Ext›, main_next: List‹Ext›, prep: List‹Ext›, prep_next: List‹Ext›,
      s2: List‹Ext›, s2next: List‹Ext›, publics: List‹Ext›,
      isf: Ext, isl: Ext, ist: Ext) -> Ext {
    match load(zeros) {
      ListNode.Nil => acc,
      ListNode.Cons(z, rest) =>
        let v = eval_at(nodes, z, main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
        fold_roots(ood_fold(acc, alpha, v), alpha, rest, nodes,
                   main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
    }
  }

  -- ==========================================================================
  -- Direct logUp constraint evaluation (mirrors Rust
  -- `lookup::logup_constraint_values`). The logUp constraints are protocol
  -- machinery, never compiled into the vk's node graph: their values at ζ
  -- are computed here from the lookup ids (evaluated through the memoized
  -- `eval_at`), the stage-2 openings, and the lookup publics, and folded
  -- with α after the user roots — per lookup GROUP the 2 coordinates of
  -- the chained-accumulator step constraint (see `logup_steps_fold`).
  --
  -- Coordinates: a coordinate-expanded logUp constraint is a PAIR of
  -- base-field polynomials; at ζ each coordinate is an Ext value. Pair
  -- products are in X² = 7 with Ext coefficients:
  -- (a0·b0 + 7·a1·b1, a0·b1 + a1·b0).
  -- ==========================================================================
  fn pair_mul(a0: Ext, a1: Ext, b0: Ext, b1: Ext) -> (Ext, Ext) {
    (@ext_add(@ext_mul(a0, b0), @ext_mul([@ext_w(), @val_zero()], @ext_mul(a1, b1))),
     @ext_add(@ext_mul(a0, b1), @ext_mul(a1, b0)))
  }

  -- fingerprint(γ, args) = Σᵢ argsᵢ·γ^i as a coordinate pair:
  -- fp(Cons(a, rest)) = (eval a, 0) + γ ⊗ fp(rest); args embed in coord 0.
  fn logup_fingerprint(args: List‹G›, g0: Ext, g1: Ext, nodes: List‹SysNode›,
      main: List‹Ext›, main_next: List‹Ext›, prep: List‹Ext›, prep_next: List‹Ext›,
      s2: List‹Ext›, s2next: List‹Ext›, publics: List‹Ext›,
      isf: Ext, isl: Ext, ist: Ext) -> (Ext, Ext) {
    match load(args) {
      ListNode.Nil => ([@val_zero(), @val_zero()], [@val_zero(), @val_zero()]),
      ListNode.Cons(a, rest) =>
        let (f0, f1) = logup_fingerprint(rest, g0, g1, nodes,
          main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
        let (m0, m1) = pair_mul(f0, f1, g0, g1);
        let av = eval_at(nodes, a, main, main_next, prep, prep_next, s2, s2next,
                         publics, isf, isl, ist);
        (@ext_add(m0, av), m1),
    }
  }

  -- Per-GROUP chained-accumulator constraints, folding into the α
  -- accumulator as we go (Rust `lookup::logup_constraint_values`): stage-2
  -- slot `g` holds `acc_g`, the running sum entering group `g`'s step. A
  -- group of `k` consecutive lookups (the last group may be smaller)
  -- asserts `(Π_j m_j)·(acc_{g+1} − acc_g) − Σ_j mult_j·Π_{j'≠j} m_{j'}`;
  -- the wrap step (last group) targets the NEXT row's slot 0 plus the
  -- boundary injection `is_last_row·(acc_final − acc_initial)` (`inj`),
  -- which converts the cyclic telescoped sum into the public accumulator
  -- difference. Group state is built in one pass with the recurrence
  -- `R ← R·m + mult·P; P ← P·m` (P the message product, R the mult sum);
  -- `rem` counts the group's remaining capacity, `j` the lookup index.
  -- Ungrouped (k = 1) closes every step: P = m, R = (mult, 0), exactly the
  -- per-lookup chained constraint.
  fn logup_steps_fold(acc: Ext, alpha: Ext, lks: List‹SysLookup›, j: G, lcount: G,
      g: G, rem: G, k: G, p0: Ext, p1: Ext, r0: Ext, r1: Ext,
      inj0: Ext, inj1: Ext, b0: Ext, b1: Ext, g0: Ext, g1: Ext,
      nodes: List‹SysNode›,
      main: List‹Ext›, main_next: List‹Ext›, prep: List‹Ext›, prep_next: List‹Ext›,
      s2: List‹Ext›, s2next: List‹Ext›, publics: List‹Ext›,
      isf: Ext, isl: Ext, ist: Ext) -> Ext {
    match load(lks) {
      ListNode.Nil => acc,
      ListNode.Cons(lk, rest) =>
        let SysLookup.Mk(mid, args) = lk;
        let (f0, f1) = logup_fingerprint(args, g0, g1, nodes,
          main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
        let m0 = @ext_add(f0, b0);
        let m1 = @ext_add(f1, b1);
        let mv = eval_at(nodes, mid, main, main_next, prep, prep_next, s2, s2next,
                         publics, isf, isl, ist);
        -- R ← R·m + mult·P, then P ← P·m.
        let (rm0, rm1) = pair_mul(r0, r1, m0, m1);
        let nr0 = @ext_add(rm0, @ext_mul(mv, p0));
        let nr1 = @ext_add(rm1, @ext_mul(mv, p1));
        let (np0, np1) = pair_mul(p0, p1, m0, m1);
        match (j + 1 - lcount) {
          0 =>
            -- Final lookup: close the (possibly smaller) last group against
            -- the wrap target.
            let s0 = list_lookup(s2, g + g);
            let s1 = list_lookup(s2, g + g + 1);
            let t0 = @ext_add(list_lookup(s2next, 0), inj0);
            let t1 = @ext_add(list_lookup(s2next, 1), inj1);
            let (c0, c1) = pair_mul(np0, np1, @ext_sub(t0, s0), @ext_sub(t1, s1));
            ood_fold(ood_fold(acc, alpha, @ext_sub(c0, nr0)), alpha, @ext_sub(c1, nr1)),
          _ => match rem - 1 {
            0 =>
              -- Group full: close against the next slot, reset the state.
              let s0 = list_lookup(s2, g + g);
              let s1 = list_lookup(s2, g + g + 1);
              let t0 = list_lookup(s2, g + g + 2);
              let t1 = list_lookup(s2, g + g + 3);
              let (c0, c1) = pair_mul(np0, np1, @ext_sub(t0, s0), @ext_sub(t1, s1));
              let acc1 = ood_fold(ood_fold(acc, alpha, @ext_sub(c0, nr0)), alpha,
                                  @ext_sub(c1, nr1));
              logup_steps_fold(acc1, alpha, rest, j + 1, lcount,
                g + 1, k, k, [@val_one(), @val_zero()], [@val_zero(), @val_zero()], [@val_zero(), @val_zero()], [@val_zero(), @val_zero()],
                inj0, inj1, b0, b1, g0, g1, nodes,
                main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
            _ =>
              -- Keep accumulating within the group.
              logup_steps_fold(acc, alpha, rest, j + 1, lcount,
                g, rem - 1, k, np0, np1, nr0, nr1,
                inj0, inj1, b0, b1, g0, g1, nodes,
                main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
          },
        },
    }
  }

  -- The composition polynomial `composition(ζ)` for one circuit: interpret
  -- the compiled node graph at each USER constraint root, then fold the
  -- directly-evaluated chained-logUp step values, all Horner-folded with α
  -- in the canonical protocol order.
  fn ood_composition(nodes: List‹SysNode›, zeros: List‹G›, lks: List‹SysLookup›,
      k: G,
      main: List‹Ext›, main_next: List‹Ext›, prep: List‹Ext›, prep_next: List‹Ext›,
      s2: List‹Ext›, s2next: List‹Ext›, publics: List‹Ext›,
      lch: Ext, fch: Ext, accp: Ext, naccp: Ext,
      isf: Ext, isl: Ext, ist: Ext, alpha: Ext, inorm: Val) -> Ext {
    let base = fold_roots([@val_zero(), @val_zero()], alpha, zeros, nodes,
               main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist);
    -- The lookup-argument coordinates come straight from the challenge /
    -- accumulator values (pure wiring) — `publics` is only for the node
    -- graph's Public(idx) leaves; looking these 8 back out of the list cost
    -- 8 calls for values already in hand.
    let b0 = [lch[0], @val_zero()]; let b1 = [lch[1], @val_zero()];
    let g0 = [fch[0], @val_zero()]; let g1 = [fch[1], @val_zero()];
    let a0 = [accp[0], @val_zero()]; let a1 = [accp[1], @val_zero()];
    let na0 = [naccp[0], @val_zero()]; let na1 = [naccp[1], @val_zero()];
    -- Boundary injection: is_last_row·(acc_final − acc_initial) with the
    -- selector's normalization constant 1/(n·g) absorbed into Δ (`inorm`;
    -- p3's raw selector has value n·g at the last row, and Δ is constant
    -- across the domain, mirroring the Rust prover/verifier).
    let inj0 = @ext_mul(isl, @ext_mul(@ext_sub(na0, a0), [inorm, @val_zero()]));
    let inj1 = @ext_mul(isl, @ext_mul(@ext_sub(na1, a1), [inorm, @val_zero()]));
    match load(lks) {
      -- No lookups: single pass-through column, acc′ − acc + inj = 0.
      ListNode.Nil =>
        let acc = ood_fold(base, alpha,
          @ext_add(@ext_sub(list_lookup(s2next, 0), list_lookup(s2, 0)), inj0));
        ood_fold(acc, alpha,
          @ext_add(@ext_sub(list_lookup(s2next, 1), list_lookup(s2, 1)), inj1)),
      ListNode.Cons(_h, _t) =>
        logup_steps_fold(base, alpha, lks, 0, list_length(lks),
          0, k, k, [@val_one(), @val_zero()], [@val_zero(), @val_zero()], [@val_zero(), @val_zero()], [@val_zero(), @val_zero()], inj0, inj1,
          b0, b1, g0, g1, nodes,
          main, main_next, prep, prep_next, s2, s2next, publics, isf, isl, ist),
    }
  }

  -- The public-input coordinates for one circuit's lookup argument: the base
  -- coordinates of (β, γ, current acc, next acc), each lifted into ExtVal
  -- (`EF::from(coord)`). Indexed by the compiled `Public` node index
  -- (`num_publics = 4·D`, `D = 2`).
  fn build_publics(lch: Ext, fch: Ext, accp: Ext, naccp: Ext) -> List‹Ext› {
    store(ListNode.Cons([lch[0], @val_zero()], store(ListNode.Cons([lch[1], @val_zero()],
    store(ListNode.Cons([fch[0], @val_zero()], store(ListNode.Cons([fch[1], @val_zero()],
    store(ListNode.Cons([accp[0], @val_zero()], store(ListNode.Cons([accp[1], @val_zero()],
    store(ListNode.Cons([naccp[0], @val_zero()], store(ListNode.Cons([naccp[1], @val_zero()],
    store(ListNode.Nil)))))))))))))))))
  }

  -- ==========================================================================
  -- Quotient evaluation from the opened quotient row.
  --
  -- The quotient is sliced by COEFFICIENTS — `Q(X) = Σᵢ X^(i·n)·cᵢ(X)` with
  -- each `cᵢ` of degree < n = 2^L — and all `qd` slices of a circuit live in
  -- one wide matrix on the trace domain, opened once at ζ. Recombination is
  -- the plain power series
  --   quotient(ζ) = Σᵢ ζ^(i·n) · cᵢ(ζ),
  -- over the slice values reconstructed from the opened row
  -- (`reconstruct_ext_row`, pairs of base coordinates → extension elements).
  -- ==========================================================================

  -- `Σᵢ powᵢ·sliceᵢ` with `powᵢ = zeta_pow_n^i` (`pow` threads the running
  -- power, starting at 1).
  fn quotient_eval(slices: List‹Ext›, zeta_pow_n: Ext, pow: Ext) -> Ext {
    match load(slices) {
      ListNode.Nil => [@val_zero(), @val_zero()],
      ListNode.Cons(c, rest) =>
        @ext_add(@ext_mul(pow, c), quotient_eval(rest, zeta_pow_n, @ext_mul(pow, zeta_pow_n))),
    }
  }

  -- `quotient_degree = (max(md, 2) - 1).next_power_of_two()`.
  -- Tabulated for `max_constraint_degree ≤ 17` (covers all current circuits);
  -- larger degrees fall through to the `_` arm.
  fn quotient_degree_of(md: G) -> G {
    match md {
      0 => 1, 1 => 1, 2 => 1,
      3 => 2,
      4 => 4, 5 => 4,
      6 => 8, 7 => 8, 8 => 8, 9 => 8,
      10 => 16, 11 => 16, 12 => 16, 13 => 16, 14 => 16, 15 => 16, 16 => 16, 17 => 16,
      _ => 32,
    }
  }

  -- The preprocessed opened rows (current, next) at ζ for circuit `i`, or
  -- `(Nil, Nil)` if the circuit has no preprocessed trace.
  fn ood_prep_rows(prep_opt: PreprocessedOpt, oi: OptIdx) -> (List‹Ext›, List‹Ext›) {
    match oi {
      OptIdx.NoIdx => (store(ListNode.Nil), store(ListNode.Nil)),
      OptIdx.SomeIdx(j) =>
        match prep_opt {
          PreprocessedOpt.NoPreprocessed => (store(ListNode.Nil), store(ListNode.Nil)),
          PreprocessedOpt.SomePreprocessed(round) =>
            let pr = list_lookup(round, j);
            (list_lookup(pr, 0), list_lookup(pr, 1)),
        },
    }
  }

  -- Per-circuit OOD loop: for each circuit, recompute composition(ζ) and
  -- quotient(ζ) and assert `composition · inv_vanishing == quotient`. Threads
  -- the running lookup accumulator `accp`.
  fn ood_loop(circuits: List‹SysCircuit›, prep_indices: List‹OptIdx›,
      log_degrees: List‹U8›, accs: List‹Ext›,
      stage1: OpenedRound, stage2: OpenedRound, prep_opt: PreprocessedOpt,
      q_opened: OpenedRound, i: G, accp: Ext,
      lch: Ext, fch: Ext, alpha: Ext, zeta: Ext) -> G {
    match load(circuits) {
      ListNode.Nil => 1,
      ListNode.Cons(circ, rest) =>
        let SysCircuit.Mk(nodes, _node_count, zeros, md, lks, k) = circ;
        -- log_degrees is proof advice; bound it so `two_adic_gen`'s squaring
        -- chain (bits ≤ 32) is never entered above its base case.
        let ld8 = list_lookup(log_degrees, i);
        assert_eq!(u8_less_than(ld8, 32u8), 1);
        let l = to_field(ld8);
        let qd = quotient_degree_of(md);
        let naccp = list_lookup(accs, i);
        let s1 = list_lookup(stage1, i);
        let main = list_lookup(s1, 0);
        let main_next = list_lookup(s1, 1);
        let s2 = list_lookup(stage2, i);
        -- Stage-2 opened rows are base columns; used directly (no pairing).
        let s2row = list_lookup(s2, 0);
        let s2next = list_lookup(s2, 1);
        let (prep, prep_next) = @ood_prep_rows(prep_opt, list_lookup(prep_indices, i));
        let (isf, isl, ist, invv) = @trace_selectors(zeta, l);
        let publics = @build_publics(lch, fch, accp, naccp);
        let inorm = @val_inverse(@val_mul(pow2(l), two_adic_gen(l)));
        let comp = @ood_composition(nodes, zeros, lks, k,
                                   main, main_next, prep, prep_next, s2row, s2next,
                                   publics, lch, fch, accp, naccp,
                                   isf, isl, ist, alpha, inorm);
        -- circuit i's wide quotient row, its base-coordinate pairs folded back
        -- into the `qd` slice values (Rust: `quotient_row.chunks_exact(D)`)
        let slices = reconstruct_ext_row(list_lookup(list_lookup(q_opened, i), 0));
        assert_eq!(eq_zero(list_length(slices) - qd), 1);
        let quot = quotient_eval(slices, ext_exp_pow2(zeta, l), [@val_one(), @val_zero()]);
        assert_eq!(@ext_eq(@ext_mul(comp, invv), quot), 1);
        ood_loop(rest, prep_indices, log_degrees, accs, stage1, stage2, prep_opt,
                 q_opened, i + 1, naccp, lch, fch, alpha, zeta),
    }
  }

  -- The fingerprint of one claim's values: `Σ vᵢ · fch^i` (each `vᵢ` lifted from
  -- its raw u64 limb to an extension element). Mirrors `lookup::fingerprint`.
  fn fingerprint_vals(fch: Ext, vals: List‹U64›) -> Ext {
    match load(vals) {
      ListNode.Nil => [@val_zero(), @val_zero()],
      ListNode.Cons(v, rest) =>
        @ext_add([@val_from_bytes(v), @val_zero()], @ext_mul(fch, fingerprint_vals(fch, rest))),
    }
  }

  -- The initial lookup accumulator built from the public claims:
  -- `acc = Σ_claims 1 / (lookup_challenge + fingerprint(fingerprint_challenge, claim))`
  -- (Rust `verify_multiple_claims`, lines 227-232). Empty claim list → zero.
  fn claims_acc(acc: Ext, claims: List‹List‹U64››, lch: Ext, fch: Ext) -> Ext {
    match load(claims) {
      ListNode.Nil => acc,
      ListNode.Cons(c, rest) =>
        let msg = @ext_add(lch, fingerprint_vals(fch, c));
        claims_acc(@ext_add(acc, @ext_inverse(msg)), rest, lch, fch),
    }
  }

  -- Step 3 + 5: derive the challenges via the (prover-faithful) Fiat-Shamir
  -- replay over the verifying key's preprocessed commitment + the proof
  -- commitments + log_degrees + claims, seed the lookup accumulator from the
  -- claims, then run the OOD composition/quotient check for every circuit.
  -- Returns 1 on success (any mismatch aborts via `assert_eq!`).
  fn ood_verify(sys: Sys, proof: Proof, claims: List‹List‹U64››, cbytes: ByteStream) -> G {
    -- The FRI parameters (`log_blowup`, `num_queries`, `commit_pow_bits`,
    -- `query_pow_bits`) all come from the verifying key, which the public
    -- statement binds through `system_digest` — no separate public inputs.
    let Sys.Mk(params, tlimbs, circuits, commit, prep_indices) = sys;
    let SysParams.Mk(log_blowup, _cap_height, _log_final_poly_len,
                     _max_log_arity, num_queries, commit_pow_bits,
                     query_pow_bits) = params;
    let Proof.Mk(active, commitments, accs, log_degrees, opening,
                 q_opened, prep_opt, stage1, stage2) = proof;
    -- Sparse activation: the bitmap covers the canonical circuit set;
    -- each bit must be boolean; every per-circuit proof sequence is
    -- indexed by ACTIVE position, so the verifying key's circuit and
    -- preprocessed-index lists are filtered to the active subset once
    -- and everything downstream runs on the filtered lists. Soundness
    -- of deactivation rests on the lookup accumulator: an inactive
    -- circuit contributes no sends or receives, and dishonestly
    -- deactivating a needed circuit leaves the final accumulator
    -- nonzero (checked in `verify`).
    assert_eq!(assert_bits(active), 1);
    assert_eq!(eq_zero(list_length(active) - list_length(circuits)), 1);
    let acirc = select_active_circuits(circuits, active);
    let aprep = select_active_prep(prep_indices, active);
    assert_eq!(eq_zero(list_length(acirc) - list_length(accs)), 1);
    let Commitments.Mk(s1c, s2c, qc) = commitments;
    -- opt_commit_cap stays a cross-circuit call: its two-arm match would
    -- make the (spliced) entrypoint branchy, doubling every lookup's
    -- stage-2 cost there — the one small circuit is cheaper.
    let prep_cap = @opt_commit_cap(commit);
    let (lch, fch, alpha, zeta, post_zeta_input) = @fiat_shamir(tlimbs, active, prep_cap, s1c, s2c, qc, log_degrees, cbytes, accs);
    let acc0 = claims_acc([@val_zero(), @val_zero()], claims, lch, fch);
    -- Step 5: OOD composition/quotient identity for every active circuit.
    let _ood = ood_loop(acirc, aprep, log_degrees, accs, stage1, stage2,
             prep_opt, q_opened, 0, acc0, lch, fch, alpha, zeta);
    @pcs_fri_verify(post_zeta_input, stage1, stage2, q_opened, prep_opt, opening,
      s1c, s2c, qc, prep_cap, aprep, log_degrees, zeta,
      list_length(acirc), log_blowup, num_queries, commit_pow_bits,
      query_pow_bits)
  }

  -- 1 iff every element of `l` is boolean (0 or 1).
  fn assert_bits(l: List‹G›) -> G {
    match load(l) {
      ListNode.Nil => 1,
      ListNode.Cons(b, rest) =>
        assert_eq!(b * (b - 1), 0);
        assert_bits(rest),
    }
  }
  -- The verifying key's circuits at active positions, in order.
  fn select_active_circuits(circuits: List‹SysCircuit›, active: List‹G›) -> List‹SysCircuit› {
    match load(circuits) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, crest) =>
        let &ListNode.Cons(b, arest) = active;
        match b {
          0 => select_active_circuits(crest, arest),
          _ => store(ListNode.Cons(c, select_active_circuits(crest, arest))),
        },
    }
  }
  -- The preprocessed-index entries at active positions, in order.
  fn select_active_prep(prep_indices: List‹OptIdx›, active: List‹G›) -> List‹OptIdx› {
    match load(prep_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(p, prest) =>
        let &ListNode.Cons(b, arest) = active;
        match b {
          0 => select_active_prep(prest, arest),
          _ => store(ListNode.Cons(p, select_active_prep(prest, arest))),
        },
    }
  }

  -- Read the public claims from the verifier's IO channel. Wire format (set by
  -- the prover-side harness): u64 `num_claims`, then per claim a u64 `num_vals`
  -- followed by `num_vals` raw `u64` `Val`s (8 LE bytes each, canonical < p).
  fn read_claims(stream: ByteStream) -> (List‹List‹U64››, ByteStream) {
    let (n, s) = read_count(stream);
    read_claims_n(s, n)
  }
  fn read_claims_n(stream: ByteStream, n: G) -> (List‹List‹U64››, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (c, s) = @read_one_claim(stream);
        let (rest, s2) = read_claims_n(s, n - 1);
        (store(ListNode.Cons(c, rest)), s2),
    }
  }
  fn read_one_claim(stream: ByteStream) -> (List‹U64›, ByteStream) {
    let (m, s) = read_count(stream);
    read_claim_vals_n(s, m)
  }
  fn read_claim_vals_n(stream: ByteStream, n: G) -> (List‹U64›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_u64(stream);
        let (rest, s2) = read_claim_vals_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }
⟧

end MultiStark

end
