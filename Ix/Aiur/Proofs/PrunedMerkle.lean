/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.PrunedMerkle
import Ix.Aiur.Proofs.Merkle

/-! Shared frontier authentication through reconstructed individual paths.
Hash logs include work performed before a rejected group injection. -/

namespace Aiur.NativeAIR.Merkle

theorem walk_append (hash : Hash) (dimensions : List Dimensions) (rows : List (List G))
    (height index : Nat) (current : Digest) (before after : List Digest) :
    walk hash dimensions rows height index current (before ++ after) =
      let middle := walk hash dimensions rows height index current before
      let final := walk hash dimensions rows (height - before.length) (index / 2^before.length) middle.digest after
      ⟨final.digest, middle.inputs ++ final.inputs⟩ := by
  induction before generalizing height index current with
  | nil => simp only [List.nil_append, walk, List.length_nil, Nat.sub_zero, Nat.pow_zero, Nat.div_one]
  | cons sibling before ih =>
    have subtract : height - 1 - before.length = height - (before.length + 1) := by omega
    have divide : index / 2 / 2^before.length = index / 2^(before.length + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    simp only [List.cons_append, walk, ih, List.length_cons, subtract, divide, List.append_assoc]

end Aiur.NativeAIR.Merkle

namespace Aiur.NativeAIR.PrunedMerkle

theorem Logged.bind_success {first : Logged α} {next : α → Logged β} {value : β}
    (success : (first >>= next).result = some value) :
    ∃ middle, first.result = some middle ∧ (next middle).result = some value ∧
      (first >>= next).inputs = first.inputs ++ (next middle).inputs := by
  change (Logged.bind first next).result = some value at success
  cases running : first.result with
  | none => simp [Logged.bind, running] at success
  | some middle =>
    exact ⟨middle, rfl, by simpa only [Logged.bind, running] using success,
      by change (Logged.bind first next).inputs = _; simp only [Logged.bind, running]⟩

theorem Logged.bind_input_left {first : Logged α} {next : α → Logged β} {input : List UInt8}
    (member : input ∈ first.inputs) : input ∈ (first >>= next).inputs := by
  change input ∈ (Logged.bind first next).inputs
  cases running : first.result with
  | none => simpa only [Logged.bind, running] using member
  | some middle => simp only [Logged.bind, running, List.mem_append]; exact Or.inl member

theorem Logged.bind_input_right {first : Logged α} {next : α → Logged β} {middle : α}
    (success : first.result = some middle) {input : List UInt8} (member : input ∈ (next middle).inputs) :
    input ∈ (first >>= next).inputs := by
  change input ∈ (Logged.bind first next).inputs
  simp only [Logged.bind, success, List.mem_append]
  exact Or.inr member

theorem Logged.bind_if (condition : Prop) [Decidable condition] (left right : Logged α)
    (next : α → Logged β) :
    ((if condition then left else right) >>= next) =
      if condition then left >>= next else right >>= next := by
  by_cases condition <;> simp only [*, ↓reduceIte]

theorem hashInput_value (hash : Merkle.Hash) (input : List UInt8) :
    (hashInput hash input).result = some (hash input) := rfl

theorem hashInput_inputs (hash : Merkle.Hash) (input : List UInt8) :
    (hashInput hash input).inputs = [input] := rfl

open Merkle (Digest Hash Dimensions)

/-- An individual path ending at the current shared node, with every
ordinary hash input contained in the shared execution log. -/
structure TicketAt (hash : Hash) (dimensions : List Dimensions) (height index : Nat)
    (digest : Digest) (inputs : List (List UInt8)) (ticket : Ticket) : Prop where
  shape : Merkle.shape dimensions ticket.rows = true
  bound : ticket.index < 2^Merkle.maxHeight dimensions
  depth : ticket.proof.length + height = Merkle.maxHeight dimensions
  position : ticket.index / 2^ticket.proof.length = index
  digest_eq : (Merkle.walk hash dimensions ticket.rows (Merkle.maxHeight dimensions) ticket.index
    (hash (Merkle.rowBytes dimensions ticket.rows (Merkle.maxHeight dimensions))) ticket.proof).digest = digest
  calls : Merkle.rowBytes dimensions ticket.rows (Merkle.maxHeight dimensions) ::
    (Merkle.walk hash dimensions ticket.rows (Merkle.maxHeight dimensions) ticket.index
      (hash (Merkle.rowBytes dimensions ticket.rows (Merkle.maxHeight dimensions))) ticket.proof).inputs ⊆ inputs

def NodeAt (hash : Hash) (dimensions : List Dimensions) (height : Nat)
    (inputs : List (List UInt8)) (node : Node) : Prop :=
  ∀ ticket ∈ node.tickets, TicketAt hash dimensions height node.index node.digest inputs ticket

/-- A sibling has been paired, but shorter rows have not yet been injected.
The native verifier pairs the whole layer before performing these injections. -/
def PendingAt (hash : Hash) (dimensions : List Dimensions) (height index : Nat)
    (digest : Digest) (inputs : List (List UInt8)) (ticket : Ticket) : Prop :=
  ∃ before sibling previousIndex previousDigest,
    ticket = before.extend sibling ∧
    TicketAt hash dimensions (height + 1) previousIndex previousDigest inputs before ∧
    index = previousIndex / 2 ∧
    digest = hash (Merkle.branchBytes previousIndex previousDigest sibling) ∧
    Merkle.branchBytes previousIndex previousDigest sibling ∈ inputs

def PendingNode (hash : Hash) (dimensions : List Dimensions) (height : Nat)
    (inputs : List (List UInt8)) (node : Node) : Prop :=
  ∀ ticket ∈ node.tickets, PendingAt hash dimensions height node.index node.digest inputs ticket

def origins (nodes : List Node) : List (Nat × List (List G)) :=
  nodes.flatMap fun node => node.tickets.map fun ticket => (ticket.index, ticket.rows)

theorem TicketAt.mono {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {before after : List (List UInt8)} {ticket : Ticket}
    (valid : TicketAt hash dimensions height index digest before ticket) (subset : before ⊆ after) :
    TicketAt hash dimensions height index digest after ticket :=
  { valid with calls := fun _ member => subset (valid.calls member) }

theorem NodeAt.mono {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {before after : List (List UInt8)} {node : Node}
    (valid : NodeAt hash dimensions height before node) (subset : before ⊆ after) :
    NodeAt hash dimensions height after node :=
  fun _ member => (valid _ member).mono subset

theorem PendingAt.mono {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {before after : List (List UInt8)} {ticket : Ticket}
    (valid : PendingAt hash dimensions height index digest before ticket) (subset : before ⊆ after) :
    PendingAt hash dimensions height index digest after ticket := by
  obtain ⟨previous, sibling, previousIndex, previousDigest, same, path, position, digestEq, member⟩ := valid
  exact ⟨previous, sibling, previousIndex, previousDigest, same, path.mono subset,
    position, digestEq, subset member⟩

theorem PendingNode.mono {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {before after : List (List UInt8)} {node : Node}
    (valid : PendingNode hash dimensions height before node) (subset : before ⊆ after) :
    PendingNode hash dimensions height after node :=
  fun _ member => (valid _ member).mono subset

theorem TicketAt.extend {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {inputs : List (List UInt8)} {ticket : Ticket} (sibling : Digest)
    (valid : TicketAt hash dimensions (height + 1) index digest inputs ticket)
    (member : Merkle.branchBytes index digest sibling ∈ inputs) :
    PendingAt hash dimensions height (index / 2)
      (hash (Merkle.branchBytes index digest sibling)) inputs (ticket.extend sibling) :=
  ⟨ticket, sibling, index, digest, rfl, valid, rfl, rfl, member⟩

theorem TicketAt.finish {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {inputs : List (List UInt8)} {ticket : Ticket} (sibling : Digest)
    (valid : TicketAt hash dimensions (height + 1) index digest inputs ticket)
    (calls : (Merkle.step hash dimensions ticket.rows height index digest sibling).inputs ⊆ inputs) :
    TicketAt hash dimensions height (index / 2)
      (Merkle.step hash dimensions ticket.rows height index digest sibling).digest inputs
      (ticket.extend sibling) := by
  have level : Merkle.maxHeight dimensions - ticket.proof.length = height + 1 := by
    have := valid.depth
    omega
  have path := Merkle.walk_append hash dimensions ticket.rows (Merkle.maxHeight dimensions)
    ticket.index (hash (Merkle.rowBytes dimensions ticket.rows (Merkle.maxHeight dimensions)))
    ticket.proof [sibling]
  simp only [level, valid.position, valid.digest_eq, Merkle.walk, Nat.add_sub_cancel,
    List.append_nil] at path
  refine ⟨valid.shape, valid.bound, ?_, ?_, ?_, ?_⟩
  · simp only [Ticket.extend, List.length_append, List.length_singleton]
    have := valid.depth
    omega
  · simp only [Ticket.extend, List.length_append, List.length_singleton, Nat.pow_succ,
      ← Nat.div_div_eq_div_mul, valid.position]
  · simp only [Ticket.extend, path]
  · simp only [Ticket.extend, path]
    intro input member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with leaf | previous | current
    · exact valid.calls (List.mem_cons.mpr (Or.inl leaf))
    · exact valid.calls (List.mem_cons.mpr (Or.inr previous))
    · exact calls current

theorem PendingAt.finish_absent {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {inputs : List (List UInt8)} {ticket : Ticket}
    (valid : PendingAt hash dimensions height index digest inputs ticket)
    (absent : Merkle.hasHeight dimensions height = false) :
    TicketAt hash dimensions height index digest inputs ticket := by
  obtain ⟨before, sibling, previousIndex, previousDigest, rfl, path, rfl, rfl, member⟩ := valid
  have calls : (Merkle.step hash dimensions before.rows height previousIndex previousDigest sibling).inputs ⊆ inputs := by
    simpa only [Merkle.step, absent, Bool.false_eq_true, ↓reduceIte, List.cons_subset,
      List.nil_subset, and_true] using member
  simpa only [Merkle.step, absent, Bool.false_eq_true, ↓reduceIte] using path.finish sibling calls

theorem PendingAt.finish_injected {hash : Hash} {dimensions : List Dimensions} {height index : Nat}
    {digest : Digest} {inputs : List (List UInt8)} {ticket : Ticket} {rows : List (List G)}
    (valid : PendingAt hash dimensions height index digest inputs ticket)
    (present : Merkle.hasHeight dimensions height = true)
    (same : Merkle.rowsAt dimensions ticket.rows height = Merkle.rowsAt dimensions rows height)
    (leaf : Merkle.rowBytes dimensions rows height ∈ inputs)
    (inject : Merkle.pairBytes digest (hash (Merkle.rowBytes dimensions rows height)) ∈ inputs) :
    TicketAt hash dimensions height index
      (hash (Merkle.pairBytes digest (hash (Merkle.rowBytes dimensions rows height)))) inputs ticket := by
  obtain ⟨before, sibling, previousIndex, previousDigest, rfl, path, rfl, rfl, member⟩ := valid
  have bytes : Merkle.rowBytes dimensions before.rows height = Merkle.rowBytes dimensions rows height := by
    change Merkle.rowsAt dimensions before.rows height = Merkle.rowsAt dimensions rows height at same
    exact congrArg (fun (values : List (List G)) => Transcript.fieldsBytes values.flatten) same
  have calls : (Merkle.step hash dimensions before.rows height previousIndex previousDigest sibling).inputs ⊆ inputs := by
    simpa only [Merkle.step, present, ↓reduceIte, bytes, List.cons_subset, List.nil_subset, and_true]
      using And.intro member (And.intro leaf inject)
  simpa only [Merkle.step, present, ↓reduceIte, bytes] using path.finish sibling calls

theorem NodeAt.singleton {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {inputs : List (List UInt8)} {node : Node} (sibling : Digest)
    (valid : NodeAt hash dimensions (height + 1) inputs node)
    (member : Merkle.branchBytes node.index node.digest sibling ∈ inputs) :
    PendingNode hash dimensions height inputs
      ⟨node.index / 2, hash (Merkle.branchBytes node.index node.digest sibling),
        node.tickets.map (Ticket.extend sibling)⟩ := by
  intro ticket ticketMem
  obtain ⟨before, beforeMem, rfl⟩ := List.mem_map.mp ticketMem
  exact (valid before beforeMem).extend sibling member

theorem NodeAt.pair {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {inputs : List (List UInt8)} {first second : Node}
    (left : NodeAt hash dimensions (height + 1) inputs first)
    (right : NodeAt hash dimensions (height + 1) inputs second)
    (adjacent : first.index % 2 = 0 ∧ second.index = first.index + 1)
    (member : Merkle.pairBytes first.digest second.digest ∈ inputs) :
    PendingNode hash dimensions height inputs
      ⟨first.index / 2, hash (Merkle.pairBytes first.digest second.digest),
        first.tickets.map (Ticket.extend second.digest) ++ second.tickets.map (Ticket.extend first.digest)⟩ := by
  have leftBytes : Merkle.branchBytes first.index first.digest second.digest =
      Merkle.pairBytes first.digest second.digest := by simp only [Merkle.branchBytes, adjacent.1, ↓reduceIte]
  have odd : second.index % 2 ≠ 0 := by omega
  have rightBytes : Merkle.branchBytes second.index second.digest first.digest =
      Merkle.pairBytes first.digest second.digest := by simp only [Merkle.branchBytes, odd, ↓reduceIte]
  have position : second.index / 2 = first.index / 2 := by omega
  intro ticket ticketMem
  rcases List.mem_append.mp ticketMem with leftMem | rightMem
  · obtain ⟨before, beforeMem, rfl⟩ := List.mem_map.mp leftMem
    simpa only [leftBytes] using (left before beforeMem).extend second.digest (leftBytes ▸ member)
  · obtain ⟨before, beforeMem, rfl⟩ := List.mem_map.mp rightMem
    simpa only [rightBytes, position] using (right before beforeMem).extend first.digest (rightBytes ▸ member)

theorem origins_cons (node : Node) (nodes : List Node) :
    origins (node :: nodes) = node.tickets.map (fun ticket => (ticket.index, ticket.rows)) ++ origins nodes := rfl

theorem origins_extend (tickets : List Ticket) (sibling : Digest) :
    (tickets.map (Ticket.extend sibling)).map (fun ticket => (ticket.index, ticket.rows)) =
      tickets.map (fun ticket => (ticket.index, ticket.rows)) := by
  simp only [List.map_map, Function.comp_def, Ticket.extend]

theorem combine_refines {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {inputs : List (List UInt8)} {nodes : List Node} {proof : List Digest}
    {parents : List Node} {remaining : List Digest}
    (valid : ∀ node ∈ nodes, NodeAt hash dimensions (height + 1) inputs node)
    (success : (combine hash nodes proof).result = some (parents, remaining)) :
    (∀ parent ∈ parents, PendingNode hash dimensions height (inputs ++ (combine hash nodes proof).inputs) parent) ∧
      origins parents = origins nodes := by
  fun_induction combine hash nodes proof generalizing parents remaining with
  | case1 proof =>
    have same : ([], proof) = (parents, remaining) := Option.some.inj success
    cases same
    exact ⟨by simp, rfl⟩
  | case2 first proof second tail adjacent ih =>
    cases running : (combine hash tail proof).result with
    | none => simp [bind, Logged.bind, hashInput, running] at success
    | some result =>
      rcases result with ⟨rest, boundary⟩
      have tailValid : ∀ node ∈ tail, NodeAt hash dimensions (height + 1) inputs node :=
        fun node member => valid node (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      obtain ⟨restValid, restOrigins⟩ := ih tailValid running
      simp only [bind, pure, Logged.bind, hashInput,
        running, Logged.pure, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      simp only [bind, pure, Logged.bind, hashInput,
        running, Logged.pure, List.append_nil]
      constructor
      · intro node member
        rcases List.mem_cons.mp member with rfl | restMem
        · apply NodeAt.pair
          · exact (valid first (by simp)).mono (by intro input h; simp only [List.mem_append]; exact Or.inl h)
          · exact (valid second (by simp)).mono (by intro input h; simp only [List.mem_append]; exact Or.inl h)
          · exact adjacent
          · simp
        · apply (restValid node restMem).mono
          intro input h
          simp only [List.mem_append] at h ⊢
          exact h.elim Or.inl (fun h => Or.inr (by simp only [List.mem_cons]; exact Or.inr h))
      · simp only [origins_cons, List.map_append, origins_extend, restOrigins, List.append_assoc]
  | case3 first second tail adjacent sibling boundary ih =>
    cases running : (combine hash (second :: tail) boundary).result with
    | none => simp [bind, Logged.bind, hashInput, running] at success
    | some result =>
      rcases result with ⟨rest, leftover⟩
      have tailValid : ∀ node ∈ second :: tail, NodeAt hash dimensions (height + 1) inputs node :=
        fun node member => valid node (List.mem_cons.mpr (Or.inr member))
      obtain ⟨restValid, restOrigins⟩ := ih tailValid running
      simp only [bind, pure, Logged.bind, hashInput,
        running, Logged.pure, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      simp only [bind, pure, Logged.bind, hashInput,
        running, Logged.pure, List.append_nil]
      constructor
      · intro node member
        rcases List.mem_cons.mp member with rfl | restMem
        · apply NodeAt.singleton
          · exact (valid first (by simp)).mono (by intro input h; simp only [List.mem_append]; exact Or.inl h)
          · simp
        · apply (restValid node restMem).mono
          intro input h
          simp only [List.mem_append] at h ⊢
          exact h.elim Or.inl (fun h => Or.inr (by simp only [List.mem_cons]; exact Or.inr h))
      · simp only [origins_cons, origins_extend, restOrigins]
  | case4 => cases success
  | case5 first sibling boundary =>
    simp only [bind, pure, Logged.bind, hashInput, Logged.pure,
      Option.some.injEq, Prod.mk.injEq] at success
    rcases success with ⟨rfl, rfl⟩
    simp only [bind, pure, Logged.bind, hashInput, Logged.pure, List.append_nil]
    constructor
    · intro node member
      obtain rfl := List.mem_singleton.mp member
      apply NodeAt.singleton
      · exact (valid first (by simp)).mono (by intro input h; simp only [List.mem_append]; exact Or.inl h)
      · simp
    · simp only [origins_cons, origins_extend]
  | case6 => cases success

theorem inject_refines {hash : Hash} {dimensions : List Dimensions} {height : Nat}
    {inputs : List (List UInt8)} {nodes output : List Node}
    (present : Merkle.hasHeight dimensions height = true)
    (valid : ∀ node ∈ nodes, PendingNode hash dimensions height inputs node)
    (success : (inject hash dimensions height nodes).result = some output) :
    (∀ node ∈ output, NodeAt hash dimensions height (inputs ++ (inject hash dimensions height nodes).inputs) node) ∧
      origins output = origins nodes := by
  induction nodes generalizing output with
  | nil =>
    have same : [] = output := Option.some.inj success
    subst output
    exact ⟨by simp, rfl⟩
  | cons node nodes ih =>
    unfold inject at success ⊢
    cases ticketsEq : node.tickets with
    | nil => simp only [ticketsEq] at success; cases success
    | cons lead members =>
      simp only [ticketsEq] at success ⊢
      by_cases consistent : (members.all fun ticket =>
          Merkle.rowsAt dimensions ticket.rows height == Merkle.rowsAt dimensions lead.rows height) = true
      · simp only [consistent, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success ⊢
        cases running : (inject hash dimensions height nodes).result with
        | none => simp [bind, Logged.bind, hashInput, running] at success
        | some rest =>
          have tailValid : ∀ child ∈ nodes, PendingNode hash dimensions height inputs child :=
            fun child member => valid child (List.mem_cons.mpr (Or.inr member))
          obtain ⟨restValid, restOrigins⟩ := ih tailValid running
          simp only [bind, pure, Logged.bind, hashInput, running, Logged.pure, Option.some.injEq] at success
          subst output
          simp only [bind, pure, Logged.bind, hashInput, running, Logged.pure, List.append_nil]
          constructor
          · intro child member
            rcases List.mem_cons.mp member with rfl | restMem
            · intro ticket ticketMem
              apply PendingAt.finish_injected (rows := lead.rows)
              · exact (valid node (by simp) ticket (by simpa only [ticketsEq] using ticketMem)).mono
                  (by intro input h; simp only [List.mem_append]; exact Or.inl h)
              · exact present
              · rcases List.mem_cons.mp ticketMem with rfl | member
                · rfl
                · exact beq_iff_eq.mp (List.all_eq_true.mp consistent ticket member)
              · simp
              · simp
            · apply (restValid child restMem).mono
              intro input h
              simp only [List.mem_append] at h ⊢
              exact h.elim Or.inl (fun h => Or.inr (by simp only [List.mem_cons]; exact Or.inr (Or.inr h)))
          · simp only [origins_cons, restOrigins, ticketsEq]
      · have rejected : (members.all fun ticket =>
            Merkle.rowsAt dimensions ticket.rows height == Merkle.rowsAt dimensions lead.rows height) = false :=
          Bool.eq_false_iff.mpr consistent
        simp only [rejected, Bool.not_false, ↓reduceIte] at success
        cases success

theorem initial_refines {hash : Hash} {dimensions : List Dimensions}
    {inputs : List (List UInt8)} {tickets : List Ticket} {nodes : List Node}
    (valid : ∀ ticket ∈ tickets, Merkle.shape dimensions ticket.rows = true ∧
      ticket.index < 2^Merkle.maxHeight dimensions ∧ ticket.proof = [])
    (success : (initial hash dimensions (Merkle.maxHeight dimensions) tickets).result = some nodes) :
    (∀ node ∈ nodes, NodeAt hash dimensions (Merkle.maxHeight dimensions)
      (inputs ++ (initial hash dimensions (Merkle.maxHeight dimensions) tickets).inputs) node) ∧
      origins nodes = tickets.map (fun ticket => (ticket.index, ticket.rows)) := by
  induction tickets generalizing nodes with
  | nil =>
    have same : [] = nodes := Option.some.inj success
    subst nodes
    exact ⟨by simp, rfl⟩
  | cons ticket tickets ih =>
    cases running : (initial hash dimensions (Merkle.maxHeight dimensions) tickets).result with
    | none => simp [initial, bind, Logged.bind, hashInput, running] at success
    | some rest =>
      have tailValid : ∀ child ∈ tickets, Merkle.shape dimensions child.rows = true ∧
          child.index < 2^Merkle.maxHeight dimensions ∧ child.proof = [] :=
        fun child member => valid child (List.mem_cons.mpr (Or.inr member))
      obtain ⟨restValid, restOrigins⟩ := ih tailValid running
      simp only [initial, bind, pure, Logged.bind, hashInput, running, Logged.pure, Option.some.injEq] at success
      subst nodes
      simp only [initial, bind, pure, Logged.bind, hashInput, running, Logged.pure, List.append_nil]
      constructor
      · intro node member
        rcases List.mem_cons.mp member with rfl | restMem
        · intro child childMem
          obtain rfl := List.mem_singleton.mp childMem
          obtain ⟨shape, bound, empty⟩ := valid child (by simp)
          refine ⟨shape, bound, ?_, ?_, ?_, ?_⟩
          · simp only [empty, List.length_nil, Nat.zero_add]
          · simp only [empty, List.length_nil, Nat.pow_zero, Nat.div_one]
          · simp only [empty, Merkle.walk]
          · intro input member
            simp only [empty, Merkle.walk, List.mem_singleton] at member
            subst input
            simp
        · apply (restValid node restMem).mono
          intro input h
          simp only [List.mem_append] at h ⊢
          exact h.elim Or.inl (fun h => Or.inr (by simp only [List.mem_cons]; exact Or.inr h))
      · simp only [origins_cons, restOrigins, List.map_cons, List.map_nil, List.singleton_append]

theorem walk_refines {hash : Hash} {dimensions : List Dimensions} {steps height : Nat}
    {inputs : List (List UInt8)} {nodes output : List Node} {proof remaining : List Digest}
    (bounded : steps ≤ height)
    (valid : ∀ node ∈ nodes, NodeAt hash dimensions height inputs node)
    (success : (walk hash dimensions steps height nodes proof).result = some (output, remaining)) :
    (∀ node ∈ output, NodeAt hash dimensions (height - steps)
      (inputs ++ (walk hash dimensions steps height nodes proof).inputs) node) ∧
      origins output = origins nodes := by
  induction steps generalizing height inputs nodes output proof remaining with
  | zero =>
    have same : (nodes, proof) = (output, remaining) := Option.some.inj success
    cases same
    simp only [walk, pure, Logged.pure, Nat.sub_zero, List.append_nil]
    exact ⟨valid, trivial⟩
  | succ steps ih =>
    have level : height - 1 + 1 = height := by omega
    unfold walk at success ⊢
    obtain ⟨⟨parents, boundary⟩, combined, continued, logEq⟩ := Logged.bind_success success
    obtain ⟨parentValid, parentOrigins⟩ := combine_refines (height := height - 1)
      (by simpa only [level] using valid) combined
    dsimp only at continued logEq
    rw [← Logged.bind_if] at continued logEq
    obtain ⟨next, injected, finished, nextLog⟩ := Logged.bind_success continued
    have nextValid : ∀ node ∈ next, NodeAt hash dimensions (height - 1)
        ((inputs ++ (combine hash nodes proof).inputs) ++
          (if Merkle.hasHeight dimensions (height - 1) then inject hash dimensions (height - 1) parents
           else pure parents).inputs) node := by
      by_cases present : Merkle.hasHeight dimensions (height - 1) = true
      · simp only [present, ↓reduceIte] at injected ⊢
        exact (inject_refines present parentValid injected).1
      · simp only [present, Bool.false_eq_true, ↓reduceIte] at injected ⊢
        have same : parents = next := Option.some.inj injected
        subst next
        intro node member ticket ticketMem
        have missing : Merkle.hasHeight dimensions (height - 1) = false := Bool.eq_false_iff.mpr present
        simpa only [pure, Logged.pure, List.append_nil] using
          (parentValid node member ticket ticketMem).finish_absent missing
    have nextOrigins : origins next = origins parents := by
      split at injected
      next present => exact (inject_refines present parentValid injected).2
      next absent =>
        have same : parents = next := Option.some.inj injected
        subst next
        rfl
    obtain ⟨outputValid, outputOrigins⟩ := ih (by omega) nextValid finished
    constructor
    · have finalHeight : height - 1 - steps = height - (steps + 1) := by omega
      simpa only [logEq, nextLog, List.append_assoc, finalHeight] using outputValid
    · exact outputOrigins.trans (nextOrigins.trans parentOrigins)

theorem mapM_members {read : α → Option β} {inputs : List α} {outputs : List β}
    (success : inputs.mapM read = some outputs) :
    (∀ input ∈ inputs, ∃ output ∈ outputs, read input = some output) ∧
      (∀ output ∈ outputs, ∃ input ∈ inputs, read input = some output) := by
  induction inputs generalizing outputs with
  | nil =>
    have same : [] = outputs := Option.some.inj success
    subst outputs
    simp
  | cons input inputs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at success
    obtain ⟨output, first, rest, running, rfl⟩ := success
    obtain ⟨forward, backward⟩ := ih running
    constructor
    · intro source member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨output, by simp, first⟩
      · obtain ⟨result, member, read⟩ := forward source member
        exact ⟨result, List.mem_cons.mpr (Or.inr member), read⟩
    · intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨input, by simp, first⟩
      · obtain ⟨source, member, read⟩ := backward result member
        exact ⟨source, List.mem_cons.mpr (Or.inr member), read⟩

theorem representatives_refines {indices : List Nat} {rows : List (List (List G))}
    {tickets : List Ticket} (success : representatives indices rows = some tickets) :
    (∀ ticket ∈ tickets, ticket.index ∈ indices ∧ ticket.proof = []) ∧
      ∀ source ∈ indices.zip rows, ∃ ticket ∈ tickets, ticket.index = source.1 ∧ ticket.rows = source.2 := by
  let read : Nat → Option Ticket := fun index => do
    let (_, values) ← (indices.zip rows).find? fun entry => entry.1 == index
    if (indices.zip rows).all (fun entry => entry.1 != index || entry.2 == values) then
      some (Ticket.mk index values [])
    else none
  change (uniqueIndices indices).mapM read = some tickets at success
  have readSpec {index : Nat} {ticket : Ticket} (evaluated : read index = some ticket) :
      ticket.index = index ∧ ticket.proof = [] ∧
        ∀ source ∈ indices.zip rows, source.1 = index → ticket.rows = source.2 := by
    simp only [read, bind, Option.bind_eq_some_iff] at evaluated
    obtain ⟨⟨found, values⟩, _, checked⟩ := evaluated
    split at checked
    next consistent =>
      have same := Option.some.inj checked
      subst ticket
      refine ⟨rfl, rfl, ?_⟩
      intro source member atIndex
      have equality := List.all_eq_true.mp consistent source member
      simp only [atIndex, bne_self_eq_false, Bool.false_or, beq_iff_eq] at equality
      exact equality.symm
    next => cases checked
  obtain ⟨forward, backward⟩ := mapM_members success
  constructor
  · intro ticket member
    obtain ⟨index, indexMem, evaluated⟩ := backward ticket member
    obtain ⟨position, empty, _⟩ := readSpec evaluated
    refine ⟨?_, empty⟩
    simpa only [position, uniqueIndices, List.mem_eraseDups, List.mem_mergeSort] using indexMem
  · intro source member
    have indexMem : source.1 ∈ uniqueIndices indices := by
      simpa only [uniqueIndices, List.mem_eraseDups, List.mem_mergeSort] using (List.of_mem_zip member).1
    obtain ⟨ticket, ticketMem, evaluated⟩ := forward source.1 indexMem
    obtain ⟨position, _, same⟩ := readSpec evaluated
    exact ⟨ticket, ticketMem, position, same source member rfl⟩

theorem replay_refines {hash : Hash} {dimensions : List Dimensions} {capHeight : Nat}
    {indices : List Nat} {rows : List (List (List G))} {proof : List Digest} {nodes : List Node}
    (success : (replay hash dimensions capHeight indices rows proof).result = some nodes) :
    dimensions ≠ [] ∧ rows.length = indices.length ∧
      (∀ node ∈ nodes, NodeAt hash dimensions (min capHeight (Merkle.maxHeight dimensions))
        (replay hash dimensions capHeight indices rows proof).inputs node) ∧
      ∀ source ∈ indices.zip rows, source ∈ origins nodes := by
  unfold replay at success ⊢
  split at success
  · cases success
  next structural =>
    have nonempty : dimensions ≠ [] := by
      simp only [Bool.or_eq_true, List.isEmpty_iff, bne_iff_ne, not_or] at structural
      exact structural.1
    have count : rows.length = indices.length := by
      simp only [Bool.or_eq_true, List.isEmpty_iff, bne_iff_ne, not_or] at structural
      exact Decidable.not_not.mp structural.2
    simp only [if_neg structural]
    dsimp only at success ⊢
    split at success
    · cases success
    next bounded =>
      simp only [if_neg bounded]
      have bounds : ∀ index ∈ indices, index < 2^Merkle.maxHeight dimensions := by
        simpa only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, decide_eq_true_eq] using bounded
      obtain ⟨tickets, represented, continued, firstLog⟩ := Logged.bind_success success
      have representation : representatives indices rows = some tickets := represented
      obtain ⟨ticketIndices, sources⟩ := representatives_refines representation
      split at continued
      · cases continued
      next fitted =>
        have fits : ∀ ticket ∈ tickets, Merkle.shape dimensions ticket.rows = true := by
          have checked := fitted
          simp only [Bool.or_eq_true, bne_iff_ne, Bool.not_eq_true', not_or] at checked
          exact List.all_eq_true.mp (by simpa only [Bool.not_eq_false] using checked.2)
        obtain ⟨leaves, initialized, walked, leafLog⟩ := Logged.bind_success continued
        have initialValid : ∀ ticket ∈ tickets, Merkle.shape dimensions ticket.rows = true ∧
            ticket.index < 2^Merkle.maxHeight dimensions ∧ ticket.proof = [] := by
          intro ticket member
          exact ⟨fits ticket member, bounds ticket.index (ticketIndices ticket member).1,
            (ticketIndices ticket member).2⟩
        obtain ⟨leafValid, leafOrigins⟩ := initial_refines (inputs := []) initialValid initialized
        obtain ⟨⟨roots, remaining⟩, traversed, finished, walkLog⟩ := Logged.bind_success walked
        obtain ⟨rootValid, rootOrigins⟩ := walk_refines (Nat.sub_le _ _) leafValid traversed
        dsimp only at finished walkLog
        split at finished
        next consumed =>
          have same : roots = nodes := Option.some.inj finished
          subst nodes
          refine ⟨nonempty, count, ?_, ?_⟩
          · have heightEq : Merkle.maxHeight dimensions - (Merkle.maxHeight dimensions - capHeight) =
                min capHeight (Merkle.maxHeight dimensions) := by omega
            rw [firstLog, if_neg fitted, leafLog, walkLog]
            simpa only [consumed, ↓reduceIte,
              pure, Logged.pure, ofOption, List.nil_append, List.append_nil, heightEq] using rootValid
          · intro source member
            obtain ⟨ticket, ticketMem, indexEq, rowsEq⟩ := sources source member
            rw [rootOrigins, leafOrigins]
            exact List.mem_map.mpr ⟨ticket, ticketMem, by simp only [indexEq, rowsEq]⟩
        next => cases finished

/-- Every original query, including duplicates and queries merged along the
frontier, has an individual path reaching its shared node. -/
theorem replay_individual {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {indices : List Nat} {rows : List (List (List G))} {query : List (List G)}
    {proof : List Digest} {nodes : List Node}
    (success : (replay hash dimensions capHeight indices rows proof).result = some nodes)
    (member : (index, query) ∈ indices.zip rows) :
    ∃ node ∈ nodes, ∃ path result,
      Merkle.replay hash dimensions capHeight index query path = some result ∧
      result.index = node.index ∧ result.hashing.digest = node.digest ∧
      result.hashing.inputs ⊆ (replay hash dimensions capHeight indices rows proof).inputs := by
  obtain ⟨nonempty, _, valid, sources⟩ := replay_refines success
  have source := sources (index, query) member
  simp only [origins, List.mem_flatMap, List.mem_map] at source
  obtain ⟨node, nodeMem, ticket, ticketMem, same⟩ := source
  obtain ⟨indexEq, rowsEq⟩ := Prod.mk.inj same
  subst index
  subst query
  have path := valid node nodeMem ticket ticketMem
  have count : ticket.proof.length = Merkle.maxHeight dimensions - capHeight := by
    have := path.depth
    omega
  exact ⟨node, nodeMem, ticket.proof, _,
    Merkle.replay_complete nonempty path.shape count path.bound,
    path.position, path.digest_eq, path.calls⟩

theorem verify_individual {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {indices : List Nat} {cap : List Digest} {rows : List (List (List G))} {query : List (List G)}
    {proof : List Digest}
    (accepted : verify hash dimensions capHeight indices cap rows proof = true)
    (member : (index, query) ∈ indices.zip rows) :
    ∃ path result, Merkle.replay hash dimensions capHeight index query path = some result ∧
      Merkle.verify hash dimensions capHeight index cap query path = true ∧
      result.hashing.inputs ⊆ (replay hash dimensions capHeight indices rows proof).inputs := by
  cases running : (replay hash dimensions capHeight indices rows proof).result with
  | none => simp only [verify, running, Bool.false_eq_true] at accepted
  | some nodes =>
    obtain ⟨node, nodeMem, path, result, individual, position, digestEq, inputs⟩ :=
      replay_individual running member
    have capEq : cap[node.index]? = some node.digest := by
      simp only [verify, running, accepts, List.all_eq_true] at accepted
      exact beq_iff_eq.mp (accepted node nodeMem)
    refine ⟨path, result, individual, ?_, inputs⟩
    simp only [Merkle.verify, individual, Merkle.accepts, position, digestEq, capEq, beq_self_eq_true]

theorem verifyCovered_individual {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {indices : List Nat} {cap : List Digest} {rows : List (List (List G))} {query : List (List G)}
    {proof : List Digest}
    (accepted : verifyCovered hash dimensions capHeight indices cap rows proof = true)
    (member : (index, query) ∈ indices.zip rows) :
    ∃ path result, Merkle.replay hash dimensions capHeight index query path = some result ∧
      Merkle.verifyCovered hash dimensions capHeight index cap query path = true ∧
      result.hashing.inputs ⊆ (replay hash dimensions capHeight indices rows proof).inputs := by
  simp only [verifyCovered, Bool.and_eq_true] at accepted
  obtain ⟨path, result, individual, verified, inputs⟩ := verify_individual accepted.2 member
  exact ⟨path, result, individual,
    by simp only [Merkle.verifyCovered, accepted.1, verified, Bool.and_self], inputs⟩

/-- Conflicting shared openings at a common public index expose a collision
within two reconstructed paths. All witness inputs occur in the actual
shared executions, although native verification may reuse their hashes. -/
theorem verify_collision {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List G))} {leftQuery rightQuery : List (List G)}
    {leftProof rightProof : List Digest}
    (coverage : Merkle.covered dimensions capHeight = true)
    (left : verify hash dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verify hash dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery) :
    ∃ inputs,
      inputs ⊆ (replay hash dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replay hash dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn hash inputs ∧ inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, input.length ≤ max 64 (8 * max leftQuery.flatten.length rightQuery.flatten.length) := by
  obtain ⟨leftPath, leftResult, leftReplay, leftAccepted, leftInputs⟩ := verify_individual left leftMember
  obtain ⟨rightPath, rightResult, rightReplay, rightAccepted, rightInputs⟩ := verify_individual right rightMember
  obtain ⟨leftWitness, rightWitness, leftRun, rightRun, collision, count⟩ :=
    Merkle.verify_collision coverage leftAccepted rightAccepted different
  have leftSame := Option.some.inj (leftRun.symm.trans leftReplay)
  have rightSame := Option.some.inj (rightRun.symm.trans rightReplay)
  subst leftWitness
  subst rightWitness
  refine ⟨leftResult.hashing.inputs ++ rightResult.hashing.inputs, ?_, collision, count, ?_⟩
  · intro input member
    simp only [List.mem_append] at member ⊢
    exact member.elim (fun h => Or.inl (leftInputs h)) (fun h => Or.inr (rightInputs h))
  · intro input member
    rcases List.mem_append.mp member with member | member
    · have := Merkle.replay_input_length leftReplay member
      omega
    · have := Merkle.replay_input_length rightReplay member
      omega

theorem verifyCovered_collision {hash : Hash} {dimensions : List Dimensions} {capHeight index : Nat}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List G))} {leftQuery rightQuery : List (List G)}
    {leftProof rightProof : List Digest}
    (left : verifyCovered hash dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verifyCovered hash dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery) :
    ∃ inputs,
      inputs ⊆ (replay hash dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replay hash dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn hash inputs ∧ inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, input.length ≤ max 64 (8 * max leftQuery.flatten.length rightQuery.flatten.length) := by
  simp only [verifyCovered, Bool.and_eq_true] at left right
  exact verify_collision left.1 left.2 right.2 leftMember rightMember different

theorem blake3_collision {dimensions : List Dimensions} {capHeight index : Nat}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List G))} {leftQuery rightQuery : List (List G)}
    {leftProof rightProof : List Digest}
    (left : verifyCovered Blake3.digest dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verifyCovered Blake3.digest dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery) :
    ∃ inputs,
      inputs ⊆ (replay Blake3.digest dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replay Blake3.digest dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn Blake3.digest inputs ∧
      inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, input.length ≤ max 64 (8 * max leftQuery.flatten.length rightQuery.flatten.length) :=
  verifyCovered_collision left right leftMember rightMember different

theorem blake3_native_collision {dimensions : List Dimensions} {capHeight index : Nat}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List G))} {leftQuery rightQuery : List (List G)}
    {leftProof rightProof : List Digest}
    (left : verifyCovered Blake3.digest dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verifyCovered Blake3.digest dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery)
    (leftBound : leftQuery.flatten.length < 2^61) (rightBound : rightQuery.flatten.length < 2^61) :
    ∃ inputs,
      inputs ⊆ (replay Blake3.digest dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replay Blake3.digest dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn Blake3.digest inputs ∧
      inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, Blake3.NativeInput input := by
  obtain ⟨inputs, subset, collision, count, bytes⟩ := blake3_collision left right leftMember rightMember different
  refine ⟨inputs, subset, collision, count, ?_⟩
  intro input member
  have := bytes input member
  unfold Blake3.NativeInput
  omega

end Aiur.NativeAIR.PrunedMerkle
