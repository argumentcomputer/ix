import IxAIBench.Bench

/-!
# LLM baseline batches for IxBench

`ixai bench export DIR` writes fixed batches of 25 items as plain text for a language model to
answer zero-shot, and answer keys in a separate directory:

* triage: the first `triageItems` formulas of the full model's held-out set, each asked the three
  triage questions (`valid`, `head`, `coverage`), one question per batch;
* premise reranking: every theorem of the time split's test set with 30 candidates, the IDF
  top 30 among its accessible library theorems in a fixed shuffled order.

`ixai bench score DIR` reads `DIR/answers/{triage,premises}-*.txt`, rebuilds the same items, and scores the model's
answers next to ours on exactly those items. Everything is a pure function of the dataset files
and fixed seeds, so export and score agree without reading each other's state; the manifest's
digests confirm it.

```
DIR/batches/NAME.txt      the prompt for one batch
DIR/keys/triage.tsv       ID, question, formula, answer
DIR/keys/premises.tsv     ID, theorem, gold premises, gold premises among the candidates
DIR/manifest.tsv          batch, kind, items, BLAKE3 of the batch file
DIR/answers/NAME.txt      one answer file per batch, written by the baseline run
```
-/

namespace IxAIBench

open IxAICore IxAIData

def batchSize : Nat := 25
def triageItems : Nat := 100
def candidateCount : Nat := 30
def rerankSeed : Nat := 4711

/-! ## Rendering -/

def atomName : Nat → String
  | 0 => "P" | 1 => "Q" | 2 => "R" | n => s!"P{n}"

def wrapIf (paren : Bool) (s : String) : String := if paren then s!"({s})" else s

/-- A formula in infix notation; `paren` parenthesizes it if compound. -/
def renderAt (paren : Bool) : Formula → String
  | .atom n => atomName n
  | .top => "⊤"
  | .imp a b => wrapIf paren s!"{renderAt true a} → {renderAt true b}"
  | .and a b => wrapIf paren s!"{renderAt true a} ∧ {renderAt true b}"

def renderFormula (f : Formula) : String := renderAt false f

/-- The question text and answer labels for each triage question. -/
def triagePrompt : String → String
  | "valid" =>
    "Question: is the formula valid, i.e. true under every one of the 8 assignments of true/false to P, Q, R?\n" ++
    "Labels: true (valid) | false (some assignment makes it false)"
  | "head" =>
    "Question: what is the formula's conclusion? Follow the implication spine: while the formula has the form A → B, replace it by B. The conclusion is the first formula reached that is not an implication.\n" ++
    "Labels: P | Q | R | top (the conclusion is ⊤) | none (the conclusion is a conjunction)"
  | _ =>
    "Question: how many of the 8 assignments of true/false to P, Q, R make the formula true?\n" ++
    "Labels: never (0 of 8) | rarely (1 to 3) | mostly (4 to 7) | always (all 8)"

def notationText : String :=
  "Notation: P, Q, R are propositional atoms; ⊤ is true; → is implication; ∧ is conjunction. Every compound subformula is parenthesized."

def idPrefix : String → String
  | "valid" => "V" | "head" => "H" | _ => "C"

def itemId (pfx : String) (i : Nat) : String := s!"{pfx}{pad 3 (i + 1)}"

/-- `name ×count` for the extracted constants `name*count,…`, most frequent first, at most
`limit`. -/
def renderConsts (consts : String) (limit : Nat) : String :=
  let named := (splitComma consts).map fun e => match e.splitOn "*" with
    | [n, k] => (n, k.toNat!)
    | _ => (e, 1)
  let sorted := (named.toArray.qsort fun (a, i) (b, j) => i > j || (i == j && a < b)).toList
  let shown := sorted.take limit |>.map fun (n, k) => if k == 1 then n else s!"{n} ×{k}"
  ", ".intercalate shown ++ (if sorted.length > limit then s!", … ({sorted.length - limit} more)" else "")

/-- The extracted `HEAD,LHS,RHS` and `BINDERS,HYPS` fields in words. -/
def renderShape (heads arity : String) : String :=
  let hs := (heads.splitOn ",").map fun h => if h.isEmpty then "–" else h
  let hs := if hs.length == 3 then hs else ["–", "–", "–"]
  let ar := match arity.splitOn "," with
    | [b, h] => s!"{b} leading binders, {h} of them hypotheses"
    | _ => "binders not extracted"
  s!"conclusion head {hs.getD 0 "–"}, its last two arguments' heads {hs.getD 1 "–"} and {hs.getD 2 "–"}; {ar}"

/-- Shape and constants of a library theorem, by name. -/
def describe (p : Premises) (name : String) (limit : Nat) (indent : String) : String :=
  let (tc, hs, ar) := p.raw.getD name ("", "", "")
  s!"{indent}shape: {renderShape hs ar}\n{indent}mentions: {renderConsts tc limit}\n"

/-! ## The items -/

structure TriageItem where
  id : String
  question : String
  pos : Nat
  formula : Formula

def triageSet (full : Config) : List TriageItem :=
  let fs := ({ full with testSize := triageItems }.test Triage.spec)
  questions.flatMap fun (q, pos, _) =>
    (fs.zipIdx.map fun (f, i) => { id := itemId (idPrefix q) i, question := q, pos, formula := f })

structure RerankItem where
  id : String
  item : Item Addr
  /-- Library indices, in presentation order. -/
  cands : Array Nat

/-- The time split's test theorems, each with the IDF top 30 of its candidates in a shuffled order. -/
def rerankSet (p : Premises) : List RerankItem :=
  let sd := p.split .time
  sd.test.zipIdx.map fun (it, i) =>
    let cs := candidates p.pl it
    let ss := idfRankScore p.pl it cs
    let top := ((rankBy ((Array.range cs.size).map fun k => (ss[k]!, k))).extract 0 candidateCount).map (cs[·]!)
    let order := (shuffle (List.range top.size) (Rng.seeded (rerankSeed + i))).1
    { id := itemId "P" i, item := it, cands := order.toArray.map (top[·]!) }

def nameOf (p : Premises) (a : Addr) : String := p.names.getD a (toString a)

def candName (p : Premises) (j : Nat) : String := (p.ld.ex.library[j]?.map (·.2)).getD "?"

/-! ## Export -/

def chunks {α : Type} (xs : List α) : List (List α) := chunk batchSize xs xs.length

def triageBatch (name q : String) (items : List TriageItem) : String :=
  let labels := ((questions.find? (·.1 == q)).map (·.2.2)).getD []
  s!"IxBench v0 baseline batch {name} ({items.length} items)\n\n" ++
  "Answer each item yourself, by reasoning alone: do not write or run code.\n\n" ++
  notationText ++ "\n" ++ triagePrompt q ++ "\n" ++
  "For every item also give your confidence, an integer from 0 to 100, that your label is correct.\n\nItems:\n" ++
  String.join (items.map fun it => s!"{it.id}\t{renderFormula it.formula}\n") ++
  "\nAnswer format: exactly one line per item and nothing else, in the order above:\n" ++
  "ID<TAB>LABEL<TAB>CONFIDENCE\n" ++
  s!"LABEL is one of: {", ".intercalate labels}. CONFIDENCE is an integer 0-100.\n" ++
  s!"Example line: {(items.headD ⟨"V001", q, 0, .top⟩).id}\t{labels.headD "?"}\t80\n"

def rerankBatch (p : Premises) (name : String) (items : List RerankItem) : String :=
  s!"IxBench v0 baseline batch {name} ({items.length} items)\n\n" ++
  "Premise selection in Lean 4 Mathlib (Mathlib.Order.Basic, Mathlib.Logic.Function.Iterate and their imports). " ++
  "For each theorem below, rank the candidate library theorems by how likely the theorem's proof uses them, " ++
  "and give your top 10, most likely first. Answer by reasoning alone: do not write or run code.\n\n" ++
  "Statements are described by their shape, since only that is extracted: the conclusion's head constant and " ++
  "the heads of its last two arguments (for `a ≤ b`: LE.le, then the heads of a and b; – when not a constant " ++
  "application), the number of leading binders and how many are hypotheses, and the constants the statement " ++
  "mentions with their multiplicity.\n\n" ++
  String.join (items.map fun ri =>
    let t := ri.item.thm
    s!"=== {ri.id} theorem {nameOf p t.addr}\n" ++ describe p (nameOf p t.addr) 25 "  " ++ "  candidates:\n" ++
    String.join (ri.cands.toList.zipIdx.map fun (j, k) =>
      s!"  {pad 2 (k + 1)}. {candName p j}\n" ++ describe p (candName p j) 12 "      ") ++ "\n") ++
  "Answer format: exactly one line per theorem and nothing else, in the order above:\n" ++
  "ID<TAB>NAME1,NAME2,…,NAME10\n" ++
  "with the 10 candidate names copied exactly as listed, most likely first, separated by commas.\n" ++
  s!"Example line: {(items.headD ⟨"P001", default, #[]⟩).id}\tname_of_best_candidate,second_name,…\n"

def labelOf (q : String) (k : Nat) : String :=
  (((questions.find? (·.1 == q)).map (·.2.2)).getD []).getD k "?"

def exportBaseline (full : Config) (dir : System.FilePath) : IO UInt32 := do
  let p ← match ← loadPremises with
    | .ok p => pure p
    | .error e => IO.eprintln s!"premise dataset: {e}"; return 1
  IO.FS.createDirAll (dir / "batches")
  IO.FS.createDirAll (dir / "keys")
  IO.FS.createDirAll (dir / "answers")
  let tri := triageSet full
  let mut manifest := #["batch\tkind\titems\tblake3"]
  for (q, _, _) in questions do
    for (b, i) in (chunks (tri.filter (·.question == q))).zipIdx do
      let name := s!"triage-{q}-{pad 2 (i + 1)}"
      let path := dir / "batches" / s!"{name}.txt"
      IO.FS.writeFile path (triageBatch name q b)
      manifest := manifest.push s!"{name}\ttriage-{q}\t{b.length}\t{IxAI.blake3 (← IO.FS.readBinFile path)}"
  IO.FS.writeFile (dir / "keys" / "triage.tsv") ("id\tquestion\tformula\tanswer\n" ++
    String.join (tri.map fun it => s!"{it.id}\t{it.question}\t{renderFormula it.formula}\t{labelOf it.question (slotTarget it.pos it.formula)}\n"))
  let rr := rerankSet p
  for (b, i) in (chunks rr).zipIdx do
    let name := s!"premises-{pad 2 (i + 1)}"
    let path := dir / "batches" / s!"{name}.txt"
    IO.FS.writeFile path (rerankBatch p name b)
    manifest := manifest.push s!"{name}\tpremises\t{b.length}\t{IxAI.blake3 (← IO.FS.readBinFile path)}"
  IO.FS.writeFile (dir / "keys" / "premises.tsv") ("id\ttheorem\tgold\tgold_among_candidates\n" ++
    String.join (rr.map fun ri =>
      let gold := ri.item.premises
      let inC := ri.cands.toList.filter fun j => gold.contains p.pl.prep[j]!.premise.addr
      s!"{ri.id}\t{nameOf p ri.item.addr}\t{",".intercalate (gold.map (nameOf p))}\t{",".intercalate (inC.map (candName p))}\n"))
  IO.FS.writeFile (dir / "manifest.tsv") ("\n".intercalate manifest.toList ++ "\n")
  let goldIn := rr.foldl (fun a ri => a + (ri.item.premises.filter fun g => ri.cands.any (p.pl.prep[·]!.premise.addr == g)).length) 0
  let goldAll := rr.foldl (fun a ri => a + ri.item.premises.length) 0
  IO.println s!"wrote {manifest.size - 1} batches to {dir / "batches"}: {(chunks tri).length} triage ({tri.length} items: {triageItems} formulas × 3 questions), {(chunks rr).length} premise reranking ({rr.length} theorems × {candidateCount} candidates; {goldIn} of {goldAll} gold premises among the candidates)"
  IO.println s!"answer keys in {dir / "keys"}; put each batch's answers in {dir / "answers"}/NAME.txt"
  IO.println s!"manifest {dir / "manifest.tsv"}, BLAKE3 {IxAI.blake3 (← IO.FS.readBinFile (dir / "manifest.tsv"))}"
  return 0

/-! ## Score -/

def trimPunct (s : String) : String :=
  String.ofList (s.toList.filter fun c => c != '`' && c != '*' && c != '"' && c != '\'')

def tokens (l : String) : List String :=
  (((l.replace "\t" " ").replace "," " ").splitOn " ").filter (· ≠ "")

structure Parsed where
  /-- First valid answer per ID. -/
  triage : Std.HashMap String (Nat × Int)
  ranking : Std.HashMap String (Array Nat)
  lines : Nat := 0
  invalid : Nat := 0
  duplicates : Nat := 0
  unknownNames : Nat := 0

/-- Parse every answer line. A line is invalid unless it starts with a known ID followed by a
valid answer for that item. -/
def parseAnswers (p : Premises) (tri : List TriageItem) (rr : List RerankItem) (texts : List String) :
    Parsed := Id.run do
  let triById : Std.HashMap String TriageItem := tri.foldl (fun m it => m.insert it.id it) {}
  let rrById : Std.HashMap String RerankItem := rr.foldl (fun m it => m.insert it.id it) {}
  let mut out : Parsed := { triage := {}, ranking := {} }
  for text in texts do
    for raw in text.splitOn "\n" do
      let l := trimPunct raw.trimAscii.toString
      if l.isEmpty || l.startsWith "```" then continue
      out := { out with lines := out.lines + 1 }
      match tokens l with
      | id :: rest =>
        if let some it := triById.get? id then
          let labels := ((questions.find? (·.1 == it.question)).map (·.2.2)).getD []
          match rest with
          | [lab, conf] =>
            let k? := labels.findIdx? (·.toLower == lab.toLower)
            let c? := (conf.replace "%" "").toNat?
            match k?, c? with
            | some k, some c =>
              if c ≤ 100 then
                if out.triage.contains id then out := { out with duplicates := out.duplicates + 1 }
                else out := { out with triage := out.triage.insert id (k, Int.ofNat (c * 256 / 100)) }
              else out := { out with invalid := out.invalid + 1 }
            | _, _ => out := { out with invalid := out.invalid + 1 }
          | _ => out := { out with invalid := out.invalid + 1 }
        else if let some ri := rrById.get? id then
          let byName : Std.HashMap String Nat := ri.cands.foldl (fun m j => m.insert (candName p j) j) {}
          let mut picks : Array Nat := #[]
          let mut unknown := 0
          for t in rest do
            match byName.get? t with
            | some j => if !picks.contains j && picks.size < 10 then picks := picks.push j
            | none => unknown := unknown + 1
          out := { out with unknownNames := out.unknownNames + unknown }
          if picks.isEmpty then out := { out with invalid := out.invalid + 1 }
          else if out.ranking.contains id then out := { out with duplicates := out.duplicates + 1 }
          else out := { out with ranking := out.ranking.insert id picks }
        else out := { out with invalid := out.invalid + 1 }
      | [] => pure ()
  return out

def scoreBaseline (full : Config) (dir : System.FilePath) : IO UInt32 := do
  let p ← match ← loadPremises with
    | .ok p => pure p
    | .error e => IO.eprintln s!"premise dataset: {e}"; return 1
  let ansDir := dir / "answers"
  let files ← if ← ansDir.pathExists then ansDir.readDir else pure #[]
  let files := (files.filter fun f => f.fileName.endsWith ".txt" &&
    (f.fileName.startsWith "triage-" || f.fileName.startsWith "premises-")).qsort (·.fileName < ·.fileName)
  let texts ← files.toList.mapM fun f => IO.FS.readFile f.path
  let tri := triageSet full
  let rr := rerankSet p
  let parsed := parseAnswers p tri rr texts
  let m := train Triage.spec full
  IO.println s!"# IxBench v0 baseline score ({files.size} answer files, {parsed.lines} answer lines: {parsed.invalid} invalid, {parsed.duplicates} duplicate IDs ignored, {parsed.unknownNames} names not among the candidates)\n"
  IO.println s!"## Triage ({triageItems} held-out formulas of the full model; ours: `train Triage.spec full`)\n"
  let mut rows : Array (List String) := #[]
  for (q, pos, labels) in questions do
    let items := (tri.filter (·.question == q)).toArray
    let ours := predsOf m pos (items.toList.map (·.formula))
    let theirs := items.map fun it =>
      let t := slotTarget pos it.formula
      match parsed.triage.get? it.id with
      | some (k, c) => { target := t, pred := some k, conf := c : Pred }
      | none => { target := t, pred := none, conf := 0 }
    let answered := countIf theirs (·.pred.isSome)
    let rs := resamples boot items.size
    let accT := fun (idx : Array Nat) => (accuracyBp (pick theirs idx) : Int)
    let accO := fun (idx : Array Nat) => (accuracyBp (pick ours idx) : Int)
    let all := identity items.size
    rows := rows.push [q, s!"{answered}/{items.size}",
      s!"{showPct (accT all).toNat} {showCI (bootCI rs accT)}", s!"{showPct (accO all).toNat} {showCI (bootCI rs accO)}",
      s!"{showGap (accT all - accO all)} {showGapCI (pairedCI rs accT accO)}",
      s!"{showPct (macroF1Bp labels.length theirs)} / {showPct (macroF1Bp labels.length ours)}",
      s!"{showMilli (eceMilli theirs)} / {showMilli (eceMilli ours)}"]
  IO.println (table ["question", "answered", "LLM accuracy [95% CI]", "our model", "gap LLM − ours [95% CI]", "macro-F1 LLM / ours", "ECE LLM / ours"] rows.toList)
  IO.println "Unanswered or invalid items count as wrong; ECE is over answered items.\n"
  let f? ← fitScorer (pinnedScorer .time) p.pl (p.split .time)
  let some f := f?.toOption | IO.eprintln "premise scorer left its bounds"; return 1
  let top10 := fun (xs : Array Addr) => xs.extract 0 10
  let addrs := fun (js : Array Nat) => js.map (p.pl.prep[·]!.premise.addr)
  let llm := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    (addrs ((parsed.ranking.get? ri.id).getD #[])) candidateCount).toArray
  let ours := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    (top10 (rankAmong p.pl ri.item ri.cands (f.score p.pl))) candidateCount).toArray
  let idf := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    (top10 (rankAmong p.pl ri.item ri.cands (idfRankScore p.pl))) candidateCount).toArray
  let some f2 := (← fitScorer (v2Scorer .time) p.pl (p.split .time)).toOption
    | IO.eprintln "v2 premise scorer left its bounds"; return 1
  let v2 := (rr.map fun ri => ItemRank.ofRanked benchKs ri.item.premises
    (top10 (rankAmong p.pl ri.item ri.cands (f2.score p.pl))) candidateCount).toArray
  let rs := resamples boot rr.length
  let answered := rr.filter fun ri => parsed.ranking.contains ri.id
  let goldIn := rr.foldl (fun a ri => a + (ri.item.premises.filter fun g => ri.cands.any (p.pl.prep[·]!.premise.addr == g)).length) 0
  let goldAll := rr.foldl (fun a ri => a + ri.item.premises.length) 0
  IO.println s!"## Premise reranking (time split, {rr.length} theorems, {candidateCount} IDF candidates each; {answered.length} answered; {goldIn} of {goldAll} gold premises among the candidates, so R@k ≤ {showPct (bp goldIn goldAll)})\n"
  IO.println "Every ranker reorders the same 30 candidates; recall counts all gold premises; MRR is over the top 10.\n"
  IO.println (table ["ranker", "R@1 [95% CI]", "R@5 [95% CI]", "R@10 [95% CI]", "MRR@10 [95% CI]"]
    [rankRow rs "LLM" llm, rankRow rs "bilinear model" ours, rankRow rs "bilinear model v2" v2, rankRow rs "IDF" idf,
     gapRow rs "LLM − model (paired)" llm ours, gapRow rs "LLM − v2 model (paired)" llm v2,
     gapRow rs "model − v2 model (paired)" ours v2, gapRow rs "LLM − IDF (paired)" llm idf])
  return 0

def main (full : Config) (args : List String) : IO UInt32 :=
  match args with
  | ["export", dir] => exportBaseline full dir
  | ["score", dir] => scoreBaseline full dir
  | _ => do IO.eprintln "usage: ixai bench [tiny|small|full] | ixai bench export DIR | ixai bench score DIR"; return 2

end IxAIBench
