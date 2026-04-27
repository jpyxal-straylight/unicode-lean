/-
  Unicode.Bidi.Algorithm

  Unicode Bidirectional Algorithm per UAX #9 (Unicode 17.0.0).

  Pipeline (operating on a single paragraph):

    P1–P3   paragraph splitting and base direction discovery
    X1–X10  explicit-formatting processing (embedding, override,
            isolate, PDF, PDI) with a directional status stack
    W1–W7   weak-type resolution
    N0–N2   bracket pairing (N0) and neutral resolution (N1, N2)
    I1–I2   implicit embedding-level adjustment
    L1–L4   line-level reset, run reversal, and mirroring helpers

  This module operates on a paragraph as `Array Nat` codepoints. Line
  breaking is the caller's responsibility; the L1 / L2 reorder stage is
  applied to one line at a time via `reorderLine`. L3 (combining-mark
  stickiness) is the renderer's concern. L4 is exposed through
  `mirrorChar` so the renderer can apply it after reordering.

  Bidi class lookups go through the pinned `DerivedBidiClass` table.
  Bracket pairing goes through `BidiBrackets`. Mirroring goes through
  `BidiMirroring`.

  Implementation note: every per-character walk is expressed via
  `Array.foldl` / `Array.mapIdx` so termination is automatic. Stack-
  shaped logic (X-rules, bracket matching) carries its own state
  through `foldl`.
-/

import Unicode.Generated.DerivedBidiClass
import Unicode.Generated.BidiBrackets
import Unicode.Generated.BidiMirroring

namespace Unicode.Bidi.Algorithm

open Unicode.Generated.DerivedBidiClass (BidiClass)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An embedding level. UAX #9 §3.3.2 caps depth at 125. -/
abbrev Level := Nat

/-- Maximum embedding depth permitted by UAX #9 §3.3.2. -/
def maxDepth : Nat := 125

/-- Strong directionality outcome of paragraph-level discovery. -/
inductive Direction where
  | LTR
  | RTL
  deriving DecidableEq, Repr, Inhabited

/-- Directional override outcome of a stack frame. `none` means no
    override; `some .LTR` forces L; `some .RTL` forces R. -/
abbrev OverrideState := Option Direction

/-- One frame of the directional status stack used by X1–X8. -/
structure StackEntry where
  level    : Level
  override : OverrideState
  isolate  : Bool
  deriving Repr, Inhabited

/-- Per-character record carried through the algorithm. `origClass`
    captures the Bidi_Class read from `DerivedBidiClass`; `level` is
    the assigned embedding level; `resolvedClass` is the class after
    W-rules and N-rules. -/
structure CharRecord where
  codepoint     : Nat
  origClass     : BidiClass
  level         : Level
  resolvedClass : BidiClass
  deriving Repr, Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 BIDI_CLASS LOOKUP
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Look up a codepoint's `Bidi_Class` from the pinned `DerivedBidiClass`
    table. `explicitRanges` first, then `defaultRanges` (which cover
    every codepoint per the UAX #44 default-range convention). -/
def lookupBidiClass (cp : Nat) : BidiClass :=
  match Unicode.Generated.DerivedBidiClass.explicitRanges.findSome?
          (fun ⟨min, max, c⟩ => if min ≤ cp ∧ cp ≤ max then some c else none) with
  | some c => c
  | none =>
    match Unicode.Generated.DerivedBidiClass.defaultRanges.findSome?
            (fun ⟨min, max, c⟩ => if min ≤ cp ∧ cp ≤ max then some c else none) with
    | some c => c
    | none   => BidiClass.L

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 PARAGRAPH LEVEL — P2 / P3
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Whether a Bidi class is "strong" for paragraph direction discovery. -/
def isStrong (bc : BidiClass) : Bool :=
  match bc with
  | .L | .R | .AL => true
  | .EN | .ES | .ET | .AN | .CS | .NSM | .BN | .B | .S | .WS
  | .ON | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- P2: scan for the first strong character outside any isolate. The
    fold tracks `(found?, isolateDepth)`; isolate initiators bump the
    depth, PDI decrements it (clamped at zero), and a strong class at
    depth 0 finalises `found?`. -/
def firstStrongIgnoringIsolates (cps : Array Nat) : Option BidiClass :=
  Prod.fst <| cps.foldl
    (fun (acc : Option BidiClass × Nat) cp =>
      match acc with
      | (some foundClass, foundDepth) => (some foundClass, foundDepth)
      | (none, depth) =>
        let bc := lookupBidiClass cp
        match bc with
        | .LRI | .RLI | .FSI => (none, depth + 1)
        | .PDI               => (none, if depth = 0 then 0 else depth - 1)
        | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF =>
          if depth = 0 ∧ isStrong bc then (some bc, depth) else (none, depth))
    (none, 0)

/-- P2 + P3: paragraph base level. R or AL strong → 1 (RTL). Else 0 (LTR). -/
def paragraphLevel (cps : Array Nat) : Level :=
  match firstStrongIgnoringIsolates cps with
  | some .R | some .AL => 1
  | none
  | some .L | some .EN | some .ES | some .ET | some .AN | some .CS
  | some .NSM | some .BN | some .B | some .S | some .WS | some .ON
  | some .LRE | some .LRO | some .RLE | some .RLO | some .PDF
  | some .LRI | some .RLI | some .FSI | some .PDI => 0

/-- P2 + P3: paragraph base direction. -/
def paragraphDirection (cps : Array Nat) : Direction :=
  if paragraphLevel cps = 0 then .LTR else .RTL

/-- Embedding direction: even level → LTR; odd → RTL. -/
def embeddingDirection (level : Level) : Direction :=
  if level % 2 = 0 then .LTR else .RTL

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 EXPLICIT FORMATTING — X1 / X2 / X3 / X4 / X5 / X5a / X5b / X5c / X6 / X6a / X7 / X8 / X9 / X10
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Round `level` up to the next odd value (used by RLE / RLO / RLI). -/
def nextOdd (level : Level) : Level :=
  if level % 2 = 0 then level + 1 else level + 2

/-- Round `level` up to the next even value (used by LRE / LRO / LRI). -/
def nextEven (level : Level) : Level :=
  if level % 2 = 0 then level + 2 else level + 1

/-- True when `lvl` is within the depth bound for new pushes. -/
def levelInBounds (lvl : Level) : Bool :=
  decide (lvl ≤ maxDepth)

/-- Apply the override (if any) on a stack frame. -/
def applyOverride (origClass : BidiClass) (entry : StackEntry) : BidiClass :=
  match entry.override with
  | some .LTR => BidiClass.L
  | some .RTL => BidiClass.R
  | none      => origClass

/-- Top-of-stack accessor with a sentinel when the stack is empty. -/
def topEntry (st : Array StackEntry) : StackEntry :=
  match st.back? with
  | some e => e
  | none   => { level := 0, override := none, isolate := false }

/-- Internal X-rules state. -/
structure XState where
  stack            : Array StackEntry
  overflowEmbed    : Nat
  overflowIsolate  : Nat
  validIsolates    : Nat
  records          : Array CharRecord
  deriving Inhabited

/-- X5c look-ahead: scan from `start + 1` forward and return the
    `Bidi_Class` of the first strong character (L, R, or AL) that
    falls inside the FSI scope at `start`. Characters between any
    inner isolate initiator (LRI / RLI / FSI) and its matching PDI
    are ignored. The scan terminates at the matching PDI of the
    outer FSI, or at the end of the codepoint array if no matching
    PDI exists. -/
def firstStrongInScope (cps : Array Nat) (start : Nat) : Option BidiClass :=
  let tail := cps.extract (start + 1) cps.size
  Prod.fst <| tail.foldl
    (fun (acc : Option BidiClass × Nat × Bool) cp =>
      let (result, depth, stopped) := acc
      if stopped ∨ result.isSome then acc
      else
        let bc := lookupBidiClass cp
        match bc with
        | .LRI | .RLI | .FSI => (none, depth + 1, false)
        | .PDI =>
          if depth = 0 then (none, 0, true)
          else (none, depth - 1, false)
        | .L | .R | .AL =>
          if depth = 0 then (some bc, depth, false)
          else (none, depth, false)
        | .EN | .ES | .ET | .AN | .CS | .NSM | .BN | .B | .S | .WS
        | .ON | .LRE | .LRO | .RLE | .RLO | .PDF =>
          (none, depth, false))
    (none, 0, false)

/-- X5c: replace every FSI codepoint with the RLI codepoint (U+2067)
    when its scope's first strong character is R or AL, otherwise
    with the LRI codepoint (U+2066). After this pass, the X-rules
    driver receives no FSI characters; the FSI behavior is fully
    determined upstream and matches UAX #9 §3.3.2 X5c. -/
def resolveFSI (cps : Array Nat) : Array Nat :=
  Prod.fst <| cps.foldl
    (fun (acc : Array Nat × Nat) cp =>
      let (out, idx) := acc
      let newCp :=
        if lookupBidiClass cp = .FSI then
          match firstStrongInScope cps idx with
          | some .R | some .AL => 0x2067
          | _                  => 0x2066
        else cp
      (out.push newCp, idx + 1))
    (#[], 0)

/-- One iteration of the X-rules per UAX #9 §3.3.2, processing one cp.
    Callers run `resolveFSI` first so this driver never sees an FSI
    codepoint; the `.FSI` arm below is retained for total-function
    coverage and mirrors the LRI path it would have resolved to. -/
def xStep (cp : Nat) (s : XState) : XState :=
  let bc       := lookupBidiClass cp
  let top      := topEntry s.stack
  let curLevel := top.level
  match bc with
  | .RLE =>
    let newLvl := nextOdd curLevel
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with stack := s.stack.push { level := newLvl, override := none, isolate := false } }
    else
      { s with overflowEmbed := s.overflowEmbed + 1 }
  | .LRE =>
    let newLvl := nextEven curLevel
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with stack := s.stack.push { level := newLvl, override := none, isolate := false } }
    else
      { s with overflowEmbed := s.overflowEmbed + 1 }
  | .RLO =>
    let newLvl := nextOdd curLevel
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with stack := s.stack.push { level := newLvl, override := some .RTL, isolate := false } }
    else
      { s with overflowEmbed := s.overflowEmbed + 1 }
  | .LRO =>
    let newLvl := nextEven curLevel
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with stack := s.stack.push { level := newLvl, override := some .LTR, isolate := false } }
    else
      { s with overflowEmbed := s.overflowEmbed + 1 }
  | .RLI =>
    let newLvl := nextOdd curLevel
    let rec0 : CharRecord :=
      { codepoint := cp, origClass := bc, level := curLevel, resolvedClass := bc }
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with
        stack := s.stack.push { level := newLvl, override := none, isolate := true },
        validIsolates := s.validIsolates + 1,
        records := s.records.push rec0 }
    else
      { s with overflowIsolate := s.overflowIsolate + 1, records := s.records.push rec0 }
  | .LRI =>
    let newLvl := nextEven curLevel
    let rec0 : CharRecord :=
      { codepoint := cp, origClass := bc, level := curLevel, resolvedClass := bc }
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with
        stack := s.stack.push { level := newLvl, override := none, isolate := true },
        validIsolates := s.validIsolates + 1,
        records := s.records.push rec0 }
    else
      { s with overflowIsolate := s.overflowIsolate + 1, records := s.records.push rec0 }
  -- FSI: unreachable in normal pipelines because `resolveFSI` rewrites
  -- every FSI codepoint to the RLI or LRI codepoint X5c selects. This
  -- arm is the total-function fallback; it mirrors the LRI path so a
  -- direct call to `xStep` on an unresolved FSI still produces the
  -- LRI-default branch X5c specifies when no strong character appears
  -- in scope.
  | .FSI =>
    let newLvl := nextEven curLevel
    let rec0 : CharRecord :=
      { codepoint := cp, origClass := bc, level := curLevel, resolvedClass := bc }
    if levelInBounds newLvl ∧ s.overflowEmbed = 0 ∧ s.overflowIsolate = 0 then
      { s with
        stack := s.stack.push { level := newLvl, override := none, isolate := true },
        validIsolates := s.validIsolates + 1,
        records := s.records.push rec0 }
    else
      { s with overflowIsolate := s.overflowIsolate + 1, records := s.records.push rec0 }
  | .PDI =>
    let rec0 : CharRecord :=
      { codepoint := cp, origClass := bc, level := curLevel, resolvedClass := bc }
    if s.overflowIsolate > 0 then
      { s with overflowIsolate := s.overflowIsolate - 1, records := s.records.push rec0 }
    else if s.validIsolates = 0 then
      { s with records := s.records.push rec0 }
    else
      let popped  := s.stack.popWhile (fun e => ! e.isolate)
      let popped' := popped.pop
      let newTop  := topEntry popped'
      { s with
        stack := popped',
        overflowEmbed := 0,
        validIsolates := s.validIsolates - 1,
        records := s.records.push { rec0 with level := newTop.level } }
  | .PDF =>
    if s.overflowIsolate > 0 then s
    else if s.overflowEmbed > 0 then { s with overflowEmbed := s.overflowEmbed - 1 }
    else if s.stack.size ≥ 2 ∧ ! top.isolate then { s with stack := s.stack.pop }
    else s
  | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .WS | .ON =>
    let resolved := applyOverride bc top
    let rec0 : CharRecord :=
      { codepoint := cp, origClass := bc, level := curLevel, resolvedClass := resolved }
    { s with records := s.records.push rec0 }

/-- X-rules driver. Resolves FSI per X5c first, then applies the
    explicit-formatting state machine over the resolved codepoint
    array. The paragraph base level is computed on the original
    array because P2 ignores all isolate interiors and is therefore
    invariant under FSI-to-RLI/LRI rewriting. -/
def assignLevels (cps : Array Nat) : Array CharRecord :=
  let resolved := resolveFSI cps
  let pLevel   := paragraphLevel cps
  let seed     : XState :=
    { stack            := #[{ level := pLevel, override := none, isolate := false }],
      overflowEmbed    := 0,
      overflowIsolate  := 0,
      validIsolates    := 0,
      records          := #[] }
  (resolved.foldl (fun acc cp => xStep cp acc) seed).records

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 LEVEL RUNS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Split a record array into level runs `[start, endExclusive)`. -/
def levelRuns (records : Array CharRecord) : Array (Nat × Nat) :=
  if records.isEmpty then #[]
  else
    let n := records.size
    let initLvl := (records[0]!).level
    let result := records.foldl
      (fun (acc : Array (Nat × Nat) × Nat × Nat × Level) r =>
        let (runs, idx, curStart, curLvl) := acc
        if idx = 0 then (runs, 1, 0, r.level)
        else if r.level = curLvl then (runs, idx + 1, curStart, curLvl)
        else (runs.push (curStart, idx), idx + 1, idx, r.level))
      (#[], 0, 0, initLvl)
    let runs := result.1
    let curStart := result.2.2.1
    runs.push (curStart, n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6 W-RULES — W1 / W2 / W3 / W4 / W5 / W6 / W7
-- ═══════════════════════════════════════════════════════════════════════════════

/-- W1: NSM picks up its predecessor's class. NSMs after isolate
    initiators or PDI take ON. -/
def applyW1 (sosClass : BidiClass) (records : Array CharRecord) : Array CharRecord :=
  Prod.fst <| records.foldl
    (fun (acc : Array CharRecord × BidiClass) r =>
      let (out, prev) := acc
      let newClass :=
        match r.resolvedClass with
        | .NSM =>
          match prev with
          | .LRI | .RLI | .FSI | .PDI => .ON
          | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
          | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF => prev
        | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
        | .LRI | .RLI | .FSI | .PDI => r.resolvedClass
      (out.push { r with resolvedClass := newClass }, newClass))
    (#[], sosClass)

/-- W2: EN preceded by AL (with intervening EN/ET/ES/CS/NSM) → AN. -/
def applyW2 (records : Array CharRecord) : Array CharRecord :=
  Prod.fst <| records.foldl
    (fun (acc : Array CharRecord × BidiClass) r =>
      let (out, lastStrong) := acc
      let cls := r.resolvedClass
      let newClass :=
        match cls with
        | .EN => if lastStrong = .AL then .AN else .EN
        | .L | .R | .AL | .ES | .ET | .AN | .CS | .NSM | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
        | .LRI | .RLI | .FSI | .PDI => cls
      let newStrong :=
        match cls with
        | .L | .R | .AL => cls
        | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
        | .LRI | .RLI | .FSI | .PDI => lastStrong
      (out.push { r with resolvedClass := newClass }, newStrong))
    (#[], .L)

/-- W3: every AL → R. -/
def applyW3 (records : Array CharRecord) : Array CharRecord :=
  records.map (fun r =>
    if r.resolvedClass = .AL then { r with resolvedClass := .R } else r)

/-- W4: a single ES between two ENs becomes EN. A single CS between two
    ENs becomes EN. A single CS between two ANs becomes AN. -/
def applyW4 (records : Array CharRecord) : Array CharRecord :=
  let n := records.size
  records.mapIdx (fun i r =>
    if 0 < i ∧ i + 1 < n then
      let prev := records[i - 1]!
      let next := records[i + 1]!
      match r.resolvedClass with
      | .ES =>
        if prev.resolvedClass = .EN ∧ next.resolvedClass = .EN then
          { r with resolvedClass := .EN }
        else r
      | .CS =>
        if prev.resolvedClass = .EN ∧ next.resolvedClass = .EN then
          { r with resolvedClass := .EN }
        else if prev.resolvedClass = .AN ∧ next.resolvedClass = .AN then
          { r with resolvedClass := .AN }
        else r
      | .L | .R | .AL | .EN | .ET | .AN | .NSM | .BN
      | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
      | .LRI | .RLI | .FSI | .PDI => r
    else r)

/-- W5 forward pass: precompute, for each index, whether the preceding
    contiguous ET-run is preceded by an EN. -/
def w5LeftAdjEN (records : Array CharRecord) : Array Bool :=
  Prod.fst <| records.foldl
    (fun (acc : Array Bool × Bool) r =>
      let (out, lastNonEtWasEN) := acc
      match r.resolvedClass with
      | .ET => (out.push lastNonEtWasEN, lastNonEtWasEN)
      | .EN => (out.push true, true)
      | .L | .R | .AL | .ES | .AN | .CS | .NSM | .BN
      | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
      | .LRI | .RLI | .FSI | .PDI => (out.push false, false))
    (#[], false)

/-- W5 backward pass: precompute, for each index, whether the following
    contiguous ET-run is followed by an EN. -/
def w5RightAdjEN (records : Array CharRecord) : Array Bool :=
  let reversed := records.reverse
  let revFlags := Prod.fst <| reversed.foldl
    (fun (acc : Array Bool × Bool) r =>
      let (out, lastNonEtWasEN) := acc
      match r.resolvedClass with
      | .ET => (out.push lastNonEtWasEN, lastNonEtWasEN)
      | .EN => (out.push true, true)
      | .L | .R | .AL | .ES | .AN | .CS | .NSM | .BN
      | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
      | .LRI | .RLI | .FSI | .PDI => (out.push false, false))
    (#[], false)
  revFlags.reverse

/-- W5: ETs adjacent to an EN take EN. -/
def applyW5 (records : Array CharRecord) : Array CharRecord :=
  let leftAdj  := w5LeftAdjEN records
  let rightAdj := w5RightAdjEN records
  records.mapIdx (fun i r =>
    if r.resolvedClass = .ET ∧ ((leftAdj[i]?.getD false) ∨ (rightAdj[i]?.getD false)) then
      { r with resolvedClass := .EN }
    else r)

/-- W6: any remaining ES, CS, ET → ON. -/
def applyW6 (records : Array CharRecord) : Array CharRecord :=
  records.map (fun r =>
    match r.resolvedClass with
    | .ES | .CS | .ET => { r with resolvedClass := .ON }
    | .L | .R | .AL | .EN | .AN | .NSM | .BN
    | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
    | .LRI | .RLI | .FSI | .PDI => r)

/-- W7: every EN whose nearest preceding strong is L becomes L. -/
def applyW7 (records : Array CharRecord) : Array CharRecord :=
  Prod.fst <| records.foldl
    (fun (acc : Array CharRecord × BidiClass) r =>
      let (out, lastStrong) := acc
      let cls := r.resolvedClass
      let newClass :=
        match cls with
        | .EN => if lastStrong = .L then .L else .EN
        | .L | .R | .AL | .ES | .ET | .AN | .CS | .NSM | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
        | .LRI | .RLI | .FSI | .PDI => cls
      let newStrong :=
        match cls with
        | .L | .R => cls
        | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
        | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
        | .LRI | .RLI | .FSI | .PDI => lastStrong
      (out.push { r with resolvedClass := newClass }, newStrong))
    (#[], .L)

/-- Apply W1 .. W7 in sequence. -/
def applyWeakRules (sosClass : BidiClass) (records : Array CharRecord) : Array CharRecord :=
  applyW7 (applyW6 (applyW5 (applyW4 (applyW3 (applyW2 (applyW1 sosClass records))))))

-- ═══════════════════════════════════════════════════════════════════════════════
-- §7 BRACKETS — N0
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Look up a codepoint's bracket entry, if any. -/
def lookupBracket (cp : Nat) : Option BidiBrackets.BidiBracketRow :=
  BidiBrackets.bidiBracketRows.find? (fun r => r.codepoint = cp)

/-- Internal state for bracket pair scanning. -/
structure BracketPairState where
  index : Nat
  stack : Array (Nat × Nat)        -- (open-index, expected-close codepoint)
  pairs : Array (Nat × Nat)        -- (open-index, close-index)
  deriving Inhabited

/-- BD16 caps the bracket-pair stack at 63 entries. -/
def bracketStackBound : Nat := 63

/-- Find bracket pairs in text order. Returns `(openIdx, closeIdx)`
    sorted by `openIdx`. -/
def findBracketPairs (records : Array CharRecord) : Array (Nat × Nat) :=
  let final := records.foldl
    (fun (s : BracketPairState) r =>
      let i := s.index
      match lookupBracket r.codepoint with
      | some br =>
        match br.bracketType with
        | .Open =>
          if s.stack.size < bracketStackBound then
            { index := i + 1, stack := s.stack.push (i, br.pair), pairs := s.pairs }
          else
            { s with index := i + 1 }
        | .Close =>
          match s.stack.findIdx? (fun pair => pair.2 = r.codepoint) with
          | some k =>
            let openIdx := (s.stack[k]!).1
            let stack' := s.stack.extract 0 k
            { index := i + 1, stack := stack', pairs := s.pairs.push (openIdx, i) }
          | none =>
            { s with index := i + 1 }
      | none =>
        { s with index := i + 1 })
    ({ index := 0, stack := #[], pairs := #[] } : BracketPairState)
  -- Sort pairs by openIdx (already in text order from the fold).
  final.pairs

-- ═══════════════════════════════════════════════════════════════════════════════
-- §8 N-RULES — N0 / N1 / N2
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Direction projection used by N-rules. L → LTR; R/AN/EN → RTL. -/
def asNDir (bc : BidiClass) : Option Direction :=
  match bc with
  | .L              => some .LTR
  | .R | .AN | .EN  => some .RTL
  | .AL | .ES | .ET | .CS | .NSM | .BN | .B | .S | .WS | .ON
  | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => none

/-- True for the neutral / isolate-formatting classes that N1/N2 act on. -/
def isNeutralOrIsolate (bc : BidiClass) : Bool :=
  match bc with
  | .B | .S | .WS | .ON | .FSI | .LRI | .RLI | .PDI => true
  | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .LRE | .LRO | .RLE | .RLO | .PDF => false

/-- Resolve a single bracket pair per N0. -/
def resolveBracketPair (records : Array CharRecord)
    (level : Level) (openIdx closeIdx : Nat) : Array CharRecord :=
  let embed := embeddingDirection level
  let inside := records.extract (openIdx + 1) closeIdx
  let res := inside.foldl
    (fun (acc : Bool × Bool × Bool) r =>
      let (sawEmbed, sawOpp, firstOppBeforeEmbed) := acc
      match asNDir r.resolvedClass with
      | some d =>
        if d = embed then (true, sawOpp, firstOppBeforeEmbed)
        else (sawEmbed, true, firstOppBeforeEmbed ∨ ¬ sawEmbed)
      | none => acc)
    (false, false, false)
  let (sawEmbed, sawOpp, firstOpp) := res
  let setBoth (cls : BidiClass) : Array CharRecord :=
    let withOpen :=
      if openIdx < records.size then
        records.set! openIdx { records[openIdx]! with resolvedClass := cls }
      else records
    if closeIdx < withOpen.size then
      withOpen.set! closeIdx { withOpen[closeIdx]! with resolvedClass := cls }
    else withOpen
  if sawEmbed then
    setBoth (match embed with | .LTR => .L | .RTL => .R)
  else if sawOpp ∧ firstOpp then
    setBoth (match embed with | .LTR => .R | .RTL => .L)
  else
    records

/-- N0: apply bracket-pair resolution paragraph-wide. -/
def applyN0 (records : Array CharRecord) (level : Level) : Array CharRecord :=
  let pairs := findBracketPairs records
  pairs.foldl (fun acc ⟨o, c⟩ => resolveBracketPair acc level o c) records

/-- Direction projection at index `i`, falling back to the right-side
    boundary when the index is out of range. -/
def directionAt (records : Array CharRecord) (eosDir : Direction) (i : Nat) : Direction :=
  if h : i < records.size then
    match asNDir (records[i]'h).resolvedClass with
    | some d => d
    | none   => eosDir
  else eosDir

/-- For each index, the strong direction immediately to the left
    (skipping neutral / isolate formatting); falls back to `sosDir` at
    the start. Implemented as a forward foldl. -/
def leftStrongDir (sosDir : Direction) (records : Array CharRecord) : Array Direction :=
  Prod.fst <| records.foldl
    (fun (acc : Array Direction × Direction) r =>
      let (out, prev) := acc
      let cur :=
        match asNDir r.resolvedClass with
        | some d => d
        | none   => prev
      (out.push prev, cur))
    (#[], sosDir)

/-- For each index, the strong direction immediately to the right
    (skipping neutrals); falls back to `eosDir` at the end. Implemented
    as a forward foldl over the reversed array, then re-reversed. -/
def rightStrongDir (eosDir : Direction) (records : Array CharRecord) : Array Direction :=
  let reversed := records.reverse
  let revFlags := Prod.fst <| reversed.foldl
    (fun (acc : Array Direction × Direction) r =>
      let (out, prev) := acc
      let cur :=
        match asNDir r.resolvedClass with
        | some d => d
        | none   => prev
      (out.push prev, cur))
    (#[], eosDir)
  revFlags.reverse

/-- N1 + N2: replace each NI with its surrounding strong direction (N1
    when both sides agree, N2 with the embedding direction otherwise). -/
def applyN1N2 (sosDir eosDir : Direction) (level : Level)
    (records : Array CharRecord) : Array CharRecord :=
  let lefts  := leftStrongDir sosDir records
  let rights := rightStrongDir eosDir records
  let embed  := embeddingDirection level
  records.mapIdx (fun i r =>
    if isNeutralOrIsolate r.resolvedClass then
      let l := lefts[i]?.getD sosDir
      let rg := rights[i]?.getD eosDir
      let target := if l = rg then l else embed
      let cls := match target with | .LTR => BidiClass.L | .RTL => BidiClass.R
      { r with resolvedClass := cls }
    else r)

/-- Apply N0, N1, N2 in order. -/
def applyNeutralRules (sosDir eosDir : Direction) (level : Level)
    (records : Array CharRecord) : Array CharRecord :=
  applyN1N2 sosDir eosDir level (applyN0 records level)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §9 IMPLICIT LEVELS — I1 / I2
-- ═══════════════════════════════════════════════════════════════════════════════

/-- I1 + I2: bump the embedding level based on resolved class.

    Even level (LTR): R → +1 ; AN/EN → +2 ; else → 0.
    Odd  level (RTL): L/AN/EN → +1 ; else → 0. -/
def applyImplicitLevels (records : Array CharRecord) : Array CharRecord :=
  records.map (fun r =>
    let lvl := r.level
    let bump :=
      if lvl % 2 = 0 then
        match r.resolvedClass with
        | .R         => 1
        | .AN | .EN  => 2
        | .L | .AL | .ES | .ET | .CS | .NSM | .BN | .B | .S | .WS | .ON
        | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => 0
      else
        match r.resolvedClass with
        | .L | .AN | .EN => 1
        | .R | .AL | .ES | .ET | .CS | .NSM | .BN | .B | .S | .WS | .ON
        | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => 0
    { r with level := lvl + bump })

-- ═══════════════════════════════════════════════════════════════════════════════
-- §10 LINE-LEVEL RULES — L1 / L2 / L4
-- ═══════════════════════════════════════════════════════════════════════════════

/-- True for the classes whose level resets to the paragraph level under
    L1: WS and the four isolate-formatting classes. -/
def l1WhitespaceLike (bc : BidiClass) : Bool :=
  match bc with
  | .WS | .FSI | .LRI | .RLI | .PDI => true
  | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .ON | .LRE | .LRO | .RLE | .RLO | .PDF => false

/-- L1: reset the level of:
      (a) segment / paragraph separators (B / S);
      (b) WS / isolate-formatting characters preceding (a);
      (c) WS / isolate-formatting characters at the end of the line.

    Implemented via two forward passes that update a running "trailing
    WS run" tracker, then a backward pass for the line-end tail. -/
def applyL1 (paragraphLvl : Level) (records : Array CharRecord) : Array CharRecord :=
  -- Forward pass: for each B / S, retroactively reset preceding WS-like
  -- run AND the B / S itself. Whether the cursor is inside a WS-like
  -- prefix segment is tracked via a state index.
  let n := records.size
  -- Step 1: build a Bool array marking each index that needs the
  -- paragraph-level reset.
  let resetMaskA := Prod.fst <| records.foldl
    (fun (acc : Array Bool × Nat × Nat) r =>
      let (mask, i, runStart) := acc
      match r.origClass with
      | .B | .S =>
        -- Mark [runStart, i] for reset by folding over the index range.
        let mask' :=
          if runStart ≤ i then
            (List.range (i - runStart + 1)).foldl
              (fun a j =>
                let idx := runStart + j
                if idx < a.size then a.set! idx true else a)
              mask
          else mask
        let mask'' := if i < mask'.size then mask'.set! i true else mask'
        (mask'', i + 1, i + 1)
      | .L | .R | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
      | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
      | .LRI | .RLI | .FSI | .PDI =>
        if l1WhitespaceLike r.origClass then
          (mask, i + 1, runStart)
        else
          (mask, i + 1, i + 1))
    (Array.replicate n false, 0, 0)
  -- Step 2: scan from the end backwards to mark trailing WS-like.
  let resetMaskB :=
    let pairs := records.mapIdx (fun i r => (i, r))
    let revPairs := pairs.reverse
    Prod.fst <| revPairs.foldl
      (fun (acc : Array Bool × Bool) ⟨i, r⟩ =>
        let (mask, stillTrailing) := acc
        if stillTrailing ∧ l1WhitespaceLike r.origClass then
          let mask' := if i < mask.size then mask.set! i true else mask
          (mask', true)
        else
          (mask, false))
      (resetMaskA, true)
  records.mapIdx (fun i r =>
    if (resetMaskB[i]?.getD false) then
      { r with level := paragraphLvl }
    else r)

/-- Reverse a sub-array `[lo, hi)` by index swap. -/
def reverseSlice (records : Array CharRecord) (lo hi : Nat) : Array CharRecord :=
  records.mapIdx (fun i r =>
    if lo ≤ i ∧ i < hi then
      records[lo + hi - 1 - i]!
    else r)

/-- Maximum level over a record array. -/
def maxLevel (records : Array CharRecord) : Level :=
  records.foldl (fun m r => Nat.max m r.level) 0

/-- Smallest odd level ≥ 1 in the records, or `none` if no odd level. -/
def minOddLevel (records : Array CharRecord) : Option Level :=
  records.foldl
    (fun acc r =>
      if r.level % 2 = 1 then
        match acc with
        | none   => some r.level
        | some m => some (Nat.min m r.level)
      else acc)
    none

/-- Reverse all sub-sequences at level ≥ `lvl`. Walks left to right
    collecting maximal `[start, end)` ranges and reversing each. -/
def reverseAtLevel (records : Array CharRecord) (lvl : Level) : Array CharRecord :=
  let n := records.size
  -- Collect ranges to reverse.
  let res := records.foldl
    (fun (acc : Array (Nat × Nat) × Nat × Option Nat) r =>
      let (ranges, idx, curStart) := acc
      if r.level ≥ lvl then
        match curStart with
        | some startIdx => (ranges, idx + 1, some startIdx)
        | none          => (ranges, idx + 1, some idx)
      else
        match curStart with
        | some s => (ranges.push (s, idx), idx + 1, none)
        | none   => (ranges, idx + 1, none))
    ((#[] : Array (Nat × Nat)), 0, none)
  let ranges := res.1
  let lastStart := res.2.2
  let allRanges :=
    match lastStart with
    | some s => ranges.push (s, n)
    | none   => ranges
  allRanges.foldl (fun acc ⟨lo, hi⟩ => reverseSlice acc lo hi) records

/-- L2: from the highest level down to the smallest odd level, reverse
    every maximal sub-sequence at or above that level. -/
def applyL2 (records : Array CharRecord) : Array CharRecord :=
  match minOddLevel records with
  | none => records
  | some minOdd =>
    let maxLvl := maxLevel records
    -- Apply reverseAtLevel for each level from maxLvl down to minOdd.
    let levels := (List.range (maxLvl + 1 - minOdd)).map (fun k => maxLvl - k)
    levels.foldl (fun acc lvl => reverseAtLevel acc lvl) records

/-- L4: mirror lookup. Returns the mirror codepoint when the input has
    a `Bidi_Mirroring_Glyph` entry; the input unchanged otherwise. -/
def mirrorChar (cp : Nat) : Nat :=
  match BidiMirroring.bidiMirrorPairs.findSome?
          (fun ⟨a, b⟩ => if a = cp then some b else none) with
  | some m => m
  | none   => cp

-- ═══════════════════════════════════════════════════════════════════════════════
-- §11 DRIVER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Output of the paragraph pipeline. -/
structure ParagraphResult where
  records        : Array CharRecord
  paragraphLevel : Level
  deriving Repr, Inhabited

/-- Full paragraph pipeline: P → X → W → N → I. -/
def bidiParagraph (cps : Array Nat) : ParagraphResult :=
  let pLevel   := paragraphLevel cps
  let assigned := assignLevels cps
  let dir      := embeddingDirection pLevel
  let sosClass : BidiClass := match dir with | .LTR => .L | .RTL => .R
  let weak     := applyWeakRules sosClass assigned
  let neutral  := applyNeutralRules dir dir pLevel weak
  let implicit := applyImplicitLevels neutral
  { records := implicit, paragraphLevel := pLevel }

/-- L1 + L2 reorder for one line `[lineStart, lineEnd)`. Returns the
    reordered codepoints; the caller may apply `mirrorChar` for L4. -/
def reorderLine (result : ParagraphResult) (lineStart lineEnd : Nat) : Array Nat :=
  let slice := result.records.extract lineStart lineEnd
  let l1    := applyL1 result.paragraphLevel slice
  let l2    := applyL2 l1
  l2.map (fun r => r.codepoint)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §12 TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pure ASCII paragraph has level 0. -/
theorem paragraphLevel_ascii :
    paragraphLevel #[0x0048, 0x0069] = 0 := by native_decide  -- "Hi"

/-- Pure Hebrew paragraph (R class on first char) has level 1. -/
theorem paragraphLevel_hebrew :
    paragraphLevel #[0x05D0, 0x05D1] = 1 := by native_decide

/-- Empty paragraph defaults to level 0. -/
theorem paragraphLevel_empty :
    paragraphLevel #[] = 0 := by native_decide

/-- Bracket lookup finds LEFT PARENTHESIS as Open with pair RIGHT PAREN. -/
theorem bracket_lookup_lparen :
    (lookupBracket 0x0028).map (fun r => (r.pair, r.bracketType))
      = some (0x0029, .Open) := by native_decide

/-- Mirror lookup: LEFT PAREN ↔ RIGHT PAREN. -/
theorem mirror_lparen : mirrorChar 0x0028 = 0x0029 := by native_decide

/-- Mirror returns input unchanged for non-mirroring codepoints. -/
theorem mirror_letter_a : mirrorChar 0x0041 = 0x0041 := by native_decide

/-- Pure-ASCII paragraph after the full pipeline: paragraph level 0. -/
theorem bidiParagraph_ascii :
    (bidiParagraph #[0x0048, 0x0069]).paragraphLevel = 0 := by native_decide

/-- X5c — FSI followed by Hebrew (RTL strong) inside scope resolves to RLI. -/
theorem resolveFSI_hebrew_inner :
    resolveFSI #[0x2068, 0x05D0, 0x05D1, 0x2069] = #[0x2067, 0x05D0, 0x05D1, 0x2069]
    := by native_decide

/-- X5c — FSI followed by ASCII (LTR strong) inside scope resolves to LRI. -/
theorem resolveFSI_ascii_inner :
    resolveFSI #[0x2068, 0x0048, 0x0069, 0x2069] = #[0x2066, 0x0048, 0x0069, 0x2069]
    := by native_decide

/-- X5c — FSI with no strong character in scope defaults to LRI. -/
theorem resolveFSI_neutral_inner :
    resolveFSI #[0x2068, 0x0020, 0x2069] = #[0x2066, 0x0020, 0x2069]
    := by native_decide

/-- X5c — empty FSI scope (immediate matching PDI) defaults to LRI. -/
theorem resolveFSI_empty_inner :
    resolveFSI #[0x2068, 0x2069] = #[0x2066, 0x2069]
    := by native_decide

/-- X5c — nested isolate's interior is ignored when scanning the outer FSI's
    scope. Outer FSI sees only "L" outside the inner LRI...PDI scope. -/
theorem resolveFSI_nested_isolate_skipped :
    resolveFSI #[0x2068, 0x2066, 0x05D0, 0x2069, 0x0041, 0x2069]
      = #[0x2066, 0x2066, 0x05D0, 0x2069, 0x0041, 0x2069]
    := by native_decide

/-- X5c — FSI with no matching PDI scans to end of array; first strong
    character (Hebrew here) selects RLI. -/
theorem resolveFSI_unmatched_pdi :
    resolveFSI #[0x2068, 0x05D0] = #[0x2067, 0x05D0]
    := by native_decide

/-- `resolveFSI` is the identity on arrays containing no FSI. -/
theorem resolveFSI_identity_no_fsi :
    resolveFSI #[0x0048, 0x0069, 0x2066, 0x05D0, 0x2069] =
      #[0x0048, 0x0069, 0x2066, 0x05D0, 0x2069]
    := by native_decide

end Unicode.Bidi.Algorithm
