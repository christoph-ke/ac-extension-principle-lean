# Certification of the statement of Theorem 1

This file explains how the Lean statement of Theorem 1 was fixed and checked, and what the proof status means.

## Certified claim

`AcExtensionPrinciple.mainTheorem : AcExtensionPrinciple.MainTheoremStatement` is proved in Lean with the standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`). `MainTheoremStatement` has the form

    SmallBVExistence → BVUniqueness → ∀ ui S, StandingAssumptions ui S → (continuation ∧ terminal bounds)

so the certified claim is: **Theorem 1 holds for every solution in the class, assuming the external inputs E1
(`SmallBVExistence`) and E2 (`BVUniqueness`)**. E1 and E2 are not proved here; they were checked to be implied by their
sources (Luk–Oh, Anal. PDE 8 (2015), Theorem 5.12, and Christodoulou, CPAM 46 (1993), Theorems 6.2 and 3.1).

## Frozen statement files

The statement consists of 41 definitions (exactly the dependency closure of `MainTheoremStatement`) and the theorem
`mainTheorem`. Each is the only declaration in its own file in `AcExtensionPrinciple/Frozen/`. The manifest
`planning/frozen-anchors.json` records, for each file, the paper revision and line range it encodes, the SHA-256 of the
file, a hash of the elaborated declaration, and its dependencies among the frozen files. For `mainTheorem` it records
the hashes of everything except the proof body, which is the single line `by exact AcExtensionPrinciple.mainTheoremProof`
(the proof is in `AcExtensionPrinciple/Main/Theorem1Proof.lean`).

The paper's author approved the exact bytes of these 42 files on 2026-10-12 (paper source revision `203e554`). The
files were first frozen with the theorem in a quarantined draft state and then sealed by inserting the one-line proof
body. Frozen files are never edited; a change would require a new, separately approved version of the affected
declaration. `scripts/check_frozen_anchors.py` checks the frozen files, the manifest, the sealed proof body and the
absence of unregistered `sorry`. `planning/frozen-bytes-v1.4.md` lists the approved file hashes and the docstring-only
edits made when the statement files were split out of the package files.

## Independent audits

Each audit was refute-first and done by a reviewer who had not written the code under review.

1. **Statement audit (package v1.3).** Every definition was compared with the paper. E1 and E2 were compared page by
   page with Luk–Oh and Christodoulou and found not stronger than their sources. The class was found non-vacuous, and no
   hypothesis makes Theorem 1 trivially true.
2. **Re-audit of package v1.4** (one-sided axis traces; ruling Q10): the new fields match the paper, and the class is
   unchanged. In the repository, `StandingAssumptions.axis_dvpsi_trace` and `axis_dupsi_trace`
   (`Minimal/OneSidedTraces.lean`) derive the former two-dimensional limits from the one-sided ones. Conversely,
   `oneSided_outgoing_of_joint` and `oneSided_incoming_of_joint` (`Minimal/OneSidedPaths.lean`) restrict the
   two-dimensional limits to the characteristics. The auditor also proved in Lean that the old and new standing
   assumptions are equivalent, and so are the old and new statements.
3. **Layout audit.** The frozen files are byte-identical to the approved package declarations, up to the listed
   docstring edits. The `pp.all` elaborations agree, and the frozen set is exactly the statement's dependency closure.
4. **Seal audit.** It found no blocking findings and checked the following:
   - the frozen bytes equal the approved ones;
   - all manifest hashes, recomputed;
   - the checker, which differs from its upstream version only by the change described in the README; deliberate
     breakages were caught;
   - a build from a fresh clone and the axioms;
   - a kernel re-check of the full dependency closure of `mainTheorem`;
   - the proof route: E1 is used to construct the continuation (Lemma 4.1), and E2 only at the identification step.

## Encoding decisions (author rulings cited in the docstrings)

- **Q1 (solution class).** The statement uses a minimal class. Continuity of the incoming expansion ν is assumed, as in
  the paper. Every further regularity property used in the proof (continuity of r, m, λ, φ; absolute continuity along
  characteristics; right-continuous representatives) is derived in Lean (`StandingAssumptions.toFull`).
- **Q2 (chart of the continuation).** The continuation is stated in the original double null chart: there are
  ū ∈ (u_i, 0) and a solution on 𝒬 ∪ {ū ≤ u < v} in Christodoulou's BV class that agrees with the original solution
  off the axis.
- **Q3 (constants).** Constants are chosen inside proofs, after the solution; the statement contains no constants.
- **Q5.** Condition (5) of Luk–Oh's Definition 2.1 (vanishing variation of φ at the axis) is part of the class.
- **Q6.** The class bounds are required on every compact subset of 𝒬, including those reaching v = 0.
- **Q7.** Lemma 4.1 and the continuation are stated in Christodoulou's BV class:
  - E1 = Luk–Oh Theorem 5.12 (Christodoulou's Theorem 6.2);
  - E2 = Christodoulou's Theorem 3.1.
- **Q8.** The reduced equations hold in integral form along characteristic segments.
- **Q10.** The regular-axis traces of ∂ᵥψ/λ and ∂ᵤψ/ν are one-sided limits along both characteristics. Within the
  class they imply the two-dimensional limits (proved in Lean, `Minimal/OneSidedTraces.lean`).
- **D1–D3 (freeze).**
  - D1: the checker accepts `structure` declarations as definition anchors.
  - D2: there are 42 frozen files.
  - D3: E1 and E2 are frozen as definitions and enter as hypotheses.

## Limitations

- E1 and E2 are assumptions of the statement, not formalized theorems.
- The elaborated-declaration hashes in the manifest contain names generated by the Lean compiler. After a toolchain
  change they must be recomputed; the frozen source files and their whole-file hashes are unaffected.
- Paper line numbers in docstrings refer to the LaTeX source revisions named next to them (see the README).
