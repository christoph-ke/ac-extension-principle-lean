# Author rulings and approval (public excerpt)

This is a public excerpt of the project's internal log of questions to the paper's author. It keeps the parts that the
frozen statement files and the manifest `planning/frozen-anchors.json` cite. See [CERTIFICATION.md](../CERTIFICATION.md)
for the context.

## Encoding rulings

- **Q1 (solution class).** The statement uses a minimal class. Continuity of the incoming expansion ν is assumed, as in
  the paper. Every further regularity property used in the proof is derived in Lean (`StandingAssumptions.toFull`).
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

## A1. Approval of the exact frozen bytes — approved 2026-10-12

The author, Christoph Kehle, approved the following on 2026-10-12:
- the exact bytes of the 42 frozen files: the 41 definition files and the theorem file
  `AcExtensionPrinciple/Frozen/MainTheorem.lean` in its draft form. The hashes are listed in
  `planning/frozen-bytes-v1.4.md`, including the draft form's hash;
- decisions D1–D3 (see `planning/freeze-plan.md`);
- the freeze, the seal with `by exact AcExtensionPrinciple.mainTheoremProof`, and an independent seal audit that also
  checks the project's checker copy.

The seal audit passed.
