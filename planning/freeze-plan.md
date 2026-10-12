# Freeze-and-seal plan for Theorem 1 (public excerpt)

This is a public excerpt of the plan by which the statement of Theorem 1 was frozen and sealed; the manifest
`planning/frozen-anchors.json` cites its decisions. See [CERTIFICATION.md](../CERTIFICATION.md) for the context.

## Author decisions (2026-10-12)

- **D1 (checker).** `scripts/check_frozen_anchors.py` is the project's copy of the upstream frozen-anchor checker
  (see the README). It also accepts a literal `structure` as a definition anchor; the whole-file hash covers every field.
  The seal audit reviewed this change.
- **D2 (granularity).** There is one declaration per frozen file: 41 definition anchors, exactly the dependency closure
  of `MainTheoremStatement` computed in Lean, plus the theorem anchor `mainTheorem`. Other declarations of the statement
  files are not frozen.
- **D3 (external inputs).** `SmallBVExistence` (E1) and `BVUniqueness` (E2) are frozen as definitions and enter
  `MainTheoremStatement` as hypotheses, never as axioms. The certified claim is "Theorem 1 assuming E1 and E2".

## Procedure

1. The statement declarations were moved, with their code unchanged, into one file each under
   `AcExtensionPrinciple/Frozen/`. The elaborated declarations were checked to be unchanged.
2. The author approved the exact bytes of the 42 files.
3. Freeze (F1): the files and the manifest were committed. The theorem `mainTheorem` had the draft body `by sorry` and was
   quarantined: nothing imported it, and only the anchor itself imported its proof module.
4. Seal (F2): only the proof body was replaced, by `by exact AcExtensionPrinciple.mainTheoremProof`, and the anchor was
   added to the library root.
5. An independent seal audit checked the bytes, the manifest, the checker, a build from a fresh clone, the axioms and
   the proof route.
