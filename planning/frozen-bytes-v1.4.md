# Approved bytes of the frozen statement files (package v1.4)

The 42 files in `AcExtensionPrinciple/Frozen/` (41 definitions and the theorem `mainTheorem`) were approved byte for byte
by the paper's author on 2026-10-12; see [CERTIFICATION.md](../CERTIFICATION.md). They were split out of the statement
files of approval package v1.4 (paper source revision `203e554`) with their code unchanged; five declarations received
docstring-only edits, listed below. The theorem file was approved with the draft proof body `by sorry` and then sealed
by replacing exactly that body with `by exact AcExtensionPrinciple.mainTheoremProof`. The approved draft form of
`AcExtensionPrinciple/Frozen/MainTheorem.lean` had SHA-256
`155f7a5a80400d1c6d4ac015417839d6459a8c97bf370f0ffceaab3d9c42f779`. The manifest `planning/frozen-anchors.json`
records the hashes of the bytes before and after the proof body, which the seal did not change.

## Docstring-only edits relative to the v1.4 package code

Code with comments stripped is identical for all 41 declarations; 36 declaration blocks are byte-identical.

```diff
--- approved package v1.4: AcExtensionPrinciple/External/BVUniqueness.lean
+++ Frozen/BVUniqueness.lean
@@ -1,8 +1,8 @@
-/-- Candidate external input E2: uniqueness of r, φ, m in a common chart
-from equal r, φ on the initial cone u = 0, on any domain of development.
-Paper `203e554`, lines 1400–1406; Christodoulou Thm. 3.1, p. 1148,
-and its proof pp. 1148–1156. The chart is Christodoulou's: Γ = {u = v} (pp. 1135–1136), and on the
-initial cone v = 2r, i.e. r(0,v) = v/2, which p. 1136 offers as an alternative natural choice and which is
-adopted from p. 1157 on; the proof of Thm. 3.1 does not use the normalization on the initial cone, so this
-premise only weakens E2. The axis parameters are determined by D,
-so no arbitrary parameter set can discard required boundary conditions. -/
+/-- External input E2 (a hypothesis of `MainTheoremStatement`, not an axiom): uniqueness of r, φ, m
+in a common chart from equal r, φ on the initial cone u = 0, on any domain of development. Paper
+`203e554`, lines 1400–1406; Christodoulou Thm. 3.1, p. 1148, and its proof pp. 1148–1156. The chart
+is Christodoulou's: Γ = {u = v} (pp. 1135–1136), and on the initial cone v = 2r, i.e. r(0,v) = v/2,
+which p. 1136 offers as an alternative natural choice and which is adopted from p. 1157 on; the
+proof of Thm. 3.1 does not use the normalization on the initial cone, so this premise only weakens
+E2. The axis parameters are determined by D, so no arbitrary parameter set can discard required
+boundary conditions. -/
```

```diff
--- approved package v1.4: AcExtensionPrinciple/External/ChristodoulouBV.lean
+++ Frozen/ChrBVCore.lean
@@ -44,5 +44,6 @@
-  /-- BV representative convention: the BV fields are right-continuous in their BV direction (items 1 and 5:
-  λ, θ in v; ν, ζ in u; equivalently, since φ is continuous off Γ, λ, ∂ᵥψ = θ + λφ in v and ν,
-  ∂ᵤψ = ζ + νφ in u, as stated in the paper, line 269). Sources: Luk–Oh pp. 1608–1609 ("functions of bounded variation … will be assumed to be
-  right-continuous"); for Christodoulou's constructed solutions: ν, β adjusted to be right-continuous in u (p. 1196),
-  α(u,·) right-continuous (p. 1197), λ continuous except on Γ (p. 1198), φ continuous off Γ (p. 1185). -/
+  /-- BV representative convention: the BV fields are right-continuous in their BV direction (items
+  1 and 5: λ, θ in v; ν, ζ in u; equivalently, since φ is continuous off Γ, λ, ∂ᵥψ = θ + λφ in v and
+  ν, ∂ᵤψ = ζ + νφ in u, as stated in the paper, line 269). Sources: Luk–Oh pp. 1608–1609 ("functions
+  of bounded variation … will be assumed to be right-continuous"); for Christodoulou's constructed
+  solutions: ν, β adjusted to be right-continuous in u (p. 1196), α(u,·) right-continuous (p. 1197),
+  λ continuous except on Γ (p. 1198), φ continuous off Γ (p. 1185). -/
```

```diff
--- approved package v1.4: AcExtensionPrinciple/Main/Statement.lean
+++ Frozen/MainTheoremStatement.lean
@@ -1,4 +1,3 @@
-/-- Candidate Theorem 1, conditional only on E1/E2 and the standing
-hypotheses. Paper `203e554`, `thm:main`, lines 112–146,
-`eq:terminal-bv-bound`, and line 145; author rulings Q2 and Q5–Q8.
-The regular axis parameters are all a ≥ ui, including a = 0. -/
+/-- Theorem 1, conditional only on E1/E2 and the standing hypotheses. Paper `203e554`, `thm:main`,
+lines 112–146, `eq:terminal-bv-bound`, and line 145; author rulings Q1–Q3, Q5–Q8 and Q10. The
+regular axis parameters are all a ≥ ui, including a = 0. -/
```

```diff
--- approved package v1.4: AcExtensionPrinciple/Solution/Fields.lean
+++ Frozen/SSFieldsRadiusCoeff.lean
@@ -2 +2 @@
-Luk–Oh (2-6). This additional shared definition belongs to this draft. -/
+Luk–Oh (2-6). It is the common right-hand side ∂ᵥν = ∂ᵤλ = κϰν. -/
```

```diff
--- approved package v1.4: AcExtensionPrinciple/External/SmallBVExistence.lean
+++ Frozen/SmallBVExistence.lean
@@ -1,2 +1,2 @@
-/-- Candidate external input E1: universal small-data existence and strict
-ε-parametrized estimates, in the original Christodoulou BV class.
+/-- External input E1 (a hypothesis of `MainTheoremStatement`, not an axiom): universal
+small-data existence and strict ε-parametrized estimates, in the original Christodoulou BV class.
```

## File hashes (SHA-256 of the shipped files)

- `AcExtensionPrinciple/Frozen/AdjacentAxis.lean`: `76989fcae93030eea6e8133df5da7b27d4faff89082941d2795b8d537fad2f14`
- `AcExtensionPrinciple/Frozen/Axis.lean`: `c844d9db21c248a214b3a48474a65a5cf6e2b9127e3fb5459c476415dd0aabb1`
- `AcExtensionPrinciple/Frozen/AxisDiagonal.lean`: `87f4964a4932b668041dc0d52d04b1f622fcd4f343b575b63e6499154c077de6`
- `AcExtensionPrinciple/Frozen/AxisVanishingVariation.lean`: `5e5c8bc9d6d011b38db3480c399b3554ae0b7460d0b59ab9789abd7d20f619d2`
- `AcExtensionPrinciple/Frozen/BVUniqueness.lean`: `bf56106a6a52ce351b34bcd54ade8f7fae49ca160310f2ed8b9b72afb4ddb0db`
- `AcExtensionPrinciple/Frozen/BlueshiftSup.lean`: `7a5854716522982e04ed812df2cdae2e722b6155e202ecb047c1cadc3709bdda`
- `AcExtensionPrinciple/Frozen/ChrAxisVanishingVariation.lean`: `408f062e916f8e01bfa60d350683bdd1128d648f92d6aeea19d85c995960b499`
- `AcExtensionPrinciple/Frozen/ChrBVBoundsOn.lean`: `d4af7fe8a0758ce1e4e3255878ecf1881dbf6cc6ac102c7b16385b3b14bf58cc`
- `AcExtensionPrinciple/Frozen/ChrBVCore.lean`: `f01d6715466d64951e7bd3ffd0caa636d969d14ef84c0c88be502f6b868c54aa`
- `AcExtensionPrinciple/Frozen/ChristodoulouBV.lean`: `d2b55662563e3847d51bc288f4279f7cbb18f4ca198a416af8755d08a384c87b`
- `AcExtensionPrinciple/Frozen/ContinuationDomain.lean`: `cad44251c02fd725527db82fff1d9a16b054ead134039c42e579fbd07aab79ea`
- `AcExtensionPrinciple/Frozen/DomainOfDevelopment.lean`: `57c23569fa8098169aa629e903d6862959965368c1c82e8e80fcf1e33e29d172`
- `AcExtensionPrinciple/Frozen/FieldsAgreeAt.lean`: `8b1ca8674a54bc2b5e6f520aa124da870cdae020b2914b6624c6ec5c72a55fd9`
- `AcExtensionPrinciple/Frozen/GammaOf.lean`: `2edc4a1cde6cb3b923a2cefbd22f3919f314f8e090fbafe461bc642084796542`
- `AcExtensionPrinciple/Frozen/InSeg.lean`: `eb70c1253cfa6970dc486832a0a7c96a15daadba46e727f7aa51c8022956c4ff`
- `AcExtensionPrinciple/Frozen/IntervalPrimitive.lean`: `08d4da2e23760083491ca10208f24fe304adf16d31c009cf33c506781042682d`
- `AcExtensionPrinciple/Frozen/LocalBVSolution.lean`: `faf61e1840fe53159d7159848882f8773c74eb1517ebbf6ca9486f9b4d5abae0`
- `AcExtensionPrinciple/Frozen/LocalChristodoulouBV.lean`: `cf8adf8399e70a04ff5994562e25be4a274dbfd494d3d12270ec770c8629dd32`
- `AcExtensionPrinciple/Frozen/MainTheorem.lean`: `23d479fa412248ba5ff14c63e4084e31fdb2efe1851636f2a633c0cb10d11970`
- `AcExtensionPrinciple/Frozen/MainTheoremStatement.lean`: `c7a0113cb50fec44fa80250674b1aff5864adfb9e0c4ac8d881720c76f7f8621`
- `AcExtensionPrinciple/Frozen/MassRatio.lean`: `3e84d8246171ee02ea24c799ffe638555806139ce1ed96f01e6b34191348495e`
- `AcExtensionPrinciple/Frozen/OffAxis.lean`: `e59c0f296def750f1568ef586eaf14ddd80147f4e956da8d9b5d0d9140a7a852`
- `AcExtensionPrinciple/Frozen/OutSeg.lean`: `15c5f85b530d674e75b086d93f2cf2c16e0aa6d53e9ef299295d7780138e674b`
- `AcExtensionPrinciple/Frozen/PastSet.lean`: `65817171d4f31adf9a0c0bdc7cff3320275a2f0fe9c69d703deb11dca7aa2daa`
- `AcExtensionPrinciple/Frozen/PastTriangle.lean`: `dfef32bf687d0cb9a9bc7b1d2f7aa16fa7d4da31b695cd357800c1da71538269`
- `AcExtensionPrinciple/Frozen/RegularCenterLocalACBV.lean`: `0d6cf39510d4dbdffddc76d4b2baf2b81259f5714015d73dfd05975b755dfd6e`
- `AcExtensionPrinciple/Frozen/SSFields.lean`: `300a334e30842118e479b96d9f1e82de899618d4ad1f623665a9025017613c11`
- `AcExtensionPrinciple/Frozen/SSFieldsGamma.lean`: `fc1064a9512c2522690d0cdfce132eba301456e01cebb23ea90650046795cdd1`
- `AcExtensionPrinciple/Frozen/SSFieldsMassU.lean`: `e46e62225addc5355b5a3818fb84bda4c760fc692d274e7855863ab5e8b4c044`
- `AcExtensionPrinciple/Frozen/SSFieldsMassV.lean`: `6b46ae6f5d721a944485dcc2ac74f7cece2f9722a9537e513ed9e161a1e14698`
- `AcExtensionPrinciple/Frozen/SSFieldsMu.lean`: `8b2688140ba2b6893f36348c4ea5c9a01205bda9e737df5bdec3ce72e9d035f8`
- `AcExtensionPrinciple/Frozen/SSFieldsRadiusCoeff.lean`: `b88fa3e1730916303d47304b5d65e7617ac716a691ff65710396308929b45a28`
- `AcExtensionPrinciple/Frozen/SSFieldsTheta.lean`: `68e3819ef05a9097bdacc20b6d96b8897cda58c02960f71c2a969edde0de16a8`
- `AcExtensionPrinciple/Frozen/SSFieldsVarkappa.lean`: `cc06789b722aa693433f993494e0adf8dd00482611a6e4702950167f5b21f1e2`
- `AcExtensionPrinciple/Frozen/SSFieldsZeta.lean`: `d7567562b3dbc2a44b7aed16d9697dfaa0e85cd556f7c93c5fd3982258d54554`
- `AcExtensionPrinciple/Frozen/SmallBVDomain.lean`: `cf828488c319f5b1d7f54eeade94bccd85d034b29e159a07bca87efb124d05d3`
- `AcExtensionPrinciple/Frozen/SmallBVExistence.lean`: `a74a353d328b762357178b0047bb46e00ea7fa9f4f0eba3cd2ec3536efd2aa9a`
- `AcExtensionPrinciple/Frozen/SmallBVGeometry.lean`: `c8e30996c673948aee98f118f3e274a0a874c4015b0f32039283c520751b760b`
- `AcExtensionPrinciple/Frozen/SmallBVIncomingTV.lean`: `1f9d54d9271a2d59f1cadc8d4d7ca0f6f2ae6be4206203e55d3c3bcfa215453c`
- `AcExtensionPrinciple/Frozen/SmallBVOutgoingTV.lean`: `d7bfdf78694f002232c1a7127eb4ecccb9fbeae24450f4b6169d0587d7c321e1`
- `AcExtensionPrinciple/Frozen/StandingAssumptions.lean`: `7997eeb23a774de52f220bce1c59050519bd6521e9f3fc1acbdc0021694c10e3`
- `AcExtensionPrinciple/Frozen/VarkappaOf.lean`: `a40fa06801a2f0202f2aae4a97276914912db9fceb66129cf069a2f2bcd334f4`
