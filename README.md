# A blueshift criterion for continuation of the spherically symmetric Einstein–scalar field system — Lean formalization

This repository contains a Lean 4 formalization of the main theorem (Theorem 1) of

> John Anderson, Serban Cicortas, Christoph Kehle, Warren Lee, Jonathan Luk, Yakov Shlapentokh-Rothman,
> Maxime Van de Moortel,
> *A blueshift criterion for continuation of the spherically symmetric Einstein–scalar field system*, in preparation.

This formalization is part of a joint project by John Anderson, Serban Cicortas, Christoph Kehle, Warren Lee,
Jonathan Luk, Yakov Shlapentokh-Rothman and Maxime Van de Moortel, carried out with AI assistance (OpenAI ChatGPT/Codex and Anthropic
Claude), using source-first statement review, frozen declarations, independent audits, and Lean kernel checking. The
paper was prompted by Serban Cicortas and Maxime Van de Moortel.

**In short.** Consider a spherically symmetric Einstein–scalar field solution of bounded variation with a regular
centre, untrapped away from the centre, on a past triangle ending at a possibly singular point $(0,0)$ of the centre.
If $\partial_v(r\phi)$ is absolutely continuous on the initial outgoing cone in the initial radius gauge and the
incoming blueshift is uniformly bounded, then the solution extends, in Christodoulou's BV class, across $(0,0)$, and the
terminal scalar and geometric data have finite variation. The formal statement assumes two
classical results as explicit hypotheses: Christodoulou's small-BV existence theorem (E1) and BV uniqueness (E2). The
proof is complete and uses only the standard axioms of Lean.

The paper is not yet public. This README therefore states the theorem completely; the Lean declarations it refers to
are in [`AcExtensionPrinciple/Frozen/`](AcExtensionPrinciple/Frozen).

## 1. Setting

**Unknowns.** We work in double null coordinates $(u,v)$ on the quotient of a spherically symmetric spacetime. The
unknowns are seven real functions of $(u,v)$ (the Lean structure `SSFields`):

| symbol | Lean | meaning |
|---|---|---|
| $r$ | `r` | area radius |
| $\phi$ | `phi` | scalar field |
| $m$ | `m` | Hawking mass |
| $\lambda$ | `lam` | outgoing derivative of $r$ |
| $\nu$ | `nu` | incoming derivative of $r$ |
| $\Psi_v$ | `dvpsi` | outgoing derivative of $\psi = r\phi$ |
| $\Psi_u$ | `dupsi` | incoming derivative of $\psi = r\phi$ |

All seven are independent functions; the equations below relate them. For solutions, $\lambda = \partial_v r$,
$\nu = \partial_u r$, $\Psi_v = \partial_v(r\phi)$ and $\Psi_u = \partial_u(r\phi)$ in the integral sense.

**Derived quantities.**

$$\mu = \frac{2m}{r}, \qquad \gamma = \frac{\nu}{1-\mu}, \qquad \varkappa = \frac{\mu}{r}, \qquad \theta = \Psi_v - \lambda\phi, \qquad \zeta = \Psi_u - \nu\phi,$$

$$R = \frac{\mu\lambda\nu}{(1-\mu)\,r}, \qquad M_v = \frac{(1-\mu)\,\theta^2}{2\lambda}, \qquad M_u = \frac{(1-\mu)\,\zeta^2}{2\nu}.$$

Here $\theta = r\partial_v\phi$, $\zeta = r\partial_u\phi$, $R = \partial_v\nu = \partial_u\lambda$, and $M_v$, $M_u$ are the null
derivatives of $m$. Division by zero is $0$ (Lean's convention), so $\mu = 0$ where $r = 0$; this is the paper's
convention $\mu = 0$ on the axis.

**Reduced equations in integral form.** A pair $(f,g)$ satisfies $f' = g$ on $[a,b]$ if $g$ is integrable on $[a,b]$
and $f(b) - f(a) = \int_a^b g$ (Lean `IntervalPrimitive`). The reduced Einstein–scalar field equations are imposed in
this form along closed characteristic segments $\lbrace u\rbrace \times [a,b]$ (outgoing) and $[a,b] \times \lbrace v\rbrace$
(incoming):

$$\partial_v r = \lambda,\quad \partial_u r = \nu,\quad \partial_v(r\phi) = \Psi_v,\quad \partial_u(r\phi) = \Psi_u,\quad \partial_v m = M_v,\quad \partial_u m = M_u,$$

$$\partial_u\lambda = R,\quad \partial_v\nu = R,\quad \partial_u\Psi_v = R\,\phi,\quad \partial_v\Psi_u = R\,\phi .$$

**Domain.** For $u_i \lt 0$, the past triangle, its regular axis, and the off-axis part are

$$\mathcal Q = \lbrace (u,v) : u_i \le u \lt 0,\ u \le v \le 0 \rbrace, \qquad \Gamma = \lbrace (u,u) : u_i \le u \lt 0 \rbrace, \qquad \mathcal Q\setminus\Gamma .$$

The endpoint $(0,0)$ of the axis does not belong to $\mathcal Q$.

## 2. The solution class (`RegularCenterLocalACBV`, `LocalBVSolution`)

A solution of the class on $\mathcal Q$ satisfies:

1. **Equations.** The first six equations hold on every closed characteristic segment contained in $\mathcal Q$. The
   last four hold on every closed characteristic segment contained in $\mathcal Q \setminus \Gamma$.
2. **Luk–Oh, Definition 2.1, localized.** The conditions of Luk–Oh, *Anal. PDE* 8 (2015), Definition 2.1 (1)–(7)
   (p. 1611), except the absolute continuity of $\phi$ required in (4), hold with bounds that are uniform on each
   compact $K \subseteq \mathcal Q$, including compact sets that reach $v = 0$ (the paper also imposes this absolute
   continuity; Lean derives it):
   - there is $c_K \gt 0$ with $\lambda \ge c_K$ and $-\nu \le 1/c_K$ on $K$;
   - there is $C_K$ bounding the total variation of $\lambda$, $\phi$ and $\Psi_v$ on every outgoing segment in $K$, and
     of $\nu$, $\phi$ and $\Psi_u$ on every incoming segment in $K$;
   - at every axis point $(a,a) \in \Gamma$:
     - $r(a,a) = m(a,a) = 0$;
     - $\lim_{\varepsilon\downarrow 0}(\nu+\lambda)(a,a+\varepsilon) = 0$ and
       $\lim_{\varepsilon\downarrow 0}(\Psi_v+\Psi_u)(a,a+\varepsilon) = 0$;
     - condition (5), vanishing variation of $\phi$ near the axis: as $\varepsilon \downarrow 0$, the suprema over
       $0 \lt \delta \le \varepsilon$ of $\mathrm{TV}\,\phi(a-\delta,\cdot)$ on $(a-\delta,a)$, of $\mathrm{TV}\,\phi(\cdot,a-\delta)$
       on $(a-\varepsilon,a-\delta)$, of $\mathrm{TV}\,\phi(\cdot,a+\delta)$ on $(a,a+\delta)$ and of
       $\mathrm{TV}\,\phi(a+\delta,\cdot)$ on $(a+\delta,a+\varepsilon)$ tend to $0$. Each variation is taken over the
       part of the interval inside $\mathcal Q$, so at $a = u_i$ only the last two conditions remain.
3. **Continuity of $\nu$.** $\nu$ is continuous on $\mathcal Q$.
4. **Regular axis.** For every $(a,a) \in \Gamma$:
   - $\nu(a,a) = -\lambda(a,a)$;
   - $(\Psi_v/\lambda)(a,a) = (\Psi_u/\nu)(a,a) = \phi(a,a)$;
   - the normalized derivatives have one-sided limits along both characteristics through $(a,a)$:
     $(\Psi_v/\lambda)(a,a+\varepsilon)$, $(\Psi_u/\nu)(a,a+\varepsilon)$, $(\Psi_v/\lambda)(a-\varepsilon,a)$ and
     $(\Psi_u/\nu)(a-\varepsilon,a)$ all tend to $\phi(a,a)$ as $\varepsilon \downarrow 0$, the last two only for
     $a \gt u_i$.

The Lean proof derives every further regularity property it uses from this class together with the hypotheses of
Section 3 (`StandingAssumptions.toFull`): continuity of $r$, $m$, $\lambda$ and $\phi$; absolute continuity along
characteristics; and the two-dimensional limits at the axis.

## 3. Hypotheses of Theorem 1 (`StandingAssumptions`)

- $u_i \lt 0$, and the fields are a solution of the class above on $\mathcal Q$.
- **Signs** away from the axis: $\lambda \gt 0$, $\nu \lt 0$ and $0 \le \mu \lt 1$ at every $(u,v) \in \mathcal Q$ with
  $u \lt v$.
- **Initial radius gauge**: $r(u_i,v) = v - u_i$ and $\lambda(u_i,v) = 1$ for $v \in [u_i,0]$.
- **Absolutely continuous data**: $v \mapsto \Psi_v(u_i,v)$ is absolutely continuous on $[u_i,0]$.
- **Uniform incoming blueshift**:

  $$B_* = \sup_{u_i \lt v \lt 0} \int_{u_i}^{v} \max\bigl(0,\,-\gamma\varkappa\bigr)(u,v)\,du \lt \infty .$$

## 4. Christodoulou's BV class (`ChristodoulouBV`, `LocalChristodoulouBV`)

This follows Christodoulou, *Comm. Pure Appl. Math.* 46 (1993) 1131–1220, definition on pp. 1146–1147. Let $D$ be a
set with $D \subseteq \lbrace u \lt v\rbrace$; the axis is not part of $D$. Let $A$ be a set of axis parameters. The
core conditions (`ChrBVCore`) are:

- all ten equations of Section 1 on every closed characteristic segment contained in $D$;
- $\phi$ is absolutely continuous on every such segment;
- $\lambda$ and $\theta$ are right-continuous in $v$, and $\nu$ and $\zeta$ are right-continuous in $u$, within $D$;
- for every $a \in A$:
  - as $v \downarrow a$ along the outgoing ray $\lbrace(a,v) \in D\rbrace$: $r \to 0$, $m \to 0$, $\nu + \lambda \to 0$ and
    $\Psi_v + \Psi_u \to 0$;
  - $\phi$ has vanishing variation near $(a,a)$ in the form of Christodoulou's item 4. This has the same four families
    as condition (5) above, with the variations taken over the parts of the intervals inside $D$, except that in the
    second and fourth family $\delta$ ranges over $[0,\varepsilon)$.

The bounds on a set $K$ (`ChrBVBoundsOn K D`) are, for constants depending on $K$:

- $\lambda \ge c \gt 0$ and $-\nu \le N$ on $K \cap D$;
- the total variations of $\lambda$, $\phi$ and $\theta$ along every outgoing line in $K \cap D$ are at most $C$;
- the total variations of $\nu$, $\phi$ and $\zeta$ along every incoming line in $K \cap D$ are at most $C$.

The two classes are then defined as follows:
- `ChristodoulouBV D A`: the core conditions and the bounds with $K$ the whole plane;
- `LocalChristodoulouBV D A`: the core conditions and the bounds on every compact
  $K \subseteq D \cup \lbrace (a,a) : a \in A\rbrace$.

## 5. Theorem 1 (`MainTheoremStatement`, proved as `mainTheorem`)

**Theorem.** Assume E1 and E2 (Section 6). Let $u_i \lt 0$ and let $(r,\phi,m,\lambda,\nu,\Psi_v,\Psi_u)$ satisfy the
hypotheses of Section 3. Then:

1. **Continuation.** There are $\bar u \in (u_i,0)$ and fields $(r^+,\phi^+,m^+,\lambda^+,\nu^+,\Psi_v^+,\Psi_u^+)$ in
   `LocalChristodoulouBV` on

   $$\mathcal Q^+ = (\mathcal Q \setminus \Gamma) \cup \lbrace (u,v) : \bar u \le u \lt v \rbrace$$

   with axis parameters $A = [u_i,\infty)$. In particular:
   - the axis conditions hold at every $(a,a)$ with $a \ge u_i$, including the endpoint $(0,0)$, as one-sided limits;
   - the bounds hold on every compact $K \subseteq \mathcal Q^+ \cup \lbrace (a,a) : a \ge u_i\rbrace$, including compact
     sets that reach $v = 0$.

   All seven continued fields agree with the original ones at every point of $\mathcal Q \setminus \Gamma$. The
   continuation is in the original double null chart.
2. **Terminal bounds.** On the terminal cone $v = 0$, each of the functions

   $$u \mapsto \frac{\Psi_u}{\nu}(u,0), \quad \phi(u,0), \quad \log\bigl(-\nu(u,0)\bigr), \quad \nu(u,0), \quad \Psi_u(u,0)$$

   has finite total variation on $[u_i,0)$.

In Lean ([`Frozen/MainTheoremStatement.lean`](AcExtensionPrinciple/Frozen/MainTheoremStatement.lean)):

```lean
@[expose] def MainTheoremStatement : Prop :=
  SmallBVExistence → BVUniqueness → ∀ ui : ℝ, ∀ S : SSFields,
    StandingAssumptions ui S →
    (∃ ū ∈ Ioo ui 0, ∃ Splus : SSFields,
      LocalChristodoulouBV (continuationDomain ui ū) (Ici ui) Splus ∧
      ∀ p ∈ pastTriangle ui \ axis ui, FieldsAgreeAt Splus S p) ∧
    eVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.dupsi u 0) (Ico ui 0) ≠ ⊤
```

The theorem is `AcExtensionPrinciple.mainTheorem : MainTheoremStatement`
([`Frozen/MainTheorem.lean`](AcExtensionPrinciple/Frozen/MainTheorem.lean)).

## 6. The external inputs E1 and E2

Both are **hypotheses** of `MainTheoremStatement`, not axioms. They were compared with their sources page by page and are
not stronger than them.

**E1 (`SmallBVExistence`), small-BV existence.** Source: Luk–Oh, *Anal. PDE* 8 (2015), Theorem 5.12, with Remark 5.13
and footnote 13 (p. 1633), which rests on Christodoulou, *CPAM* 46 (1993), Theorem 6.2 (p. 1183). The statement: there
are $\varepsilon_0 \gt 0$ and $C_0 \gt 0$ such that the following holds for every $\varepsilon \in (0,\varepsilon_0)$ and
every function $\alpha_0$ on $[0,\infty)$ that is right-continuous with $\mathrm{TV}_{(0,\infty)}\alpha_0 \lt \varepsilon$.
There are fields in `ChristodoulouBV` on $\lbrace 0 \le u \lt v\rbrace$, with axis parameters $[0,\infty)$, such that:
- the data are $r(0,v) = v/2$ and $\Psi_v(0,v) = \alpha_0(v)$ for $v \gt 0$;
- $\tfrac13 \le \lambda \le \tfrac12$, $\tfrac13 \le -\nu \le \tfrac23$ and $\tfrac23 \le 1-\mu \le 1$ hold throughout;
- for every $u \ge 0$:

  $$\mathrm{TV}_{(u,\infty)}\tfrac{\Psi_v}{\lambda}(u,\cdot) + \mathrm{TV}_{(u,\infty)}\phi(u,\cdot) + \mathrm{TV}_{(u,\infty)}\log\lambda(u,\cdot) \lt C_0\varepsilon;$$

- for every $v \gt 0$:

  $$\mathrm{TV}_{(0,v)}\tfrac{\Psi_u}{\nu}(\cdot,v) + \mathrm{TV}_{(0,v)}\phi(\cdot,v) + \mathrm{TV}_{(0,v)}\log(-\nu)(\cdot,v) \lt C_0\varepsilon .$$

**E2 (`BVUniqueness`), uniqueness in Christodoulou's BV class.** Source: Christodoulou, *CPAM* 46 (1993), Theorem 3.1
(p. 1148). Let $D \subseteq \lbrace 0 \le u \lt v\rbrace$ be a domain of development: with every $(u,v) \in D$ it
contains $\lbrace (u',v') : 0 \le u' \le u,\ u' \lt v' \le v\rbrace$. Let two solutions in `ChristodoulouBV` on $D$, with
axis parameters $\lbrace a : (a,a) \in \overline D\rbrace$, satisfy:
- $r(0,v) = v/2$ for the first solution;
- equal $r$ and equal $\phi$ on the initial cone $u = 0$.

Then they have the same $r$, $\phi$ and $m$ on $D$.

## 7. What is not formalized

- **E1 and E2** are assumed as hypotheses of the statement, not proved.
- **The reduction itself.** The derivation of the reduced equations of Section 1 from the Einstein–scalar field
  equations in spherical symmetry is not formalized; the formalization starts from the reduced system in integral form.
- **Other results of the paper.** Only Theorem 1 is a certified (frozen and audited) statement. The lemmas and
  propositions of Sections 1–3 and of Appendix A are proved in Lean as steps of the proof, but their Lean forms are
  internal and were not separately audited against the paper. Lemma 4.1 (small-BV existence) is not proved: its
  existence part and estimates are E1, and its uniqueness part is E2.
- **The paper's examples and remarks** are not formalized, including the Roberts example.
- **Existence of solutions in the class.** Non-vacuity is shown for examples only: `AcExtensionPrinciple/Sanity/`
  proves that flat space and every solution that is $C^1$ up to the boundary (with a regular axis, the signs and the
  initial gauge) satisfy the hypotheses, and that the conclusions of E1 hold for constant data. General existence is
  not formalized.

## 8. Status and certification

- `mainTheorem` is proved. `#print axioms AcExtensionPrinciple.mainTheorem` gives
  `[propext, Classical.choice, Quot.sound]`; there is no `sorry`, `admit` or custom axiom in the repository.
- The 41 definitions of the statement (exactly the dependency closure of `MainTheoremStatement`) and the theorem are
  frozen, one declaration per file, in `AcExtensionPrinciple/Frozen/`. Their SHA-256 hashes are recorded in
  `planning/frozen-anchors.json` and checked by `scripts/check_frozen_anchors.py`.
- See [CERTIFICATION.md](CERTIFICATION.md) for how the statement was reviewed, approved, frozen, sealed and audited, and
  for the encoding decisions (author rulings Q1–Q10 and D1–D3) that the docstrings cite.

## 9. Building and checking

Toolchain: Lean `leanprover/lean4:v4.35.0-rc3` (see `lean-toolchain`). Dependency: Mathlib at commit
`7d6757bc18680044fc0ff6efc8ee20494b408556` (see `lakefile.toml` and `lake-manifest.json`). With
[elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get          # download the prebuilt Mathlib cache
lake build                  # build the library (about 9550 jobs)
lake env lean scripts/AxiomAudit.lean        # axiom audit of the main theorem
python3 scripts/check_frozen_anchors.py --root . --manifest planning/frozen-anchors.json
python3 scripts/test_check_frozen_anchors.py # tests of the checker
```

Expected output:
- axiom audit: `[propext, Classical.choice, Quot.sound]` for `mainTheorem` and for its proof `mainTheoremProof`;
- checker: `FROZEN-ANCHOR GUARD OK`.

The workflow `.github/workflows/build.yml`, run by manual dispatch, performs the same steps.

## 10. Layout and conventions

| Directory | Content |
|---|---|
| `Frozen/` | the statement of Theorem 1: one declaration per file (frozen, see CERTIFICATION.md) |
| `Reduced/`, `Solution/`, `External/` | the reduced equations, the solution classes and E1/E2 (the package files re-export the frozen declarations) |
| `Minimal/`, `Redundancy/` | derivation of the full working class from the minimal solution class of the statement |
| `GeometricBounds/` | Section 1: Lemma 1.1 (geometric bounds and incoming scalar flux) |
| `ScalarBound/`, `ACDatum/`, `Interpolation/` | Section 2: Lemmas 2.1–2.3 (uniform scalar bound, AC datum, AC interpolation) |
| `BoundaryEnergy/`, `Cylinder/`, `LateCylinder/` | Section 2: Lemmas 2.4–2.6 (boundary energy identity, boundary contraction, late cylinder segments) |
| `Decay/` | Section 2: Propositions 2.7–2.8 (uniform mass-ratio decay, common scalar limit) |
| `Renormalized/`, `Weighted/` | Section 3: Lemmas 3.1–3.3 and Propositions 3.4–3.5 (renormalized equations, weighted estimates, small outgoing BV cones) |
| `Continuation/`, `Gauge/`, `Main/` | Section 4: continuation across the endpoint (Lemma 4.1 via E1, identification via E2, gauge change and gluing); `Main/Theorem1Proof.lean` is the proof of `mainTheorem` |
| `Observability/` | Appendix A: boundary observability (Propositions A.1, A.4, Lemmas A.2–A.3) |
| `Integration/` | assembly of the decay chain and of the main theorem from its parts |
| `Analysis/`, `Basic.lean` | general one-variable analysis used throughout |
| `Sanity/` | non-vacuity and encoding sanity checks |

Docstrings use the tags G0–G6 for the conclusions of Lemma 1.1 and W1, W3 for the late expansion comparison and
Lemma 3.3; they are explained in `GeometricBounds/Blueshift.lean` and `Weighted/Lemma33.lean`.

Docstrings cite the paper's LaTeX source by revision and line range: revision `203e554` in the frozen statement files
and revision `e1a0fd5` in all other files. The two revisions have identical statements; from line 211 on, lines are
shifted by 6 in `e1a0fd5`. The LaTeX source is not public, so these line numbers and the LaTeX labels (`eq:...`,
`lem:...`) refer to the source; the lemma and proposition numbers match the typeset paper.

## 11. License, citation and third-party material

Copyright 2026 John Anderson, Serban Cicortas, Christoph Kehle, Warren Lee, Jonathan Luk, Yakov Shlapentokh-Rothman,
Maxime Van de Moortel.

- The Lean code and the documentation in this repository are licensed under the Apache License 2.0
  ([LICENSE](LICENSE)), except the two checker scripts below.
- `scripts/check_frozen_anchors.py` and `scripts/test_check_frozen_anchors.py` are adapted from
  LeanAutoformalizationSkills by Scott Armstrong, <https://github.com/scottnarmstrong/LeanAutoformalizationSkills>,
  licensed under CC BY 4.0 (<https://creativecommons.org/licenses/by/4.0/>). Changes: definition anchors may also be
  `structure` declarations, with three added tests.
- The formalization depends on [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache License 2.0).
- Citation metadata: [CITATION.cff](CITATION.cff).
- The sources cited (Luk–Oh, *Anal. PDE* 8 (2015) 1603–1674; Christodoulou, *CPAM* 46 (1993) 1131–1220) are not
  included.
