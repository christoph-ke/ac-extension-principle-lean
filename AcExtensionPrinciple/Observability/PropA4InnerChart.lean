module

public import AcExtensionPrinciple.Observability.PropA4Mass
public import AcExtensionPrinciple.Observability.PropA4LemmaA3

/-!
# The inner-cylinder coordinate interface

Paper `e1a0fd5`, `equations.tex` lines 1877–1904. If the inner cylinder is
`t = tₐ(s)`, set `A(s) = -r_s(s,tₐ(s))` and
`τ(s) = ∫ A`. The new incoming label is
`η(t) = τ(tₐ⁻¹(t))`, so the boundary is `η = τ`. Pull back by the
two different inverse maps `U = τ⁻¹` and `V = η⁻¹`, not by a common map.
On the boundary `U' = 1/A` and `V' = 1/r_t`. These give both normalized
expansions, the same incoming ratio bound K, and the energy density below.
The inverse maps also need increasing extensions to the earlier incoming
labels on the initial inner cone; the full chart hypotheses must hold there.

`PropA4.innerChartStatement` in `Observability/InnerChartConstruction.lean`
produces `NormalizedChartData a (Hε*a) K` for these pulled-back fields,
and identifies its observation with the integral
of `innerBoundaryDensity` over the corresponding outer-time interval. Merely
restricting the outer fields to `r = a` does not satisfy this interface.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set

/-- Pullback by separate incoming and outgoing coordinate maps. Paper
`e1a0fd5`, `eq:observability-boundary-gauge`, lines 1460–1473,
and the inner-cylinder use at lines 1897–1904. -/
@[expose] noncomputable def separatePullback (S : SSFields)
    (U V dU dV : ℝ → ℝ) : SSFields where
  r s t := S.r (U s) (V t)
  phi s t := S.phi (U s) (V t)
  m s t := S.m (U s) (V t)
  nu s t := S.nu (U s) (V t) * dU s
  lam s t := S.lam (U s) (V t) * dV t
  dupsi s t := S.dupsi (U s) (V t) * dU s
  dvpsi s t := S.dvpsi (U s) (V t) * dV t

/-- The mass ratio is invariant under the two independent maps. Paper
`e1a0fd5`, lines 1877–1879 and 1897–1904. -/
theorem separatePullback_mu (S : SSFields) (U V dU dV : ℝ → ℝ) (s t : ℝ) :
    (separatePullback S U V dU dV).mu s t = S.mu (U s) (V t) := rfl

/-- The radial scalar derivative is invariant under the label change.
Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1880–1886. -/
theorem separatePullback_radial (S : SSFields) (U V dU dV : ℝ → ℝ)
    (s t : ℝ) (hV : dV t ≠ 0) :
    (separatePullback S U V dU dV).dvpsi s t /
        (separatePullback S U V dU dV).lam s t =
      S.dvpsi (U s) (V t) / S.lam (U s) (V t) := by
  exact mul_div_mul_right _ _ hV

/-- The independent inverse derivatives normalize both boundary expansions.
Paper `e1a0fd5`, lines 1880–1887 and 1900–1904. -/
theorem separatePullback_boundary_gauge (S : SSFields)
    (U V dU dV : ℝ → ℝ) {a x : ℝ}
    (hr : S.r (U x) (V x) = a)
    (hn : S.nu (U x) (V x) < 0) (hl : 0 < S.lam (U x) (V x))
    (hU : dU x = (-S.nu (U x) (V x))⁻¹)
    (hV : dV x = (S.lam (U x) (V x))⁻¹) :
    (separatePullback S U V dU dV).r x x = a ∧
      (separatePullback S U V dU dV).nu x x = -1 ∧
      (separatePullback S U V dU dV).lam x x = 1 := by
  refine ⟨hr, ?_, ?_⟩
  · change S.nu (U x) (V x) * dU x = -1
    rw [hU, inv_neg, mul_neg, mul_inv_cancel₀ hn.ne]
  · change S.lam (U x) (V x) * dV x = 1
    rw [hV, mul_inv_cancel₀ hl.ne']

/-- The scalar energy density on the inner curve, with respect to outer
`s`, using radial rather than incoming-label derivatives. Paper `e1a0fd5`,
`eq:observability-inner-boundary-measure`, lines 1880–1886. -/
@[expose] noncomputable def innerBoundaryDensity (S : SSFields) (s t : ℝ) : ℝ :=
  (-S.nu s t) * (S.dvpsi s t / S.lam s t) ^ 2 +
    (S.dupsi s t - S.nu s t * (S.dvpsi s t / S.lam s t)) ^ 2 / (-S.nu s t)

/-- The normalized boundary energy pulls back to the displayed density
with Jacobian `dτ/ds = -r_s`. The boundary chain rule will replace the
sum of pulled-back scalar derivatives by the trace derivative a.e.
Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1880–1886. -/
theorem separatePullback_energy_density (S : SSFields)
    (U V dU dV : ℝ → ℝ) {x : ℝ}
    (hn : S.nu (U x) (V x) < 0) (hl : 0 < S.lam (U x) (V x))
    (hU : dU x = (-S.nu (U x) (V x))⁻¹)
    (hV : dV x = (S.lam (U x) (V x))⁻¹) :
    (-S.nu (U x) (V x)) *
      ((separatePullback S U V dU dV).dvpsi x x ^ 2 +
        ((separatePullback S U V dU dV).dupsi x x +
          (separatePullback S U V dU dV).dvpsi x x) ^ 2) =
      innerBoundaryDensity S (U x) (V x) := by
  simp only [separatePullback, innerBoundaryDensity, hU, hV]
  field_simp [hn.ne, hl.ne']
  ring

/-- Entry at a smaller radius improves the incoming expansion ratio.
This scalar fact is applied on the same old incoming ray, so the outgoing
coordinate Jacobian cancels. Paper `e1a0fd5`, lines 1900–1901. -/
theorem inner_incoming_ratio {entry later K : ℝ}
    (hlater : 0 < later) (hentry : entry ≤ 1) (houter : 1 / later ≤ K) :
    entry / later ≤ K :=
  (div_le_div_of_nonneg_right hentry hlater.le).trans houter

/-- The outgoing coordinate Jacobian cancels in the incoming ratio.
Paper `e1a0fd5`, line 1901 and `eq:observability-boundary-gauge`. -/
theorem separatePullback_incoming_ratio (S : SSFields) (U V dU dV : ℝ → ℝ)
    (s t : ℝ) (hV : dV t ≠ 0) :
    (separatePullback S U V dU dV).lam t t /
        (separatePullback S U V dU dV).lam s t =
      S.lam (U t) (V t) / S.lam (U s) (V t) := by
  exact mul_div_mul_right _ _ hV

/-- Retained inner mass gives exactly the printed threshold. Paper
`e1a0fd5`, `eq:observability-inner-mass`, lines 1863–1879. -/
theorem inner_mass_ratio {K L M m : ℝ} (hK : 1 ≤ K) (hL : 0 < L)
    (hM : 0 < M) (hm : M / (4 * K) ≤ m) :
    1 / (2 * K * (K + 2) * L) ≤ massRatio (L * ((K + 2) * M)) m := by
  have hK0 : 0 < K := by linarith
  have ha : 0 < L * ((K + 2) * M) := by positivity
  have hd : 0 < 2 * K * (K + 2) * L := by positivity
  unfold massRatio
  apply (le_div_iff₀ ha).mpr
  have heq : (1 / (2 * K * (K + 2) * L)) * (L * ((K + 2) * M)) = M / (2 * K) := by
    field_simp
  rw [heq]
  have hh := (div_le_iff₀ (show 0 < 4 * K by positivity)).mp hm
  rw [div_le_iff₀ (show 0 < 2 * K by positivity)]
  nlinarith

/-- Apply the proved, globally quantified A.3 to a genuinely normalized
inner chart, with its own radius and duration. The chart construction and
energy change of variables must supply precisely these premises. Paper
`e1a0fd5`, `eq:observability-inner-boundary-lower-bound`, lines 1900–1904. -/
theorem inner_observation_of_chart {K : ℝ} (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a ε : ℝ) (inner : SSFields),
      0 < ε → ε < 1 →
      NormalizedChartData a (positiveMassDuration K ε * a) K inner →
      ε ≤ inner.mu 0 0 →
        c * ε ^ 3 * a / (1 + |Real.log ε|) ^ 2 ≤
          chartScalarEnergy inner (positiveMassDuration K ε * a) := by
  obtain ⟨c, hc, hobs⟩ := lemmaA3Statement hK
  refine ⟨c, hc, ?_⟩
  intro a ε inner hε hε1 hchart hμ
  simpa only [translatedScalarEnergy_zero] using hobs ε a inner hε hε1 hchart hμ 0

end PropA4
end AcExtensionPrinciple

end
