module

public import AcExtensionPrinciple.Renormalized.ClassEnergy
public import AcExtensionPrinciple.Weighted.Prop34Measure

/-!
# The coercive remainder energy identity on incoming rays

Helpers, paper `e1a0fd5`, `eq:renormalized-energy-identity`,
`equations.tex` lines 1240–1254. The incoming remainder equation is exactly
the Lemma 3.2 input; the geometry is derived from the standing class.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Young's inequality with the constants in the frozen energy estimate.
Paper `e1a0fd5`, lines 1248–1254 and 1265–1268.
Multiplication by `(-ν)/(1-μ)²` gives the two energy densities. -/
theorem frozen_source_young_bound {c lam ε A F J : ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hA : |A| ≤ ε) :
    |6 * A * F * J| ≤ c / (2 * lam) * J ^ 2 +
      (18 * ε ^ 2 * lam / c) * F ^ 2 := by
  have hε : 0 ≤ ε := (abs_nonneg A).trans hA
  have hprod : |6 * A * F * J| ≤ 6 * ε * |F| * |J| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    gcongr
  apply hprod.trans
  have he : c / (2 * lam) * J ^ 2 + (18 * ε ^ 2 * lam / c) * F ^ 2 =
      (c ^ 2 * J ^ 2 + 36 * ε ^ 2 * lam ^ 2 * F ^ 2) / (2 * c * lam) := by
    field_simp [hc.ne', hlam.ne']
    ring
  rw [he]
  apply (le_div_iff₀ (mul_pos (by positivity : 0 < 2 * c) hlam)).mpr
  rw [← sq_abs J, ← sq_abs F]
  nlinarith only [sq_nonneg (c * |J| - 6 * ε * lam * |F|)]

/-- Integrate a coercive energy inequality and discard its nonnegative
future boundary value. Paper `e1a0fd5`, lines 1268–1276 and 1311–1318.
The local integrability premise for `q` is the preliminary cutoff bound,
not the global energy conclusion being proved. -/
theorem ac_coercive_energy_bound {E q g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hq : IntervalIntegrable q volume a b) (hg : IntervalIntegrable g volume a b)
    (hderiv : ∀ᵐ x ∂volume.restrict (Ioc a b), deriv E x + c * q x ≤ g x)
    (hboundary : 0 ≤ E b) :
    (∫ x in a..b, q x) ≤ (E a + ∫ x in a..b, g x) / c := by
  have hh : (∫ x in a..b, deriv E x + c * q x) ≤ ∫ x in a..b, g x := by
    apply intervalIntegral.integral_mono_ae_restrict hab
      (hE.intervalIntegrable_deriv.add (hq.const_mul c)) hg
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact hderiv
  rw [intervalIntegral.integral_add hE.intervalIntegrable_deriv (hq.const_mul c),
    hE.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hh
  apply (le_div_iff₀ hc).mpr
  linarith

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual class-level incoming remainder energy identity, a.e. on each
off-axis incoming segment. Paper `e1a0fd5`, `eq:renormalized-energy-identity`,
lines 1240–1248. Its sole transport input is Lemma 3.2's remainder equation. -/
theorem renormalized_remainder_energy_identity_ae {q : ℝ → ℝ → ℝ} {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hJ : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt
      (fun s => S.renormalizedRemainder q ui s v)
      (S.incomingFlux x v * S.renormalizedRemainder q ui x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt
      (fun s => S.renormalizedRemainderEnergy q ui s v)
      (-weightedRemainderDensity S (x, v) *
        (1 - 3 * S.mu x v / (1 - S.mu x v)) * S.renormalizedRemainder q ui x v ^ 2 +
        (6 * S.nu x v / (1 - S.mu x v) ^ 2) *
          (S.r x v / S.lam x v * S.dvphi x v) *
          (S.renormalizedInteraction x v / S.r x v) * S.renormalizedRemainder q ui x v) x := by
  filter_upwards [h.incoming_reduced_ae hab ha hb hbv hv, hJ] with x hx hJx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb, (hxI.2.trans hbv).le, hv⟩
  obtain ⟨hr, hl, hm, _, _⟩ := hx hxI
  let J := fun s => S.renormalizedRemainder q ui s v
  have hJ' : HasDerivAt J
      ((S.r x v / (-S.nu x v)) * S.duphi x v ^ 2 * J x +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x :=
    hJx hxI
  have he := Renormalized.Incoming.renormalized_energy_identity
    (r := fun s => S.r s v) (lam := fun s => S.lam s v)
    (nu := fun s => S.nu s v) (m := fun s => S.m s v)
    (phiU := fun s => S.duphi s v) (phiV := fun s => S.dvphi s v) (J := J)
    hr hl hm hJ' (h.r_pos hp (hxI.2.trans hbv)) (h.lam_pos hp)
    (h.nu_neg hp) (h.mu_bounds hp).2
  convert he using 1
  · rfl
  · dsimp [J, weightedRemainderDensity, SSFields.mu, SSFields.renormalizedInteraction]
    ring

end StandingFull

end AcExtensionPrinciple

end
