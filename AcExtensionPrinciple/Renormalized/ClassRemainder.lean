module

public import AcExtensionPrinciple.Renormalized.ClassSplitting

/-!
# Pointwise remainder bound and the incoming radius kernel

Paper `e1a0fd5`, `equations.tex` lines 1100–1125.
The flux bound is the intended Lemma 1.1 G6 input; the source bound is
discharged by the bounded normalized scalar amplitudes and interaction.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Uniform interaction bound from the two normalized scalar amplitudes.
Paper `e1a0fd5`, `eq:renormalized-interaction`, lines 1022–1023 and 1120. -/
theorem interaction_abs_bound {mu A B M N : ℝ} (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hA : |A| ≤ M) (hB : |B| ≤ N) : |mu + (1 - mu) * A * B| ≤ 1 + M * N := by
  have hM := (abs_nonneg A).trans hA
  have hN := (abs_nonneg B).trans hB
  calc
    _ ≤ |mu| + |(1 - mu) * A * B| := abs_add_le _ _
    _ = mu + (1 - mu) * |A| * |B| := by
      rw [abs_of_nonneg hmu0, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hmu1)]
    _ ≤ mu + (1 - mu) * M * N := by gcongr
    _ ≤ 1 + M * N := by nlinarith [mul_nonneg hmu0 (mul_nonneg hM hN)]

/-- Bounded outgoing amplitude and interaction give the radius-kernel source
majorant. Paper `e1a0fd5`, `eq:renormalized-remainder-pointwise`, lines 1107–1120. -/
theorem renormalized_source_bound {r lam nu phiV interaction M N : ℝ}
    (hr : 0 < r) (hl : 0 < lam) (hl1 : lam ≤ 1) (hn : nu < 0)
    (hA : |r / lam * phiV| ≤ M) (hC : |interaction| ≤ N) :
    |(3 * nu / r) * phiV * interaction| ≤ (3 * M * N) * (-nu / r ^ 2) := by
  have hM := (abs_nonneg _).trans hA
  have hN := (abs_nonneg _).trans hC
  have hnu : 0 ≤ -nu := (neg_pos.mpr hn).le
  have hphi : |phiV| ≤ M * lam / r := by
    rw [abs_mul, abs_of_pos (div_pos hr hl)] at hA
    apply (le_div_iff₀ hr).mpr
    have he := (div_le_iff₀ hl).mp (show r * |phiV| / lam ≤ M by
      simpa [div_mul_eq_mul_div] using hA)
    nlinarith
  calc
    _ = (3 * (-nu) / r) * |phiV| * |interaction| := by
      rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_neg hn, abs_of_pos hr]
    _ ≤ (3 * (-nu) / r) * (M * lam / r) * N := by gcongr
    _ ≤ (3 * (-nu) / r) * (M * 1 / r) * N := by gcongr
    _ = _ := by ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming radius kernel has an exact reciprocal-radius primitive.
Paper `e1a0fd5`, `eq:renormalized-remainder-pointwise`, lines 1107–1109. -/
theorem incoming_radius_kernel_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => 1 / S.r u v) (fun u => -S.nu u v / S.r u v ^ 2) a b := by
  have hr := (h.incoming_components_ac hab ha hb0 hbv hv0).1
  have hi := positive_ac_inv hr (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact h.r_pos ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
      (hx.2.trans_lt hbv))
  apply ac_integral_eq_sub hab (by simpa only [one_div] using hi)
  filter_upwards [h.incoming_reduced_ae hab ha hb0 hbv hv0] with x hx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
  exact ((hasDerivAt_const x (1 : ℝ)).div (hx hxI).1
    (ne_of_gt (h.r_pos hp (hxI.2.trans hbv)))).congr_deriv (by simp)

/-- In particular the kernel integral is at most the final reciprocal radius.
Paper `e1a0fd5`, `eq:renormalized-remainder-pointwise`, lines 1107–1109. -/
theorem incoming_radius_kernel_le {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    (∫ u in a..b, -S.nu u v / S.r u v ^ 2) ≤ 1 / S.r b v := by
  rw [← (h.incoming_radius_kernel_primitive hab ha hb0 hbv hv0).2]
  have hp : (a, v) ∈ pastTriangle ui :=
    ⟨ha, hab.trans_lt hb0, (hab.trans_lt hbv).le, hv0⟩
  exact sub_le_self _ (one_div_nonneg.mpr (h.r_pos hp (hab.trans_lt hbv)).le)

/-- Variation of constants gives the remainder bound with explicit constants,
then the radius primitive gives `C exp(Λ)/r`. Paper `e1a0fd5`,
`eq:renormalized-remainder-pointwise`, lines 1107–1120.
The AC and transport premises come from Lemma 2.2 and the preceding class helpers. -/
theorem renormalizedRemainder_bound_of_transport {q : ℝ → ℝ → ℝ} {u v C Λ : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) (hC : 0 ≤ C)
    (hJ : AbsolutelyContinuousOnInterval (fun s => S.renormalizedRemainder q ui s v) ui u)
    (hODE : ∀ᵐ x, x ∈ Ioo ui u → HasDerivAt
      (fun s => S.renormalizedRemainder q ui s v)
      (S.incomingFlux x v * S.renormalizedRemainder q ui x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x)
    (hflux : (∫ s in ui..u, S.incomingFlux s v) ≤ Λ)
    (hsource : ∀ x ∈ Icc ui u,
      |(3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v| ≤
        C * (-S.nu x v / S.r x v ^ 2)) :
    |S.renormalizedRemainder q ui u v| ≤
      C * Real.exp Λ * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ∧
    |S.renormalizedRemainder q ui u v| ≤ C * Real.exp Λ / S.r u v := by
  have hk := h.incoming_radius_kernel_primitive hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have ha := (h.incoming_flux_identity hp.1 le_rfl hp.2.1 huv hp.2.2.2).1
  have hODE' : ∀ᵐ x, x ∈ Icc ui u → HasDerivAt
      (fun s => S.renormalizedRemainder q ui s v)
      (S.incomingFlux x v * S.renormalizedRemainder q ui x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x := by
    filter_upwards [hODE, show ∀ᵐ x : ℝ, x ≠ ui by simp [ae_iff],
      show ∀ᵐ x : ℝ, x ≠ u by simp [ae_iff]] with x hx hxi hxu hxI
    exact hx ⟨lt_of_le_of_ne hxI.1 hxi.symm, lt_of_le_of_ne hxI.2 hxu⟩
  have hpoint (x : ℝ) (hx : x ∈ Icc ui u) : (x, v) ∈ pastTriangle ui ∧ x < v :=
    ⟨⟨hx.1, hx.2.trans_lt hp.2.1, (hx.2.trans_lt huv).le, hp.2.2.2⟩, hx.2.trans_lt huv⟩
  have hb := ac_transport_bound hp.1 hJ ha hk.1 hODE'
    (h.renormalizedRemainder_initial q ⟨hp.1.trans hp.2.2.1, hp.2.2.2⟩)
    (ae_of_all _ (fun x hx => mul_nonneg
      (div_nonneg (h.r_pos (hpoint x hx).1 (hpoint x hx).2).le
        (neg_pos.mpr (h.nu_neg (hpoint x hx).1)).le) (sq_nonneg _))) hflux
    (ae_of_all _ (fun x hx => ⟨div_nonneg (neg_pos.mpr (h.nu_neg (hpoint x hx).1)).le
      (sq_nonneg _), hsource x hx⟩))
  refine ⟨hb, hb.trans ?_⟩
  calc
    _ ≤ C * Real.exp Λ * (1 / S.r u v) := mul_le_mul_of_nonneg_left
      (h.incoming_radius_kernel_le hp.1 le_rfl hp.2.1 huv hp.2.2.2)
      (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring

end StandingFull

end AcExtensionPrinciple

end
