module

public import AcExtensionPrinciple.ScalarBound.Calculus
public import AcExtensionPrinciple.Solution.Raychaudhuri

/-!
# Radius-weighted incoming time integrals

Paper commit `e1a0fd5`, `equations.tex`
lines 472–506, `eq:scalar-bound-radius-integral` and
`eq:scalar-bound-weighted-time-integral`. The weighted estimate uses
the scaled Young inequality, an equivalent Cauchy–Schwarz bound.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Scaled weighted Cauchy–Schwarz, pointwise form. The endpoint radius R
is chosen after integration. Paper `e1a0fd5`, lines 498–504. -/
theorem weighted_scalar_young {r n R p : ℝ} (hr : 0 < r) (hn : 0 < n) (hR : 0 < R) :
    |p| / r ≤ (r / n * p ^ 2) / (2 * R) + R * n / (2 * r ^ 3) := by
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * R * n * r ^ 3)).mp
  have he : ((r / n * p ^ 2) / (2 * R) + R * n / (2 * r ^ 3)) *
      (2 * R * n * r ^ 3) = r ^ 4 * p ^ 2 + R ^ 2 * n ^ 2 := by
    field_simp
  have hl : |p| / r * (2 * R * n * r ^ 3) = 2 * R * n * r ^ 2 * |p| := by
    field_simp
  rw [mul_comm (2 * R * n * r ^ 3) (|p| / r),
    mul_comm (2 * R * n * r ^ 3)
      ((r / n * p ^ 2) / (2 * R) + R * n / (2 * r ^ 3)), he, hl]
  have heq : (r ^ 2 * |p| - R * n) ^ 2 =
      r ^ 4 * p ^ 2 + R ^ 2 * n ^ 2 - 2 * R * n * r ^ 2 * |p| := by
    calc
      _ = r ^ 4 * |p| ^ 2 + R ^ 2 * n ^ 2 - 2 * R * n * r ^ 2 * |p| := by ring
      _ = _ := by rw [sq_abs]
  have hz := sq_nonneg (r ^ 2 * |p| - R * n)
  rw [heq] at hz
  linarith

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Exact reciprocal-radius primitive on every proper incoming segment.
Paper `e1a0fd5`, `eq:scalar-bound-radius-integral`, lines 472–476. -/
theorem inv_radius_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => 1 / S.r u v)
      (fun u => -S.nu u v / S.r u v ^ 2) a b := by
  have hP : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.r u v)
      (fun u => S.nu u v) a x := fun x hx =>
    h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0)
  have hr : ∀ x ∈ Icc a b, 0 < S.r x v := fun x hx =>
    h.r_pos ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
      (hx.2.trans_lt hbv)
  have hac := positive_ac_inv (intervalPrimitive_ac hab hP)
    (fun x hx => hr x (by simpa [uIcc_of_le hab] using hx))
  apply ac_integral_eq_sub hab (by simpa only [one_div] using hac)
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hP] with x hx
  intro hxI
  convert (hx hxI).inv (hr x ⟨hxI.1.le, hxI.2.le⟩).ne' using 1
  funext y
  simp only [one_div, Pi.inv_apply]

/-- Exact integral of the cubic radius weight.
Paper `e1a0fd5`, lines 500–506, `eq:scalar-bound-weighted-time-integral`. -/
theorem inv_sq_radius_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => 1 / S.r u v ^ 2)
      (fun u => -2 * S.nu u v / S.r u v ^ 3) a b := by
  have hP : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => 1 / S.r u v)
      (fun u => -S.nu u v / S.r u v ^ 2) a x := fun x hx =>
    h.inv_radius_primitive hx.1 ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hac := (intervalPrimitive_ac hab hP).fun_mul (intervalPrimitive_ac hab hP)
  apply ac_integral_eq_sub hab (by simpa [one_div, sq] using hac)
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hP] with x hx
  intro hxI
  have hd := (hx hxI).pow 2
  convert hd using 1
  · funext y
    simp [one_div, sq, Pi.pow_apply]
  · norm_num
    ring

/-- The reciprocal-radius integral has a bound independent of the size of ν.
Paper `e1a0fd5`, `eq:scalar-bound-radius-integral`, lines 474–476. -/
theorem radius_time_integral_le {u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ≤ 1 / S.r u v := by
  have hi := h.inv_radius_primitive hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have he := hi.2
  dsimp only at he
  have hr : 0 < S.r ui v := h.r_pos
    ⟨le_rfl, h.initial_negative, (hp.1.trans_lt huv).le, hp.2.2.2⟩ (hp.1.trans_lt huv)
  linarith [one_div_pos.mpr hr]

/-- The cubic radius weight integrates to half a reciprocal-square
difference. Paper `e1a0fd5`, lines 500–506. -/
theorem cubic_radius_integral {u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    IntervalIntegrable (fun s => -S.nu s v / S.r s v ^ 3) volume ui u ∧
      (∫ s in ui..u, -S.nu s v / S.r s v ^ 3) =
        (1 / S.r u v ^ 2 - 1 / S.r ui v ^ 2) / 2 := by
  have hi := h.inv_sq_radius_primitive hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have he : (fun s => -S.nu s v / S.r s v ^ 3) =
      fun s => (1 / 2 : ℝ) * (-2 * S.nu s v / S.r s v ^ 3) := by
    funext s
    ring
  rw [he]
  refine ⟨hi.1.const_mul _, ?_⟩
  rw [intervalIntegral.integral_const_mul, ← hi.2]
  dsimp only
  ring

/-- The complete incoming flux bound controls every proper partial
integral. This premise is exactly the conclusion supplied by G6, with
K = Bstar + log(1/ci). Paper `e1a0fd5`, lines 498–504. -/
theorem partial_incoming_flux_le_of_geometric {K u v : ℝ}
    (hflux : (∫⁻ s in Ioo ui v, ENNReal.ofReal (S.incomingFlux s v)) ≤ ENNReal.ofReal K)
    (hK : 0 ≤ K) (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    (∫ s in ui..u, S.incomingFlux s v) ≤ K := by
  have hi := (h.incoming_flux_identity hp.1 le_rfl hp.2.1 huv hp.2.2.2).1
  have hn : ∀ s ∈ Ioo ui u, 0 ≤ S.incomingFlux s v := by
    intro s hs
    unfold SSFields.incomingFlux
    exact mul_nonneg (div_nonneg
      (h.r_pos ⟨hs.1.le, hs.2.trans hp.2.1, (hs.2.trans huv).le, hp.2.2.2⟩
        (hs.2.trans huv)).le
      (neg_pos.mpr (h.nu_neg (p := (s, v))
        ⟨hs.1.le, hs.2.trans hp.2.1, (hs.2.trans huv).le, hp.2.2.2⟩)).le) (sq_nonneg _)
  have hb : ENNReal.ofReal (∫ s in ui..u, S.incomingFlux s v) ≤ ENNReal.ofReal K := by
    rw [ofReal_intervalIntegral hp.1 hi hn]
    exact (lintegral_mono_set (Ioo_subset_Ioo_right huv.le)).trans hflux
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hb

/-- Integrability of the weighted incoming scalar derivative on proper
segments. Paper `e1a0fd5`, lines 498–506. -/
theorem weighted_time_integrable {u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    IntervalIntegrable (fun s => |S.duphi s v| / S.r s v) volume ui u := by
  have hs : ∀ s ∈ Icc ui u, (s, v) ∈ pastTriangle ui ∧ s < v := by
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans_lt hp.2.1, (hs.2.trans_lt huv).le, hp.2.2.2⟩,
      hs.2.trans_lt huv⟩
  have hiF := (h.scalar_primitive_in hp.1 le_rfl hp.2.1 huv hp.2.2.2).1.abs
  have hri : ContinuousOn (fun s => (S.r s v)⁻¹) (Icc ui u) :=
    (continuous_in h.regularCenter.continuous_r
      (inSeg_subset_triangle le_rfl hp.2.1 huv.le hp.2.2.2)).inv₀
      (fun s hsu => (h.r_pos (hs s hsu).1 (hs s hsu).2).ne')
  simpa only [div_eq_mul_inv] using hiF.mul_continuousOn
    (by simpa only [uIcc_of_le hp.1] using hri)

/-- The weighted time integral is bounded by a constant divided by the
final radius, independently of ν. The flux premise comes from G6.
Paper `e1a0fd5`, `eq:scalar-bound-weighted-time-integral`, lines 498–506. -/
theorem weighted_time_integral_le_of_flux {K u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v)
    (hflux : (∫ s in ui..u, S.incomingFlux s v) ≤ K) :
    (∫ s in ui..u, |S.duphi s v| / S.r s v) ≤
      (K / 2 + 1 / 4) / S.r u v := by
  have hs : ∀ s ∈ Icc ui u, (s, v) ∈ pastTriangle ui ∧ s < v := by
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans_lt hp.2.1, (hs.2.trans_lt huv).le, hp.2.2.2⟩,
      hs.2.trans_lt huv⟩
  have hr := h.r_pos hp huv
  have hiF := (h.scalar_primitive_in hp.1 le_rfl hp.2.1 huv hp.2.2.2).1.abs
  have hri : ContinuousOn (fun s => (S.r s v)⁻¹) (Icc ui u) :=
    (continuous_in h.regularCenter.continuous_r
      (inSeg_subset_triangle le_rfl hp.2.1 huv.le hp.2.2.2)).inv₀
      (fun s hsu => (h.r_pos (hs s hsu).1 (hs s hsu).2).ne')
  have hiW : IntervalIntegrable (fun s => |S.duphi s v| / S.r s v) volume ui u := by
    simpa only [div_eq_mul_inv] using hiF.mul_continuousOn
      (by simpa only [uIcc_of_le hp.1] using hri)
  have hiC := h.cubic_radius_integral hp huv
  have hiFlux := (h.incoming_flux_identity hp.1 le_rfl hp.2.1 huv hp.2.2.2).1
  have hY : (∫ s in ui..u, |S.duphi s v| / S.r s v) ≤
      (∫ s in ui..u, S.incomingFlux s v / (2 * S.r u v) +
        (S.r u v / 2) * (-S.nu s v / S.r s v ^ 3)) := by
    apply intervalIntegral.integral_mono_on hp.1 hiW
      ((hiFlux.div_const _).add (hiC.1.const_mul _))
    intro s hsu
    have hy := weighted_scalar_young (h.r_pos (hs s hsu).1 (hs s hsu).2)
      (neg_pos.mpr (h.nu_neg (hs s hsu).1)) hr (p := S.duphi s v)
    convert hy using 1 <;> simp only [SSFields.incomingFlux] <;> ring
  rw [intervalIntegral.integral_add (hiFlux.div_const _) (hiC.1.const_mul _),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hiC.2] at hY
  have hC : (1 / S.r u v ^ 2 - 1 / S.r ui v ^ 2) / 2 ≤ 1 / (2 * S.r u v ^ 2) := by
    have ht := one_div_nonneg.mpr (sq_nonneg (S.r ui v))
    have he : 1 / (2 * S.r u v ^ 2) = (1 / S.r u v ^ 2) / 2 := by ring
    rw [he]
    linarith
  calc
    _ ≤ _ := hY
    _ ≤ K / (2 * S.r u v) + (S.r u v / 2) * (1 / (2 * S.r u v ^ 2)) := by
      gcongr
    _ = _ := by field_simp; ring

end StandingFull

end AcExtensionPrinciple

end
