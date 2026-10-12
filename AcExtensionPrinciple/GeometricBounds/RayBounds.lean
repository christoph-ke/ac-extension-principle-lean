module

public import AcExtensionPrinciple.Solution.Geometry
public import AcExtensionPrinciple.Solution.PositiveAC
public import AcExtensionPrinciple.Reduced.IncomingRay

/-!
# Incoming logarithmic expansion and elementary comparison bounds

Paper `e1a0fd5`, `eq:lambda-integrating-factor`,
`eq:outward-nu-monotonicity`, `eq:radius-from-axis` (lines 311–349).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The radius coefficient in the integral class matches the reduced ray calculus.
Paper `e1a0fd5`, `eq:radius`, lines 70–73. -/
theorem SSFields.radiusCoeff_eq (S : SSFields) (u v : ℝ) :
    S.radiusCoeff u v = S.kappa u v * S.varkappa u v * S.nu u v := by
  simp only [SSFields.radiusCoeff, SSFields.kappa, SSFields.varkappa, kappaOf, varkappaOf,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- Bounds on an open interval extend to its endpoints by continuity.
Paper `e1a0fd5`, lines 342–352 (regular-axis and terminal extension). -/
theorem interval_bounds_of_open {f : ℝ → ℝ} {a b L U : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hb : ∀ x ∈ Ioo a b, L ≤ f x ∧ f x ≤ U) :
    ∀ x ∈ Icc a b, L ≤ f x ∧ f x ≤ U := by
  intro x hx
  have hxcl : x ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  have : (𝓝[Ioo a b] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  have ht := (hf x hx).mono Ioo_subset_Icc_self
  exact ⟨ge_of_tendsto ht (eventually_mem_nhdsWithin.mono (fun y hy => (hb y hy).1)),
    le_of_tendsto ht (eventually_mem_nhdsWithin.mono (fun y hy => (hb y hy).2))⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The radius coefficient is nonpositive away from the axis.
Paper `e1a0fd5`, `eq:radius`, lines 66–73, 343–346. -/
theorem radiusCoeff_nonpos {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    S.radiusCoeff u v ≤ 0 := by
  have hs := h.signs (u, v) hp huv
  unfold SSFields.radiusCoeff
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs.2.2.1 hs.1.le) hs.2.1.le)
    (mul_nonneg (sub_pos.mpr hs.2.2.2).le (h.r_pos hp huv).le)

/-- Nonnegative incoming blueshift density. Paper `e1a0fd5`, lines 311–316. -/
theorem blueshift_nonneg {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    0 ≤ -(S.gamma u v * S.varkappa u v) := by
  have hs := h.signs (u, v) hp huv
  unfold SSFields.gamma gammaOf SSFields.varkappa varkappaOf
  exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg hs.2.1.le (sub_pos.mpr hs.2.2.2).le)
    (div_nonneg hs.2.2.1 (h.r_pos hp huv).le))

/-- λ is AC along every off-axis incoming segment, from the incoming radius primitive. Paper
`e1a0fd5`, lines 70–73, 222, 311–316. -/
theorem lam_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.lam u v) a b := by
  apply intervalPrimitive_ac (g := fun u => S.radiusCoeff u v) hab
  intro x hx
  exact h.regularCenter.localBV.lam_in v a x hx.1
    (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)

/-- Integral form of the incoming logarithmic expansion, recovered from the incoming radius
primitive. Paper `e1a0fd5`, `eq:logarithmic-expansions`, `eq:lambda-integrating-factor`. -/
theorem log_lam_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => Real.log (S.lam u v))
      (fun u => S.gamma u v * S.varkappa u v) a b := by
  have hlam := h.lam_ac_in hab ha hb0 hbv hv0
  apply ac_integral_eq_sub hab (positive_ac_log hlam ?_)
  · have hd := intervalPrimitive_ae_hasDerivAt hab (f := fun u => S.lam u v)
      (g := fun u => S.radiusCoeff u v) (fun x hx =>
        h.regularCenter.localBV.lam_in v a x hx.1
            (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
    filter_upwards [hd] with x hx
    intro hxI
    have hp : (x, v) ∈ pastTriangle ui :=
      ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
    exact IncomingRay.log_lam (r := fun s => S.r s v) (m := fun s => S.m s v)
      (nu := fun s => S.nu s v)
      ((hx hxI).congr_deriv (S.radiusCoeff_eq x v)) (h.lam_pos hp)
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.lam_pos (p := (x, v)) ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩

/-- Outgoing ν is nonincreasing between off-axis endpoints.
Paper `e1a0fd5`, `eq:outward-nu-monotonicity`. -/
theorem nu_le_of_le {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a)
    (hab : a ≤ b) (hb0 : b ≤ 0) : S.nu u b ≤ S.nu u a := by
  have hi := h.regularCenter.localBV.nu_out u a b hab
    (outSeg_subset_offAxis hu hu0 hua hb0)
  have hn : (∫ s in a..b, S.radiusCoeff u s) ≤ 0 := by
    have hi' := intervalIntegral.integral_nonneg (μ := volume) hab
      (f := fun s => -S.radiusCoeff u s)
      (fun s hs => neg_nonneg.mpr (h.radiusCoeff_nonpos
        ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩ (hua.trans_le hs.1)))
    rw [intervalIntegral.integral_neg] at hi'
    linarith
  linarith [hi.2]

/-- Comparison with the axis value, extending the off-axis monotonicity by continuity.
Paper `e1a0fd5`, `eq:outward-nu-monotonicity`, lines 342–346. -/
theorem nu_le_axis {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) : S.nu u v ≤ S.nu u u := by
  rcases hp.2.2.1.eq_or_lt with he | huv
  · change u = v at he
    rw [he]
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  have hc := continuous_out h.regularCenter.continuous_nu hs
  have : (𝓝[Ioo u v] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (by rw [closure_Ioo huv.ne]; exact left_mem_Icc.mpr huv.le)
  apply ge_of_tendsto ((hc u (left_mem_Icc.mpr huv.le)).mono Ioo_subset_Icc_self)
  filter_upwards [eventually_mem_nhdsWithin] with a ha
  exact h.nu_le_of_le hp.1 hp.2.1 ha.1 ha.2.le hp.2.2.2

end StandingFull

end AcExtensionPrinciple

end
