module

public import AcExtensionPrinciple.Weighted.Prop34RayEnergy
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Kato's inequality for the frozen incoming transport

Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1316.
The absolute value derivative is controlled also at zeros. The actual
geometric weight leaves an additional nonnegative incoming scalar square.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Kato's scalar transport inequality, including zeros of the solution.
Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1309. -/
theorem abs_transport_derivative_le {J : ℝ → ℝ} {x c g d : ℝ}
    (hJ : HasDerivAt J (c * J x + g) x)
    (habs : HasDerivAt (fun s => |J s|) d x) :
    d ≤ c * |J x| + |g| := by
  rcases lt_trichotomy (J x) 0 with hneg | hzero | hpos
  · have he := habs.unique ((hasDerivAt_abs_neg hneg).comp x hJ)
    rw [he, abs_of_neg hneg]
    nlinarith [neg_le_abs g]
  · have hmin : IsLocalMin (fun s => |J s|) x := by
      change ∀ᶠ s in 𝓝 x, |J x| ≤ |J s|
      exact Filter.Eventually.of_forall (fun s => by
        simpa only [hzero, abs_zero] using abs_nonneg (J s))
    have he : d = 0 := habs.deriv.symm.trans hmin.deriv_eq_zero
    simp only [he, hzero, abs_zero, mul_zero, zero_add]
    exact abs_nonneg g
  · have he := habs.unique ((hasDerivAt_abs_pos hpos).comp x hJ)
    rw [he, abs_of_pos hpos]
    nlinarith [le_abs_self g]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Kato with the actual weight at a differentiability point. This is the
paper's exact bracket, with the extra incoming square retained.
Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1309. -/
theorem frozen_ray_kato_point {x v : ℝ} {J F : ℝ → ℝ} {d : ℝ}
    (hp : (x, v) ∈ pastTriangle ui) (hxv : x < v)
    (hr : HasDerivAt (fun s => S.r s v) (S.nu x v) x)
    (hl : HasDerivAt (fun s => S.lam s v) (S.kappa x v * S.varkappa x v * S.nu x v) x)
    (hm : HasDerivAt (fun s => S.m s v)
      (S.r x v ^ 2 / (2 * S.gamma x v) * S.duphi x v ^ 2) x)
    (hJ : HasDerivAt J (S.incomingFlux x v * J x +
      3 * S.nu x v * S.dvphi x v * F x) x)
    (habs : HasDerivAt (fun s => |J s|) d x) :
    deriv (fun s => S.r s v * |J s| / ((1 - S.mu s v) ^ 2 * S.lam s v)) x +
      weightedRemainderDensity S (x, v) *
        (1 + (S.r x v / S.nu x v * S.duphi x v) ^ 2 -
          3 * S.mu x v / (1 - S.mu x v)) * |J x| ≤
      (3 * (-S.nu x v) / (1 - S.mu x v) ^ 2) *
        |S.r x v / S.lam x v * S.dvphi x v| * |F x| := by
  have hr0 := h.r_pos hp hxv
  have hl0 := h.lam_pos hp
  have hn0 := h.nu_neg hp
  have hg0 := sub_pos.mpr (h.mu_bounds hp).2
  let w := S.r x v / ((1 - S.mu x v) ^ 2 * S.lam x v)
  have hw : 0 < w := div_pos hr0 (mul_pos (sq_pos_of_pos hg0) hl0)
  have hweight := Renormalized.Incoming.energy_weight_derivative
    (r := fun s => S.r s v) (lam := fun s => S.lam s v)
    (nu := fun s => S.nu s v) (m := fun s => S.m s v)
    (phiU := fun s => S.duphi s v) hr hl hm hr0 hl0 hn0 (h.mu_bounds hp).2
  have hE := hweight.mul habs
  have hE' : HasDerivAt
      (fun s => S.r s v * |J s| / ((1 - S.mu s v) ^ 2 * S.lam s v))
      (w * ((-S.nu x v / S.r x v) *
        (-1 - 2 * (S.r x v / S.nu x v * S.duphi x v) ^ 2 +
          3 * S.mu x v / (1 - S.mu x v))) * |J x| + w * d) x := by
    convert hE using 1
    · funext s
      dsimp only [Pi.mul_apply, SSFields.mu]
      ring
    · rfl
  have hDE : deriv (fun s => S.r s v * |J s| /
      ((1 - S.mu s v) ^ 2 * S.lam s v)) x =
      w * ((-S.nu x v / S.r x v) *
        (-1 - 2 * (S.r x v / S.nu x v * S.duphi x v) ^ 2 +
          3 * S.mu x v / (1 - S.mu x v))) * |J x| + w * d := by
    exact hE'.deriv
  have ht := mul_le_mul_of_nonneg_left (abs_transport_derivative_le hJ habs) hw.le
  have he : w * ((-S.nu x v / S.r x v) *
        (-1 - 2 * (S.r x v / S.nu x v * S.duphi x v) ^ 2 +
          3 * S.mu x v / (1 - S.mu x v))) * |J x| + w * d +
      weightedRemainderDensity S (x, v) *
        (1 + (S.r x v / S.nu x v * S.duphi x v) ^ 2 -
          3 * S.mu x v / (1 - S.mu x v)) * |J x| =
      w * (d - S.incomingFlux x v * |J x|) := by
    dsimp only [w, weightedRemainderDensity, SSFields.incomingFlux]
    field_simp [hr0.ne', hl0.ne', hn0.ne, hg0.ne']
    ring
  have hs : w * |3 * S.nu x v * S.dvphi x v * F x| =
      (3 * (-S.nu x v) / (1 - S.mu x v) ^ 2) *
        |S.r x v / S.lam x v * S.dvphi x v| * |F x| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_neg hn0, abs_mul, abs_div, abs_of_pos hr0, abs_of_pos hl0]
    dsimp only [w]
    field_simp [hl0.ne', hg0.ne']
  rw [hDE, he, ← hs]
  nlinarith

/-- The actual Kato inequality holds almost everywhere on every proper
incoming segment of an AC frozen transport solution. No nonzero-solution
premise is needed. Paper `e1a0fd5`, `eq:remainder-difference-kato`,
lines 1305–1309. -/
theorem frozen_ray_kato_ae {a b v : ℝ} {J F : ℝ → ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hJ : AbsolutelyContinuousOnInterval J a b)
    (hJode : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt J
      (S.incomingFlux x v * J x + 3 * S.nu x v * S.dvphi x v * F x) x) :
    ∀ᵐ x, x ∈ Ioo a b →
      deriv (fun s => S.r s v * |J s| / ((1 - S.mu s v) ^ 2 * S.lam s v)) x +
        weightedRemainderDensity S (x, v) *
          (1 + (S.r x v / S.nu x v * S.duphi x v) ^ 2 -
            3 * S.mu x v / (1 - S.mu x v)) * |J x| ≤
        (3 * (-S.nu x v) / (1 - S.mu x v) ^ 2) *
          |S.r x v / S.lam x v * S.dvphi x v| * |F x| := by
  have hAbs : AbsolutelyContinuousOnInterval (fun s => |J s|) a b := by
    have hLip : LipschitzWith 1 (norm : ℝ → ℝ) := lipschitzWith_one_norm
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      hLip.comp_absolutelyContinuousOnInterval hJ
  filter_upwards [h.incoming_reduced_ae hab ha hb hbv hv, hJode,
    hAbs.ae_differentiableAt] with x hx hJx hAx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb, (hxI.2.trans hbv).le, hv⟩
  obtain ⟨hr, hl, hm, _, _⟩ := hx hxI
  exact h.frozen_ray_kato_point hp (hxI.2.trans hbv) hr hl hm (hJx hxI)
    (hAx (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hxI)).hasDerivAt

end StandingFull

end AcExtensionPrinciple

end
