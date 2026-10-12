module

public import AcExtensionPrinciple.Observability.Chart
public import AcExtensionPrinciple.Decay.ClassCylinderStatements
public import AcExtensionPrinciple.Gauge.Primitive
public import Mathlib.Tactic

/-!
# Fields and boundary identities for two independent chart coordinates

Paper `e1a0fd5`, `equations.tex` lines 1460–1475 and 1923–1929. The
outgoing inverse coordinate U and incoming inverse coordinate V differ;
the existing common-coordinate pullback cannot encode this chart. Algebra
and primitive transport below do not assert existence of the coordinates.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

namespace SSFields

/-- Pull back by two inverse coordinates and translate the scalar by c.
Paper `e1a0fd5`, lines 1460–1475 and 1923–1929. -/
@[expose] noncomputable def normalizedPullback (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c : ℝ) : SSFields where
  r s t := S.r (U s) (V t)
  phi s t := S.phi (U s) (V t) - c
  m s t := S.m (U s) (V t)
  lam s t := S.lam (U s) (V t) * dV t
  nu s t := S.nu (U s) (V t) * dU s
  dvpsi s t := (S.dvpsi (U s) (V t) - c * S.lam (U s) (V t)) * dV t
  dupsi s t := (S.dupsi (U s) (V t) - c * S.nu (U s) (V t)) * dU s

/-- The mass ratio is unchanged by both coordinate changes and the scalar
translation. Paper `e1a0fd5`, lines 1473–1475 and 1928–1929. -/
@[simp] theorem normalizedPullback_mu (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c s t : ℝ) :
    (S.normalizedPullback U V dU dV c).mu s t = S.mu (U s) (V t) := rfl

/-- The radial scalar derivative acquires exactly the constant subtraction.
Paper `e1a0fd5`, `equations.tex` lines 1923–1926. -/
theorem normalizedPullback_dvpsi_div_lam (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c s t : ℝ)
    (hdV : dV t ≠ 0) (hl : S.lam (U s) (V t) ≠ 0) :
    (S.normalizedPullback U V dU dV c).dvpsi s t /
      (S.normalizedPullback U V dU dV c).lam s t =
      S.dvpsi (U s) (V t) / S.lam (U s) (V t) - c := by
  change ((_ - c * _) * dV t) / (_ * dV t) = _
  rw [mul_div_mul_right _ _ hdV, sub_div, mul_div_cancel_right₀ _ hl]

/-- The incoming ratio has the same incoming-coordinate factor on numerator
and denominator. Paper `e1a0fd5`, `equations.tex` line 1473. -/
theorem normalizedPullback_incoming_ratio (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c s t : ℝ) (hdV : dV t ≠ 0) :
    (S.normalizedPullback U V dU dV c).lam t t /
      (S.normalizedPullback U V dU dV c).lam s t =
      S.lam (U t) (V t) / S.lam (U s) (V t) :=
  mul_div_mul_right _ _ hdV

/-- Normalizing the inverse Jacobians on the cylinder gives ν=-1 and λ=1.
Paper `e1a0fd5`, `eq:observability-boundary-gauge`, lines 1460–1465. -/
theorem normalizedPullback_boundary_gauge (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c s b : ℝ)
    (hr : S.r (U s) (V s) = b)
    (hn : S.nu (U s) (V s) ≠ 0) (hl : S.lam (U s) (V s) ≠ 0)
    (hU : dU s = (-S.nu (U s) (V s))⁻¹)
    (hV : dV s = (S.lam (U s) (V s))⁻¹) :
    (S.normalizedPullback U V dU dV c).r s s = b ∧
      (S.normalizedPullback U V dU dV c).nu s s = -1 ∧
      (S.normalizedPullback U V dU dV c).lam s s = 1 := by
  refine ⟨hr, ?_, ?_⟩
  · change S.nu (U s) (V s) * dU s = -1
    rw [hU, inv_neg, mul_neg, mul_inv_cancel₀ hn]
  · change S.lam (U s) (V s) * dV s = 1
    rw [hV, mul_inv_cancel₀ hl]

/-- The initial shifted chart energy is precisely the physical boundary
expression. Paper `e1a0fd5`, `equations.tex` lines 1928–1929. -/
theorem normalizedPullback_initial_energy (S : SSFields)
    (U V dU dV : ℝ → ℝ) (c b u v : ℝ) (hb : b ≠ 0)
    (hU : U 0 = u) (hV : V 0 = v) (hr : S.r u v = b) :
    ((S.normalizedPullback U V dU dV c).r 0 0 *
      (S.normalizedPullback U V dU dV c).phi 0 0) ^ 2 / (2 * b) -
      b / 2 * Real.log (1 - (S.normalizedPullback U V dU dV c).mu 0 0) =
      b / 2 * ((S.phi u v - c) ^ 2 - Real.log (1 - S.mu u v)) := by
  rw [normalizedPullback_mu]
  simp only [normalizedPullback, hU, hV, hr]
  field_simp

end SSFields

/-- The outgoing chart coordinate is the boundary clock shifted to start at
zero. Paper `e1a0fd5`, `equations.tex` line 1460. -/
@[expose] noncomputable def normalizedCylinderClock {ui b a₀ a₁ : ℝ}
    {S : SSFields} (c : DecayCylinder ui S b a₀ a₁) (a u : ℝ) : ℝ := c.tau u - c.tau a

/-- Subtracting the initial clock value leaves ds=dτ_b exactly as an integral
primitive. Paper `e1a0fd5`, `equations.tex` lines 1460, 1926–1927. -/
theorem normalizedCylinderClock_primitive {ui b a₀ a₁ a d : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    IntervalPrimitive (normalizedCylinderClock c a)
      (fun u => -S.nu u (c.v u)) a d := by
  refine ⟨(c.clock a d ha had hd).1, ?_⟩
  simp only [normalizedCylinderClock]
  linarith [(c.clock a d ha had hd).2]

/-- Along a regular boundary and a differentiable inverse clock, the derivative
of the translated amplitude is b times the derivative in boundary time. The
boundary identification is local; the trace derivative is the AC chain-rule
input, not an added source hypothesis. Paper `e1a0fd5`, lines 1923–1927. -/
theorem normalizedPullback_boundary_psi_hasDerivAt
    {ui b a₀ a₁ s u q shift : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (U V dU dV : ℝ → ℝ)
    (hU : U s = u)
    (hUd : HasDerivAt U (-S.nu u (c.v u))⁻¹ s)
    (hphi : HasDerivAt (cylinderPhi S c) q u)
    (hB : ∀ᶠ z in nhds s, U z ∈ Icc a₀ a₁ ∧ V z = c.v (U z)) :
    HasDerivAt (fun z => (S.normalizedPullback U V dU dV shift).r z z *
      (S.normalizedPullback U V dU dV shift).phi z z)
      (b * q / (-S.nu u (c.v u))) s := by
  have hphi' : HasDerivAt (cylinderPhi S c) q (U s) := by simpa only [hU] using hphi
  have hp := ((hphi'.comp s hUd).sub_const shift).const_mul b
  have hd : b * (q * (-S.nu u (c.v u))⁻¹) =
      b * q / (-S.nu u (c.v u)) := by rw [div_eq_mul_inv]; ring
  rw [hd] at hp
  apply hp.congr_of_eventuallyEq
  filter_upwards [hB] with z hz
  simp only [SSFields.normalizedPullback, hz.2, (c.points (U z) hz.1).2.2,
    Function.comp_apply, cylinderPhi]

/-- The solution supplies substitution premises for its shifted boundary
clock, without an added regularity hypothesis. Paper `e1a0fd5`,
`eq:cylinder-time`, lines 671–673, 1460 and 1926–1927. -/
theorem normalizedCylinderClock_gaugeSegment {ui b a₀ a₁ a d : ℝ} {S : SSFields}
    (h : StandingFull ui S) (c : DecayCylinder ui S b a₀ a₁)
    (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    GaugeSegment (normalizedCylinderClock c a) (fun u => -S.nu u (c.v u)) a d := by
  have hmem {u : ℝ} (hu : u ∈ Icc a d) : u ∈ Icc a₀ a₁ :=
    ⟨ha.trans hu.1, hu.2.trans hd⟩
  have hp {u : ℝ} (hu : u ∈ Icc a d) : (u, c.v u) ∈ pastTriangle ui :=
    ⟨c.initial_le.trans (hmem hu).1, (hmem hu).2.trans_lt c.terminal_negative,
      (c.points u (hmem hu)).1.le, (c.points u (hmem hu)).2.1⟩
  have hw : ContinuousOn (fun u => -S.nu u (c.v u)) (Icc a d) :=
    (h.regularCenter.continuous_nu.comp
      (continuousOn_id.prodMk (c.smooth_v.continuousOn.mono (Icc_subset_Icc ha hd)))
      (fun _ hu => hp hu)).neg
  apply GaugeSegment.of_hasDerivWithinAt
  · intro u hu
    rw [uIcc_of_le had] at hu ⊢
    exact hasDerivWithinAt_of_intervalPrimitives
      (fun x hx => normalizedCylinderClock_primitive c ha hx.1 (hx.2.trans hd)) hw hu
  · intro u hu
    rw [uIcc_of_le had] at hu
    exact (neg_pos.mpr (h.nu_neg (hp hu))).le

/-- The shifted boundary clock is strictly increasing on a regular cylinder.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673 and 1460. -/
theorem normalizedCylinderClock_strictMonoOn {ui b a₀ a₁ : ℝ} {S : SSFields}
    (h : StandingFull ui S) (c : DecayCylinder ui S b a₀ a₁) (a : ℝ) :
    StrictMonoOn (normalizedCylinderClock c a) (Icc a₀ a₁) := by
  intro x hx y hy hxy
  have hp {u : ℝ} (hu : u ∈ Icc a₀ a₁) : (u, c.v u) ∈ pastTriangle ui :=
    ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
      (c.points u hu).1.le, (c.points u hu).2.1⟩
  have hc : ContinuousOn (fun u => -S.nu u (c.v u)) (Icc x y) :=
    ((h.regularCenter.continuous_nu.comp
      (continuousOn_id.prodMk c.smooth_v.continuousOn) (fun _ hu => hp hu)).neg).mono
      (Icc_subset_Icc hx.1 hy.2)
  have hi : 0 < ∫ u in x..y, -S.nu u (c.v u) := by
    apply intervalIntegral.integral_pos hxy hc
    · intro u hu
      exact (neg_pos.mpr (h.nu_neg (hp ⟨hx.1.trans hu.1.le, hu.2.trans hy.2⟩))).le
    · exact ⟨y, ⟨hxy.le, le_rfl⟩, neg_pos.mpr (h.nu_neg (hp hy))⟩
  have he := (c.clock x y hx.1 hxy.le hy.2).2
  simp only [normalizedCylinderClock]
  linarith

/-- The inverse-clock chain rule holds a.e. from AC of the actual scalar
trace. The inverse derivative and boundary identification are coordinate
construction obligations, not extra assumptions on the solution. Paper
`e1a0fd5`, `equations.tex` lines 1923–1927. -/
theorem normalizedPullback_boundary_psi_ae_deriv
    {ui b a₀ a₁ a d T : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (F U V dU dV : ℝ → ℝ)
    (hphi : AbsolutelyContinuousOnInterval (cylinderPhi S c) a d)
    (hF : StrictMonoOn F (Icc a d)) (hFa : F a = 0) (hFd : F d = T)
    (hU : ∀ u ∈ Icc a d, U (F u) = u)
    (hUd : ∀ u ∈ Ioo a d, HasDerivAt U (-S.nu u (c.v u))⁻¹ (F u))
    (hB : ∀ z ∈ Icc 0 T, U z ∈ Icc a₀ a₁ ∧ V z = c.v (U z)) :
    ∀ᵐ u ∂volume, u ∈ Ioo a d →
      deriv (fun s => (S.normalizedPullback U V dU dV 0).r s s *
        (S.normalizedPullback U V dU dV 0).phi s s) (F u) =
          b * deriv (cylinderPhi S c) u / (-S.nu u (c.v u)) := by
  filter_upwards [hphi.ae_differentiableAt] with u hu huI
  have huC := Ioo_subset_Icc_self huI
  have had : a ≤ d := huI.1.le.trans huI.2.le
  have hFu0 : 0 < F u := by
    rw [← hFa]
    exact hF (left_mem_Icc.mpr had) huC huI.1
  have hFuT : F u < T := by
    rw [← hFd]
    exact hF huC (right_mem_Icc.mpr had) huI.2
  have hboundary : ∀ᶠ z in nhds (F u), U z ∈ Icc a₀ a₁ ∧ V z = c.v (U z) := by
    filter_upwards [Icc_mem_nhds hFu0 hFuT] with z hz
    exact hB z hz
  have hdu := (hu (by simpa only [uIcc_of_le had] using huC)).hasDerivAt
  exact (normalizedPullback_boundary_psi_hasDerivAt c U V dU dV
    (hU u huC) (hUd u huI) hdu hboundary).deriv

end AcExtensionPrinciple

end
