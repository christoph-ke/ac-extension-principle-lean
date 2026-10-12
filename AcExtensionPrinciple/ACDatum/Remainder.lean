module

public import AcExtensionPrinciple.ACDatum.IncomingPrimitives

/-!
# Integrating factor and estimates for the nonlinear derivative remainder

Paper commit `e1a0fd5`,
`eq:radial-datum-transport`, `eq:rough-derivative-decomposition`, and
`eq:derivative-remainder-bound` (`equations.tex` lines 564–581, 603).
The integrating-factor helper takes derivative transport as an explicit
premise, discharged for the radial datum in `ACDatum.RadialTransport`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Inhomogeneous source in the incoming equation for q. Paper `e1a0fd5`,
`eq:radial-datum-transport`, lines 565–567. -/
@[expose] noncomputable def radialDatumSource (S : SSFields) (u v : ℝ) : ℝ :=
  -S.gamma u v / S.r u v ^ 2 * (S.theta u v / S.lam u v) *
    ((S.theta u v / S.lam u v) ^ 2 - 3 * S.mu u v)

/-- Variation-of-constants remainder, identified with the radial derivative
remainder in `ACDatum.RadialTransport`. Paper `e1a0fd5`,
`eq:rough-derivative-decomposition`, lines 572–574 and 603. -/
@[expose] noncomputable def radialDatumRemainderIntegral
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  (∫ s in ui..u, S.lam s v ^ 2 * radialDatumSource S s v) / S.lam u v ^ 2

/-- The remainder integral vanishes on the initial cone. Paper `e1a0fd5`,
`eq:rough-derivative-decomposition`, line 573. -/
theorem radialDatumRemainderIntegral_initial (ui : ℝ) (S : SSFields) (v : ℝ) :
    radialDatumRemainderIntegral ui S ui v = 0 := by
  simp [radialDatumRemainderIntegral]

/-- AC integrating factor for an explicitly supplied a.e. incoming transport.
Paper `e1a0fd5`, `eq:radial-datum-transport` and proof line 603. -/
theorem weighted_datum_transport_primitive {lam q c F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hlam : AbsolutelyContinuousOnInterval lam a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hdlam : ∀ᵐ s, s ∈ Ioo a b → HasDerivAt lam (lam s * c s) s)
    (hdq : ∀ᵐ s, s ∈ Ioo a b → HasDerivAt q (-2 * c s * q s + F s) s) :
    IntervalPrimitive (fun s => lam s ^ 2 * q s) (fun s => lam s ^ 2 * F s) a b := by
  have hac : AbsolutelyContinuousOnInterval (fun s => lam s ^ 2 * q s) a b := by
    simpa only [pow_two] using (hlam.fun_mul hlam).fun_mul hq
  apply ac_integral_eq_sub hab hac
  filter_upwards [hdlam, hdq] with s hls hqs
  intro hs
  convert ((hls hs).pow 2).mul (hqs hs) using 1
  simp only [Pi.pow_apply]
  ring

/-- Algebraic variation-of-constants decomposition once the weighted integral
equation is available. Paper `e1a0fd5`, `eq:rough-derivative-decomposition`,
lines 572–574 and 603. -/
theorem datum_decomposition_of_weighted_primitive {lam q F : ℝ → ℝ} {a b : ℝ}
    (hlam : lam a = 1) (hlam0 : lam b ≠ 0)
    (he : IntervalPrimitive (fun s => lam s ^ 2 * q s)
      (fun s => lam s ^ 2 * F s) a b) :
    q b = q a / lam b ^ 2 + (∫ s in a..b, lam s ^ 2 * F s) / lam b ^ 2 := by
  have hi := he.2
  dsimp only at hi
  rw [hlam, one_pow, one_mul] at hi
  field_simp [hlam0]
  linarith

/-- Scalar and mass-gap bounds control the cubic transport source. This is an
internal algebraic helper: M is supplied by Lemma 2.1, and c by Lemma 1.1.
Paper `e1a0fd5`, `eq:derivative-remainder-bound`, proof line 603. -/
theorem cubic_datum_source_bound {r nu mu A M c : ℝ}
    (hr : 0 < r) (hnu : nu < 0) (hmu0 : 0 ≤ mu) (hmu1 : mu < 1)
    (hc : 0 < c) (hgap : c ≤ 1 - mu) (hM : 0 ≤ M) (hA : |A| ≤ M) :
    |-(gammaOf nu mu) / r ^ 2 * A * (A ^ 2 - 3 * mu)| ≤
      (M * (M ^ 2 + 3) / c) * (-nu / r ^ 2) := by
  have hb : |A ^ 2 - 3 * mu| ≤ M ^ 2 + 3 := by
    calc
      _ ≤ |A ^ 2| + |3 * mu| := abs_sub _ _
      _ = A ^ 2 + 3 * mu := by rw [abs_of_nonneg (sq_nonneg A),
        abs_of_nonneg (mul_nonneg (by norm_num) hmu0)]
      _ ≤ M ^ 2 + 3 := by
        have hsq : A ^ 2 ≤ M ^ 2 := by nlinarith [abs_le.mp hA]
        linarith
  have hprod : |A| * |A ^ 2 - 3 * mu| ≤ M * (M ^ 2 + 3) :=
    mul_le_mul hA hb (abs_nonneg _) hM
  have hquot : (|A| * |A ^ 2 - 3 * mu|) / (1 - mu) ≤ M * (M ^ 2 + 3) / c := by
    exact div_le_div₀ (mul_nonneg hM (by positivity)) hprod hc hgap
  have he : |-(gammaOf nu mu) / r ^ 2 * A * (A ^ 2 - 3 * mu)| =
      (-nu / r ^ 2) * (|A| * |A ^ 2 - 3 * mu| / (1 - mu)) := by
    rw [abs_mul, abs_mul, abs_div]
    simp only [gammaOf, abs_neg, abs_div, abs_of_neg hnu,
      abs_of_pos (sub_pos.mpr hmu1), abs_of_pos (sq_pos_of_pos hr)]
    ring
  rw [he, mul_comm (M * (M ^ 2 + 3) / c)]
  exact mul_le_mul_of_nonneg_left hquot (div_nonneg (neg_nonneg.mpr hnu.le) (sq_nonneg r))

/-- Bound a weighted source integral using λ ≤ 1 and a positive lower bound
for the final λ. Paper `e1a0fd5`, `eq:derivative-remainder-bound`, line 603. -/
theorem weighted_source_integral_bound {lam F G : ℝ → ℝ} {a b C L : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hL : 0 < L) (hlamb : L ≤ lam b)
    (hlam : ∀ s ∈ Icc a b, 0 ≤ lam s ∧ lam s ≤ 1)
    (hF : IntervalIntegrable F volume a b) (hG : IntervalIntegrable G volume a b)
    (hcont : ContinuousOn lam (uIcc a b))
    (hG0 : ∀ s ∈ Icc a b, 0 ≤ G s)
    (hbound : ∀ s ∈ Icc a b, |F s| ≤ C * G s) :
    |(∫ s in a..b, lam s ^ 2 * F s) / lam b ^ 2| ≤
      (C / L ^ 2) * ∫ s in a..b, G s := by
  have hw : IntervalIntegrable (fun s => lam s ^ 2 * F s) volume a b :=
    hF.continuousOn_mul (hcont.pow 2)
  have hle : (∫ s in a..b, |lam s ^ 2 * F s|) ≤ C * ∫ s in a..b, G s := by
    calc
      _ ≤ ∫ s in a..b, C * G s := by
        apply intervalIntegral.integral_mono_on hab (by simpa only [Real.norm_eq_abs] using hw.norm)
          (hG.const_mul C)
        intro s hs
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hl := hlam s hs
        have hsq : lam s ^ 2 ≤ 1 := by nlinarith
        calc
          _ ≤ 1 * |F s| := mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
          _ ≤ C * G s := by simpa only [one_mul] using hbound s hs
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hi0 : 0 ≤ ∫ s in a..b, G s := intervalIntegral.integral_nonneg hab hG0
  have hsq : L ^ 2 ≤ lam b ^ 2 := by nlinarith
  have hpos : 0 < lam b ^ 2 := sq_pos_of_pos (hL.trans_le hlamb)
  rw [abs_div, abs_of_pos hpos]
  calc
    _ ≤ (C * ∫ s in a..b, G s) / lam b ^ 2 := by
      apply div_le_div_of_nonneg_right _ hpos.le
      have hnorm : |∫ s in a..b, lam s ^ 2 * F s| ≤ ∫ s in a..b, |lam s ^ 2 * F s| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s => lam s ^ 2 * F s) hab
      exact hnorm.trans hle
    _ ≤ (C * ∫ s in a..b, G s) / L ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hC hi0) (sq_pos_of_pos hL) hsq
    _ = _ := by ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Connect the radial derivative to the integral remainder once its incoming
AC transport has been justified. The initial equality holds for a.e. v by
`radialDatumDerivative_initial_ae`; `ACDatum.RadialTransport` discharges the
two q transport premises at each differentiable initial label. Paper `e1a0fd5`,
`eq:rough-derivative-decomposition`, lines 572–574 and 603. -/
theorem radialDatumDerivative_decomposition_of_transport {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hinit : radialDatumDerivative S ui v = deriv (S.dvpsi ui) v)
    (hq : AbsolutelyContinuousOnInterval (fun s => radialDatumDerivative S s v) ui u)
    (hdq : ∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => radialDatumDerivative S t v)
      (-2 * (S.gamma s v * S.varkappa s v) * radialDatumDerivative S s v +
        radialDatumSource S s v) s) :
    radialDatumDerivative S u v = deriv (S.dvpsi ui) v / S.lam u v ^ 2 +
      radialDatumRemainderIntegral ui S u v := by
  have hlam := h.lam_ac_in hu le_rfl hu0 huv hv0
  have hl := intervalPrimitive_ae_hasDerivAt hu
    (fun x hx => h.regularCenter.localBV.lam_in v ui x hx.1
      (inSeg_subset_offAxis le_rfl (hx.2.trans_lt hu0) (hx.2.trans_lt huv) hv0))
  have hdlam : ∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => S.lam t v)
      (S.lam s v * (S.gamma s v * S.varkappa s v)) s := by
    filter_upwards [hl] with s hls
    intro hs
    convert hls hs using 1
    rw [S.radiusCoeff_eq_lam_gamma]
    ring
  have hw := weighted_datum_transport_primitive hu hlam hq hdlam hdq
  have hv : v ∈ Icc ui 0 := ⟨(hu.trans_lt huv).le, hv0⟩
  have he := datum_decomposition_of_weighted_primitive
    (lam := fun s => S.lam s v) (q := fun s => radialDatumDerivative S s v)
    (F := fun s => radialDatumSource S s v) (a := ui) (b := u) (h.initial_gauge v hv).2
    (h.lam_pos (p := (u, v)) ⟨hu, hu0, huv.le, hv0⟩).ne' hw
  simpa only [hinit, radialDatumRemainderIntegral] using he

/-- The nonlinear source is continuous on every proper off-axis incoming
segment. Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–567 and 603. -/
theorem radialDatumSource_continuous_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ContinuousOn (fun s => radialDatumSource S s v) (Icc a b) := by
  have hs := inSeg_subset_triangle ha hb0 hbv.le hv0
  have hr := continuous_in h.regularCenter.continuous_r hs
  have hn := continuous_in h.regularCenter.continuous_nu hs
  have hm := continuous_in h.regularCenter.continuous_m hs
  have hl := continuous_in h.regularCenter.continuous_lam hs
  have hp := continuous_in h.regularCenter.continuous_phi hs
  have hd := h.dvpsi_ac_in hab ha hb0 hbv hv0 |>.continuousOn
  rw [uIcc_of_le hab] at hd
  have hpoint : ∀ s ∈ Icc a b, (s, v) ∈ pastTriangle ui := fun s hs' =>
    ⟨ha.trans hs'.1, hs'.2.trans_lt hb0, (hs'.2.trans_lt hbv).le, hv0⟩
  have hr0 : ∀ s ∈ Icc a b, S.r s v ≠ 0 := fun s hs' =>
    (h.r_pos (hpoint s hs') (hs'.2.trans_lt hbv)).ne'
  have hl0 : ∀ s ∈ Icc a b, S.lam s v ≠ 0 := fun s hs' => (h.lam_pos (hpoint s hs')).ne'
  have hmu : ContinuousOn (fun s => S.mu s v) (Icc a b) := by
    exact (continuousOn_const.mul hm).div hr hr0
  have hgap0 : ∀ s ∈ Icc a b, 1 - S.mu s v ≠ 0 := fun s hs' =>
    (sub_pos.mpr (h.mu_bounds (hpoint s hs')).2).ne'
  have hg : ContinuousOn (fun s => S.gamma s v) (Icc a b) :=
    hn.div (continuousOn_const.sub hmu) hgap0
  have hA : ContinuousOn (fun s => S.theta s v / S.lam s v) (Icc a b) :=
    (hd.sub (hl.mul hp)).div hl hl0
  have h3mu : ContinuousOn (fun s => 3 * S.mu s v) (Icc a b) :=
    continuousOn_const.mul hmu
  exact ((hg.neg.div (hr.pow 2) (fun s hs' => pow_ne_zero 2 (hr0 s hs'))).mul hA).mul
    ((hA.pow 2).sub h3mu)

/-- A uniform geometric gap and Lemma 2.1 bound control the integral remainder.
This internal helper does not identify that remainder with the derivative q.
The gap premise is discharged by G2 with c = cᵢ exp(-B*), and the scalar
premise by Lemma 2.1. Paper `e1a0fd5`,
`eq:derivative-remainder-bound`, lines 578–581 and 603. -/
theorem radialDatumRemainderIntegral_bound_of_geometric {c M : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M)
    (hgap : ∀ p ∈ pastTriangle ui, c ≤ 1 - S.mu p.1 p.2)
    (hscalar : ∀ p ∈ pastTriangle ui,
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
      |radialDatumRemainderIntegral ui S u v| ≤
        C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ∧
      C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ≤ C / S.r u v := by
  let K := M * (M ^ 2 + 3) / c
  let L := Real.exp (-Bstar ui S)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hM (by positivity)) hc.le
  have hL : 0 < L := Real.exp_pos _
  have hKL : 0 ≤ K / L ^ 2 := div_nonneg hK (sq_nonneg _)
  refine ⟨K / L ^ 2 + 1, by linarith, ?_⟩
  intro u v hu hu0 huv hv0
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, huv.le, hv0⟩
  have hpoint : ∀ s ∈ Icc ui u, (s, v) ∈ pastTriangle ui := fun s hs =>
    ⟨hs.1, hs.2.trans_lt hu0, (hs.2.trans_lt huv).le, hv0⟩
  have hn : ∀ s ∈ Icc ui u, 0 ≤ -S.nu s v / S.r s v ^ 2 := by
    intro s hs
    exact div_nonneg (neg_nonneg.mpr (h.nu_neg (hpoint s hs)).le) (sq_nonneg _)
  have hI : 0 ≤ ∫ s in ui..u, -S.nu s v / S.r s v ^ 2 :=
    intervalIntegral.integral_nonneg hu hn
  have hF := h.radialDatumSource_continuous_in hu le_rfl hu0 huv hv0
  have hl := continuous_in h.regularCenter.continuous_lam
    (inSeg_subset_triangle le_rfl hu0 huv.le hv0)
  have hb : |radialDatumRemainderIntegral ui S u v| ≤
      (K / L ^ 2) * ∫ s in ui..u, -S.nu s v / S.r s v ^ 2 := by
    apply weighted_source_integral_bound hu hK hL (h.lam_bounds hp).1
      (fun s hs => ⟨(h.lam_pos (hpoint s hs)).le, (h.lam_bounds (hpoint s hs)).2⟩)
      (hF.intervalIntegrable_of_Icc hu)
      (h.reciprocal_radius_primitive hu le_rfl hu0 huv hv0).1
      (by simpa only [uIcc_of_le hu] using hl) hn
    intro s hs
    have hmu := h.mu_bounds (hpoint s hs)
    have hA : |S.theta s v / S.lam s v| ≤ M := by
      have hbnd := hscalar (s, v) (hpoint s hs)
      linarith [abs_nonneg (S.dvpsi s v / S.lam s v), abs_nonneg (S.phi s v)]
    exact cubic_datum_source_bound (h.r_pos (hpoint s hs) (hs.2.trans_lt huv))
      (h.nu_neg (hpoint s hs)) hmu.1 hmu.2 hc (hgap (s, v) (hpoint s hs)) hM hA
  constructor
  · exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hI)
  · calc
      _ ≤ (K / L ^ 2 + 1) * (1 / S.r u v) :=
        mul_le_mul_of_nonneg_left (h.incoming_reciprocal_integral_le hu hu0 huv hv0)
          (by linarith)
      _ = _ := by ring

end StandingFull

end AcExtensionPrinciple

end
