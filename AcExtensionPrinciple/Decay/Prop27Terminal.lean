module

public import AcExtensionPrinciple.Decay.ClassRayConsequences
public import AcExtensionPrinciple.Analysis.TerminalMassDecay

/-!
# Decay on the terminal incoming ray

Paper `e1a0fd5`, lines 847–857. This is the annular argument in the original time coordinate: radius
comparison pulls the annular lower bound back to `[2u,u]`. It uses the finite terminal blueshift
integral directly, and hence avoids introducing a global inverse-radius chart.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The pulled-back annular lower bound, using mass monotonicity and G3/G4.
Paper `e1a0fd5`, `eq:terminal-radial-blueshift`, lines 848–854. -/
theorem decay_terminal_annulus {u : ℝ} (hu : u < 0) (hui : ui ≤ 2 * u) :
    ENNReal.ofReal (Real.exp (-Bstar ui S) ^ 2 * S.mu u 0 / 4) ≤
      ∫⁻ s in Ioo (2 * u) u, ENNReal.ofReal (-(S.gamma s 0 * S.varkappa s 0)) := by
  let c := Real.exp (-Bstar ui S)
  have hc : 0 < c := Real.exp_pos _
  have hup : (u, 0) ∈ pastTriangle ui := ⟨by linarith, hu, hu.le, le_rfl⟩
  have hmu := (h.mu_bounds hup).1
  have hru := (h.radius_bounds hup).1
  change 0 ≤ S.mu u 0 at hmu
  change Real.exp (-Bstar ui S) * (0 - u) ≤ S.r u 0 at hru
  rw [zero_sub] at hru
  have hidu : S.mu u 0 * S.r u 0 = 2 * S.m u 0 := by
    simp [SSFields.mu, massRatio, ne_of_gt (h.r_pos hup hu)]
  have hpoint (s : ℝ) (hs : s ∈ Ioo (2 * u) u) :
      c ^ 2 * S.mu u 0 / (-4 * u) ≤ -(S.gamma s 0 * S.varkappa s 0) := by
    have hsp : (s, 0) ∈ pastTriangle ui := ⟨hui.trans hs.1.le, hs.2.trans hu,
      (hs.2.trans hu).le, le_rfl⟩
    have hrs := h.r_pos hsp (hs.2.trans hu)
    have hms := h.mu_bounds hsp
    change 0 ≤ S.mu s 0 ∧ S.mu s 0 < 1 at hms
    have hmass := h.decay_mass_in_le hs.2.le hsp.1 hu hu.le le_rfl
    have hids : S.mu s 0 * S.r s 0 = 2 * S.m s 0 := by
      simp [SSFields.mu, massRatio, ne_of_gt hrs]
    have hrupper : S.r s 0 ≤ -2 * u := by
      have hh := (h.radius_bounds hsp).2
      change S.r s 0 ≤ 0 - s at hh
      rw [zero_sub] at hh
      linarith [hs.1]
    have hmus : S.mu u 0 * c / 2 ≤ S.mu s 0 := by
      have h1 := mul_le_mul_of_nonneg_left hru hmu
      have h2 := mul_le_mul_of_nonneg_left hrupper hms.1
      dsimp [c] at h1 ⊢
      nlinarith
    have hquot : S.mu u 0 * c / (-4 * u) ≤ S.mu s 0 / S.r s 0 := by
      apply (div_le_div_iff₀ (by linarith : 0 < -4 * u) hrs).mpr
      have h1 := mul_le_mul_of_nonneg_left hrupper (mul_nonneg hmu hc.le)
      have h2 := mul_le_mul_of_nonneg_right hmus (show 0 ≤ -4 * u by linarith)
      nlinarith
    have hnu : c ≤ -S.nu s 0 / (1 - S.mu s 0) := by
      apply (le_div_iff₀ (sub_pos.mpr hms.2)).mpr
      have hn := h.neg_nu_lower hsp
      dsimp [c] at *
      nlinarith [mul_nonneg (Real.exp_pos (-Bstar ui S)).le hms.1]
    have heq : -(S.gamma s 0 * S.varkappa s 0) =
        (-S.nu s 0 / (1 - S.mu s 0)) * (S.mu s 0 / S.r s 0) := by
      simp only [SSFields.gamma, SSFields.varkappa, gammaOf, varkappaOf, neg_div, neg_mul]
    rw [heq]
    calc
      _ = c * (S.mu u 0 * c / (-4 * u)) := by ring
      _ ≤ c * (S.mu s 0 / S.r s 0) := mul_le_mul_of_nonneg_left hquot hc.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hnu (div_nonneg hms.1 hrs.le)
  have hle := setLIntegral_mono' (μ := volume) measurableSet_Ioo
    (fun s hs => ENNReal.ofReal_le_ofReal (hpoint s hs))
  have hconst : 0 ≤ c ^ 2 * S.mu u 0 / (-4 * u) :=
    div_nonneg (mul_nonneg (sq_nonneg c) hmu) (by linarith)
  rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hconst] at hle
  have heq : c ^ 2 * S.mu u 0 / (-4 * u) * (u - 2 * u) = c ^ 2 * S.mu u 0 / 4 := by
    field_simp [ne_of_lt hu]
    ring
  simpa only [heq, c] using hle

/-- Terminal mass-ratio decay from the finite G5 integral, by the annular method. Paper `e1a0fd5`,
`eq:terminal-mass-decay`, lines 847–857. -/
theorem decay_terminal_mu : Tendsto (fun u => S.mu u 0) (𝓝[<] 0) (𝓝 0) := by
  let g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (-(S.gamma s 0 * S.varkappa s 0))
  have hfin : (∫⁻ s in Ioo ui 0, g s) < ⊤ :=
    lt_of_le_of_lt h.terminal_blueshift_le h.blueshift_finite
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hvol : Tendsto (fun u : ℝ => ENNReal.ofReal (u - 2 * u)) (𝓝[<] 0) (𝓝 0) := by
    have ht : Tendsto (fun u : ℝ => u - 2 * u) (𝓝[<] 0) (𝓝 0) := by
      simpa using hid.sub (hid.const_mul 2)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  have hrestricted : Tendsto (fun u : ℝ => (volume.restrict (Ioo ui 0)) (Ioo (2 * u) u))
      (𝓝[<] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
      (fun _ => bot_le)
    intro u
    exact (Measure.restrict_le_self _).trans_eq Real.volume_Ioo
  have hsmall := tendsto_setLIntegral_zero hfin.ne hrestricted
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [Ioo_mem_nhdsLT h.initial_negative] with u hu
    exact ha.trans_le (h.mu_bounds (p := (u, 0)) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩).1
  · intro eps heps
    have hc : 0 < Real.exp (-Bstar ui S) ^ 2 := by positivity
    have he : 0 < ENNReal.ofReal (Real.exp (-Bstar ui S) ^ 2 * eps / 4) := by positivity
    filter_upwards [Ioo_mem_nhdsLT (show ui / 2 < 0 by linarith [h.initial_negative]),
      hsmall.eventually (gt_mem_nhds he)] with u hu hs
    have hui : ui ≤ 2 * u := by linarith [hu.1]
    have hsub : Ioo (2 * u) u ⊆ Ioo ui 0 :=
      fun s hs => ⟨lt_of_le_of_lt hui hs.1, hs.2.trans hu.2⟩
    rw [Measure.restrict_restrict_of_subset hsub] at hs
    have hh := (h.decay_terminal_annulus hu.2 hui).trans_lt hs
    have hlt := (ENNReal.ofReal_lt_ofReal_iff
      (show 0 < Real.exp (-Bstar ui S) ^ 2 * eps / 4 by positivity)).mp hh
    nlinarith

/-- The terminal mass is o(-u). Paper `e1a0fd5`,
`eq:terminal-mass-decay`, lines 855–857. -/
theorem decay_terminal_mass_scale :
    Tendsto (fun u => S.m u 0 / (-u)) (𝓝[<] 0) (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa using h.decay_terminal_mu.div_const 2)
  · filter_upwards [Ioo_mem_nhdsLT h.initial_negative] with u hu
    exact div_nonneg (h.decay_mass_nonneg (u := u) (v := 0)
      ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩) (by linarith [hu.2] : 0 ≤ -u)
  · filter_upwards [Ioo_mem_nhdsLT h.initial_negative] with u hu
    have hp : (u, 0) ∈ pastTriangle ui := ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩
    have heq : S.mu u 0 * S.r u 0 = 2 * S.m u 0 := by
      simp [SSFields.mu, massRatio, ne_of_gt (h.r_pos hp hu.2)]
    apply (div_le_iff₀ (neg_pos.mpr hu.2)).mpr
    have hh := mul_le_mul_of_nonneg_left (h.radius_bounds hp).2 (h.mu_bounds hp).1
    simp only [zero_sub] at hh
    nlinarith

end AcExtensionPrinciple.StandingFull

end
