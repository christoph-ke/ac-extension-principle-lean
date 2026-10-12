module

public import AcExtensionPrinciple.ScalarBound.BootstrapEstimate
public import AcExtensionPrinciple.ScalarBound.MassContradiction

/-!
# Uniform outgoing scalar-amplitude bound

Paper commit `e1a0fd5`, `equations.tex`
lines 428–524, `eq:scalar-bound-running-maximum` through
`eq:scalar-bound-mass-contradiction`. The geometric helper premises
are exactly a positive uniform gap and the complete incoming flux
bound, supplied by Lemma 1.1; the terminal ray is included throughout.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The complete running-maximum, strip-bootstrap and mass-contradiction
argument. The two geometric bounds are discharged by G2/G6.
Paper `e1a0fd5`, lines 428–524, `lem:uniform-scalar-bound`. -/
theorem exists_theta_bound_of_flux_and_gap {g K : ℝ} (hg : 0 < g) (hK : 0 ≤ K)
    (hgap : ∀ p ∈ pastTriangle ui, g ≤ 1 - S.mu p.1 p.2)
    (hflux : ∀ v ∈ Ioc ui 0,
      (∫⁻ x in Ioo ui v, ENNReal.ofReal (S.incomingFlux x v)) ≤ ENNReal.ofReal K) :
    ∃ T : ℝ, ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T := by
  obtain ⟨A, hA0, hA⟩ := h.exists_initial_scalar_bound
  let M := 2 * A
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM : ∀ s ∈ Icc ui 0, |S.theta ui s| ≤ M := fun s hs => (hA s hs).2.2
  let C₀ := scalarStripDifferenceConstant ui S g K
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀, scalarStripDifferenceConstant, scalarStripTransportConstant,
      scalarStripCoefficientConstant]
    positivity
  let δ := 1 / (4 * (C₀ + 1))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (C₀ + 1))).mpr
    nlinarith
  have hδsmall : scalarStripDifferenceConstant ui S g K * δ ≤ 1 / 4 := by
    change C₀ * (1 / (4 * (C₀ + 1))) ≤ 1 / 4
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (C₀ + 1))).mpr
    nlinarith
  refine ⟨max (8 * (1 + M)) (16 / (g * δ)), ?_⟩
  rintro ⟨u₁, v⟩ hp huv
  have hc : ContinuousOn (fun u => |S.theta u v|) (Icc ui u₁) :=
    (h.theta_continuous_rectangle hp.1 huv le_rfl hp.2.2.2).abs.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, ⟨le_rfl, le_rfl⟩⟩)
  obtain ⟨U, hU, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hp.1) hc
  let F := 1 + |S.theta U v|
  have hF1 : 1 ≤ F := by dsimp [F]; linarith [abs_nonneg (S.theta U v)]
  have hF0 : 0 < F := zero_lt_one.trans_le hF1
  have hrun : ∀ u ∈ Icc ui u₁, |S.theta u v| ≤ F - 1 := by
    intro u hu
    have ht := hmax hu
    change |S.theta u v| ≤ |S.theta U v| at ht
    dsimp [F]
    linarith
  have heval : |S.theta u₁ v| ≤ F - 1 := hrun u₁ (right_mem_Icc.mpr hp.1)
  by_cases hsmall : F ≤ 8 * (1 + M)
  · exact (by linarith : |S.theta u₁ v| ≤ 8 * (1 + M)).trans (le_max_left _ _)
  have hlarge : 8 * (1 + M) < F := lt_of_not_ge hsmall
  have hF8 : 8 < F := by nlinarith
  have hMsmall : 2 * M ≤ F / 4 := by nlinarith
  have hUv : U < v := hU.2.trans_lt huv
  have hU0 : U < 0 := hU.2.trans_lt hp.2.1
  have hpU : (U, v) ∈ pastTriangle ui := ⟨hU.1, hU0, hUv.le, hp.2.2.2⟩
  have hR := h.r_pos hpU hUv
  let η := δ * S.r U v / F
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηhalf : η ≤ S.r U v / 2 := by
    have ht := div_le_div₀ (by positivity : 0 ≤ (1 / 2 : ℝ) * S.r U v)
      (mul_le_mul_of_nonneg_right hδhalf hR.le) zero_lt_one hF1
    have ht' : η ≤ (1 / 2 : ℝ) * S.r U v := by simpa only [div_one] using ht
    exact ht'.trans_eq (by ring)
  have hUη : U < v - η := by
    have hrup := (h.radius_bounds hpU).2
    linarith
  have hfull : ∀ u ∈ Icc ui U, ∀ s ∈ Icc (v - η) v, |S.theta u s| < 2 * F := by
    apply close_scalar_strip_bootstrap
      (h.theta_continuous_rectangle hU.1 hUη (by linarith) hp.2.2.2)
    · intro u hu
      have hru := hrun u ⟨hu.1, hu.2.trans hU.2⟩
      linarith
    · intro w hw hboot u hu s hs
      have hdiff := h.scalar_bootstrap_difference_le_half hU.1 hUη hp.2.2.2 hg hK hF1
        hη0.le hηhalf rfl hδsmall hMsmall hgap hflux hM hw hboot hu hs
      have hru := hrun u ⟨hu.1, hu.2.trans hU.2⟩
      have ht : |S.theta u s| ≤ |S.theta u s - S.theta u v| + |S.theta u v| := by
        calc
          _ = |(S.theta u s - S.theta u v) + S.theta u v| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      linarith
  have hpersist : ∀ s ∈ Icc (v - η) v, F / 4 ≤ |S.theta U s| := by
    intro s hs
    have hdiff := h.scalar_bootstrap_difference_le_half hU.1 hUη hp.2.2.2 hg hK hF1
      hη0.le hηhalf rfl hδsmall hMsmall hgap hflux hM (right_mem_Icc.mpr hη0.le)
      (fun u hu s hs => (hfull u hu s hs).le) (right_mem_Icc.mpr hU.1) hs
    exact scalar_large_value_persists hF8 (by dsimp [F]; ring) hdiff
  have hbound := h.scalar_mass_contradiction hU.1 hU0 hUη (by linarith) hp.2.2.2
    hg hF0 hδ0
    (fun s hs => hgap (U, s) ⟨hU.1, hU0, (hUη.trans_le hs.1).le, hs.2.trans hp.2.2.2⟩)
    hpersist (by dsimp [η]; ring)
  exact (by linarith : |S.theta u₁ v| ≤ 16 / (g * δ)).trans (le_max_right _ _)

end AcExtensionPrinciple.StandingFull

end
