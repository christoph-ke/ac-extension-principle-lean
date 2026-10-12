module

public import AcExtensionPrinciple.Redundancy.ExpansionInterior
public import AcExtensionPrinciple.Redundancy.ScalarAxis

/-!
# Mass-ratio continuity at the regular axis without expansion continuity
Paper commit `e1a0fd5`, `equations.tex` lines 74–77 and 220–275,
`eq:mass`, `eq:regular-axis-scalar-traces`.
The normalized outgoing scalar trace bounds the mass primitive by the radius primitive.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The outgoing mass density is bounded by the squared normalized scalar amplitude times λ.
The scalar trace will supply the amplitude bound. Paper `e1a0fd5`, `eq:mass`, lines 74–77, 259. -/
theorem Q1StandingCore.massV_le_of_normalized_bound {ui B : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui)
    (hB : |S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2| ≤ B) :
    S.massV p.1 p.2 ≤ (B ^ 2 / 2) * S.lam p.1 p.2 := by
  have hl := h.lam_pos hp
  have he : S.massV p.1 p.2 =
      (1 - S.mu p.1 p.2) * S.lam p.1 p.2 / 2 *
        (S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2) ^ 2 := by
    unfold SSFields.massV SSFields.theta
    field_simp
  rw [he]
  have hsq : (S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2) ^ 2 ≤ B ^ 2 := by
    have hs : |S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2| ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hB)).mpr hB
    simpa only [sq_abs] using hs
  calc
    _ ≤ S.lam p.1 p.2 / 2 *
        (S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [(h.mu_bounds hp).1]
    _ ≤ S.lam p.1 p.2 / 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- An outgoing normalized amplitude bound controls μ on the whole cone segment, without λ
continuity. Paper `e1a0fd5`, `eq:mass`, `eq:radius-from-axis`, lines 66–77, 259. -/
theorem Q1StandingCore.mu_le_of_outgoing_normalized_bound {ui u v B : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hp : (u, v) ∈ pastTriangle ui) (huv : u < v)
    (hB : ∀ s ∈ Ioo u v, |S.dvpsi u s / S.lam u s - S.phi u s| ≤ B) :
    S.mu u v ≤ B ^ 2 := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  have hr := h.regularCenter.localBV.radius_out u u v huv.le hs
  have hm := h.regularCenter.localBV.mass_out u u v huv.le hs
  have hav := h.regularCenter.localBV.axis_values u
    ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩
  have hle : S.m u v ≤ (B ^ 2 / 2) * S.r u v := by
    have hI := intervalIntegral.integral_mono_on_of_le_Ioo huv.le hm.1
      (hr.1.const_mul (B ^ 2 / 2)) (fun s hs' =>
        h.massV_le_of_normalized_bound (p := (u, s))
          ⟨hp.1, hp.2.1, hs'.1.le, hs'.2.le.trans hp.2.2.2⟩ (hB s hs'))
    rw [intervalIntegral.integral_const_mul] at hI
    rw [← hr.2, ← hm.2, hav.1, hav.2, sub_zero, sub_zero] at hI
    exact hI
  change 2 * S.m u v / S.r u v ≤ B ^ 2
  apply (div_le_iff₀ (h.r_pos hp huv)).mpr
  nlinarith

/-- The regular scalar traces force μ to tend to zero jointly at the axis. This uses no
the additional geometric continuity fields. Paper `e1a0fd5`, lines 247–275,
`eq:regular-axis-scalar-traces`. -/
theorem q1_mu_axis_trace {ui a : ℝ} {S : SSFields} (h : Q1StandingCore ui S)
    (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.mu p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let B := min (ε / 2) (1 / 2)
  have hB : 0 < B := lt_min (by positivity) (by norm_num)
  obtain ⟨δd, hδd, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (h.regularCenter.axis_dvpsi_trace a ha) (B / 2) (by positivity)
  obtain ⟨δφ, hδφ, hφ⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (q1_phi_axis_trace h ha) (B / 2) (by positivity)
  refine ⟨min δd δφ, lt_min hδd hδφ, ?_⟩
  intro p hp hpd
  have hpa : p.1 < p.2 := (cylinderScalarRegion_eq_axisComplement ui ▸ hp).2.1
  have hnear (s : ℝ) (hs : s ∈ Ioo p.1 p.2) :
      (p.1, s) ∈ pastTriangle ui \ axis ui ∧ dist (p.1, s) (a, a) < min δd δφ := by
    constructor
    · rw [← cylinderScalarRegion_eq_axisComplement]
      exact ⟨hp.1.1, hs.1, hs.2.le.trans hp.1.2.2.2⟩
    · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hpd ⊢
      exact ⟨hpd.1, ⟨by dsimp only at hpd ⊢; linarith [hpd.1.1, hs.1],
        by dsimp only at hpd ⊢; linarith [hpd.2.2, hs.2]⟩⟩
  have hbound := h.mu_le_of_outgoing_normalized_bound hp.1 hpa (B := B) (by
    intro s hs
    have hn := hnear s hs
    have hd' := hd hn.1 (hn.2.trans_le (min_le_left _ _))
    have hφ' := hφ hn.1 (hn.2.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at hd' hφ'
    rw [abs_le]
    constructor <;> linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h.mu_bounds hp.1).1]
  have hBε : B ≤ ε / 2 := min_le_left _ _
  have hB1 : B ≤ 1 / 2 := min_le_right _ _
  nlinarith

end AcExtensionPrinciple

end
