module

public import AcExtensionPrinciple.Observability.ChartRegularity

/-!
# AC mass traces and the cylinder chain rule

Paper `e1a0fd5`, `equations.tex` line 1522. The mass equations turn bounded
first scalar derivatives into bounded characteristic mass derivatives.
Their joint continuity at almost every diagonal point gives the chain rule.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A bounded scalar derivative and continuous geometric factors bound the
quadratic mass derivative. Paper `e1a0fd5`, `equations.tex` line 1522. -/
theorem chart_quadratic_bound {C : Set (ℝ × ℝ)} {U A D : ℝ × ℝ → ℝ} {M : ℝ}
    (hC : IsCompact C) (_hM : 0 ≤ M) (hU : ∀ q ∈ C, |U q| ≤ M)
    (hA : ContinuousOn A C) (hD : ContinuousOn D C) :
    ∃ N, 0 ≤ N ∧ ∀ q ∈ C, |A q * (U q - D q) ^ 2| ≤ N := by
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hA
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn hD
  refine ⟨|B| * (M + |L|) ^ 2, by positivity, ?_⟩
  intro q hq
  have hα : |A q| ≤ |B| := (hB q hq).trans (le_abs_self _)
  have hδ : |U q - D q| ≤ M + |L| :=
    (abs_sub _ _).trans (add_le_add (hU q hq) ((hL q hq).trans (le_abs_self _)))
  rw [abs_mul, abs_pow]
  gcongr

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- Geometry is continuous, including the mass ratio, on positive-radius
subdomains. Paper `e1a0fd5`, `equations.tex` line 1522 and lines 220–275. -/
theorem geometry_continuous_on {C : Set (ℝ × ℝ)}
    (hC : C ⊆ chartInterior (chartCylinder h.g T) S) :
    ContinuousOn (fun q => S.mu q.1 q.2) C ∧
    ContinuousOn (fun q => S.nu q.1 q.2) C ∧
    ContinuousOn (fun q => S.lam q.1 q.2) C ∧
    ContinuousOn (fun q => S.phi q.1 q.2) C := by
  have hr := h.continuous_r.mono (fun q hq => (hC hq).1)
  have hm := h.continuous_m.mono (fun q hq => (hC hq).1)
  refine ⟨(continuousOn_const.mul hm).div hr (fun q hq => (hC hq).2.ne'),
    h.continuous_nu.mono (fun q hq => (hC hq).1),
    h.continuous_lam.mono (fun q hq => (hC hq).1),
    h.continuous_phi.mono (fun q hq => (hC hq).1)⟩

/-- Both characteristic mass derivatives are bounded on a positive-radius
triangle and continuous at almost every boundary point. Paper `e1a0fd5`, line 1522. -/
theorem mass_triangle_regularity {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ T) (hg : h.g c < a) :
    (∃ M, 0 ≤ M ∧ ∀ s t, (s, t) ∈ chartTriangle a c →
      |S.massU s t| ≤ M ∧ |S.massV s t| ≤ M) ∧
    (∀ᵐ x ∂volume, x ∈ Icc a c →
      ContinuousWithinAt (fun q => S.massU q.1 q.2) (chartTriangle a c) (x, x) ∧
      ContinuousWithinAt (fun q => S.massV q.1 q.2) (chartTriangle a c) (x, x)) := by
  have htri := h.triangle_subset ha hac hc hg
  obtain ⟨hμ, hn, hl, hp⟩ := h.geometry_continuous_on htri
  have hnu : ∀ q ∈ chartTriangle a c, S.nu q.1 q.2 ≠ 0 :=
    fun q hq => (h.signs q.1 q.2 (htri hq).1).2.1.ne
  have hlam : ∀ q ∈ chartTriangle a c, S.lam q.1 q.2 ≠ 0 :=
    fun q hq => (h.signs q.1 q.2 (htri hq).1).1.ne'
  obtain ⟨hbound, hae⟩ := h.scalar_triangle_regularity ha hac hc hg
  obtain ⟨M, hM, hMbound⟩ := hbound
  have hA : ContinuousOn (fun q => (1 - S.mu q.1 q.2) / (2 * S.nu q.1 q.2))
      (chartTriangle a c) :=
    (continuousOn_const.sub hμ).div (continuousOn_const.mul hn)
      (fun q hq => mul_ne_zero two_ne_zero (hnu q hq))
  have hB : ContinuousOn (fun q => (1 - S.mu q.1 q.2) / (2 * S.lam q.1 q.2))
      (chartTriangle a c) :=
    (continuousOn_const.sub hμ).div (continuousOn_const.mul hl)
      (fun q hq => mul_ne_zero two_ne_zero (hlam q hq))
  obtain ⟨N, hN, hNb⟩ := chart_quadratic_bound (isCompact_chartTriangle a c) hM
    (fun q hq => (hMbound q.1 q.2 hq).1) hA (hn.mul hp)
  obtain ⟨L, hL, hLb⟩ := chart_quadratic_bound (isCompact_chartTriangle a c) hM
    (fun q hq => (hMbound q.1 q.2 hq).2) hB (hl.mul hp)
  constructor
  · refine ⟨N + L, add_nonneg hN hL, ?_⟩
    intro s t hq
    constructor
    · have hh := hNb (s, t) hq
      simpa only [SSFields.massU, SSFields.zeta, div_mul_eq_mul_div, Pi.mul_apply] using
        hh.trans (le_add_of_nonneg_right hL)
    · have hh := hLb (s, t) hq
      simpa only [SSFields.massV, SSFields.theta, div_mul_eq_mul_div, Pi.mul_apply] using
        hh.trans (le_add_of_nonneg_left hN)
  · filter_upwards [hae] with x hx
    intro hxI
    have hq : (x, x) ∈ chartTriangle a c := ⟨hxI.1, le_rfl, hxI.2⟩
    have hu := (hx hxI).1
    have hv := (hx hxI).2
    have hU := (hA (x, x) hq).mul
      ((hu.sub ((hn (x, x) hq).mul (hp (x, x) hq))).pow 2)
    have hV := (hB (x, x) hq).mul
      ((hv.sub ((hl (x, x) hq).mul (hp (x, x) hq))).pow 2)
    change ContinuousWithinAt (fun q : ℝ × ℝ => (1 - S.mu q.1 q.2) / (2 * S.nu q.1 q.2) *
      (S.dupsi q.1 q.2 - S.nu q.1 q.2 * S.phi q.1 q.2) ^ 2) _ _ at hU
    change ContinuousWithinAt (fun q : ℝ × ℝ => (1 - S.mu q.1 q.2) / (2 * S.lam q.1 q.2) *
      (S.dvpsi q.1 q.2 - S.lam q.1 q.2 * S.phi q.1 q.2) ^ 2) _ _ at hV
    simpa only [SSFields.massU, SSFields.massV, SSFields.zeta, SSFields.theta,
      div_mul_eq_mul_div, Pi.mul_apply, Pi.sub_apply] using And.intro hU hV

/-- The mass boundary trace is Lipschitz, hence AC. Paper `e1a0fd5`, `equations.tex` line 1522 (the
mass trace and chain rule). -/
theorem boundary_mass_lipschitz : ∃ L, LipschitzOnWith L (fun s => S.m s s) (Icc 0 T) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro x hx
  obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
  obtain ⟨M, hM, hbound⟩ := (h.mass_triangle_regularity ha hac hc hg).1
  have htri := h.triangle_subset ha hac hc hg
  refine ⟨⟨2 * M, by positivity⟩, Icc a c, hnhds, ?_⟩
  apply chart_diagonal_lipschitz hM
  · intro l r hl hlr hr
    exact h.equations.mass_s l l r hlr
      (fun q hq => (htri (chartTriangle_in_subset hl le_rfl hr hq)).1)
  · intro l r hl hlr hr
    exact h.equations.mass_t r l r hlr
      (fun q hq => (htri (chartTriangle_out_subset hl le_rfl hr hq)).1)
  · exact hbound

/-- The mass chain rule along the cylinder holds almost everywhere. Paper
`e1a0fd5`, `eq:observability-shifted-balance`, lines 1518, 1522. -/
theorem boundary_mass_ae_hasDerivAt :
    ∀ᵐ s ∂volume, s ∈ Icc 0 T →
      HasDerivAt (fun s => S.m s s) (S.massU s s + S.massV s s) s := by
  apply chart_ae_of_local isCompact_Icc
  intro x hx
  obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
  have htri := h.triangle_subset ha hac hc hg
  refine ⟨Icc a c, hnhds, ?_⟩
  filter_upwards [(h.mass_triangle_regularity ha hac hc hg).2,
    show ∀ᵐ y : ℝ ∂volume, y ≠ a by simp [ae_iff],
    show ∀ᵐ y : ℝ ∂volume, y ≠ c by simp [ae_iff]] with y hy hya hyc
  intro hyI
  apply chart_diagonal_hasDerivAt ⟨lt_of_le_of_ne hyI.1 hya.symm, lt_of_le_of_ne hyI.2 hyc⟩
  · intro l r hl hlr hr
    exact h.equations.mass_s l l r hlr
      (fun q hq => (htri (chartTriangle_in_subset hl le_rfl hr hq)).1)
  · intro l r hl hlr hr
    exact h.equations.mass_t r l r hlr
      (fun q hq => (htri (chartTriangle_out_subset hl le_rfl hr hq)).1)
  · exact (hy hyI).1
  · exact (hy hyI).2

/-- Both boundary traces are absolutely continuous without an extra trace
hypothesis. Paper `e1a0fd5`, `equations.tex` line 1522. -/
theorem boundary_traces_ac :
    AbsolutelyContinuousOnInterval (fun s => chartPsi S s s) 0 T ∧
      AbsolutelyContinuousOnInterval (fun s => S.m s s) 0 T := by
  obtain ⟨Lψ, hψ⟩ := h.boundary_psi_lipschitz
  obtain ⟨Lm, hm⟩ := h.boundary_mass_lipschitz
  have hψ' : LipschitzOnWith Lψ (fun s => chartPsi S s s) (uIcc 0 T) := by
    simpa [uIcc_of_le h.T_nonneg] using hψ
  have hm' : LipschitzOnWith Lm (fun s => S.m s s) (uIcc 0 T) := by
    simpa [uIcc_of_le h.T_nonneg] using hm
  exact ⟨hψ'.absolutelyContinuousOnInterval, hm'.absolutelyContinuousOnInterval⟩

end NormalizedChartData

end AcExtensionPrinciple

end
