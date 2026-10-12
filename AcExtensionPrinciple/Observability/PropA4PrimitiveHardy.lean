module

public import AcExtensionPrinciple.Observability.Hardy
public import AcExtensionPrinciple.Observability.PropA4AmplitudeMass

/-!
# The boundary primitive Hardy estimate in the actual chart

Paper `e1a0fd5`, `eq:observability-primitive-hardy`, lines 1838–1847.
Translation of the proved singular Hardy inequality gives its exact
factor four. The chart radius and expansion bounds then give `4K²E`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Translate the singular Hardy inequality to any initial label. Both
integrability conclusions follow from the given squared boundary data.
Paper `e1a0fd5`, lines 1838–1847. -/
theorem shifted_primitive_hardy {f : ℝ → ℝ} {g s : ℝ} (hgs : g ≤ s)
    (hf : IntervalIntegrable f volume g s)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume g s) :
    IntervalIntegrable (fun t => (∫ z in g..t, f z) ^ 2 / (t - g) ^ 2) volume g s ∧
    (∫ t in g..s, (∫ z in g..t, f z) ^ 2 / (t - g) ^ 2) ≤
      4 * (∫ t in g..s, f t ^ 2) := by
  have hL : 0 ≤ s - g := sub_nonneg.mpr hgs
  have hfi : IntervalIntegrable (fun t => f (g + t)) volume 0 (s - g) := by
    simpa only [sub_self] using hf.comp_add_left g
  have hfi2 : IntervalIntegrable (fun t => f (g + t) ^ 2) volume 0 (s - g) := by
    simpa only [sub_self] using hf2.comp_add_left g
  have hLp : MemLp (fun t => f (g + t)) 2 (volume.restrict (Ioc 0 (s - g))) := by
    apply (memLp_two_iff_integrable_sq ?_).mpr
    · simpa only [uIoc_of_le hL, IntegrableOn] using hfi2.def'
    · simpa only [uIoc_of_le hL, IntegrableOn] using hfi.def'.aestronglyMeasurable
  obtain ⟨hHi, hH⟩ := l2_primitive_hardy hL hLp
  have hHi' : IntervalIntegrable
      (fun ξ => (∫ t in 0..ξ, f (g + t)) ^ 2 / ξ ^ 2) volume 0 (s - g) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mpr hHi
  have he (ξ : ℝ) : (∫ t in 0..ξ, f (g + t)) = ∫ t in g..g + ξ, f t := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left f g (a := 0) (b := ξ)
  have hi : IntervalIntegrable
      (fun t => (∫ z in g..t, f z) ^ 2 / (t - g) ^ 2) volume g s := by
    convert hHi'.comp_add_left (-g) using 1
    · funext t
      rw [he]
      simp only [add_neg_cancel_left]
      congr 1
      ring
    · ring
    · ring
  refine ⟨hi, ?_⟩
  have hleft : (∫ ξ in 0..s - g, (∫ t in 0..ξ, f (g + t)) ^ 2 / ξ ^ 2) =
      ∫ t in g..s, (∫ z in g..t, f z) ^ 2 / (t - g) ^ 2 := by
    calc
      _ = ∫ ξ in 0..s - g, (∫ z in g..g + ξ, f z) ^ 2 / ((g + ξ) - g) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro ξ _
        dsimp only
        rw [he]
        congr 2
        ring
      _ = _ := by
        simpa only [add_zero, show g + (s - g) = s by ring] using
          intervalIntegral.integral_comp_add_left
            (fun t => (∫ z in g..t, f z) ^ 2 / (t - g) ^ 2) g (a := 0) (b := s - g)
  have hright : (∫ ξ in 0..s - g, f (g + ξ) ^ 2) = ∫ t in g..s, f t ^ 2 := by
    simpa only [add_zero, show g + (s - g) = s by ring] using
      intervalIntegral.integral_comp_add_left (fun t => f t ^ 2) g (a := 0) (b := s - g)
  rwa [hleft, hright] at hH

/-- The singular boundary primitive is integrable and obeys Hardy with
factor four on each late outgoing slice. Paper `e1a0fd5`, lines 1838–1847. -/
theorem boundary_primitive_hardy {b T K s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T) (hlate : K * b ≤ s) :
    IntervalIntegrable (fun t => exteriorBoundaryPrimitive h (s, t) ^ 2 /
      (t - h.g s) ^ 2) volume (h.g s) s ∧
    (∫ t in h.g s..s, exteriorBoundaryPrimitive h (s, t) ^ 2 / (t - h.g s) ^ 2) ≤
      4 * chartScalarEnergy S T := by
  have hg0 := axis_label_nonneg h hs hlate
  have hgs := (h.axis_before_boundary s hs).le
  have hsub : uIcc (h.g s) s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hgs, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hg0 hs.2
  obtain ⟨hi, hb⟩ := shifted_primitive_hardy hgs
    (h.boundary_dvpsi_integrable.mono_set hsub)
    (h.boundary_scalar_square_integrable.2.mono_set hsub)
  refine ⟨hi, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (boundary_radial_energy_le h hg0 hgs hs.2) (by norm_num)

/-- The exact radial Hardy bound `4K²E`, expressed with the outgoing
Jacobian in the original chart. All continuity and integrability follow
from the chart; no boundary regularity premise is added. Paper `e1a0fd5`,
`eq:observability-primitive-hardy`, lines 1838–1847. -/
theorem radial_primitive_hardy {b T K P s u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hs : s ∈ Icc 0 T) (hlate : (K + 2) * b ≤ s)
    (hu : h.g s ≤ u) (huv : u ≤ v) (hv : v ≤ s) (hcut : 32 * P ≤ S.r s u) :
    IntervalIntegrable (fun t => exteriorBoundaryPrimitive h (s, t) ^ 2 /
      S.r s t ^ 2 * S.lam s t) volume u v ∧
    (∫ t in u..v, exteriorBoundaryPrimitive h (s, t) ^ 2 /
      S.r s t ^ 2 * S.lam s t) ≤ 4 * K ^ 2 * chartScalarEnergy S T := by
  have hK : 0 < K := by linarith only [h.K_ge_one]
  have hKb : K * b ≤ s := by nlinarith only [hlate, h.b_pos]
  have hmem (t : ℝ) (ht : t ∈ Icc u v) : (s, t) ∈ chartCylinder h.g T :=
    h.out_subset hs hu hv ⟨by simp, ht⟩
  have hrad (t : ℝ) (ht : t ∈ Icc u v) : S.r s u ≤ S.r s t :=
    h.radius_t_mono ht.1 (h.out_subset hs hu (ht.2.trans hv))
  have hext (t : ℝ) (ht : t ∈ Icc u v) : (s, t) ∈ exteriorDomain h P :=
    late_exterior_mem h hP hmass (hmem t ht) (hcut.trans (hrad t ht)) hlate
  have hpos (t : ℝ) (ht : t ∈ Icc u v) : 0 < S.r s t :=
    (exteriorDomain_interior h hP (hext t ht)).2
  have hR : ContinuousOn (S.r s) (Icc u v) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hL : ContinuousOn (S.lam s) (Icc u v) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn hmem
  have hB : ContinuousOn (fun t => exteriorBoundaryPrimitive h (s, t)) (Icc u v) :=
    (exteriorBoundaryPrimitive_continuous h hP hT).comp
      (continuous_const.prodMk continuous_id).continuousOn hext
  have hi : IntervalIntegrable (fun t => exteriorBoundaryPrimitive h (s, t) ^ 2 /
      S.r s t ^ 2 * S.lam s t) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact ((hB.pow 2).div (hR.pow 2)
      (fun t ht => pow_ne_zero _ (hpos t ht).ne')).mul hL
  obtain ⟨hHi, hHb⟩ := boundary_primitive_hardy h hs hKb
  have hsub : uIcc u v ⊆ uIcc (h.g s) s := by
    rw [uIcc_of_le huv, uIcc_of_le (h.axis_before_boundary s hs).le]
    exact Icc_subset_Icc hu hv
  have hHuv := hHi.mono_set hsub
  have hb := intervalIntegral.integral_mono_on huv hi (hHuv.const_mul (K ^ 2)) (by
    intro t ht
    have hq := hmem t ht
    have hr := hpos t ht
    have hgt : h.g s < t := by
      rcases hq.2.2.1.eq_or_lt with he | he
      · have hh := (h.axis_values s hs).1
        rw [he] at hh
        linarith only [hh, hr]
      · exact he
    have htg : 0 < t - h.g s := sub_pos.mpr hgt
    have hlen := (div_le_iff₀ hK).mp (radius_label_bounds h hKb hq).1
    have hsq : (t - h.g s) ^ 2 ≤ K ^ 2 * S.r s t ^ 2 := by
      have hh := pow_le_pow_left₀ htg.le hlen 2
      simpa only [mul_pow, mul_comm] using hh
    have hrec : 1 / S.r s t ^ 2 ≤ K ^ 2 / (t - h.g s) ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos htg)]
      simpa only [one_mul] using hsq
    have hBrec := mul_le_mul_of_nonneg_left hrec
      (sq_nonneg (exteriorBoundaryPrimitive h (s, t)))
    have ht0 := (axis_label_nonneg h hs hKb).trans hq.2.2.1
    have hLam := (h.lam_bounds ht0 ⟨hq, hr⟩).2
    calc
      _ ≤ exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hLam
          (show 0 ≤ exteriorBoundaryPrimitive h (s, t) ^ 2 / S.r s t ^ 2 by positivity)
      _ ≤ K ^ 2 * (exteriorBoundaryPrimitive h (s, t) ^ 2 / (t - h.g s) ^ 2) := by
        convert hBrec using 1 <;> ring)
  have hmono := intervalIntegral.integral_mono_interval hu huv hv
    (Filter.Eventually.of_forall (fun t =>
      show 0 ≤ exteriorBoundaryPrimitive h (s, t) ^ 2 / (t - h.g s) ^ 2 by positivity)) hHi
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_const_mul] at hb
  calc
    _ ≤ K ^ 2 * (∫ t in u..v,
        exteriorBoundaryPrimitive h (s, t) ^ 2 / (t - h.g s) ^ 2) := hb
    _ ≤ K ^ 2 * (4 * chartScalarEnergy S T) :=
      mul_le_mul_of_nonneg_left (hmono.trans hHb) (sq_nonneg K)
    _ = _ := by ring

end PropA4
end AcExtensionPrinciple

end
