module

public import AcExtensionPrinciple.Renormalized.ClassTransport
public import AcExtensionPrinciple.Renormalized.ClassHardy
public import AcExtensionPrinciple.Decay.ScalarComparison

/-!
# Damping from the axis and the renormalized cone L¹ estimate

Paper `e1a0fd5`, `equations.tex` lines 1071–1078.
The scalar bound is the Lemma 2.1 conclusion; the two variation
majorants in the L¹ helper are the AC derivative bound and the cone Hardy bound.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Damping comparison starting at a regular-axis trace, without imposing a
value of the representative at the axis. Paper `e1a0fd5`, lines 1071–1073. -/
theorem scalar_damping_bound_from_axis {Q phi k : ℝ → ℝ} {u v L M : ℝ}
    (huv : u < v) (htrace : Tendsto Q (𝓝[Ioo u v] u) (𝓝 L)) (hL : |L| ≤ M)
    (hQ : ∀ a ∈ Ioo u v, AbsolutelyContinuousOnInterval Q a v)
    (hphi : ∀ x ∈ Icc u v, |phi x| ≤ M)
    (hk : ∀ᵐ x, x ∈ Ioo u v → 0 ≤ k x)
    (hode : ∀ a ∈ Ioo u v, ∀ᵐ x, x ∈ Ioo a v →
      deriv Q x = -k x * (Q x - phi x)) :
    |Q v| ≤ M := by
  have hn : (𝓝[Ioo u v] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (by rw [closure_Ioo huv.ne]; exact left_mem_Icc.mpr huv.le)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsmall := htrace.abs.eventually (gt_mem_nhds (hL.trans_lt (lt_add_of_pos_right M hε)))
  obtain ⟨a, ha, hQa⟩ := (eventually_mem_nhdsWithin.and hsmall).exists
  have hb : |Q v - 0| ≤ M + ε := by
    apply incoming_scalar_comparison_bound (L := 0) (phi := phi) (k := k) ha.2.le (hQ a ha)
      (by simpa using hQa.le)
    · intro x hx
      simpa using (hphi x ⟨ha.1.le.trans hx.1, hx.2⟩).trans (le_add_of_nonneg_right hε.le)
    · filter_upwards [hk] with x hx hxI
      exact hx ⟨ha.1.trans hxI.1, hxI.2⟩
    · exact hode a ha
  simpa only [sub_zero] using hb

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The normalized incoming scalar datum is AC on off-axis outgoing segments.
Paper `e1a0fd5`, `eq:incoming-normalized-damping`, lines 974–980 and 1071. -/
theorem incoming_normalized_ac_out {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    AbsolutelyContinuousOnInterval (fun v => S.dupsi u v / S.nu u v) a b := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hd := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (hs x hx))
  have hn := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (hs x hx))
  have hi := (positive_ac_inv hn.fun_neg (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact neg_pos.mpr (h.nu_neg (p := (u, x))
      ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩))).fun_neg
  simpa only [neg_inv, neg_neg, div_eq_mul_inv] using hd.fun_mul hi

/-- The damping equation follows directly from the two class integral
equations for `ν` and `∂ᵤψ`. Paper `e1a0fd5`, lines 974–980 and 1071. -/
theorem incoming_normalized_damping_ae {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun v => S.dupsi u v / S.nu u v)
      (-(S.kappa u x * S.varkappa u x) * (S.dupsi u x / S.nu u x - S.phi u x)) x := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (hs x hx))
  have hn := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (hs x hx))
  filter_upwards [hd, hn] with x hdx hnx hx
  have hp : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans hx.1).le, hx.2.le.trans hb0⟩
  convert (hdx hx).div (hnx hx) (ne_of_lt (h.nu_neg hp)) using 1
  rw [S.radiusCoeff_eq u x]
  field_simp [ne_of_lt (h.nu_neg hp)]
  ring

/-- Uniform incoming normalized scalar amplitude from damping and the
regular-axis trace. Paper `e1a0fd5`, lines 1071–1073.
The sole uniform-bound input is the scalar part of Lemma 2.1. -/
theorem incoming_amplitude_bound_of_scalar_bound {M : ℝ}
    (hphi : ∀ p ∈ pastTriangle ui, |S.phi p.1 p.2| ≤ M) :
    ∀ p ∈ pastTriangle ui,
      |S.r p.1 p.2 / S.nu p.1 p.2 * S.duphi p.1 p.2| ≤ 2 * M := by
  rintro ⟨u, v⟩ hp
  change ui ≤ u ∧ u < 0 ∧ u ≤ v ∧ v ≤ 0 at hp
  change |S.r u v / S.nu u v * S.duphi u v| ≤ 2 * M
  have hM : 0 ≤ M := (abs_nonneg _).trans (hphi (u, v) hp)
  rcases hp.2.2.1.eq_or_lt with he | huv
  · subst v
    simp only [(h.regularCenter.localBV.axis_values u hp).1, zero_div, zero_mul, abs_zero]
    linarith
  have htrace : Tendsto (fun x => S.dupsi u x / S.nu u x) (𝓝[Ioo u v] u)
      (𝓝 (S.phi u u)) := by
    have ht : Tendsto (fun x : ℝ => (u, x)) (𝓝[Ioo u v] u)
        (𝓝[pastTriangle ui \ axis ui] (u, u)) := by
      apply tendsto_nhdsWithin_iff.mpr
      have hc : Continuous (fun x : ℝ => (u, x)) := continuous_const.prodMk continuous_id
      refine ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      exact ⟨⟨hp.1, hp.2.1, hx.1.le, hx.2.le.trans hp.2.2.2⟩,
        fun he => (ne_of_lt hx.1) he.2.2.symm⟩
    exact (h.regularCenter.axis_dupsi_trace u ⟨hp.1, hp.2.1, rfl⟩).comp ht
  have hQ : |S.dupsi u v / S.nu u v| ≤ M := by
    apply scalar_damping_bound_from_axis (k := fun x => S.kappa u x * S.varkappa u x)
      huv htrace (hphi (u, u) ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩)
    · intro a ha
      exact h.incoming_normalized_ac_out ha.2.le hp.1 hp.2.1 ha.1 hp.2.2.2
    · intro x hx
      exact hphi (u, x) ⟨hp.1, hp.2.1, hx.1, hx.2.trans hp.2.2.2⟩
    · exact ae_of_all _ (fun x hx => mul_nonneg
        (h.kappa_pos (p := (u, x)) ⟨hp.1, hp.2.1, hx.1.le, hx.2.le.trans hp.2.2.2⟩).le
        (div_nonneg (h.mu_bounds (p := (u, x))
          ⟨hp.1, hp.2.1, hx.1.le, hx.2.le.trans hp.2.2.2⟩).1
          (h.r_pos (u := u) (v := x) ⟨hp.1, hp.2.1, hx.1.le, hx.2.le.trans hp.2.2.2⟩ hx.1).le))
    · intro a ha
      filter_upwards [h.incoming_normalized_damping_ae ha.2.le hp.1 hp.2.1 ha.1 hp.2.2.2]
        with x hx hxI
      exact (hx hxI).deriv
  rw [h.incoming_amplitude_eq hp huv]
  exact (abs_sub _ _).trans (by linarith [hphi (u, v) hp])

end StandingFull

end AcExtensionPrinciple

end
