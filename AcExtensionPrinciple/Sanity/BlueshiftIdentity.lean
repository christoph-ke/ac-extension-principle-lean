module

public import AcExtensionPrinciple.Sanity.BlueshiftIdentityCalculus
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Complete incoming blueshift and the axis expansion
Paper `e1a0fd5`, `eq:radius`, `eq:logarithmic-expansions`, `eq:uniform-blueshift`,
`eq:lambda-integrating-factor`. The identity does not assume finite blueshift.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The entire incoming exponent is exactly minus the log of the axis expansion. Only the
regular-center class, signs, and initial gauge are used. Paper `e1a0fd5`, `eq:radius`,
`eq:uniform-blueshift`, `eq:lambda-integrating-factor`. -/
theorem blueshift_identity {ui : ℝ} {S : SSFields} (h : RegularCenterFull ui S)
    (signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1)
    {v : ℝ} (hv : v ∈ Ioo ui 0) :
    (∫⁻ u in Ioo ui v, ENNReal.ofReal (-(S.gamma u v * S.varkappa u v))) =
      ENNReal.ofReal (-Real.log (S.lam v v)) := by
  let b : ℕ → ℝ := fun n => v - (v - ui) / ((n : ℝ) + 2)
  have hb : ∀ n, ui ≤ b n ∧ b n < v := by
    intro n
    have hn : 1 ≤ (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hn0 : 0 < (n : ℝ) + 2 := by positivity
    have hl := div_le_self (sub_nonneg.mpr hv.1.le) hn
    have hr := div_pos (sub_pos.mpr hv.1) hn0
    dsimp [b]
    constructor <;> linarith
  have hmono : Monotone b := by
    intro n m hnm
    have hd := div_le_div_of_nonneg_left (sub_nonneg.mpr hv.1.le)
      (show 0 < (n : ℝ) + 2 by positivity)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hnm 2)
    dsimp [b]
    linarith
  have ht : Tendsto b atTop (𝓝 v) := by
    have hz : Tendsto (fun n : ℕ => (v - ui) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := v - ui)).div_atTop
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [b] using (tendsto_const_nhds (x := v)).sub
      (hz : Tendsto (fun n : ℕ => (v - ui) / ((n : ℝ) + 2)) atTop (𝓝 0))
  have hUnion : (⋃ n, Ioo ui (b n)) = Ioo ui v := by
    ext u
    constructor
    · intro hu
      obtain ⟨n, hn⟩ := mem_iUnion.mp hu
      exact ⟨hn.1, hn.2.trans (hb n).2⟩
    · intro hu
      obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds hu.2)).exists
      exact mem_iUnion.mpr ⟨n, hu.1, hn⟩
  have hdir : Directed (· ⊆ ·) (fun n => Ioo ui (b n)) :=
    fun n m => ⟨max n m, Ioo_subset_Ioo_right (hmono (le_max_left _ _)),
      Ioo_subset_Ioo_right (hmono (le_max_right _ _))⟩
  let J := fun n => ∫⁻ u in Ioo ui (b n),
    ENNReal.ofReal (-(S.gamma u v * S.varkappa u v))
  have hJmono : Monotone J := fun n m hnm =>
    lintegral_mono_set (Ioo_subset_Ioo_right (hmono hnm))
  have hs := inSeg_subset_triangle (ui := ui) le_rfl hv.2 le_rfl hv.2.le
  have hc := StandingFull.continuous_in h.continuous_lam hs
  have hlam : 0 < S.lam v v := blueshift_lam_pos h (p := (v, v))
    ⟨hv.1.le, hv.2, le_rfl, hv.2.le⟩
  have hbt : Tendsto b atTop (𝓝[Icc ui v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => ⟨(hb n).1, (hb n).2.le⟩)⟩
  have hLc : Tendsto (fun u => S.lam u v) (𝓝[Icc ui v] v) (𝓝 (S.lam v v)) :=
    hc v ⟨hv.1.le, le_rfl⟩
  have hlamt := hLc.comp hbt
  have hlog := (Real.continuousAt_log hlam.ne').tendsto.comp hlamt
  have hJt : Tendsto J atTop (𝓝 (ENNReal.ofReal (-Real.log (S.lam v v)))) := by
    have he : J = fun n => ENNReal.ofReal (-Real.log (S.lam (b n) v)) := by
      funext n
      exact blueshift_partial_identity h signs gauge hv (hb n).1 (hb n).2
    rw [he]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hlog.neg
  rw [← hUnion, setLIntegral_iUnion_of_directed _ hdir]
  exact tendsto_nhds_unique (tendsto_atTop_iSup hJmono) hJt

/-- Finite uniform incoming blueshift is equivalent to a uniform positive axis expansion.
No finite-blueshift premise enters the identity used here. Paper `e1a0fd5`,
`eq:uniform-blueshift`, `eq:lambda-kappa-bounds`, `eq:lambda-integrating-factor`. -/
theorem blueshift_finite_iff_axis_lam_lower {ui : ℝ} {S : SSFields}
    (h : RegularCenterFull ui S)
    (signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1) :
    blueshiftSup ui S < ⊤ ↔ ∃ c > 0, ∀ v ∈ Ioo ui 0, c ≤ S.lam v v := by
  constructor
  · intro hf
    refine ⟨Real.exp (-(blueshiftSup ui S).toReal), Real.exp_pos _, ?_⟩
    intro v hv
    have hb : ENNReal.ofReal (-Real.log (S.lam v v)) ≤ blueshiftSup ui S := by
      rw [← blueshift_identity h signs gauge hv]
      exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    have hlog := (ENNReal.ofReal_le_iff_le_toReal hf.ne).mp hb
    have hlam := blueshift_lam_pos h (p := (v, v)) ⟨hv.1.le, hv.2, le_rfl, hv.2.le⟩
    calc
      _ ≤ Real.exp (Real.log (S.lam v v)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hlam
  · rintro ⟨c, hc, hb⟩
    apply lt_of_le_of_lt (b := ENNReal.ofReal (-Real.log c)) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    rw [blueshift_identity h signs gauge hv]
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log hc (hb v hv)))

end AcExtensionPrinciple

end
