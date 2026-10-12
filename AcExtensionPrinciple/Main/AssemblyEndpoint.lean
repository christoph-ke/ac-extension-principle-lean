module

public import AcExtensionPrinciple.Main.AssemblyExistence
public import AcExtensionPrinciple.Solution.PositiveAC

/-!
# Identification at the terminal outgoing endpoint

Paper `e1a0fd5`, `equations.tex` lines 1404–1422. Right continuity gives
initial λ from the complete radial gauge datum. Incoming transport then
identifies λ and ∂ᵥψ at the last outgoing endpoint.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Positive solutions of the same scalar linear integral equation with the
same initial value agree. Paper `e1a0fd5`, lines 1411–1422. Positivity is
supplied by the standing expansion bound and E1 geometry in the application.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem positive_linear_primitive_unique {f g k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, IntervalPrimitive f (fun t => k t * f t) a x)
    (hg : ∀ x ∈ Icc a b, IntervalPrimitive g (fun t => k t * g t) a x)
    (hfp : ∀ x ∈ Icc a b, 0 < f x) (hgp : ∀ x ∈ Icc a b, 0 < g x)
    (hinit : f a = g a) : ∀ x ∈ Icc a b, f x = g x := by
  have hfAC := intervalPrimitive_ac hab hf
  have hgAC := intervalPrimitive_ac hab hg
  have hfL := positive_ac_log hfAC (by simpa only [uIcc_of_le hab] using hfp)
  have hgL := positive_ac_log hgAC (by simpa only [uIcc_of_le hab] using hgp)
  have hd : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun t => Real.log (f t) - Real.log (g t)) 0 x := by
    filter_upwards [intervalPrimitive_ae_hasDerivAt hab hf,
      intervalPrimitive_ae_hasDerivAt hab hg,
      show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],
      show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hfx hgx hxa hxb
    intro hx
    rw [uIcc_of_le hab] at hx
    have hx' : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
    have hfd := (hfx hx').log (ne_of_gt (hfp x hx))
    have hgd := (hgx hx').log (ne_of_gt (hgp x hx))
    convert hfd.sub hgd using 1
    simp [ne_of_gt (hfp x hx), ne_of_gt (hgp x hx)]
  obtain ⟨C, hC⟩ := (hfL.fun_sub hgL).const_of_ae_hasDerivAt_zero hd
  have hC0 : C = 0 := by
    have hh := hC a (by simp)
    rw [hinit, sub_self] at hh
    exact hh.symm
  intro x hx
  have hh := hC x (by simpa only [uIcc_of_le hab] using hx)
  rw [hC0] at hh
  have hh' := congrArg Real.exp (sub_eq_zero.mp hh)
  simpa only [Real.exp_log (hfp x hx), Real.exp_log (hgp x hx)] using hh'

/-- The complete initial radius gauge and right continuity fix λ pointwise
also beyond the selected terminal endpoint. Paper `e1a0fd5`,
`eq:continuation-initial-datum`, lines 1396–1402 and 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem initial_expansion_half {S : SSFields}
    (h : ChrBVCore smallBVDomain (Ici 0) S)
    (hr : ∀ v > 0, S.r 0 v = v / 2) {b : ℝ} (hb : 0 < b) : S.lam 0 b = 1 / 2 := by
  have hs (x : ℝ) (hx : x ∈ Icc b (b + 1)) : outSeg 0 b x ⊆ smallBVDomain := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu0 : u = 0 := hu
    subst u
    exact ⟨le_rfl, hb.trans_le hv.1⟩
  have hd := intervalPrimitive_ae_hasDerivAt (show b ≤ b + 1 by linarith)
    (fun x hx => h.radius_out 0 b x hx.1 (hs x hx))
  apply right_continuous_eq_of_ae_eq (show b < b + 1 by linarith)
    ((h.lam_right_cont (0, b) ⟨le_rfl, hb⟩).mono
      (fun x hx => ⟨hx.1, le_rfl, hb.trans_le hx.1⟩)) continuousWithinAt_const
  filter_upwards [hd] with x hx
  intro hxI
  have he : S.r 0 =ᶠ[𝓝 x] fun v => v / 2 := by
    filter_upwards [Ioi_mem_nhds (hb.trans hxI.1)] with v hv
    exact hr v hv
  have hdx := ((hasDerivAt_id x).div_const 2).congr_of_eventuallyEq he
  exact (hx hxI).unique hdx

/-- The transverse outgoing fields agree along a closed incoming segment
when its primitives and incoming expansion agree, and the initial outgoing
fields agree. Paper `e1a0fd5`, lines 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem terminal_outgoing_transport {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S₁ S₂ : SSFields} {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ D)
    (h₁ : ChrBVCore D A S₁) (h₂ : ChrBVCore D A S₂)
    (he : ∀ u ∈ Icc a b, S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
      S₁.m u v = S₂.m u v ∧ S₁.nu u v = S₂.nu u v)
    (hpos₁ : ∀ u ∈ Icc a b, 0 < S₁.lam u v)
    (hpos₂ : ∀ u ∈ Icc a b, 0 < S₂.lam u v)
    (hinit : S₁.lam a v = S₂.lam a v ∧ S₁.dvpsi a v = S₂.dvpsi a v) :
    ∀ u ∈ Icc a b, S₁.lam u v = S₂.lam u v ∧ S₁.dvpsi u v = S₂.dvpsi u v := by
  let k := fun u => S₁.mu u v * S₁.nu u v / ((1 - S₁.mu u v) * S₁.r u v)
  have hc₁ (u : ℝ) : S₁.radiusCoeff u v = k u * S₁.lam u v := by
    dsimp [k, SSFields.radiusCoeff]
    ring
  have hc₂ (u : ℝ) (hu : u ∈ Icc a b) :
      S₂.radiusCoeff u v = k u * S₂.lam u v := by
    obtain ⟨hr, _, hm, hn⟩ := he u hu
    dsimp [k, SSFields.radiusCoeff, SSFields.mu]
    rw [← hr, ← hm, ← hn]
    ring
  have hs' (x : ℝ) (hx : x ∈ Icc a b) : inSeg v a x ⊆ D :=
    (prod_mono_left (Icc_subset_Icc le_rfl hx.2)).trans hs
  have hl := positive_linear_primitive_unique hab
    (fun x hx => (h₁.lam_in v a x hx.1 (hs' x hx)).congr
      (fun _ _ => rfl) (fun u hu => hc₁ u))
    (fun x hx => (h₂.lam_in v a x hx.1 (hs' x hx)).congr
      (fun _ _ => rfl) (fun u hu => hc₂ u (by
        rw [uIcc_of_le hx.1] at hu
        exact ⟨hu.1, hu.2.trans hx.2⟩))) hpos₁ hpos₂ hinit.1
  intro u hu
  refine ⟨hl u hu, ?_⟩
  have hd₁ := (h₁.dvpsi_in v a u hu.1 (hs' u hu)).2
  have hd₂ := (h₂.dvpsi_in v a u hu.1 (hs' u hu)).2
  have hi : (∫ x in a..u, S₁.radiusCoeff x v * S₁.phi x v) =
      ∫ x in a..u, S₂.radiusCoeff x v * S₂.phi x v := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hu.1] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans hu.2⟩
    dsimp only
    rw [hc₁, hc₂ x hx', hl x hx', (he x hx').2.1]
  dsimp only at hd₁ hd₂
  rw [hi, hinit.2] at hd₁
  linarith

/-- Incoming transport identifies the final outgoing endpoint even though
that endpoint has no common right outgoing interval. Paper `e1a0fd5`,
lines 1411–1422. The initial values follow from the complete E1 datum and
the selected cone normalization.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem late_triangle_outgoing_endpoint_agree {S₁ S₂ : SSFields} {b : ℝ}
    (h₁ : ∀ a ∈ Ico 0 b,
      ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (hgeom : SmallBVGeometry S₂)
    (he : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ b →
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
        S₁.m p.1 p.2 = S₂.m p.1 p.2)
    (hinit : S₁.lam 0 b = S₂.lam 0 b ∧ S₁.dvpsi 0 b = S₂.dvpsi 0 b) :
    ∀ u ∈ Ico 0 b, S₁.lam u b = S₂.lam u b ∧ S₁.dvpsi u b = S₂.dvpsi u b := by
  have hin := (late_triangle_derivatives_agree h₁ h₂
    (fun p hu huv hv => ⟨(he p hu huv hv).1, (he p hu huv hv).2.1⟩)).2
  intro u hu
  have hb : 0 < b := hu.1.trans_lt hu.2
  have hs : inSeg b 0 u ⊆ pastSet u b := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hyv : y = b := hy
    subst y
    exact ⟨hx, hx.2.trans_lt hu.2, le_rfl⟩
  obtain ⟨c, N, hc, hbound⟩ := (h₁ u hu).2.expansion_bounds
  have hp₁ : ∀ x ∈ Icc 0 u, 0 < S₁.lam x b := by
    intro x hx
    exact hc.trans_le (hbound (x, b) ⟨mem_univ _, hs ⟨hx, by simp⟩⟩).1
  have hp₂ : ∀ x ∈ Icc 0 u, 0 < S₂.lam x b := by
    intro x hx
    have h := (hgeom (x, b) ⟨hx.1, hx.2.trans_lt hu.2⟩).1
    linarith
  exact terminal_outgoing_transport hu.1 hs (h₁ u hu).1 (h₂.on_pastSet u b).1
    (fun x hx => ⟨(he (x, b) hx.1 (hx.2.trans_lt hu.2) le_rfl).1,
      (he (x, b) hx.1 (hx.2.trans_lt hu.2) le_rfl).2.1,
      (he (x, b) hx.1 (hx.2.trans_lt hu.2) le_rfl).2.2,
      (hin b ⟨hb, le_rfl⟩ x ⟨hx.1, hx.2.trans_lt hu.2⟩).1⟩) hp₁ hp₂ hinit u
    ⟨hu.1, le_rfl⟩

end AcExtensionPrinciple

end
