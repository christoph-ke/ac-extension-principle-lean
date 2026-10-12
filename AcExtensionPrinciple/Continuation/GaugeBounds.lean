module

public import AcExtensionPrinciple.Continuation.RawBounds
public import AcExtensionPrinciple.Continuation.GaugeAxis

/-!
# Uniform BV bounds after weighting by the inverse Jacobian

Paper `e1a0fd5`, `equations.tex` lines 1390–1411. The component premises are uniform raw-field
bounds and variations from the proper original triangle, and positive BV bounds for the inverse
Jacobian.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped ENNReal

/-- Uniform raw-field variations on every whole ray portion. Paper `e1a0fd5`,
lines 220–275 and 1411, component premises for gauge transport. -/
structure RawRayVariation (D : Set (ℝ × ℝ)) (S : SSFields) (C : ℝ≥0∞) : Prop where
  outgoing : ∀ u, eVariationOn (S.lam u) {v | (u, v) ∈ D} ≤ C ∧
    eVariationOn (S.phi u) {v | (u, v) ∈ D} ≤ C ∧
    eVariationOn (S.dvpsi u) {v | (u, v) ∈ D} ≤ C
  incoming : ∀ v, eVariationOn (fun u => S.nu u v) {u | (u, v) ∈ D} ≤ C ∧
    eVariationOn (fun u => S.phi u v) {u | (u, v) ∈ D} ≤ C ∧
    eVariationOn (fun u => S.dupsi u v) {u | (u, v) ∈ D} ≤ C

/-- Q6 provides raw-field variation bounds on the whole proper triangle.
Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem StandingFull.proper_triangle_raw_variation {ui ū c : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ui ≤ ū) (hc : c < 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ RawRayVariation (properOriginalTriangle ū c) S C := by
  let K := properOriginalTriangle ū c
  have hK := isCompact_properOriginalTriangle ū c
  have hKD := properOriginalTriangle_subset hū hc
  rcases h.regularCenter.localBV.expansion_variation K hK hKD with ⟨Cl, hl, hn⟩
  rcases h.regularCenter.localBV.scalar_ac_variation K hK hKD with ⟨Cp, hpout, hpin⟩
  rcases h.regularCenter.localBV.psi_variation K hK hKD with ⟨Cd, hdout, hdin⟩
  let C := ENNReal.ofReal Cl + ENNReal.ofReal Cp + ENNReal.ofReal Cd
  have hlC : ENNReal.ofReal Cl ≤ C := le_self_add.trans le_self_add
  have hpC : ENNReal.ofReal Cp ≤ C := le_add_self.trans le_self_add
  have hdC : ENNReal.ofReal Cd ≤ C := le_add_self
  refine ⟨C, by simp [C], ?_, ?_⟩
  · intro u
    exact ⟨(proper_triangle_out_variation hl u).trans hlC,
      (proper_triangle_out_variation (fun u a b hab hs => (hpout u a b hab hs).2) u).trans hpC,
      (proper_triangle_out_variation hdout u).trans hdC⟩
  · intro v
    exact ⟨(proper_triangle_in_variation hn v).trans hlC,
      (proper_triangle_in_variation (fun v a b hab hs => (hpin v a b hab hs).2) v).trans hpC,
      (proper_triangle_in_variation hdin v).trans hdC⟩

/-- A raw field's variation after composition and Jacobian multiplication. Paper `e1a0fd5`, lines
1390–1411, product estimate for class membership. -/
theorem weighted_variation_bound {f U dU : ℝ → ℝ} {s t I : Set ℝ}
    {M J : ℝ} {C F : ℝ≥0∞} (hU : Monotone U) (hs : MapsTo U s t) (hsI : s ⊆ I)
    (hf : eVariationOn f t ≤ C) (hF : eVariationOn dU I ≤ F)
    (hM : ∀ x ∈ t, |f x| ≤ M) (hJ : ∀ x ∈ I, |dU x| ≤ J) :
    eVariationOn (fun x => f (U x) * dU x) s ≤ ENNReal.ofReal M * F + ENNReal.ofReal J * C := by
  exact (variation_mul_le _ _ _ (fun x hx => hM _ (hs hx)) (fun x hx => hJ x (hsI hx))).trans
    (add_le_add (mul_le_mul_right ((eVariationOn.mono _ hsI).trans hF) _)
      (mul_le_mul_right (variation_pullback_le hU hs |>.trans hf) _))

/-- The weighted fields satisfy Christodoulou's uniform bounds. Paper `e1a0fd5`, lines 1390–1411.
Raw bounds/TV come from the original compact triangle, while the Jacobian premises come from the
inverse of the selected cone's positive BV expansion. -/
theorem chr_pullback_bounds_of_raw {D E : Set (ℝ × ℝ)} {I : Set ℝ} {S : SSFields}
    {U dU : ℝ → ℝ} {cl cd M J : ℝ} {C F : ℝ≥0∞}
    (hcl : 0 < cl) (hcd : 0 < cd) (hM0 : 0 ≤ M) (_hJ0 : 0 ≤ J)
    (hC : C ≠ ⊤) (hF : F ≠ ⊤) (hU : Monotone U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D) (hI : ∀ p ∈ E, p.1 ∈ I ∧ p.2 ∈ I)
    (hl : ∀ p ∈ D, cl ≤ S.lam p.1 p.2)
    (hraw : ∀ p ∈ D, |S.lam p.1 p.2| ≤ M ∧ |S.nu p.1 p.2| ≤ M ∧
      |S.phi p.1 p.2| ≤ M ∧ |S.dvpsi p.1 p.2| ≤ M ∧ |S.dupsi p.1 p.2| ≤ M)
    (hv : RawRayVariation D S C)
    (hd : ∀ x ∈ I, cd ≤ dU x ∧ |dU x| ≤ J)
    (hJ : eVariationOn dU I ≤ F) : ChrBVBoundsOn univ E (S.pullback U dU) := by
  let V := C + (ENNReal.ofReal M * F + ENNReal.ofReal J * C)
  have hV : V ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC, ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC⟩⟩
  have hCV : C ≤ V := le_self_add
  have hWV : ENNReal.ofReal M * F + ENNReal.ofReal J * C ≤ V := le_add_self
  have houtI (u : ℝ) : {v | (u, v) ∈ E} ⊆ I := fun v hv => (hI (u, v) hv).2
  have hinI (v : ℝ) : {u | (u, v) ∈ E} ⊆ I := fun u hu => (hI (u, v) hu).1
  have houtmap (u : ℝ) : MapsTo U {v | (u, v) ∈ E} {v | (U u, v) ∈ D} :=
    fun v hv => hmap (u, v) hv
  have hinmap (v : ℝ) : MapsTo U {u | (u, v) ∈ E} {u | (u, U v) ∈ D} :=
    fun u hu => hmap (u, v) hu
  have hamp (p : ℝ × ℝ) (hp : p ∈ E) :
      |(S.pullback U dU).lam p.1 p.2| ≤ M * J ∧
      |(S.pullback U dU).nu p.1 p.2| ≤ M * J ∧
      |(S.pullback U dU).phi p.1 p.2| ≤ M := by
    have hs := hraw _ (hmap p hp)
    simp only [SSFields.pullback, abs_mul]
    exact ⟨mul_le_mul hs.1 (hd _ (hI p hp).2).2 (abs_nonneg _) hM0,
      mul_le_mul hs.2.1 (hd _ (hI p hp).1).2 (abs_nonneg _) hM0, hs.2.2.1⟩
  apply chr_bounds_of_components (mul_pos hcl hcd) hV (G := M * J) (P := M)
  · intro p hp
    have hs := hl _ (hmap p hp.2)
    have hj := hd _ (hI p hp.2).2
    refine ⟨?_, (neg_le_abs _).trans (hamp p hp.2).2.1⟩
    change cl * cd ≤ S.lam (U p.1) (U p.2) * dU p.2
    exact mul_le_mul hs hj.1 hcd.le (hcl.le.trans hs)
  · exact fun p hp => hamp p hp.2
  · intro u
    simp only [univ_inter, SSFields.pullback]
    refine ⟨?_, (variation_pullback_le hU (houtmap u)).trans
      ((hv.outgoing (U u)).2.1.trans hCV), ?_⟩
    · exact (weighted_variation_bound hU (houtmap u) (houtI u) (hv.outgoing (U u)).1 hJ
        (fun v hv => (hraw (U u, v) hv).1) (fun x hx => (hd x hx).2)).trans hWV
    · exact (weighted_variation_bound hU (houtmap u) (houtI u) (hv.outgoing (U u)).2.2 hJ
        (fun v hv => (hraw (U u, v) hv).2.2.2.1) (fun x hx => (hd x hx).2)).trans hWV
  · intro v
    simp only [univ_inter, SSFields.pullback]
    refine ⟨?_, (variation_pullback_le (f := fun u => S.phi u (U v)) hU (hinmap v)).trans
      ((hv.incoming (U v)).2.1.trans hCV), ?_⟩
    · exact (weighted_variation_bound (f := fun u => S.nu u (U v))
        hU (hinmap v) (hinI v) (hv.incoming (U v)).1 hJ
        (fun u hu => (hraw (u, U v) hu).2.1) (fun x hx => (hd x hx).2)).trans hWV
    · exact (weighted_variation_bound (f := fun u => S.dupsi u (U v))
        hU (hinmap v) (hinI v) (hv.incoming (U v)).2.2 hJ
        (fun u hu => (hraw (u, U v) hu).2.2.2.2) (fun x hx => (hd x hx).2)).trans hWV

end AcExtensionPrinciple

end
