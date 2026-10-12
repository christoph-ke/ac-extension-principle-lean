module

public import AcExtensionPrinciple.Main.AssemblyEndpoint
public import AcExtensionPrinciple.Main.AssemblyPatch
public import AcExtensionPrinciple.Main.AssemblyPrimary

/-!
# Complete seven-field identification with the selected development

Paper `e1a0fd5`, `equations.tex` lines 1404–1422. The complete radial datum
fixes the terminal outgoing initial values. Transport and right continuity
therefore identify every carried representative throughout the overlap.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Primitive and initial outgoing agreement identify every representative
on the closed late triangle away from Γ. Paper `e1a0fd5`, lines 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem late_triangle_all_fields_agree {S₁ S₂ : SSFields} {b : ℝ}
    (h₁ : ∀ a ∈ Ico 0 b,
      ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (hgeom : SmallBVGeometry S₂)
    (he : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ b →
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
        S₁.m p.1 p.2 = S₂.m p.1 p.2)
    (hinit : S₁.lam 0 b = S₂.lam 0 b ∧ S₁.dvpsi 0 b = S₂.dvpsi 0 b) :
    FieldsAgreeOn {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b} S₁ S₂ := by
  obtain ⟨hout, hin⟩ := late_triangle_derivatives_agree h₁ h₂
    (fun p hu huv hv => ⟨(he p hu huv hv).1, (he p hu huv hv).2.1⟩)
  have hend := late_triangle_outgoing_endpoint_agree h₁ h₂ hgeom he hinit
  intro p hp
  have hpu : p.1 ∈ Ico 0 b := ⟨hp.1, hp.2.1.trans_le hp.2.2⟩
  have ho : S₁.lam p.1 p.2 = S₂.lam p.1 p.2 ∧
      S₁.dvpsi p.1 p.2 = S₂.dvpsi p.1 p.2 := by
    rcases lt_or_eq_of_le hp.2.2 with hv | rfl
    · exact hout p.1 hpu p.2 ⟨hp.2.1, hv⟩
    · exact hend p.1 hpu
  have hi := hin p.2 ⟨hp.1.trans_lt hp.2.1, hp.2.2⟩ p.1 ⟨hp.1, hp.2.1⟩
  have hh := he p hp.1 hp.2.1 hp.2.2
  change FieldValues.mk _ _ _ _ _ _ _ = FieldValues.mk _ _ _ _ _ _ _
  congr 1
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2
  · exact ho.1
  · exact hi.1
  · exact ho.2
  · exact hi.2

/-- The selected cone normalization fixes its last outgoing expansion.
Paper `e1a0fd5`, `eq:continuation-initial-datum`, lines 1396–1402 and 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem StandingFull.selected_initial_expansion {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hv : T ū = 0) :
    (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))).lam 0 (T 0) =
      1 / 2 := by
  have hU0 : T.symm 0 = ū := by rw [← hv, T.symm_apply_apply]
  have hl : S.lam ū 0 ≠ 0 := ne_of_gt
    (h.lam_pos (p := (ū, 0)) ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩)
  simp only [SSFields.pullback, inverseJacobian, T.symm_apply_apply, hU0,
    selectedJacobian, radialChartDerivative_on_interval ⟨hū.2.le, le_rfl⟩]
  field_simp

/-- Inverse-chart field identification gives original-chart identification
with the development pullback. Paper `e1a0fd5`, lines 1411–1422. -/
theorem inverse_fields_agree_original {S Sdev : SSFields} {T : ℝ ≃o ℝ}
    {dT : ℝ → ℝ} {u v : ℝ} (hu : 0 < dT u) (hv : 0 < dT v)
    (he : (S.pullback T.symm (inverseJacobian T dT)).values (T u) (T v) =
      Sdev.values (T u) (T v)) : FieldsAgreeAt S (Sdev.pullback T dT) (u, v) := by
  have hr := congrArg FieldValues.r he
  have hphi := congrArg FieldValues.phi he
  have hm := congrArg FieldValues.m he
  have hl := congrArg FieldValues.lam he
  have hn := congrArg FieldValues.nu he
  have hd := congrArg FieldValues.dvpsi he
  have hz := congrArg FieldValues.dupsi he
  simp only [SSFields.values, SSFields.pullback, inverseJacobian,
    T.symm_apply_apply] at hr hphi hm hl hn hd hz
  refine ⟨hr, hphi, hm, ?_, ?_, ?_, ?_⟩
  · exact (div_eq_iff (ne_of_gt hv)).mp (by simpa only [div_eq_mul_inv] using hl)
  · exact (div_eq_iff (ne_of_gt hu)).mp (by simpa only [div_eq_mul_inv] using hn)
  · exact (div_eq_iff (ne_of_gt hv)).mp (by simpa only [div_eq_mul_inv] using hd)
  · exact (div_eq_iff (ne_of_gt hu)).mp (by simpa only [div_eq_mul_inv] using hz)

/-- The chart and exact E1 datum discharge both terminal initial values.
Every field agrees on the entire original late triangle, including v = 0.
Paper `e1a0fd5`, `eq:continuation-initial-datum`, lines 1404–1422. -/
theorem StandingFull.selected_full_agreement {ui ū : ℝ} {S Sdev : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) (hE2 : BVUniqueness)
    {T : ℝ ≃o ℝ} (hv : T ū = 0) (ht : T 0 = 2 * S.r ū 0)
    (hd : ∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x)
    (hc : Continuous (selectedJacobian S ū))
    (hp : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x)
    (hBV : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0))
    (hr : ∀ t ∈ Icc ū 0, T t = 2 * S.r ū t)
    (hdev : ChristodoulouBV smallBVDomain (Ici 0) Sdev)
    (hgeom : SmallBVGeometry Sdev)
    (hdata : ∀ v > 0, Sdev.r 0 v = v / 2 ∧
      Sdev.dvpsi 0 v = selectedInitialDatum S ū T v) :
    ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      FieldsAgreeAt S (Sdev.pullback T (selectedJacobian S ū)) (u, v) := by
  have hb : 0 < 2 * S.r ū 0 := mul_pos (by norm_num)
    (h.r_pos (u := ū) (v := 0) ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩ hū.2)
  have hsource := h.chr_in_selected_chart hū hv ht hd hc hp hBV
  have hinit := h.selected_initial_data hū hr
  have hinitdev : ∀ v ∈ Ioc 0 (2 * S.r ū 0),
      Sdev.r 0 v = v / 2 ∧ Sdev.dvpsi 0 v =
        1 / 2 * (S.dvpsi ū (T.symm v) / S.lam ū (T.symm v)) := by
    intro v hvi
    refine ⟨(hdata v hvi.1).1, ?_⟩
    rw [(hdata v hvi.1).2]
    exact selectedInitialDatum_on_segment S ū T (by simpa only [ht] using hvi.2)
  have he := uniqueness_on_late_triangle_of_bv hb hE2 hsource hdev
    (fun v hv => (hinit v hv).1) (fun v hv => (hinitdev v hv).1)
    (fun v hv => (hinit v hv).2.trans (hinitdev v hv).2.symm)
  have hterminal :
      (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))).lam 0
          (2 * S.r ū 0) = Sdev.lam 0 (2 * S.r ū 0) ∧
        (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))).dvpsi 0
          (2 * S.r ū 0) = Sdev.dvpsi 0 (2 * S.r ū 0) := by
    constructor
    · rw [← ht, h.selected_initial_expansion hū hv]
      exact (initial_expansion_half hdev.1 (fun v hv => (hdata v hv).1)
        (by simpa only [ht] using hb)).symm
    · exact (hinit _ ⟨hb, le_rfl⟩).2.trans (hinitdev _ ⟨hb, le_rfl⟩).2.symm
  have hall := late_triangle_all_fields_agree hsource hdev hgeom he hterminal
  obtain ⟨c, hc0, hcp⟩ := hp
  intro u v hu huv hv0
  apply inverse_fields_agree_original (hc0.trans_le (hcp u)) (hc0.trans_le (hcp v))
  exact hall (T u, T v) ⟨by simpa only [hv] using T.monotone hu,
    T.strictMono huv, by simpa only [ht] using T.monotone hv0⟩

end AcExtensionPrinciple

end
