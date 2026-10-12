module

public import AcExtensionPrinciple.Observability.InnerChartBounds
public import AcExtensionPrinciple.Cylinder.Smooth

/-!
# The smaller-radius cylinder is a regular level curve

Paper `e1a0fd5`, `equations.tex` lines 1877–1887 and 1901–1907.
Existence, continuity, and its tangent follow from the outer radius
primitives and continuous expansions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- The level curve has a continuous label, including the initial and
terminal slices. Compactness and uniqueness give the inverse continuity.
Paper `e1a0fd5`, lines 1877–1887 and 1901–1907. -/
theorem innerLabel_continuous {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ContinuousOn (h.innerLabel a ha hab) (Icc 0 T) := by
  classical
  let D := chartCylinder h.g T
  obtain ⟨R, hR⟩ := (⟨_, h.continuous_r.domRestrict⟩ : C(D, ℝ)).exists_restrict_eq
    h.inner_source_compact.isClosed
  have hReq (p : ℝ × ℝ) (hp : p ∈ D) : R p = S.r p.1 p.2 :=
    congrArg (fun G : C(D, ℝ) => G ⟨p, hp⟩) hR
  let C := D ∩ R ⁻¹' {a}
  have hC : IsCompact C := h.inner_source_compact.inter_right
    (isClosed_singleton.preimage R.continuous)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → ℝ := fun p => p.val.1
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  have hfi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply Prod.ext he
    have hp : S.r p.val.1 p.val.2 = a :=
      (hReq p.val p.property.1).symm.trans p.property.2
    have hq : S.r q.val.1 q.val.2 = a :=
      (hReq q.val q.property.1).symm.trans q.property.2
    have hs : p.val.1 ∈ Icc 0 T := ⟨p.property.1.1, p.property.1.2.1⟩
    have hqI : q.val.2 ∈ Icc (h.g p.val.1) p.val.1 := by
      change p.val.1 = q.val.1 at he
      rw [he]
      exact q.property.1.2.2
    apply (h.inner_radius_strictMono hs).injOn p.property.1.2.2 hqI
    change p.val.1 = q.val.1 at he
    rw [he] at hp ⊢
    exact hp.trans hq.symm
  let k : Icc (0 : ℝ) T → C := fun x =>
    ⟨(x.val, h.innerLabel a ha hab x.val),
      ⟨⟨x.property.1, x.property.2,
        (h.innerLabel_spec ha hab x.property).1.1.le,
        (h.innerLabel_spec ha hab x.property).1.2.le⟩,
        (hReq _ ⟨x.property.1, x.property.2,
          (h.innerLabel_spec ha hab x.property).1.1.le,
          (h.innerLabel_spec ha hab x.property).1.2.le⟩).trans
            (h.innerLabel_spec ha hab x.property).2⟩⟩
  have hk : Continuous k := (hf.isClosedEmbedding hfi).isEmbedding.isInducing.continuous_iff.mpr
    (show Continuous (f ∘ k) from continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hk))

/-- Interior off-axis points of the outer normalized cylinder. Paper
`e1a0fd5`, lines 1460–1473 and 1877–1887. -/
@[expose] def innerOpen : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < T ∧ h.g p.1 < p.2 ∧ p.2 < p.1}

/-- This local derivative domain is open. Paper `e1a0fd5`,
lines 1460–1473 and 1877–1887. -/
theorem innerOpen_isOpen : IsOpen h.innerOpen :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt (h.continuous_g.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd continuous_fst)))

/-- Interior points lie in the full old chart. Paper `e1a0fd5`,
lines 1460–1473 and 1877–1887. -/
theorem innerOpen_subset : h.innerOpen ⊆ chartCylinder h.g T :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

/-- The outgoing radius partial is the positive expansion. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1484–1492 and 1887. -/
theorem inner_radius_hasDerivAt_out {s t : ℝ} (hp : (s, t) ∈ h.innerOpen) :
    HasDerivAt (S.r s) (S.lam s t) t := by
  have hs : s ∈ Icc 0 T := ⟨hp.1.le, hp.2.1.le⟩
  apply intervalPrimitive_hasDerivAt ⟨hp.2.2.1, hp.2.2.2⟩
    (h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => h.out_subset hs le_rfl le_rfl ⟨by simp, hz⟩))
  intro z hz
  exact h.equations.radius_t s (h.g s) z hz.1 (h.out_subset hs le_rfl hz.2)

/-- The incoming radius partial is the negative expansion. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1484–1492 and 1887. -/
theorem inner_radius_hasDerivAt_in {s t : ℝ} (hp : (s, t) ∈ h.innerOpen) :
    HasDerivAt (fun x => S.r x t) (S.nu s t) s := by
  have hn : ∀ᶠ x in 𝓝 s, (x, t) ∈ h.innerOpen :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually
      (h.innerOpen_isOpen.mem_nhds hp)
  obtain ⟨l, r, hs, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let d := (s + r) / 2
  let e := (l + s) / 2
  have hl : l < e := by dsimp [e]; linarith [hs.1]
  have he : e < s := by dsimp [e]; linarith [hs.1]
  have hd : s < d := by dsimp [d]; linarith [hs.2]
  have hr : d < r := by dsimp [d]; linarith [hs.2]
  have hmaps : MapsTo (fun x => (x, t)) (Icc e d) (chartCylinder h.g T) := by
    intro x hx
    exact h.innerOpen_subset (hsub ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩)
  have hseg {z : ℝ} (hz : z ∈ Icc e d) : inSeg t e z ⊆ chartCylinder h.g T := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    subst y
    exact hmaps ⟨hx.1, hx.2.trans hz.2⟩
  apply intervalPrimitive_hasDerivAt ⟨he, hd⟩
    (h.continuous_nu.comp (continuous_id.prodMk continuous_const).continuousOn hmaps)
  intro z hz
  exact h.equations.radius_s t e z hz.1 (hseg hz)

/-- The continuous radius partials give its strict total derivative.
Paper `e1a0fd5`, `eq:observability-inner-measure`, lines 1467–1471 and 1887. -/
theorem inner_radius_hasStrictFDerivAt {p : ℝ × ℝ} (hp : p ∈ h.innerOpen) :
    HasStrictFDerivAt (fun p => S.r p.1 p.2)
      ((cylinderLinear (S.nu p.1 p.2)).coprod (cylinderLinear (S.lam p.1 p.2))) p := by
  have hn := h.innerOpen_isOpen.mem_nhds hp
  apply hasStrictFDerivAt_uncurry_coprod (f := S.r)
    (f₁ := fun s t => cylinderLinear (S.nu s t))
    (f₂ := fun s t => cylinderLinear (S.lam s t))
  · filter_upwards [hn] with q hq
    exact (h.inner_radius_hasDerivAt_in hq).hasFDerivAt
  · filter_upwards [hn] with q hq
    exact (h.inner_radius_hasDerivAt_out hq).hasFDerivAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      ((h.continuous_nu.mono h.innerOpen_subset).continuousAt hn)
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      ((h.continuous_lam.mono h.innerOpen_subset).continuousAt hn)

/-- The inner level curve has the printed tangent -r_s/r_t at every
interior old time. Paper `e1a0fd5`, lines 1887–1891. -/
theorem innerLabel_hasDerivAt {a s : ℝ} (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Ioo 0 T) :
    HasDerivAt (h.innerLabel a ha hab)
      (-S.nu s (h.innerLabel a ha hab s) / S.lam s (h.innerLabel a ha hab s)) s := by
  let t := h.innerLabel a ha hab s
  have ht := h.innerLabel_spec ha hab (Ioo_subset_Icc_self hs)
  have hp : (s, t) ∈ h.innerOpen := ⟨hs.1, hs.2, ht.1.1, ht.1.2⟩
  have hd := h.inner_radius_hasStrictFDerivAt hp
  have hl := cylinderLinear_invertible (h.signs _ _ (h.innerOpen_subset hp)).1.ne'
  have hi : (((cylinderLinear (S.nu s t)).coprod (cylinderLinear (S.lam s t))) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by simpa using hl
  let w := hd.implicitFunctionOfProdDomain hi
  have hw := hd.hasStrictFDerivAt_implicitFunctionOfProdDomain hi
  have hw0 : w s = t :=
    (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi).self_of_nhds.mp rfl
  have hwD : HasDerivAt w (-S.nu s t / S.lam s t) s := by
    convert hw.hasFDerivAt.hasDerivAt using 1
    have hinv : (cylinderLinear (S.lam s t)).inverse (S.nu s t) = S.nu s t / S.lam s t := by
      apply hl.inverse_apply_eq.mpr
      simp only [cylinderLinear, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact (div_mul_cancel₀ _ (h.signs _ _ (h.innerOpen_subset hp)).1.ne').symm
    simpa [ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.coprod_comp_inr,
      ContinuousLinearMap.comp_apply, cylinderLinear, hinv, neg_div] using hinv.symm
  have hpair : Tendsto (fun x => (x, w x)) (𝓝 s) (𝓝 (s, t)) := by
    simpa only [hw0, id_eq] using tendsto_id.prodMk_nhds hwD.continuousAt
  have hn := hpair.eventually (h.innerOpen_isOpen.mem_nhds hp)
  apply hwD.congr_of_eventuallyEq
  filter_upwards [hn, hd.eventually_apply_implicitFunctionOfProdDomain hi] with x hx hr
  have hxI : x ∈ Icc 0 T := ⟨hx.1.le, hx.2.1.le⟩
  have he : S.r x (w x) = a := hr.trans ht.2
  simp only [innerLabel, dite_eq_left hxI]
  exact ((h.exists_unique_inner_label ha hab hxI).choose_spec.2 (w x)
    ⟨⟨hx.2.2.1, hx.2.2.2⟩, he⟩).symm

/-- The source chart alone constructs the regular inner cylinder graph
on any late subinterval. Paper `e1a0fd5`, lines 1877–1907. -/
@[expose] noncomputable def innerCylinder {a s₀ s₁ : ℝ} (ha : 0 < a) (hab : a < b)
    (hs : s₀ ≤ s₁) (hlate : K * b ≤ s₀) (hterm : s₁ ≤ T) :
    InnerCylinder h a s₀ s₁ where
  a_pos := ha
  a_lt_b := hab
  ordered := hs
  late := hlate
  terminal_le := hterm
  v := h.innerLabel a ha hab
  continuous_v := (h.innerLabel_continuous ha hab).mono
    (Icc_subset_Icc ((mul_pos (zero_lt_one.trans_le h.K_ge_one) h.b_pos).le.trans hlate) hterm)
  points s hs :=
    let ht := h.innerLabel_spec ha hab (s := s)
      ⟨(mul_pos (zero_lt_one.trans_le h.K_ge_one) h.b_pos).le.trans (hlate.trans hs.1),
        hs.2.trans hterm⟩
    ⟨ht.1.1, ht.1.2, ht.2⟩
  tangent s hs := h.innerLabel_hasDerivAt ha hab (s := s)
    ⟨(mul_pos (zero_lt_one.trans_le h.K_ge_one) h.b_pos).trans_le
      (hlate.trans hs.1.le), hs.2.trans_le hterm⟩

end NormalizedChartData

end AcExtensionPrinciple

end
