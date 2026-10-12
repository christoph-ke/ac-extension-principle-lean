module

public import AcExtensionPrinciple.Main.AssemblyExistence

/-!
# The proposed continuation fields in the original chart

Paper `e1a0fd5`, `equations.tex` lines 1411–1422.
The patch keeps all seven original representatives on the old domain and
uses the pulled-back development elsewhere. Class membership requires a
separate representative-compatible gluing argument.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Retain the original fields on the old off-axis triangle and use the
development in the extended chart elsewhere.
Paper `e1a0fd5`, `thm:main`, line 133, and lines 1411–1422. -/
@[expose] noncomputable def continuationFields (ui : ℝ) (S Sdev : SSFields)
    (T dT : ℝ → ℝ) : SSFields := by
  classical
  let Snew := Sdev.pullback T dT
  exact {
    r u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.r u v else Snew.r u v
    phi u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.phi u v else Snew.phi u v
    m u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.m u v else Snew.m u v
    lam u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.lam u v else Snew.lam u v
    nu u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.nu u v else Snew.nu u v
    dvpsi u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.dvpsi u v else Snew.dvpsi u v
    dupsi u v := if (u, v) ∈ pastTriangle ui \ axis ui then S.dupsi u v else Snew.dupsi u v }

/-- All seven original representatives are retained exactly as required
in the main statement. Paper `e1a0fd5`, `thm:main`, line 133, and line 1422. -/
theorem continuationFields_agree (ui : ℝ) (S Sdev : SSFields) (T dT : ℝ → ℝ)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui \ axis ui) :
    FieldsAgreeAt (continuationFields ui S Sdev T dT) S p := by
  simp [FieldsAgreeAt, continuationFields, hp]

/-- Outside the original domain the patch is precisely the pullback.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuationFields_new (ui : ℝ) (S Sdev : SSFields) (T dT : ℝ → ℝ)
    {p : ℝ × ℝ} (hp : p ∉ pastTriangle ui \ axis ui) :
    FieldsAgreeAt (continuationFields ui S Sdev T dT) (Sdev.pullback T dT) p := by
  simp [FieldsAgreeAt, continuationFields, hp]

/-- Primitive agreement identifies the patched r,φ,m with the pullback on
the entire late continuation region. Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuationFields_primitives {ui ū : ℝ} {S Sdev : SSFields}
    {T dT : ℝ → ℝ}
    (he : ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      S.r u v = Sdev.r (T u) (T v) ∧ S.phi u v = Sdev.phi (T u) (T v) ∧
        S.m u v = Sdev.m (T u) (T v))
    {u v : ℝ} (hu : ū ≤ u) (huv : u < v) :
    (continuationFields ui S Sdev T dT).r u v = (Sdev.pullback T dT).r u v ∧
    (continuationFields ui S Sdev T dT).phi u v = (Sdev.pullback T dT).phi u v ∧
    (continuationFields ui S Sdev T dT).m u v = (Sdev.pullback T dT).m u v := by
  by_cases hp : (u, v) ∈ pastTriangle ui \ axis ui
  · simpa only [continuationFields, ite_eq_left hp, SSFields.pullback]
      using he u v hu huv hp.1.2.2.2
  · simp only [continuationFields, ite_eq_right hp, and_self]

/-- The selected total chart equals the paper's continuation map on the
whole interval beginning at the selected cone, including the linear future.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, line 1422. -/
theorem StandingFull.selected_chart_future {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hT : (T : ℝ → ℝ) = radialChartMap (S.r ū) (S.lam ū) ū) :
    EqOn T (continuationMap (S.r ū) (S.lam ū)) (Ici ū) := by
  intro t ht
  rw [hT]
  by_cases hleft : t ≤ ū
  · have heq : t = ū := le_antisymm hleft ht
    subst t
    have hr := (h.regularCenter.localBV.axis_values ū
      (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1
    simp [radialChartMap, continuationMap, hū.2.le, hr]
  · simp [radialChartMap, hleft]

end AcExtensionPrinciple

end
