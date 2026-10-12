module

public import AcExtensionPrinciple.Renormalized.ClassTransport

/-!
# Exactly the Lemma 2.2 inputs needed for Section 3

Interface, paper `e1a0fd5`, `equations.tex` lines 555–570.
The outgoing AC datum, its a.e. radial derivative, and its incoming
integral equation are supplied by Lemma 2.2. No geometric or scalar conclusion
is assumed in this interface.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The three Lemma 2.2 conclusions used by Lemmas 3.1 and 3.2.
Paper `e1a0fd5`, `lem:ac-datum-propagation`, `eq:radial-datum-derivative`,
`eq:radial-datum-transport`, lines 555–570. -/
structure SectionThreeDatumInputs (ui : ℝ) (S : SSFields) (q : ℝ → ℝ → ℝ) : Prop where
  outgoing_ac : ∀ u, ui ≤ u → u < 0 →
    AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0
  radial_eq : ∀ u, ui ≤ u → u < 0 →
    q u =ᵐ[volume.restrict (Ioc u 0)] S.radialDatumDerivative u
  incoming_primitive : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    IntervalPrimitive (fun u => q u v)
      (fun u => -2 * S.gamma u v * S.varkappa u v * q u v -
        (S.gamma u v / S.r u v ^ 2) * (S.r u v / S.lam u v * S.dvphi u v) *
          ((S.r u v / S.lam u v * S.dvphi u v) ^ 2 - 3 * S.mu u v)) a b

namespace SectionThreeDatumInputs

variable {ui : ℝ} {S : SSFields} {q : ℝ → ℝ → ℝ} (D : SectionThreeDatumInputs ui S q)
include D

/-- Incoming datum AC follows from the stated incoming integral equation.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 563–570. -/
theorem incoming_ac {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => q u v) a b :=
  intervalPrimitive_ac hab (fun x hx =>
    D.incoming_primitive v a x hx.1 ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)

/-- Incoming datum transport a.e. follows from its integral equation.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 563–570. -/
theorem incoming_ae {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => q u v)
      (-2 * S.gamma x v * S.varkappa x v * q x v -
        (S.gamma x v / S.r x v ^ 2) * (S.r x v / S.lam x v * S.dvphi x v) *
          ((S.r x v / S.lam x v * S.dvphi x v) ^ 2 - 3 * S.mu x v)) x :=
  intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    D.incoming_primitive v a x hx.1 ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)

/-- The prescribed radial derivative gives the outgoing datum derivative
a.e. on every off-axis subsegment. Paper `e1a0fd5`, lines 555–558 and 1064–1065. -/
theorem outgoing_ae (h : StandingFull ui S) {u a b : ℝ}
    (_hab : a ≤ b) (hu : ui ≤ u) (hu0 : u < 0) (hua : u ≤ a) (hb0 : b ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.outgoingDatum u) (S.lam u x * q u x) x := by
  have he := D.radial_eq u hu hu0
  change ∀ᵐ x ∂volume.restrict (Ioc u 0), q u x = S.radialDatumDerivative u x at he
  rw [ae_restrict_iff' measurableSet_Ioc] at he
  filter_upwards [h.radialDatumDerivative_ae hu0.le hu hu0 le_rfl le_rfl
    (D.outgoing_ac u hu hu0), he] with x hx hqx hxI
  have hx0 : x ∈ Ioo u 0 := ⟨hua.trans_lt hxI.1, hxI.2.trans_le hb0⟩
  rw [hqx ⟨hx0.1, hx0.2.le⟩]
  exact hx hx0

end SectionThreeDatumInputs

end AcExtensionPrinciple

end
