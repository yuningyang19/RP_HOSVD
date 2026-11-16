import RPHOSVD.Conditioning
import RPHOSVD.TensorMixedLift

/-! Named mathematical interfaces for the seven results in the main text.
Appendix A has its own model in BackwardStability. An entry here is a
proposition; the corresponding theorem below (or in the listed module)
certifies it for the stated mathematical model. -/
namespace RPHOSVD.Paper

noncomputable section
open Matrix
open scoped MatrixOrder

/-- Paper Lemma 4.1 with an ordered nonnegative thin SVD, and retention of its
first t columns as printed. Nonretained singular values may equal the cutoff. -/
def conditioningClaim : Prop := ∀ {m n s q t : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (S : Matrix (Fin s) (Fin m) ℝ)
    (U : Matrix (Fin s) (Fin q) ℝ) (V : Matrix (Fin n) (Fin q) ℝ)
    (σ : Fin q → ℝ) (ε η : ℝ) (htq : t ≤ q),
    0 < t → 0 ≤ ε → 0 < η → η < 1 → (∀ i, 0 ≤ σ i) → Antitone σ →
    (∀ i : Fin q, i.val < t ↔ ε < σ i) →
    S * H = U * diagonal σ * V.transpose → U.transpose * U = 1 → V.transpose * V = 1 →
    (∀ z, (1-η)*((H.mulVec z) ⬝ᵥ (H.mulVec z)) ≤
      (S.mulVec (H.mulVec z)) ⬝ᵥ (S.mulVec (H.mulVec z)) ∧
      (S.mulVec (H.mulVec z)) ⬝ᵥ (S.mulVec (H.mulVec z)) ≤
      (1+η)*((H.mulVec z) ⬝ᵥ (H.mulVec z))) →
    let X := H * Conditioning.whitening V σ (Fin.castLEEmb htq)
    X.rank = t ∧ (1/(1+η) : ℝ) • (1 : Matrix (Fin t) (Fin t) ℝ) ≤ X.transpose * X ∧
    X.transpose * X ≤ (1/(1-η) : ℝ) • (1 : Matrix (Fin t) (Fin t) ℝ) ∧
    Conditioning.conditionNumber₂ X ≤ Real.sqrt ((1+η)/(1-η))

theorem conditioning : conditioningClaim := by
  intro m n s q t H S U V σ ε η hle ht he hη hη' _ _ hth hsv hu hv hose
  apply Conditioning.conditioning H S U V σ (Fin.castLEEmb hle) ε η ht he hη.le hη' _ hsv hu hv hose
  ext i
  constructor
  · rintro ⟨k,rfl⟩; exact (hth _).mp k.isLt
  · intro h; exact ⟨⟨i.val,(hth _).mpr h⟩, Fin.ext rfl⟩

/-- Both the finite-roundoff inequality and its asymptotic clause, Theorem 5.1. -/
def mixedClaim : Prop := Mixed.MixedProjectionBound ∧ Mixed.MixedAsymptoticBound

theorem mixed : mixedClaim :=
  ⟨Mixed.mixedProjection, Mixed.mixed_asymptotic_of_explicit Mixed.mixedProjection⟩

end
end RPHOSVD.Paper
