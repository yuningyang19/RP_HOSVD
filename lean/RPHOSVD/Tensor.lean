import Mathlib

/-! Finite real arrays, the mode unfoldings actually passed to RP, and two
parts of the tensor proofs. A column enumeration is fixed by an equivalence;
all contractions and the sketch at a given step use this same order. -/
noncomputable section
namespace RPHOSVD.Tensor
open MeasureTheory
open scoped BigOperators

abbrev Index {d : ℕ} (n : Fin d → ℕ) := (k : Fin d) → Fin (n k)
abbrev ArrayR {d : ℕ} (n : Fin d → ℕ) := Index n → ℝ
abbrev Factors {d : ℕ} (n r : Fin d → ℕ) := (j : Fin d) → Matrix (Fin (n j)) (Fin (r j)) ℝ
inductive Schedule | parallel | sequential deriving DecidableEq

def compressBefore {d : ℕ} (mode : Schedule) (j k : Fin d) : Prop :=
  mode = .sequential ∧ k < j

instance {d : ℕ} (mode : Schedule) (j k : Fin d) : Decidable (compressBefore mode j k) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev Cols {d : ℕ} (n r : Fin d → ℕ) (mode : Schedule) (j : Fin d) :=
  (k : {k : Fin d // k ≠ j}) → Fin (if compressBefore mode j k.val then r k.val else n k.val)

abbrev width {d : ℕ} (n r : Fin d → ℕ) (mode : Schedule) (j : Fin d) :=
  Fintype.card (Cols n r mode j)

/-- Matrix D_j, with the first j modes (zero-based; strictly preceding j)
already contracted in sequential execution. Entries sum over the original tensor. -/
def unfolding {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) (U : Factors n r)
    (mode : Schedule) (j : Fin d) : Matrix (Fin (n j)) (Fin (width n r mode j)) ℝ :=
  fun row col ↦ ∑ p : Index n, a p * (if p j = row then 1 else 0) *
    ∏ k : {k : Fin d // k ≠ j},
      let c := (Fintype.equivFin (Cols n r mode j)).symm col k
      if h : compressBefore mode j k.val then
        U k.val (p k.val) (Fin.cast (if_pos h) c)
      else if p k.val = Fin.cast (if_neg h) c then 1 else 0

/-- Tucker reconstruction: one orthogonal column projector in each mode. -/
def reconstruction {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) (U : Factors n r) : ArrayR n :=
  fun x ↦ ∑ p : Index n, a p * ∏ j : Fin d, (U j * (U j).transpose) (x j) (p j)

def residualSq {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) (U : Factors n r) : ℝ :=
  ∑ x : Index n, (a x - reconstruction a U x)^2

/-- Squared Frobenius norm of the optimal discarded tail; index r is the
paper's (r+1)-st singular value. The operator here is Dᵀ (short domain). -/
def tailEnergy {m n : ℕ} (D : Matrix (Fin n) (Fin m) ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin n, if r ≤ i.val then ((Matrix.toEuclideanLin D.transpose).singularValues i.val)^2 else 0

/-- Fixed-subspace OSE, quantified over every subspace of dimension at most n. -/
def OSELaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m s : ℕ}
    (S : Ω → Matrix (Fin s) (Fin m) ℝ) (n : ℕ) (η δ : ℝ) : Prop :=
  (∀ k i, Measurable (fun ω ↦ S ω k i)) ∧ ∀ L : Submodule ℝ (Fin m → ℝ), Module.finrank ℝ L ≤ n →
    1 - δ ≤ μ.real {ω | ∀ x ∈ L,
      (1-η) * (∑ i, (x i)^2) ≤ ∑ k, ((S ω).mulVec x k)^2 ∧
      (∑ k, ((S ω).mulVec x k)^2) ≤ (1+η) * ∑ i, (x i)^2}

/-- Finite union bound, valid on a general probability space. The mode events
may be dependent; their marginal bounds for adaptive unfoldings must be proved separately. -/
theorem simultaneous {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (good : Fin d → Set Ω) (δ : ℝ) (hm : ∀ j, MeasurableSet (good j))
    (hp : ∀ j, 1-δ ≤ μ.real (good j)) : 1 - d * δ ≤ μ.real (⋂ j, good j) := by
  have h : μ.real (⋃ j, (good j)ᶜ) ≤ (d : ℝ) * δ := calc
    _ ≤ ∑ j, μ.real ((good j)ᶜ) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin d, δ := Finset.sum_le_sum fun j _ ↦ by
      rw [probReal_compl_eq_one_sub (hm j)]; linarith [hp j]
    _ = _ := by simp
  rw [← Set.compl_iInter, probReal_compl_eq_one_sub (MeasurableSet.iInter hm)] at h
  linarith

/-- Final summation in 3.1, after the single-mode matrix and orthogonal
projection estimates have been established. This is not Theorem 3.1. -/
theorem sumModeErrors {d : ℕ} (e tail : Fin d → ℝ) (r : Fin d → ℕ) (ε : Fin d → ℝ)
    (total η : ℝ) (hsplit : total ≤ ∑ j, e j)
    (hmode : ∀ j, e j ≤ tail j + (2*η^2/(1-η)) * ((r j : ℝ) * (ε j)^2)) :
    total ≤ (∑ j, tail j) + (2*η^2/(1-η)) * ∑ j, (r j : ℝ) * (ε j)^2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact hsplit.trans (Finset.sum_le_sum fun j _ ↦ hmode j)

end RPHOSVD.Tensor
