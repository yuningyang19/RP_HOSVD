import RPHOSVD.Tensor
import RPHOSVD.Projection
import RPHOSVD.Mixed

/-! The two public tensor targets. These are statements, not proofs. The sketch
laws are on arbitrary probability spaces. Causality is expressed by measurable
factor selection from the sketch history, including at SVD ties. -/
noncomputable section
namespace RPHOSVD.Tensor
open MeasureTheory ProbabilityTheory

universe v

abbrev Sketch {d : ℕ} (n r s : Fin d → ℕ) (mode : Schedule) (j : Fin d) :=
  Fin (s j) → Fin (width n r mode j) → ℝ

def tailSum {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) : ℝ :=
  ∑ j, tailEnergy (unfolding a (0 : Factors n r) .parallel j) (r j)

/-- At step j the factors use only the sketches through j. All random choices
in the specified algorithm are the sketches; measurable tie rules can vary. -/
def Adapted {Ω : Type v} {d : ℕ} {n r s : Fin d → ℕ} {mode : Schedule}
    (S : (j : Fin d) → Ω → Sketch n r s mode j) (U : Ω → Factors n r) : Prop :=
  ∀ j, ∃ f : ((k : {k : Fin d // k ≤ j}) → Sketch n r s mode k.val) →
        (Fin (n j) → Fin (r j) → ℝ),
    Measurable f ∧ ∀ ω i l, (U ω j) i l = f (fun k ↦ S k.val ω) i l

def fullRetained {m n s : ℕ} (H : Projection.Mat m n) (S : Projection.Mat s m) (ε : ℝ) : Prop :=
  ∀ i : Fin n, 0 < Projection.sigma (S*H) i.val → ε < Projection.sigma (S*H) i.val

/-- Run witnesses bind both the factor and the scale separation to the actual
unfolding. Only successful embeddings are needed for a high-probability guarantee. -/
def exactStep {m n s r : ℕ} (H : Projection.Mat m n) (S : Projection.Mat s m)
    (U : Projection.Mat n r) (η ε : ℝ) : Prop :=
  ∃ (t : ℕ) (a : Projection.Run m n s r t), a.H = H ∧ a.S = S ∧
    a.ε = ε ∧ a.U = U ∧ ε^2 ≤ (1-η)/2 * (Projection.sigma a.B (r-1))^2

/-- The full-retention clause tests all *nonzero* sketch singular values
at the realized steps, also for rank-deficient unfoldings. -/
def tensorRPClaim : Prop := ∀ (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} (n r s : Fin d → ℕ) (a : ArrayR n)
    (mode : Schedule) (η δ : ℝ) (ε : Fin d → ℝ)
    (S : (j : Fin d) → Ω → Sketch n r s mode j) (U : Ω → Factors n r),
    (∀ j, 1 ≤ r j ∧ r j ≤ n j ∧ 0 < ε j) → 0 < η → η < 1 → 0 < δ → δ < 1 →
    iIndepFun S μ → (∀ j, OSELaw μ (S j) (n j) η δ) → Adapted S U →
    (∀ j ω, let H := (unfolding a (U ω) mode j).transpose
            Projection.EmbedsRange H (S j ω) η → exactStep H (S j ω) (U ω j) η (ε j)) →
    1 - d * δ ≤ μ.real {ω |
      residualSq a (U ω) ≤ tailSum (r := r) a + (2*η^2/(1-η))*∑ j, (r j : ℝ)*(ε j)^2 ∧
      ((∀ j, fullRetained (unfolding a (U ω) mode j).transpose (S j ω) (ε j)) →
        residualSq a (U ω) ≤ tailSum (r := r) a)}

def mixedStep {m n s r : ℕ} (H : Mixed.Mat m n) (S : Mixed.Mat s m) (U : Mixed.Mat n r)
    (η u a b : ℝ) : Prop :=
  ∃ (t : ℕ) (Y : Mixed.Mat s n) (V : Mixed.Mat n t) (X : Mixed.Mat m t)
    (G R : Mixed.Mat t t) (ε : ℝ),
    a * Real.sqrt u * Real.sqrt (Mixed.frobSq H) ≤ ε ∧
    ε ≤ b * Real.sqrt u * Real.sqrt (Mixed.frobSq H) ∧
    Mixed.MixedRun H S Y V X G η ε u r ∧ Mixed.Output Y V G R U

/-- One pair of constants works for all sufficiently small positive unit
roundoffs in fixed dimensions, data, distortion, threshold and entry bounds.
Constants precede the random draws; the conclusion is probabilistic. -/
def tensorMPClaim : Prop := ∀ {d : ℕ} (n r s : Fin d → ℕ) (a : ArrayR n) (mode : Schedule)
    (η δ K lo hi : ℝ), (∀ j, 1 ≤ r j ∧ r j ≤ n j) →
    0 < η → η < 1 → 0 < δ → δ < 1 → 0 < lo → lo ≤ hi →
    ∃ C D u₀ : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 < u₀ ∧
    ∀ (u : ℝ), 0 < u → u ≤ u₀ →
    ∀ (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : (j : Fin d) → Ω → Sketch n r s mode j) (U : Ω → Factors n r),
      iIndepFun S μ → (∀ j, OSELaw μ (S j) (n j) η δ) → Adapted S U →
      (∀ j ω i k, |S j ω i k| ≤ K) →
      (∀ j ω, let H := (unfolding a (U ω) mode j).transpose
              Mixed.EmbedsRange η (S j ω) H → mixedStep H (S j ω) (U ω j) η u lo hi) →
      1 - d * δ ≤ μ.real {ω | residualSq a (U ω) ≤
        (1 + C * Real.sqrt u) * tailSum (r := r) a + D*u}

end RPHOSVD.Tensor
