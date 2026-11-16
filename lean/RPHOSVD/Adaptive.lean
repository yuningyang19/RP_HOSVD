import RPHOSVD.Tensor
import RPHOSVD.Projection

namespace RPHOSVD.Tensor
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If a sketch law works for every fixed input subspace, it still works for
an independent random input. The measurable relation is allowed to depend on
both arguments; no union bound over the possible input subspaces is used. -/
theorem independentSection {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (S : Ω → B) (hX : Measurable X) (hS : Measurable S)
    (hind : IndepFun X S μ) (event : Set (A × B)) (hm : MeasurableSet event)
    (p : ℝ≥0∞) (hfixed : ∀ x, p ≤ μ (S ⁻¹' (Prod.mk x ⁻¹' event))) :
    p ≤ μ ((fun ω ↦ (X ω, S ω)) ⁻¹' event) := by
  let : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  rw [← Measure.map_apply (hX.prodMk hS) hm,
      hind.map_prod_eq_prod_map_map hX.aemeasurable hS.aemeasurable, Measure.prod_apply hm]
  calc
    p = ∫⁻ _ : A, p ∂μ.map X := by simp
    _ ≤ _ := lintegral_mono fun x ↦ by
      rw [Measure.map_apply hS (hm.preimage measurable_prodMk_left)]
      exact hfixed x


abbrev Raw (m n : ℕ) := Fin m → Fin n → ℝ

/-- The successful embedding event is closed as an intersection of closed
quadratic-form inequalities over all coefficient vectors, hence measurable. -/
theorem measurableEmbedding {m n s : ℕ} (η : ℝ) :
    MeasurableSet {p : Raw m n × Raw s m | Projection.EmbedsRange p.1 p.2 η} := by
  by_cases h : 0 < η ∧ η < 1
  · let f (p : Raw m n × Raw s m) (z : Fin n → ℝ) :=
      ∑ i : Fin m, (∑ j, p.1 i j * z j)^2
    let g (p : Raw m n × Raw s m) (z : Fin n → ℝ) :=
      ∑ k : Fin s, (∑ i, p.2 k i * (∑ j, p.1 i j * z j))^2
    have eq : {p : Raw m n × Raw s m | Projection.EmbedsRange p.1 p.2 η} =
        ⋂ z, {p | (1-η) * f p z ≤ g p z ∧ g p z ≤ (1+η) * f p z} := by
      ext p; simp [Projection.EmbedsRange, h.1, h.2, Projection.vecSq, Matrix.mulVec,
        dotProduct, f, g]
    rw [eq]
    apply IsClosed.measurableSet
    apply isClosed_iInter; intro z
    have hf : Continuous (fun p ↦ f p z) := by dsimp [f]; fun_prop
    have hg : Continuous (fun p ↦ g p z) := by dsimp [g]; fun_prop
    exact (isClosed_le (continuous_const.mul hf) hg).inter
      (isClosed_le hg (continuous_const.mul hf))
  · have he : {p : Raw m n × Raw s m | Projection.EmbedsRange p.1 p.2 η} = ∅ := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hp ↦ h ⟨hp.1, hp.2.1⟩
    rw [he]; exact MeasurableSet.empty

/-- Actual random-unfolding form of the OSE bound. -/
theorem adaptiveEmbedding {Ω : Type*} [MeasurableSpace Ω] {m n s : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → Raw m n) (S : Ω → Raw s m) (η δ : ℝ)
    (he : 0 < η ∧ η < 1) (hd : δ ≤ 1)
    (hH : Measurable H) (hS : Measurable S) (hind : IndepFun H S μ)
    (hlaw : OSELaw μ S n η δ) :
    1-δ ≤ μ.real {ω | Projection.EmbedsRange (H ω) (S ω) η} := by
  let event := {p : Raw m n × Raw s m | Projection.EmbedsRange p.1 p.2 η}
  have fixed (A : Raw m n) :
      ENNReal.ofReal (1-δ) ≤ μ (S ⁻¹' (Prod.mk A ⁻¹' event)) := by
    let M : Projection.Mat m n := A
    have hdim : Module.finrank ℝ (LinearMap.range M.mulVecLin) ≤ n := by
      simpa using LinearMap.finrank_range_le M.mulVecLin
    have hh := hlaw.2 (LinearMap.range M.mulVecLin) hdim
    have sub : {ω | ∀ x ∈ LinearMap.range M.mulVecLin,
          (1-η)*(∑ i, (x i)^2) ≤ ∑ k, (Matrix.mulVec (S ω) x k)^2 ∧
          (∑ k, (Matrix.mulVec (S ω) x k)^2) ≤ (1+η)*∑ i, (x i)^2}
        ⊆ S ⁻¹' (Prod.mk A ⁻¹' event) := by
      intro ω hw
      exact ⟨he.1, he.2, fun z ↦ hw _ ⟨z, rfl⟩⟩
    have hv := ENNReal.ofReal_le_ofReal (hh.trans (measureReal_mono sub))
    rwa [ofReal_measureReal] at hv
  have hh := independentSection μ H S hH hS hind event (measurableEmbedding η)
    (ENNReal.ofReal (1-δ)) fixed
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hd)] at hr
  exact hr

end RPHOSVD.Tensor
