import RPHOSVD.Backward
import RPHOSVD.BackwardTail
import RPHOSVD.Polar

/-! Propagation from a near-orthogonal whitened matrix through formation of B. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

private theorem frame_frob {m t : ℕ} (Q : Mat m t) (hq : Qᵀ*Q=1) :
    frob Q = Real.sqrt t := by
  unfold frob frobSq
  rw [Finset.sum_comm]
  have hh (j : Fin t) : ∑ i, Q i j ^ 2 = 1 := by
    simpa [Matrix.mul_apply,sq] using congrArg (fun A : Mat t t => A j j) hq
  simp [hh]

private theorem frob_transpose {m n : ℕ} (A : Mat m n) : frob Aᵀ = frob A := by
  unfold frob frobSq
  rw [Finset.sum_comm]
  rfl

theorem retained_scales_le {s n t : ℕ} (Y : Mat s n) (ht : t ≤ n) :
    frob (scales Y t) ≤ frob Y := by
  obtain ⟨W,hW⟩ := Projection.exists_rightBasis Y
  have hy := Projection.fullBasisEnergy hW
  have hf : frobSq Y = Projection.frobSq Y := by rw [frobSq,Projection.frobSq_cols,Finset.sum_comm]; rfl
  apply Real.sqrt_le_sqrt
  rw [hf,hy]
  obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [frobSq,scales,Matrix.diagonal_apply,ite_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Fin.sum_univ_add]
  change _ ≤ (∑ j : Fin t, sigma Y j.val ^ 2) + _
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Formation of B and replacement of the computed whitened basis by its
polar representative. The constants are uniform over 0 ≤ t ≤ n. -/
theorem retainedBackwardBudget (m n : ℕ) (β L P D : ℝ)
    (hβ : 0 ≤ β) (hL : 0 ≤ L) (hP : 0 ≤ P) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {t : ℕ} (H : Mat m n) (V : Mat n t) (X Q : Mat m t) (R Dg Z : Mat t t)
      (B : Mat t n) (u : ℝ),
    t ≤ n → 0 ≤ u → u ≤ 1 → (n:ℝ)*u ≤ 1/2 → Vᵀ*V=1 → Qᵀ*Q=1 →
    IsUnit R.det → ‖R‖ ≤ L → ‖X*R⁻¹-Q‖ ≤ P*u → frob Dg ≤ D*frob H →
    frob (X*Dg-H*V) ≤ β*u*frob H →
    StoredProduct u R Dg Z → StoredProduct u Z Vᵀ B →
    frob (H*(V*Vᵀ)-Q*B) ≤ C*u*frob H ∧ frob B ≤ C*frob H := by
  let v := (n+1:ℝ)
  let fR := dimFac n n * L
  let fE := dimFac m n * P
  let g := 2*(n:ℝ)
  let z₀ := (1+g)*fR*D
  let b₀ := (1+g)*z₀*v
  let e₀ := β*v + (fE*fR)*D*v + v*(g*fR*D*v + g*z₀*v)
  have hz : 0 ≤ z₀ := by dsimp [z₀,g,fR,dimFac]; positivity
  have he0 : 0 ≤ e₀ := by dsimp [e₀,v,fE,fR,g,dimFac]; positivity
  have hb0 : 0 ≤ b₀ := by dsimp [b₀,g,v]; positivity
  refine ⟨1+e₀+b₀, by positivity, ?_⟩
  intro t H V X Q R Dg Z B u ht hu hu1 hn hV hQ hdet hR hN hDs hscale hZ hB
  let f := frob H
  have hf : 0 ≤ f := frob_nonneg _
  have htn : (t:ℝ) ≤ (n:ℝ) := by exact_mod_cast ht
  have hγt := gamma_upper t u hu ((mul_le_mul_of_nonneg_right htn hu).trans hn)
  have hγ : gamma t u ≤ g*u := hγt.2.trans (by dsimp [g]; gcongr)
  have htroot : Real.sqrt t ≤ v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by dsimp [v]; positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    dsimp [v]
    nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hVn : frob Vᵀ ≤ v := by rw [frob_transpose,frame_frob V hV]; exact htroot
  have hQn : frob Q ≤ v := by rw [frame_frob Q hQ]; exact htroot
  have hRn : frob R ≤ fR := by
    apply (frob_le_dim_op R).trans
    dsimp [fR,dimFac]
    gcongr
  have hEn : frob (X*R⁻¹-Q) ≤ fE*u := by
    apply (frob_le_dim_op _).trans
    calc
      _ ≤ dimFac m n * (P*u) := by dsimp [dimFac]; gcongr
      _ = _ := by dsimp [fE]; ring
  have hrd : frob (R*Dg) ≤ fR*(D*f) := (frob_mul _ _).trans
    (mul_le_mul hRn hDs (frob_nonneg _) (by dsimp [fR,dimFac]; positivity))
  have hze : frob (Z-R*Dg) ≤ g*u*(fR*(D*f)) := by
    apply (stored_frob R Dg Z u hZ hγt.1).trans
    exact mul_le_mul hγ (mul_le_mul hRn hDs (frob_nonneg _) (by dsimp [fR,dimFac]; positivity))
      (mul_nonneg (frob_nonneg _) (frob_nonneg _)) (by dsimp [g]; positivity)
  have hzn : frob Z ≤ z₀*f := by
    have hh := frob_add (Z-R*Dg) (R*Dg)
    rw [sub_add_cancel] at hh
    have hg0 : 0 ≤ g := by dsimp [g]; positivity
    have hfr0 : 0 ≤ fR := by dsimp [fR,dimFac]; positivity
    have hmul := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ g*(fR*(D*f)))
    dsimp [z₀]
    nlinarith only [hh,hze,hrd,hmul]
  have hbe : frob (B-Z*Vᵀ) ≤ g*u*(z₀*f*v) := by
    apply (stored_frob Z Vᵀ B u hB hγt.1).trans
    exact mul_le_mul hγ (mul_le_mul hzn hVn (frob_nonneg _) (mul_nonneg hz hf))
      (mul_nonneg (frob_nonneg _) (frob_nonneg _)) (by dsimp [g]; positivity)
  have hbn : frob B ≤ b₀*f := by
    have hh := frob_add (B-Z*Vᵀ) (Z*Vᵀ)
    rw [sub_add_cancel] at hh
    have hZv := (frob_mul Z Vᵀ).trans (mul_le_mul hzn hVn (frob_nonneg _) (mul_nonneg hz hf))
    have gg : 0 ≤ g := by dsimp [g]; positivity
    have vv : 0 ≤ v := by dsimp [v]; positivity
    have hm := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ g*(z₀*f*v))
    dsimp [b₀]
    nlinarith only [hh,hbe,hZv,hm]
  have hXeq : (X*R⁻¹-Q)*R = X-Q*R := by simp [Matrix.sub_mul,Matrix.mul_assoc,R.nonsing_inv_mul hdet]
  have hXR : frob (X-Q*R) ≤ (fE*u)*fR := by
    rw [← hXeq]
    apply (frob_mul _ _).trans
    exact mul_le_mul hEn hRn (frob_nonneg _) (by dsimp [fE,dimFac]; positivity)
  have hNeg {a b : ℕ} (A : Mat a b) : frob (-A) = frob A := by simp [frob,frobSq]
  have hrev {a b : ℕ} (A B : Mat a b) : frob (A-B) = frob (B-A) := by rw [← hNeg,neg_sub]
  have hS : frob ((H*V-X*Dg)*Vᵀ) ≤ (β*u*f)*v := by
    apply (frob_mul _ _).trans
    rw [hrev (H*V)]
    exact mul_le_mul hscale hVn (frob_nonneg _) (by positivity)
  have hE : frob ((X-Q*R)*Dg*Vᵀ) ≤ ((fE*u)*fR)*(D*f)*v := by
    apply (frob_mul _ _).trans
    have hh := (frob_mul (X-Q*R) Dg).trans (mul_le_mul hXR hDs (frob_nonneg _)
      (by dsimp [fE,fR,dimFac]; positivity))
    exact mul_le_mul hh hVn (frob_nonneg _) (by dsimp [fE,fR,dimFac]; positivity)
  have hround : frob (R*Dg*Vᵀ-B) ≤ (g*u*(fR*(D*f)))*v + g*u*(z₀*f*v) := by
    have hi : R*Dg*Vᵀ-B = (R*Dg-Z)*Vᵀ + (Z*Vᵀ-B) := by simp [Matrix.sub_mul]
    rw [hi]
    apply (frob_add _ _).trans
    apply add_le_add
    · apply (frob_mul _ _).trans
      rw [hrev (R*Dg)]
      exact mul_le_mul hze hVn (frob_nonneg _) (by dsimp [g,fR,dimFac]; positivity)
    · rwa [hrev (Z*Vᵀ)]
  have hQB := (frob_mul Q (R*Dg*Vᵀ-B)).trans (mul_le_mul hQn hround (frob_nonneg _)
    (by dsimp [v]; positivity))
  have eq : H*(V*Vᵀ)-Q*B = (H*V-X*Dg)*Vᵀ + (X-Q*R)*Dg*Vᵀ + Q*(R*Dg*Vᵀ-B) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  have herr : frob (H*(V*Vᵀ)-Q*B) ≤ e₀*u*f := by
    rw [eq]
    apply (frob_add _ _).trans
    apply (add_le_add ((frob_add _ _).trans (add_le_add hS hE)) hQB).trans
    dsimp only [e₀]
    ring_nf
    rfl
  constructor
  · exact herr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : e₀ ≤ 1+e₀+b₀) hu) hf)
  · exact hbn.trans (mul_le_mul_of_nonneg_right (by linarith : b₀ ≤ 1+e₀+b₀) hf)

end
end RPHOSVD.Mixed
