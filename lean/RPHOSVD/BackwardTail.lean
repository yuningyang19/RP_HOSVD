import RPHOSVD.MixedRecovery

noncomputable section
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator

def frob {m n : ℕ} (A : Mat m n) : ℝ := Real.sqrt (frobSq A)

open scoped Matrix.Norms.Frobenius in
private theorem fNorm {m n : ℕ} (A : Mat m n) : ‖A‖ = frob A := by
  rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
  simp [frobSq,Real.norm_eq_abs]

theorem frob_add {m n : ℕ} (A B : Mat m n) : frob (A+B) ≤ frob A + frob B := by
  simpa only [← fNorm] using @norm_add_le (Mat m n) Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup A B

theorem frob_mul {m n k : ℕ} (A : Mat m k) (B : Mat k n) : frob (A*B) ≤ frob A * frob B := by
  simpa only [fNorm] using Matrix.frobenius_norm_mul A B

theorem frob_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ frob A := Real.sqrt_nonneg _

theorem frob_sq {m n : ℕ} (A : Mat m n) : frob A ^ 2 = frobSq A := by
  apply Real.sq_sqrt; exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

def dimFac (m n : ℕ) : ℝ := (m+1 : ℝ)*(n+1)
theorem dimFac_pos (m n : ℕ) : 0 < dimFac m n := by unfold dimFac; positivity

theorem frob_le_dim_op {m n : ℕ} (A : Mat m n) : frob A ≤ dimFac m n * ‖A‖ := by
  have ent (i j) : |A i j| ≤ ‖A‖ := by
    let e : EuclideanSpace ℝ (Fin n) := PiLp.single 2 j 1
    have h := (PiLp.norm_apply_le (Matrix.toEuclideanLin A e) i).trans (Matrix.l2_opNorm_mulVec A e)
    simpa [e, Matrix.toLpLin_apply, Matrix.mulVec_single, Real.norm_eq_abs] using h
  have hr : frobSq A ≤ (m:ℝ)*(n:ℝ)*‖A‖^2 := calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, ‖A‖^2 := Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ent i j) 2
    _ = _ := by simp; ring
  have hdim : (m:ℝ)*n ≤ dimFac m n ^ 2 := by
    unfold dimFac
    have hm : (m:ℝ) ≤ (m+1 : ℝ)^2 := by nlinarith [sq_nonneg (m:ℝ)]
    have hn : (n:ℝ) ≤ (n+1 : ℝ)^2 := by nlinarith [sq_nonneg (n:ℝ)]
    rw [mul_pow]; gcongr
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg (dimFac_pos _ _).le (norm_nonneg _))).mp
  rw [frob_sq,mul_pow]
  exact hr.trans (mul_le_mul_of_nonneg_right hdim (sq_nonneg _))

theorem stored_frob {m k n : ℕ} (A : Mat m k) (B : Mat k n) (C : Mat m n)
    (u : ℝ) (h : StoredProduct u A B C) (hg : 0 ≤ gamma k u) :
    frob (C-A*B) ≤ gamma k u * (frob A * frob B) := by
  let D := magnitude A * magnitude B
  have e : frobSq (C-A*B) ≤ (gamma k u)^2 * frobSq D := by
    unfold frobSq
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    simpa only [D,mul_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
  have he := Real.sqrt_le_sqrt e
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hg] at he
  have mag {s t : ℕ} (M : Mat s t) : frob (magnitude M) = frob M := by simp [frob,frobSq,magnitude]
  change frob (C-A*B) ≤ gamma k u * frob D at he
  exact he.trans (mul_le_mul_of_nonneg_left (by simpa [D,mag] using frob_mul (magnitude A) (magnitude B)) hg)

theorem embed_frob_lower {m n s : ℕ} (H : Mat m n) (S : Mat s m) (η : ℝ)
    (h : EmbedsRange η S H) (hη : η < 1) :
    Real.sqrt (1-η)*frob H ≤ frob (S*H) := by
  have hcol (j : Fin n) :
      (1-η)*(∑ i, H i j ^ 2) ≤ ∑ k, (S*H) k j ^ 2 := by
    have hh := (h (PiLp.single 2 j 1)).1
    simpa [Matrix.toLpLin_apply, Matrix.mulVec_single, Matrix.mulVec,
      Matrix.mul_apply, dotProduct, EuclideanSpace.real_norm_sq_eq] using hh
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (frob_nonneg _)) (frob_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hη.le),frob_sq,frob_sq]
  unfold frobSq
  rw [Finset.sum_comm,Finset.mul_sum,Finset.sum_comm (s := (Finset.univ : Finset (Fin s)))]
  exact Finset.sum_le_sum fun j _ ↦ hcol j

/-- Sketch-size lower bound and a uniform Frobenius budget for the perturbation
of the sketch plus its stable SVD, independent of the input condition number. -/
theorem sketchBackwardBudget (m n s : ℕ) (η K K₁ : ℝ) (he : η < 1)
    (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) :
    ∃ α a u₀ : ℝ, 0 < α ∧ 0 < a ∧ 0 < u₀ ∧
    ∀ (H : Mat m n) (S : Mat s m) (Y E₁ : Mat s n) (u : ℝ),
      0 < u → u ≤ u₀ → ‖S‖ ≤ K → EmbedsRange η S H → StoredProduct u S H Y →
      frob E₁ ≤ K₁*u*frob Y →
      α*frob H ≤ ‖Y‖ ∧ frob (Y+E₁-S*H) ≤ a*u*frob H ∧ frob Y ≤ a*frob H := by
  let L := dimFac s m*K
  let b := 2*(m+1:ℝ)*(L+1)
  let q := Real.sqrt (1-η)
  have hq : 0 < q := Real.sqrt_pos.mpr (sub_pos.mpr he)
  have hL : 0 ≤ L := mul_nonneg (dimFac_pos _ _).le hK
  have hb : 0 < b := by dsimp [b]; positivity
  let rad := min 1 (min (1/(2*(m+1:ℝ))) (q/(2*b)))
  let a := 1 + b + L + K₁*(b+L)
  have hdpos := dimFac_pos s n
  refine ⟨q/(2*dimFac s n), a, rad, by positivity, by dsimp [a]; positivity,
    by dsimp [rad]; positivity, ?_⟩
  intro H S Y E u hu hrad hs emb hr hE
  have hu1 : u ≤ 1 := hrad.trans (min_le_left ..)
  have hhalf := hrad.trans ((min_le_right ..).trans (min_le_left ..))
  have hsmall := hrad.trans ((min_le_right ..).trans (min_le_right ..))
  change u ≤ 1/(2*(m+1:ℝ)) at hhalf
  change u ≤ q/(2*b) at hsmall
  have hμ : (m:ℝ)*u ≤ 1/2 := by
    have hc := (le_div_iff₀ (by positivity)).mp hhalf
    nlinarith
  have hgu : gamma m u ≤ 2*(m:ℝ)*u := by
    unfold gamma; apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hu.le) (show 0≤1-2*(m:ℝ)*u by linarith)]
  have hgp : 0 ≤ gamma m u := div_nonneg (by positivity) (by linarith)
  have sB : frob S ≤ L := (frob_le_dim_op S).trans (mul_le_mul_of_nonneg_left hs (dimFac_pos _ _).le)
  have hsH : frob (S*H) ≤ L*frob H := (frob_mul S H).trans (mul_le_mul_of_nonneg_right sB (frob_nonneg _))
  have err : frob (Y-S*H) ≤ b*u*frob H := calc
    _ ≤ gamma m u * (frob S * frob H) := stored_frob _ _ _ _ hr hgp
    _ ≤ (2*(m:ℝ)*u)*(L*frob H) := mul_le_mul hgu (mul_le_mul_of_nonneg_right sB (frob_nonneg H))
      (mul_nonneg (frob_nonneg S) (frob_nonneg H)) (by positivity)
    _ ≤ _ := by
      have hcoeff : 2*(m:ℝ)*L ≤ b := by dsimp [b]; nlinarith
      nlinarith only [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hu.le (frob_nonneg H))]
  have yB : frob Y ≤ (b+L)*frob H := by
    have tt := frob_add (Y-S*H) (S*H)
    rw [sub_add_cancel] at tt
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu1 hb.le) (frob_nonneg H)]
  have lo := embed_frob_lower H S η emb he
  have rev : frob (S*H) ≤ frob Y + frob (Y-S*H) := by
    have hn : frob (-(Y-S*H)) = frob (Y-S*H) := by simp only [frob,frobSq,Matrix.neg_apply,neg_sq]
    have tt := frob_add Y (-(Y-S*H))
    rw [hn,show Y + -(Y-S*H) = S*H by abel] at tt
    exact tt
  have small := (le_div_iff₀ (by positivity)).mp hsmall
  have low : q*frob H / 2 ≤ frob Y := by
    change q*frob H ≤ _ at lo
    nlinarith [mul_le_mul_of_nonneg_right small (frob_nonneg H)]
  constructor
  · rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith [frob_le_dim_op Y]
  constructor
  · have tt := frob_add (Y-S*H) E
    rw [show (Y-S*H)+E = Y+E-S*H by abel] at tt
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_left yB (mul_nonneg hK₁ hu.le),
      mul_nonneg (mul_nonneg hL hu.le) (frob_nonneg H), mul_nonneg hu.le (frob_nonneg H)]
  · exact yB.trans (mul_le_mul_of_nonneg_right (by dsimp [a]; nlinarith [mul_nonneg hK₁ (add_nonneg hb.le hL)]) (frob_nonneg _))

end RPHOSVD.Mixed
