# Numbered results and their Lean proofs

The current paper contains **8 numbered mathematical results**. Each row has a precise Lean proposition and a separate proof of that proposition. The machine-readable [target map](targets.json) binds the manuscript labels, declarations and proof modules. [Audit.lean](Audit.lean) checks that the proof has the expected type and reports its transitive axioms.

| Result | Statement | Proof | What is proved |
|---|---|---|---|
| Theorem 3.1 | [tensorRPClaim](RPHOSVD/TensorClaims.lean#L40) | [tensorRP](RPHOSVD/TensorLift.lean#L40) | Both tensor schedules, the probability bound 1−dδ and the classical tail bound when all positive sketch singular values are retained. |
| Theorem 3.2 | [tensorMPClaim](RPHOSVD/TensorClaims.lean#L64) | [tensorMP](RPHOSVD/TensorMixedLift.lean#L65) | Both mixed schedules, with a relative O(√u) term and additive O(u); constants are uniform over the sampled unfoldings. |
| Lemma 4.1 | [conditioningClaim](RPHOSVD/Paper.lean#L16) | [conditioning](RPHOSVD/Conditioning.lean#L62) via [the ordered-SVD specialization](RPHOSVD/Paper.lean#L32) | Full column rank, both Gram inequalities and the condition number defined from the extreme singular values. |
| Proposition 4.2 | [projectionClaim](RPHOSVD/Projection.lean#L79) | [projection](RPHOSVD/ExactProjection.lean#L92) | Exact projection-error decomposition and the bound with (n−t)ε²/(1−η). |
| Theorem 4.3 | [refinedProjectionClaim](RPHOSVD/Projection.lean#L87) | [refinedProjection](RPHOSVD/Refined.lean#L354) | Under the stated scale separation, excess at most 2rη²ε²/(1−η), plus the no-truncation clause. |
| Lemma 4.4 | [retainedSubspaceClaim](RPHOSVD/Projection.lean#L94) | [retainedSubspace](RPHOSVD/Retained.lean#L241) | Retained-subspace estimate with coefficient 2r, including singular-value ties. The formal proof uses a variational argument. |
| Theorem 5.1 | [mixedClaim](RPHOSVD/Paper.lean#L41) | [finite-roundoff proof](RPHOSVD/MixedProjection.lean#L42) and [asymptotic proof](RPHOSVD/MixedAsymptotic.lean#L303) | Explicit θ-based inequality, Gram positivity and the bounded-sketch, scaled-threshold corollary. |
| Proposition A.1 | [BackwardStabilityBound](RPHOSVD/Mixed.lean#L153) | [backwardStability](RPHOSVD/BackwardStability.lean#L51) | For the computed factors of a successful modeled run: an orthonormal left factor, exact perturbed SVD identity, and Frobenius backward error with uniform constants independent of κ₂(H). |

The matrix estimates are developed first, followed by the ordinary and mixed-precision projection bounds and their tensor extensions. The appendix result assumes successful runs satisfying the stated numerical error contracts. The mixed-precision result uses exact small factorizations, as in the paper's model.
