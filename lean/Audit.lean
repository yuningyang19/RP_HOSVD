import RPHOSVD

-- thm:tensor-rp
example : RPHOSVD.Tensor.tensorRPClaim := RPHOSVD.Tensor.tensorRP
#print axioms RPHOSVD.Tensor.tensorRP

-- thm:tensor-mp
example : RPHOSVD.Tensor.tensorMPClaim := RPHOSVD.Tensor.tensorMP
#print axioms RPHOSVD.Tensor.tensorMP

-- lem:conditioning
example : RPHOSVD.Paper.conditioningClaim := RPHOSVD.Paper.conditioning
#print axioms RPHOSVD.Paper.conditioning

-- thm:rp
example : RPHOSVD.Projection.projectionClaim := RPHOSVD.Projection.projection
#print axioms RPHOSVD.Projection.projection

-- thm:rp-refined
example : RPHOSVD.Projection.refinedProjectionClaim := RPHOSVD.Projection.refinedProjection
#print axioms RPHOSVD.Projection.refinedProjection

-- lem:retained-subspace-error
example : RPHOSVD.Projection.retainedSubspaceClaim := RPHOSVD.Projection.retainedSubspace
#print axioms RPHOSVD.Projection.retainedSubspace

-- prop:mp-recovery
example : RPHOSVD.Paper.mixedClaim := RPHOSVD.Paper.mixed
#print axioms RPHOSVD.Paper.mixed

-- prop:rp-backward-stability
example : RPHOSVD.Mixed.BackwardStabilityBound := RPHOSVD.Mixed.backwardStability
#print axioms RPHOSVD.Mixed.backwardStability
