function [U,S,V] = trunSVD(A,r)
% TRUNSVD Compute a rank-r truncated singular value decomposition.
%   Return the leading r singular vectors and singular values of A.

    [U,S,V] = svd(A,'econ');
    U = U(:,1:r); S = S(1:r,1:r); V = V(:,1:r);

end

