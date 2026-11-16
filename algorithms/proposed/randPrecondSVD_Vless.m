function U = randPrecondSVD_Vless(A,r,sketch,backend)
% Apply sketching and preconditioning to A, then recover its dominant left singular subspace.
% Use randPrecondQR_qless to construct a smaller, numerically stable factor B,
% then compute its economy SVD to recover the desired subspace.
%
% If A' = Q * B, the right singular vectors of B correspond to the left singular
% vectors of A, so an SVD of B gives the dominant left singular subspace of A.
%
% Inputs:
%   A : typically a short, wide matrix
%   r : target rank
%   sketch : optional right sketch; omitted to use the default sparse-sign construction
%   backend : 'tall' (default) or 'legacy'
%
% prepared-tall: A is already the physical n-by-m conjugate transpose.
% The sketch still has the original logical n-by-sketch_size shape.
%
% Outputs:
%   U : leading r left singular vectors of A

% [m,n] = size(A); 
% if m>n
%     A = A';
% end
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<3, sketch=[]; end
if nargin<4, backend='tall'; end
B = randPrecondQR_qless(A,sketch,backend);
[~,~,U] = svd(B,'econ');
U = U(:,1:min(r, size(U,2)));



end
