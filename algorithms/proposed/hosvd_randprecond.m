function [U,S] = hosvd_randprecond(T,r,sketches,coreBackend,matrixBackend)
% Randomized preconditioned HOSVD.
% For each mode unfolding A_n of tensor T, form a random sketch and construct
% a small preconditioned matrix. Its deterministic SVD is used to stably recover
% the leading r(n) left singular vectors of A_n.
%
% Inputs:
%   T : input tensor
%   r : retained rank for each mode; its length must equal ndims(T)
%   sketches : optional cell array of per-mode sketches for paired comparisons
%   coreBackend : 'fast' (default) or 'tensorlab' (modewise products); use sketches=[] if needed
%   matrixBackend : 'prepared-tall' (default, direct tall unfolding), 'tall', or 'legacy'
%
% Outputs:
%   U : cell array; U{n} is the truncated orthonormal basis for mode n
%   S : truncated core tensor
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<4, coreBackend='fast'; end
if nargin<5, matrixBackend='prepared-tall'; end
assert(any(strcmp(matrixBackend,{'tall','legacy','prepared-tall'})),'Unknown product backend.');
assert(any(strcmp(coreBackend,{'fast','tensorlab'})),...
    'hosvd_randprecond:CoreBackend','Unknown core backend.');
sz_tens = size(T);    perm = 1:length(sz_tens);
N = ndims(T);
U = cell(1,N);
other_modes = cell(1,N);

for n = 1:N
    other_modes{n} = perm([1:n-1, n+1:N]);
end

for n = 1: length(perm)
    % Apply sketching and preconditioning to the mode-n unfolding.
    if strcmp(matrixBackend,'prepared-tall')
        A=tucker_unfold_tall(T,perm(n),'native');
    else
        A = tens2mat(T,perm(n),other_modes{n});
    end
    if nargin < 3 || isempty(sketches)
        U{perm(n)} = randPrecondSVD_Vless(A,r(n),[],matrixBackend);
    else
        U{perm(n)} = randPrecondSVD_Vless(A,r(n),sketches{n},matrixBackend);
    end
    clear A
end

% Contract with the conjugate transpose of each mode basis to obtain the HOSVD core.
if strcmp(coreBackend,'fast')
    S = tucker_core_fast(T,U);
else
    S = tmprod(T,U,1:N,'H');
end

end
