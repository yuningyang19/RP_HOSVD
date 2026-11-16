function [U,S,info] = hosvd_seq_randprecond(T,r,svd_ratio,contractionBackend,matrixBackend)
% Sequential randomized preconditioned HOSVD.
% At each step, extract the dominant left singular subspace of the current mode
% from the partially compressed tensor, combining two benefits:
% 1. Progressively smaller problems through sequential compression.
% 2. Stability through randomized preconditioning.
%
% Inputs:
%   T : input tensor
%   r : target rank for each mode
%   svd_ratio : optional scalar or two-column table [mode dimension, switch aspect ratio].
%               By default, query the machine-calibrated table in rp_svd_switch_ratio.
%               Use a direct economy SVD when unfolding columns/rows is at most the threshold.
%               Scalar 0 forces RP; Inf forces a direct SVD.
%   contractionBackend : 'auto' (default), 'fast', or 'tensorlab'.
%               auto uses pagemtimes for suitable intermediate modes to limit repeated permutations.
%
% matrixBackend: prepared-tall (default), tall, or legacy.
% prepared-tall changes layout only; existing SVD policies are retained.
%
% Outputs:
%   U : truncated basis for each mode
%   S : core tensor after sequential compression
%   info : optional per-mode dimensions, selected methods, and kernel timings
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin < 3, svd_ratio = []; end
if nargin < 4, contractionBackend = 'auto'; end
if nargin<5, matrixBackend='prepared-tall'; end
assert(any(strcmp(matrixBackend,{'tall','legacy','prepared-tall'})),'Unknown product backend.');
assert(any(strcmp(contractionBackend,{'auto','fast','tensorlab'})), ...
    'hosvd_seq_randprecond:Backend','Unknown contraction backend.');
% Validate a supplied policy before processing the tensor.
rp_svd_switch_ratio(size(T,1),svd_ratio);

sz_tens = size(T);    perm = 1:length(sz_tens);  
N = ndims(T);
U = cell(1,N);
info = struct('mode',cell(1,N),'rows',[],'cols',[],'ratio',[], ...
    'threshold',[],'method',[],'kernel_seconds',[], ...
    'contraction_backend',[],'contraction_seconds',[]);
other_modes = cell(1,N);

for n = 1:N
    other_modes{n} = perm([1:n-1, n+1:N]);
end

S = T;
for n = 1: length(perm)
    if strcmp(matrixBackend,'prepared-tall')
        nrows=size(S,perm(n)); ncols=numel(S)/nrows;
    else
        C=tens2mat(S,perm(n),other_modes{n}); [nrows,ncols]=size(C);
    end
    threshold = rp_svd_switch_ratio(nrows,svd_ratio);
    if nargout > 2, kernel_start = tic; end
    if ncols/nrows <= threshold
        if strcmp(matrixBackend,'prepared-tall'), C=tens2mat(S,perm(n),other_modes{n}); end
        [Un,~,~] = svd(C,'econ');
        U{perm(n)} = Un(:,1:min(r(n),size(Un,2)));
        method = 'svd';
    else
        if strcmp(matrixBackend,'prepared-tall'), C=tucker_unfold_tall(S,perm(n),'native'); end
        U{perm(n)} = randPrecondSVD_Vless(C,r(n),[],matrixBackend);
        method = 'rp';
    end
    if nargout > 2
        info(n).mode = perm(n);
        info(n).rows = nrows;
        info(n).cols = ncols;
        info(n).ratio = ncols/nrows;
        info(n).threshold = threshold;
        info(n).method = method;
        info(n).kernel_seconds = toc(kernel_start);
    end
    clear C
    % Compress the current mode to reduce the size of subsequent computations.
    if nargout > 2, contraction_start = tic; end
    [S,usedBackend] = tucker_mode_product_fast(S,U{perm(n)},perm(n),contractionBackend);
    if nargout > 2
        info(n).contraction_backend = usedBackend;
        info(n).contraction_seconds = toc(contraction_start);
    end
end



end
