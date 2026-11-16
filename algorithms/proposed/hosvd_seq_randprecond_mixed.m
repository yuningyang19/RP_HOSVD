function [U,S,info] = hosvd_seq_randprecond_mixed(T,r,precision,svd_ratio,contractionBackend,matrixBackend)
%HOSVD_SEQ_RANDPRECOND_MIXED Sequential RP with the precision-specific lookup.
% precision: mixed (default) or double. Below the corresponding aspect-ratio
% cutoff use direct double econ-SVD; above it use the selected RP kernel.
% In mixed mode contractions use single and factors remain double. The actual
% returned core is single.
% Default tall calls retain the lookup's double-input calibration contract.
% Optional prepared-tall avoids the redundant double/single conversion in RP;
% direct econ-SVD still receives the same double unfolding. Performance switch
% tables select the kernel according to the unfolding aspect ratio.
% The tables compare the selected RP kernel with SVD.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<3, precision='mixed'; end
if nargin<4, svd_ratio=[]; end
if nargin<5, contractionBackend='auto'; end
if nargin<6, matrixBackend='prepared-tall'; end
assert(any(strcmp(matrixBackend,{'tall','legacy','prepared-tall'})),'Unknown product backend.');
assert(any(strcmp(precision,{'mixed','double'})), ...
    'hosvd_seq_randprecond_mixed:Precision','Unknown precision.');
assert(isreal(T) && isfloat(T) && ~issparse(T), ...
    'hosvd_seq_randprecond_mixed:Input','A real floating tensor is required.');
assert(numel(r)==ndims(T),'One target rank is required per mode.');
if strcmp(precision,'double')
    [U,S,info]=hosvd_seq_randprecond(double(T),r,svd_ratio,contractionBackend,matrixBackend);
    return;
end
assert(any(strcmp(contractionBackend,{'auto','fast','tensorlab'})), ...
    'hosvd_seq_randprecond_mixed:Backend','Unknown contraction backend.');
rp_mixed_svd_switch_ratio(size(T,1),svd_ratio);
d=ndims(T); U=cell(1,d); S=T;
info=struct('mode',cell(1,d),'rows',[],'cols',[],'ratio',[], ...
    'threshold',[],'method',[],'kernel_seconds',[], ...
    'contraction_backend',[],'contraction_seconds',[], ...
    'kernel_input_cast_seconds',[],'detail',[]);
for j=1:d
    castClock=tic;
    n=size(S,j); M=numel(S)/n;
    cutoff=rp_mixed_svd_switch_ratio(n,svd_ratio);
    if strcmp(matrixBackend,'prepared-tall') && M/n>cutoff
        C=tucker_unfold_tall(S,j,'mixed');
    else
        C=double(tens2mat(S,j,[1:j-1,j+1:d]));
    end
    castSeconds=toc(castClock);
    clock=tic;
    if M/n<=cutoff
        [V,~,~]=svd(C,'econ');
        U{j}=V(:,1:min(r(j),size(V,2)));
        method='svd'; detail=[];
    else
        [U{j},detail]=randPrecondSVD_mixed(C,r(j),'mixed',[],matrixBackend);
        method='mp-rp';
        assert(strcmp(detail.status,'ok'), ...
            'hosvd_seq_randprecond_mixed:Kernel','Mixed RP did not complete: %s',detail.message);
    end
    kernelSeconds=toc(clock); clear C
    clock=tic;
    [S,usedBackend]=tucker_mode_product_fast(single(S),single(U{j}),j,contractionBackend);
    contractionSeconds=toc(clock);
    info(j)=struct('mode',j,'rows',n,'cols',M,'ratio',M/n, ...
        'threshold',cutoff,'method',method,'kernel_seconds',kernelSeconds, ...
        'contraction_backend',usedBackend,'contraction_seconds',contractionSeconds, ...
        'kernel_input_cast_seconds',castSeconds,'detail',detail);
end
end
