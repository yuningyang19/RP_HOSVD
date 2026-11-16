function [U,core,info] = hosvd_randprecond_mixed(T,r,precision,sketches,coreBackend,matrixBackend)
%HOSVD_RANDPRECOND_MIXED Nonsequential RP-HOSVD with mixed precision.
% All mode bases are double. For 'mixed', the tensor is cast once to single,
% RP large products and the final core contraction use single precision.
% 'double' is the instrumented FP64 reference. Tensorlab is required.
% coreBackend is 'fast' (default) or 'tensorlab' for the previous core path.
% Pass sketches=[] to use the default sketch with an explicit core backend.
% matrixBackend: prepared-tall (default, direct unfolding), tall, or legacy.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin < 3, precision = 'mixed'; end
if nargin < 5, coreBackend = 'fast'; end
if nargin < 6, matrixBackend = 'prepared-tall'; end
assert(any(strcmp(matrixBackend,{'tall','legacy','prepared-tall'})),'Unknown product backend.');
assert(any(strcmp(coreBackend,{'fast','tensorlab'})),...
    'hosvd_randprecond_mixed:CoreBackend','Unknown core backend.');
assert(numel(r)==ndims(T),'One target rank is required per mode.');
clockTotal = tic;
d = ndims(T);
U = cell(1,d);
info = struct('status','ok','input_cast_s',0,'factor_s',0,'core_s',0,...
    'total_s',0,'modes',{{}},'core_class','','core_backend',coreBackend,...
    'matrix_backend',matrixBackend);
clockStage = tic;
if strcmp(precision,'mixed'), Twork = single(T); else, Twork = double(T); end
info.input_cast_s = toc(clockStage);
clockStage = tic;
for j = 1:d
    if strcmp(matrixBackend,'prepared-tall')
        A=tucker_unfold_tall(Twork,j,'native');
    else
        A = tens2mat(Twork,j,[1:j-1 j+1:d]);
    end
    if nargin < 4 || isempty(sketches)
        [U{j},detail] = randPrecondSVD_mixed(A,r(j),precision,[],matrixBackend);
    else
        [U{j},detail] = randPrecondSVD_mixed(A,r(j),precision,sketches{j},matrixBackend);
    end
    clear A
    info.modes{j} = detail;
    if ~strcmp(detail.status,'ok'), info.status = detail.status; end
end
info.factor_s = toc(clockStage);
clockStage = tic;
if any(cellfun(@isempty,U))
    core = [];
else
    if strcmp(precision,'mixed')
        Uwork = cellfun(@single,U,'UniformOutput',false);
    else
        Uwork = U;
    end
    if strcmp(coreBackend,'fast')
        core = tucker_core_fast(Twork,Uwork);
    else
        core = tmprod(Twork,Uwork,1:d,'H');
    end
end
info.core_s = toc(clockStage);
info.total_s = toc(clockTotal);
info.core_class = class(core);
end
