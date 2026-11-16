function [U,info] = randPrecondSVD_mixed(A,r,precision,sketch,backend)
%RANDPRECONDSVD_MIXED RP U-only SVD with single products/double factorizations.
% precision='mixed' (default) or 'double' (instrumented FP64 reference).
% Optional n-by-min(2*m,n) sketch permits an exactly paired comparison.
% The default sketch is the same sparse-sign MEX used by the original RP.
% The input conversion, products and factorizations are timed. A supplied
% sketch excludes the supplied sketch generation.
% backend selects 'tall' (default) or 'legacy'; [] uses the default sketch.
% prepared-tall accepts the physical conjugate transpose of the logical
% short-wide input; the supplied sketch retains its original logical shape.
% Tall layout is shared by sketch, whitening and Gram products. The small
% preconditioner is scaled in double before conversion to working precision.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin < 3, precision = 'mixed'; end
if nargin < 5, backend = 'tall'; end
assert(any(strcmp(backend,{'legacy','tall','prepared-tall'})),'Unknown product backend.');
assert(ismember(precision,{'mixed','double'}),'Unknown precision.');
assert(isreal(A) && ismatrix(A),'This preliminary implementation is real.');
[m,n] = size(A);
if strcmp(backend,'prepared-tall'), [m,n]=deal(n,m); end
assert(r >= 1 && r <= m && r == floor(r),'Invalid target rank.');
clockTotal = tic;
info = struct('status','ok','message','','precision',precision,...
    'input_cast_s',0,'sketch_setup_s',0,'sketch_s',0,'sketch_svd_s',0,...
    'whitening_s',0,'gram_s',0,'small_s',0,'total_s',0,...
    'retained',0,'returned_rank',0,'threshold',0,'chol_flag',0,...
    'backend',backend,'layout_s',0,'chol_s',0,'small_form_s',0,'final_svd_s',0);
clockStage = tic;
if nargin < 4 || isempty(sketch)
    sketch = sparsesign(min(2*m,n),n,8)';
end
info.sketch_setup_s = toc(clockStage);
assert(size(sketch,1)==n && size(sketch,2)>=r,'Invalid sketch size.');
clockStage = tic;
if strcmp(precision,'mixed')
    Awork = single(A);
    Swork = single(sketch);
    unit = double(eps('single'));
else
    Awork = double(A);
    Swork = double(sketch);
    unit = eps;
end
info.input_cast_s = toc(clockStage);
clockStage = tic;
if strcmp(backend,'tall'), Awork=Awork'; end
info.layout_s=toc(clockStage);
clockStage = tic;
if any(strcmp(backend,{'tall','prepared-tall'})), Y=(Swork'*Awork)';
else, Y = Awork*Swork; end
info.sketch_s = toc(clockStage);
clockStage = tic;
[V,D,~] = svd(double(Y),'econ');
sigma = diag(D);
threshold = 2*unit*sigma(1);
keep = sigma >= threshold & sigma > 0;
info.threshold = threshold;
info.retained = nnz(keep);
info.sketch_svd_s = toc(clockStage);
if ~any(keep)
    U = zeros(m,0);
    info.status = 'rank_shortfall';
    info.message = 'No retained sketch direction.';
    info.total_s = toc(clockTotal);
    return;
end
clockStage = tic;
if any(strcmp(backend,{'tall','prepared-tall'}))
    W=cast(V(:,keep)./sigma(keep)','like',Awork);
    X=Awork*W;
elseif strcmp(precision,'mixed')
    X = single(1./sigma(keep)).*(single(V(:,keep))'*Awork);
else
    X = (1./sigma(keep)).*(V(:,keep)'*Awork);
end
info.whitening_s = toc(clockStage);
clockStage = tic;
if any(strcmp(backend,{'tall','prepared-tall'})), G=X'*X;
else, G = X*X'; end
info.gram_s = toc(clockStage);
clockSmall = tic;
clockStage = tic;
[R,p] = chol(double(G));
info.chol_s = toc(clockStage);
info.chol_flag = p;
if p ~= 0
    U = zeros(m,0);
    info.status = 'chol_failure';
    info.message = sprintf('Cholesky failed at pivot %d.',p);
else
    clockStage = tic;
    B = R*(sigma(keep).*V(:,keep)');
    info.small_form_s = toc(clockStage);
    clockStage = tic;
    [~,~,U] = svd(B,'econ');
    U = U(:,1:min(r,size(U,2)));
    info.final_svd_s = toc(clockStage);
    info.returned_rank = size(U,2);
    if size(U,2) < r
        info.status = 'rank_shortfall';
        info.message = 'Precision-dependent truncation retained fewer than r directions.';
    end
end
info.small_s = toc(clockSmall);
info.total_s = toc(clockTotal);
end
