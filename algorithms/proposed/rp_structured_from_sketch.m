function [U,info] = rp_structured_from_sketch(A,Y,r,precision,prepared)
% RP recovery from a supplied sketch.
% Same tall-layout products, truncation and small SVD as production RP.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

clock=tic;
if strcmp(precision,'mixed'), Awork=single(A); unit=double(eps('single'));
else, Awork=double(A); unit=eps; end
if nargin>=5 && prepared, At=Awork; else, At=Awork'; end
[V,D,~]=svd(double(Y),'econ'); sigma=diag(D);
keep=sigma>=2*unit*sigma(1) & sigma>0;
info=struct('retained',nnz(keep),'chol_flag',0,'recovery_s',0);
if ~any(keep), error('probe:Rank','No sketch direction retained.'); end
W=cast(V(:,keep)./sigma(keep)','like',At);
X=At*W;
[R,p]=chol(double(X'*X)); info.chol_flag=p;
if p~=0, error('probe:Cholesky','Cholesky pivot %d.',p); end
B=R*(sigma(keep).*V(:,keep)');
[~,~,U]=svd(B,'econ'); U=U(:,1:min(r,size(U,2)));
% Match production's min(r,retained) return; assess its actual reconstruction.
info.recovery_s=toc(clock);
end
