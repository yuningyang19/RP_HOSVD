function R = randPrecondQR_qless(A, sketch, backend)
% Stable randomized preconditioned QR, returning only the small factor without forming Q.
%
% Construct a small factor R for A' such that A' = Q * R with orthonormal columns in Q.
% HOSVD unfoldings A are often short and wide, making a direct full decomposition
% of A or A' expensive. A random sketch first compresses the column dimension,
% then stabilization steps recover a small factor R for the original problem.
%
% Inputs:
%   A : m-by-n matrix, typically with m << n
%   sketch : optional n-by-sketch_size matrix for paired comparisons with a fixed sketch
%   backend : 'tall' (default) or 'legacy'; sketch=[] uses the default SS sketch
%
% prepared-tall: A is already the physical n-by-m conjugate transpose.
% The sketch still has the original logical n-by-sketch_size shape.
%
% Outputs:
%   R : small factor in A' = Q * R. An SVD of R recovers the dominant
%       left singular vectors of A.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<3, backend='tall'; end
assert(any(strcmp(backend,{'legacy','tall','prepared-tall'})),'Unknown product backend.');
[m,n] = size(A);
if strcmp(backend,'prepared-tall'), [m,n]=deal(n,m); end
% Use an O(m) sketch dimension for very wide matrices.
sketch_size = min([2*m n]);

% S = randn(s,m); 
% SA = S*A;

% AS = A(:,randperm(size(A, 2), sketch_size));  % randomly select s columns
% AS = A*sprandn(sketch_size,size(A,2),8/sketch_size)';
if nargin < 2 || isempty(sketch)
    sketch = sparsesign(sketch_size,n,8)';
end
if strcmp(backend,'prepared-tall')
    At=A;
    AS=(sketch'*At)';
elseif strcmp(backend,'tall')
    At=A';
    AS=(sketch'*At)';
else
    AS = A*sketch;
end
% AS = A*sparsesign(size(A,2),s,8);   % sparsesign; from epperly's github https://github.com/eepperly/Iterative-Sketching-Is-Stable
% AS = A*sprand()
% as fast as uniformly selecting columns from A

% SA = SAviaCountSketch(A,s);

% [~,RR] = qr(AS','econ');
% X = RR'\A;


% Compute an economy SVD of the sketch AS directly, avoiding an explicit transpose.
% If AS = V * S * W', V contains the right singular vectors returned by svd(AS').
[V,S,~] = svd(AS,'econ');
% Truncate tiny singular values to limit roundoff amplification during inverse scaling.
sigma = diag(S);
ee = 2 * eps * sigma(1);
idx = sigma >= ee;
if any(strcmp(backend,{'tall','prepared-tall'}))
    % Reuse the tall matrix layout and apply scaling to the small preconditioner.
    X = At*(V(:,idx)./sigma(idx)');
    R1 = chol(X'*X);
else
    ss = 1 ./ sigma(idx);
    Y = V(:,idx)' * A;
    X = ss .* Y;
    R1 = chol(X*X');
end

%%R = R1*(sigma.*V');

R = R1*(sigma(idx).*V(:,idx)');    % R from the SVD-based construction

 % R = R1*RR';          % corrs. to qr type

end
