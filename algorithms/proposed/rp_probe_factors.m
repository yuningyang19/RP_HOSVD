function Phi = rp_probe_factors(dims,s,family,workingClass)
% Reproducible small factors: n_j-by-s_j, used as Phi{j}' in contractions.
% Sparse sign: min(8,s_j) distinct signed entries per input coordinate.
% Store small factors dense to use existing pagemtimes/GEMM helper.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

d=numel(dims); Phi=cell(1,d);
for j=1:d
    if strcmp(family,'gaussian')
        P=randn(dims(j),s(j))/sqrt(s(j));
    else
        z=min(8,s(j)); P=zeros(dims(j),s(j));
        for i=1:dims(j)
            idx=randperm(s(j),z);
            P(i,idx)=(2*randi(2,1,z)-3)/sqrt(z);
        end
    end
    Phi{j}=cast(P,workingClass);
end
end
