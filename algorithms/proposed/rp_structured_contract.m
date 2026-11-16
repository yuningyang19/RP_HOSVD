function Z=rp_structured_contract(Z,P,j)
% Use the existing contiguous last-mode GEMM rather than a permuted unfolding.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if prod(arrayfun(@(k)size(Z,k),j+1:ndims(Z)))==1
    Z=tucker_mode_product_fast(Z,P,j,'fast');
else
    Z=tucker_mode_product_fast(Z,P,j,'auto');
end
end
