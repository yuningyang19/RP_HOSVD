function [U,S] = hosvd_classical(T,r,svdtype)
% Classical HOSVD.
% Independently compute a truncated SVD of each mode unfolding of tensor T.
% Use the dominant left singular vectors as mode bases, then form the core tensor.
%
% Each mode unfolding is formed from the original tensor T, so the mode
% decompositions are independent.
%
% Inputs:
%   T       : input tensor
%   r       : target rank for each mode
%   svdtype : function handle for the truncated subspace, e.g., @trunSVD or @rSVD
%
% Outputs:
%   U : cell array; U{n} is the truncated basis for mode n
%   S : HOSVD core tensor

sz_tens = size(T);    perm = 1:length(sz_tens);  
N = ndims(T);
U = cell(1,N);

for n = 1: length(perm)
    % Independently compute a truncated SVD of the original tensor's mode-n unfolding.
    U{perm(n)} = svdtype(tens2mat(T,perm(n),setdiff(perm,perm(n))),r(n));
end

% Compress the original tensor with all mode bases to obtain the core.
S = tmprod(T,U,1:N,'H');

end
