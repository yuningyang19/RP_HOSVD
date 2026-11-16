function [U,S] = hosvd_seq(T,r,contractionBackend)
% Sequentially truncated HOSVD (classical ST-HOSVD).
% After processing a mode, immediately compress the current tensor with its basis,
% then process the next mode on the compressed tensor.
%
% Subsequent modes use progressively smaller tensors, typically saving time and memory.
%
% Inputs:
%   T : input tensor
%   r : target rank for each mode
%
% Outputs:
%   U : truncated basis for each mode
%   S : core tensor after sequential compression

% Optional contractionBackend: auto (default), fast, or tensorlab.
if nargin<3, contractionBackend='auto'; end
sz_tens = size(T);    perm = 1:length(sz_tens);  
N = ndims(T);
U = cell(1,N);

% S stores the tensor at the current stage of compression.
S = T;
for n = 1: length(perm)
    % Compute a truncated SVD of the current tensor S along mode n.
    U{perm(n)} = trunSVD(tens2mat(S,perm(n),setdiff(perm,perm(n))),r(n));
    % Immediately compress mode n for the subsequent modes.
    S = tucker_mode_product_fast(S,U{perm(n)},perm(n),contractionBackend);
end



end
