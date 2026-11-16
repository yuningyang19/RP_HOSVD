function [C,P] = lit_mln(A, R, L, delta)

% A input tensor in tensor format, R vector with the desired approximation
% ranks, L vector with the sizes of the oversamples.

eps = delta*1e-16*norm(A);
N = size(A);
d = length(N);
X = cell(1, d);
Y = cell(1, d);
for i = 1:d
    not_i = N;
    not_i(i) = [];
    X{i} = tuckerbench.sparseSign(R(i),prod(not_i))';
    Y{i} = full(tuckerbench.sparseSign(R(i)+L(i),N(i))');
end

C = ttm(A, Y, 't'); % A times Y_k^T in mode-k for all k.
P = cell(1, d);
for i = 1:d
    not_i = 1:d;
    not_i(i) = [];
    A_iX_i = tenmat(A, i, not_i).data*X{i};
    P{i} =  stable_nystrom_inversion(A_iX_i, Y{i}'*A_iX_i, eps);
end 
% Return native compact factors/core; omit full reconstruction only.