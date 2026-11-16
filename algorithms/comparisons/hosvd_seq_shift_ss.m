function [U,G,info] = hosvd_seq_shift_ss(T,r,p,q,opts)
% Code sources: see ../../THIRD_PARTY.md.
%HOSVD_SEQ_SHIFT_SS Che et al. Algorithm 4, with ordinary SS projection.
if nargin<3 || isempty(p), p=10; end
if nargin<4 || isempty(q), q=1; end
if nargin<5, opts=struct(); end
opts.Sequential=true;
[U,G,info]=hosvd_shift_ss(T,r,p,q,opts);
end
