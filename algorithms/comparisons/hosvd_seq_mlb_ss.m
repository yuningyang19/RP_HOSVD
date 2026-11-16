function [U,G,info] = hosvd_seq_mlb_ss(T,r,p,opts)
% Code sources: see ../../THIRD_PARTY.md.
%HOSVD_SEQ_MLB_SS Sequential MLB Kronecker two-stage SS implementation.
if nargin<3 || isempty(p), p=5; end
if nargin<4, opts=struct(); end
opts.Sequential=true;
[U,G,info]=hosvd_mlb_ss(T,r,p,opts);
end
