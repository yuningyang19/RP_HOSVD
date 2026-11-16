function s = rp_probe_subranks(dims,targets,shared,mode)
% Shared: MLB ceil heuristic with RP targets min(2*n_j,M_j), not r_j+p.
% Sequential: balanced per-stage factors, capped by current mode sizes.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

d=numel(dims);
if shared
    s=min(dims,ceil(exp(sum(log(targets))/(d-1)-log(targets))));
    while any(prod(s)./s<targets)
        bad=find(prod(s)./s<targets,1);
        available=find((1:d)~=bad & s<dims);
        assert(~isempty(available),'probe:Subranks','Cannot meet sketch size.');
        [~,k]=min(s(available)); s(available(k))=s(available(k))+1;
    end
else
    s=min(dims,ceil(targets^(1/(d-1)))*ones(1,d)); s(mode)=dims(mode);
    other=[1:mode-1 mode+1:d];
    while prod(s(other))<targets
        available=other(s(other)<dims(other));
        [~,k]=min(s(available)); s(available(k))=s(available(k))+1;
    end
end
end
