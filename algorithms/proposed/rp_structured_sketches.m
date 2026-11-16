function [Y,stats]=rp_structured_sketches(T,Phi,useTree,policy)
% Same Kronecker factors; storage-aware contractions and optional costed tree.
% The planner minimizes a scalar multiply count model, not measured wall time.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<4,policy='balanced';end
assert(any(strcmp(policy,{'balanced','planned'})),'Unknown tree policy.');
d=numel(Phi);dims=arrayfun(@(j)size(T,j),1:d);
s=cellfun(@(P)size(P,2),Phi);Y=cell(1,d);
plans=cell(1,2^d-1);costs=nan(1,2^d-1);
if strcmp(policy,'planned')
    assert(d<=8,'Planner is bounded to at most eight modes.');
    [tree,estimate]=plan(2^d-1);
else
    tree=balanced(1:d);estimate=treecost(tree,dims);
end
if useTree
    descend(T,tree);
else
    for leafIndex=1:d
        Z=contract(T,[1:leafIndex-1 leafIndex+1:d]);
        Y{leafIndex}=tens2mat(Z,leafIndex,[1:leafIndex-1 leafIndex+1:d]);
    end
end
if nargout>1
    stats=struct('policy',policy,'model_multiply_count',estimate, ...
        'balanced_model_multiply_count',treecost(balanced(1:d),dims), ...
        'tree',tree,'subranks',s);
end
    function descend(Z,node)
        active=node.active;
        if isscalar(active)
            leafMode=active(1);Y{leafMode}=tens2mat(Z,leafMode,[1:leafMode-1 leafMode+1:d]);return;
        end
        next=contract(Z,node.right.active);descend(next,node.left);clear next
        next=contract(Z,node.left.active);descend(next,node.right);
    end
    function Z=contract(Z,modes)
        zdim=arrayfun(@(j)size(Z,j),1:d);order=ordering(zdim,modes);
        for modeIndex=order,Z=rp_structured_contract(Z,Phi{modeIndex},modeIndex);end
    end
    function order=ordering(zdim,modes)
        ratios=s(modes)./zdim(modes);
        [~,ix]=sortrows([ratios(:),-modes(:)],[1 2]);order=modes(ix(:)');
    end
    function [c,zdim]=contractcost(zdim,modes)
        c=0;
        for costMode=ordering(zdim,modes)
            c=c+prod(zdim)*s(costMode);zdim(costMode)=s(costMode);
        end
    end
    function c=treecost(node,zdim)
        if isscalar(node.active),c=0;return;end
        [c1,leftdim]=contractcost(zdim,node.right.active);
        [c2,rightdim]=contractcost(zdim,node.left.active);
        c=c1+c2+treecost(node.left,leftdim)+treecost(node.right,rightdim);
    end
    function node=balanced(active)
        node=struct('active',active,'left',[],'right',[]);
        if numel(active)>1
            k=floor(numel(active)/2);
            node.left=balanced(active(1:k));node.right=balanced(active(k+1:end));
        end
    end
    function [node,c]=plan(mask)
        if ~isnan(costs(mask)),node=plans{mask};c=costs(mask);return;end
        active=find(bitget(mask,1:d));node=struct('active',active,'left',[],'right',[]);
        if isscalar(active),c=0;
        else
            c=Inf;leftmask=bitand(mask-1,mask);zdim=s;zdim(active)=dims(active);
            while leftmask>0
                if bitget(leftmask,active(1))
                    rightmask=bitxor(mask,leftmask);
                    [a,ca]=plan(leftmask);[b,cb]=plan(rightmask);
                    va=contractcost(zdim,b.active);vb=contractcost(zdim,a.active);
                    trial=ca+cb+va+vb;
                    if trial<c,c=trial;node.left=a;node.right=b;end
                end
                leftmask=bitand(leftmask-1,mask);
            end
        end
        plans{mask}=node;costs(mask)=c;
    end
end
