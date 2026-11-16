function Y = modeSketches(T,Phi,useTree,backend)
%MODESKETCHES MLB shared-factor all-mode sketches, with binary dimension tree.

d=numel(Phi); Y=cell(1,d);
if useTree
    descend(T,1:d);
else
    for modeIndex=1:d
        other=[1:modeIndex-1 modeIndex+1:d];
        Z=tuckerbench.contract(T,Phi,other,backend);
        Y{modeIndex}=tens2mat(Z,modeIndex,other);
    end
end
    function descend(Z,active)
        if isscalar(active)
            leafMode=active(1);
            Y{leafMode}=tens2mat(Z,leafMode,[1:leafMode-1 leafMode+1:d]); return
        end
        middle=floor(numel(active)/2);
        left=active(1:middle); right=active(middle+1:end);
        next=tuckerbench.contract(Z,Phi,right,backend);
        descend(next,left); clear next
        next=tuckerbench.contract(Z,Phi,left,backend);
        descend(next,right);
    end
end
