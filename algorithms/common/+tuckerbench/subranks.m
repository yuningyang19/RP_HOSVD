function a = subranks(dims,target,shared,mode)
%SUBRANKS MLB shared-factor formula or bounded integer-factor stage heuristic.
% Original: Minster--Li--Ballard, arXiv:2211.13028v2, sections 4.2--4.3.
d=numel(dims);
if shared
    x=nthroot(prod(target),d-1)./target;
    nearest=round(x); close=abs(x-nearest)<=32*eps(max(1,abs(x)));
    x(close)=nearest(close); a=max(1,min(dims,ceil(x)));
    while any(prod(a)./a<target)
        bad=find(prod(a)./a<target,1);
        eligible=find((1:d)~=bad & a<dims);
        assert(~isempty(eligible),'tuckerbench:Subranks','Unattainable widths.');
        [~,k]=min(a(eligible)); a(eligible(k))=a(eligible(k))+1;
    end
    return
end
other=[1:mode-1 mode+1:d]; caps=dims(other);
x=nthroot(target,d-1); nearest=round(x);
if abs(x-nearest)<=32*eps(max(1,abs(x))), x=nearest; end
balanced=max(1,min(caps,ceil(x)));
while prod(balanced)<target
    eligible=find(balanced<caps);
    [~,k]=min(balanced(eligible)); balanced(eligible(k))=balanced(eligible(k))+1;
end
% Adjust the nominal width upwards only if its integer factors do not fit.
% This implements the paper's factorization heuristic, rather than forcing
% all d-1 subranks to ceil(target^(1/(d-1))) and inflating small-rank sketches.
for width=target:prod(balanced)
    trial=ones(1,d-1); primes=sort(factor(width),'descend'); feasible=true;
    for prime=primes
        eligible=find(trial*prime<=caps);
        if isempty(eligible), feasible=false; break; end
        [~,k]=min(trial(eligible)./caps(eligible));
        trial(eligible(k))=trial(eligible(k))*prime;
    end
    if feasible, a=dims; a(other)=trial; return; end
end
a=dims; a(other)=balanced;
end
