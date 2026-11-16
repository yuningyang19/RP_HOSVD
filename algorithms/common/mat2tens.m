function T=mat2tens(C,sz,k)
p=[k,1:k-1,k+1:numel(sz)];T=ipermute(reshape(C,sz(p)),p);
end
