function z=error_scale(y)
%ERROR_SCALE Signed logarithmic scale with zero retained (linear near zero).
z=sign(y).*log10(1+abs(y)/1e-6);
end
