function Z = contract(Z,Phi,modes,backend)
%CONTRACT Equivalent multi-TTM, preserving original tensor axis order.
ratios=arrayfun(@(j) size(Phi{j},2)/size(Z,j),modes);
[~,order]=sortrows([ratios(:),-modes(:)],[1 2]);
for j=modes(order(:)')
    Z=tucker_mode_product_fast(Z,Phi{j},j,backend);
end
end
