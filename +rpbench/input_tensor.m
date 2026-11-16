function T=input_tensor(spec,dataRoot,root)
%INPUT_TENSOR Regenerate synthetic input from seeds, or load original real data.
if strcmp(spec.group,'real'),T=rpbench.load_real(spec.id,dataRoot,root);return;end
stream=RandStream('mt19937ar','Seed',spec.factor_seed);F=cell(1,numel(spec.dims));
for j=1:numel(F),[F{j},~]=qr(randn(stream,spec.dims(j),spec.K),0);end
x=0:spec.K-1;scale=299/max(1,spec.K-1);
switch spec.spectrum
 case 'slow',w=1./(x+1);
 case 'medium',w=exp(-.02*scale*x);
 case 'fast',w=exp(-.06*scale*x);
end
w=w/norm(w);F{1}=F{1}.*w;T=cpdgen(F)/spec.normalizer;
end
