function run_smoke_tests
%RUN_SMOKE_TESTS Check each method on a small tensor.
root=fileparts(fileparts(mfilename('fullpath')));addpath(root);setup_rp_hosvd;
pilot_srand(321);A=tuckerbench.sparseSign(10,17);pilot_srand(321);B=sparsesign(10,17,8);assert(isequal(A,B),'SS adapter and native generator outputs differ.');
rng(710,'twister');T=randn(12,13,14);r=[3 3 3];M=rpbench.methods();
for frame={'H','ST'}
 for j=1:numel(M)
  rng(710,'twister');pilot_srand(710);
  [U,G]=rpbench.dispatch(T,r,M(j).name,frame{1});
  e=rpbench.reconstruction_error(T,U,G);
  assert(isfinite(e)&&all(cellfun(@(Q)size(Q,2),U)==r));
  fprintf('PASS %s %s\n',frame{1},M(j).name);
 end
end
fprintf('All 32 method/framework checks passed.\n');
end
