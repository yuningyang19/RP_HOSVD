function T=load_real(id,dataRoot,root)
%LOAD_REAL Unchanged DC/Miranda values; original bit-depth scaling for CAVE.
switch id
 case 'real-dc-mall'
  f=dir(fullfile(dataRoot,'dc_mall','**','dc.tif'));assert(numel(f)==1,'Download DC Mall first.');T=double(imread(fullfile(f.folder,f.name)));
 case 'real-miranda'
  f=fullfile(dataRoot,'density.mat');assert(isfile(f),'Download Miranda first.');q=load(f,'density');T=double(q.density);
 case 'real-cave32'
  scenes=jsondecode(fileread(fullfile(root,'config/cave_scenes.json')));T=zeros(512,512,31,32);
  for j=1:32
   for k=1:31
    name=sprintf('%s_%02d.png',scenes{j},k);f=dir(fullfile(dataRoot,'cave','**',name));assert(numel(f)==1,'Missing or ambiguous CAVE band %s.',name);
    [A,map,alpha]=imread(fullfile(f.folder,f.name));assert(isempty(map));
    if ~isempty(alpha),assert(all(alpha(:)==intmax(class(alpha))));end
    if ndims(A)==3,assert(size(A,3)==3 && isequal(A(:,:,1),A(:,:,2)) && isequal(A(:,:,1),A(:,:,3)));A=A(:,:,1);end
    assert(isequal(size(A),[512 512])&&(isa(A,'uint8')||isa(A,'uint16')));T(:,:,k,j)=double(A)/double(intmax(class(A)));
   end
  end
 otherwise,error('RP_HOSVD:Data','Unknown real input %s.',id);
end
end
