function specs=specs(group,profile,root)
%SPECS Current paper inputs only: 40 dimension, 3 spectrum, 10 shape, 3 real.
a=jsondecode(fileread(fullfile(root,'config/paper_inputs.json')));if ~iscell(a),a=num2cell(a);end
specs=a(cellfun(@(s)strcmp(s.group,group),a));
if strcmp(profile,'smoke')
 if strcmp(group,'real'),return;end
 if strcmp(group,'dimensions'),orders=3:6;else,orders=4;end
 out={};
 for d=orders
  s=specs{find(cellfun(@(x)numel(x.dims)==d,specs),1)};s.id=sprintf('smoke-%s-d%d',group,d);s.dims=12*ones(1,d);s.K=12;s.normalizer=1;
  s.settings=struct('id',s.id,'ranks',3*ones(1,d));out{end+1}=s; %#ok<AGROW>
 end
 if strcmp(group,'spectra')
  kinds={'slow','medium','fast'};for k=1:3,out{k}=out{1};out{k}.id=['smoke-spectra-' num2str(k)];out{k}.spectrum=kinds{k};out{k}.settings.id=out{k}.id;end
 end
 specs=out;
end
end
