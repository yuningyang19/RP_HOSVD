function p=panels(group,items)
%PANELS Category ordering follows the manuscript, including slow/medium/fast.
p=struct('title',{},'ids',{},'x',{},'xlabel',{});
if strcmp(group,'dimensions')
 for d=3:6
  a=items(cellfun(@(s)numel(s.dims)==d,items));[~,o]=sort(cellfun(@(s)s.dims(1),a));a=a(o);ids=cellfun(@(s)s.settings(1).id,a,'UniformOutput',false);
  p(end+1)=struct('title',sprintf('Order %d',d),'ids',{ids},'x',cellfun(@(s)s.dims(1),a),'xlabel','Mode dimension $n$'); %#ok<AGROW>
 end
elseif strcmp(group,'spectra')
 for kind={'slow','medium','fast'}
  a=items{find(cellfun(@(s)strcmp(s.spectrum,kind{1}),items),1)};st=a.settings;if iscell(st),st=[st{:}];end
  p(end+1)=struct('title',[upper(kind{1}(1)) kind{1}(2:end) ' decay'],'ids',{{st.id}},'x',arrayfun(@(s)s.ranks(1),st),'xlabel','Target rank $r$'); %#ok<AGROW>
 end
elseif strcmp(group,'shapes')
 ids=cellfun(@(s)s.settings(1).id,items,'UniformOutput',false);[ids,o]=sort(ids);
 p=struct('title','Fixed volume','ids',{ids},'x',1:numel(o),'xlabel','Shape');
else
 names={'real-dc-mall','real-miranda','real-cave32'};titles={'DC Mall','Miranda','CAVE'};
 for k=1:3
  a=items{find(cellfun(@(s)strcmp(s.id,names{k}),items),1)};st=a.settings;if iscell(st),st=[st{:}];end
  p(end+1)=struct('title',titles{k},'ids',{{st.id}},'x',arrayfun(@(s)s.rho,st),'xlabel','Target rank ratio $\rho$'); %#ok<AGROW>
 end
end
end
