function figures=plot_experiment(group,varargin)
%PLOT_EXPERIMENT Generate the two Section 6 curve figures for one category.
% Reads measurement records from the selected result directory.
root=fileparts(mfilename('fullpath'));addpath(root);
p=inputParser;p.addParameter('Profile','paper',@ischar);p.addParameter('OutputRoot',fullfile(root,'results'),@(x)ischar(x)||isstring(x));p.addParameter('Visible','off',@ischar);p.parse(varargin{:});o=p.Results;
base=fullfile(char(o.OutputRoot),[group '_' o.Profile]);files=dir(fullfile(base,'records','*.mat'));assert(~isempty(files),'No local records found. Run this experiment first.');
records=struct([]);for k=1:numel(files),q=load(fullfile(files(k).folder,files(k).name),'row');records=[records q.row];end %#ok<AGROW>
items=rpbench.specs(group,o.Profile,root);panels=rpbench.panels(group,items);methods=rpbench.methods();styles=rpbench.styles();figures=cell(1,2);
for fi=1:2
 frame={'H','ST'};frame=frame{fi};height=2.05*numel(panels)+.85;
 f=figure('Visible',o.Visible,'Color','w','Units','inches','Position',[1 1 8 height]);figures{fi}=f;
 layout=tiledlayout(f,numel(panels),2,'TileSpacing','compact','Padding','compact');handles=gobjects(1,numel(methods));insetData=cell(1,numel(panels));
 for pi=1:numel(panels)
  panel=panels(pi);x=panel.x;centers=nan(numel(methods),numel(x));
  for metric=1:2
   ax=nexttile(layout);hold(ax,'on');set(ax,'FontName','Times New Roman','FontSize',8,'Box','on','TickDir','in','XGrid','on','YGrid','on','GridAlpha',.13,'LineWidth',.7);
   for mi=1:numel(methods)
    name=methods(mi).name;y=nan(size(x));lo=y;hi=y;
    for xi=1:numel(x)
     here=records(strcmp({records.setting_id},panel.ids{xi})&strcmp({records.framework},frame));
     refs=here(strcmp({here.method},'SVD')&strcmp({here.status},'ok'));
     if isempty(refs),continue;end
     a=here(strcmp({here.method},name));
     if metric==1
      a=a(strcmp({a.status},'ok')&isfinite([a.seconds])&[a.seconds]>0);v=median([refs.seconds])./[a.seconds];
     else
      a=a(isfinite([a.normalized_error]));v=[a.normalized_error]/median([refs.normalized_error])-1;
     end
     if isempty(v),continue;end
     y(xi)=median(v);
     if numel(v)==5 && ~strcmp(group,'real'),q=quantile(v,[.2 .8]);lo(xi)=q(1);hi(xi)=q(2);end
    end
    if metric==2,centers(mi,:)=y;end
    st=styles(mi);color=st.color;if ~methods(mi).proposed && ~methods(mi).classical,color=.55+.45*color;end
    lw=.8;ms=3;if methods(mi).proposed,lw=1.8;ms=4;end
    yy=y;ll=lo;hh=hi;if metric==2,yy=rpbench.error_scale(y);ll=rpbench.error_scale(lo);hh=rpbench.error_scale(hi);end
    good=isfinite(ll)&isfinite(hh);
    if nnz(good)>1,fill(ax,[x(good) fliplr(x(good))],[ll(good) fliplr(hh(good))],color,'FaceAlpha',.08,'EdgeColor','none','HandleVisibility','off');end
    h=plot(ax,x,yy,'Color',color,'Marker',st.marker,'LineStyle',st.line,'LineWidth',lw,'MarkerSize',ms,'DisplayName',name);
    if methods(mi).proposed,set(h,'MarkerFaceColor','w');end
    if pi==1&&metric==1,handles(mi)=h;end
   end
   if metric==1,set(ax,'YScale','log','YMinorGrid','off');ylabel(ax,'Speedup');yline(ax,1,'--','Color',[.35 .38 .42],'HandleVisibility','off');
   else
    rpbench.error_ticks(ax,centers);ylabel(ax,'$E/E_{\mathrm{classic}}-1$','Interpreter','latex');yline(ax,0,'--','Color',[.35 .38 .42],'HandleVisibility','off');
    insetData{pi}=struct('ax',ax,'x',x,'y',centers(2:5,:),'group',group);
   end
   if numel(x)>1,xlim(ax,[min(x) max(x)]+[-1 1]*.025*(max(x)-min(x)));end
   xlabel(ax,panel.xlabel,'Interpreter','latex');
   t=title(ax,sprintf('(%c) %s',char(97+2*(pi-1)+metric-1),panel.title),'FontWeight','normal','FontSize',9);t.Units='normalized';t.Position(1)=0;t.HorizontalAlignment='left';
   if strcmp(group,'shapes'),xticks(ax,x);xticklabels(ax,compose('S%02d',x));xtickangle(ax,35);end
  end
 end
 lg=legend(handles,{methods.name},'NumColumns',5,'Interpreter','none','FontSize',7,'Box','off');lg.Layout.Tile='north';
 drawnow;
 for pi=1:numel(insetData),rpbench.add_inset(f,insetData{pi},styles(2:5));end
 stem=fullfile(base,[group '_' lower(frame)]);
 exportgraphics(f,[stem '.pdf'],'ContentType','vector');exportgraphics(f,[stem '.png'],'Resolution',180);
 if strcmp(o.Visible,'off'),close(f);end
end
end
