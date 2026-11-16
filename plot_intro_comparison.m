function f=plot_intro_comparison(varargin)
%PLOT_INTRO_COMPARISON Figure 1 from the fixed-volume S01 SS records.
root=fileparts(mfilename('fullpath'));addpath(root);
p=inputParser;p.addParameter('OutputRoot',fullfile(root,'results'));p.addParameter('Visible','off');p.parse(varargin{:});o=p.Results;
files=dir(fullfile(o.OutputRoot,'shapes_paper','records','cp-shape200-S01__H__*.mat'));
assert(~isempty(files),'Run experiments/00_intro_comparison/run_this_experiment.m first.');
rows=struct([]);for k=1:numel(files),q=load(fullfile(files(k).folder,files(k).name),'row');rows=[rows q.row];end %#ok<AGROW>
methods={'SVD','RP-SS','MP-RP-SS','KRP-SS','Shift-SS','Stable-MLN-SS','RTSMS-SS','MSK-SS','MLB-SS'};
labels=erase(methods,'-SS');t=nan(1,9);e=t;
for k=1:9
 q=rows(strcmp({rows.method},methods{k})&strcmp({rows.status},'ok'));assert(~isempty(q),'Missing successful calls for %s.',methods{k});
 t(k)=median([q.seconds]);e(k)=median([q.normalized_error]);
end
excess=e/e(1)-1;[~,ix]=sort(abs(excess));labels=labels(ix);t=t(ix);excess=excess(ix);names=methods(ix);
colors=rpbench.styles();M=rpbench.methods();C=zeros(9,3);
for k=1:9,C(k,:)=colors(find(strcmp({M.name},names{k}),1)).color;end
f=figure('Visible',o.Visible,'Color','w','Units','inches','Position',[1 1 7.5 3.6]);
g=tiledlayout(f,1,4,'TileSpacing','compact','Padding','loose');ax=nexttile(g,1,[1 3]);hold(ax,'on');
b=barh(ax,1:9,t,.59,'FaceColor','flat');b.CData=C;set(ax,'YDir','reverse','YTick',1:9,'YTickLabel',labels,'FontName','Times New Roman','FontSize',10,'Box','off');
xlim(ax,[0 max(t)*1.25]);ylim(ax,[.3 9.6]);xlabel(ax,'Time (s)');title(ax,'HOSVD computation time','FontWeight','normal');grid(ax,'on');ax.YGrid='off';
for k=1:9,text(ax,t(k)+.015*max(t),k,sprintf('%.2f',t(k)),'FontSize',9);end
bx=nexttile(g);hold(bx,'on');ylim(bx,[.3 9.6]);xlim(bx,[0 1]);set(bx,'YDir','reverse');axis(bx,'off');title(bx,'$E/E_{\mathrm{classic}}-1$','Interpreter','latex','FontWeight','normal');
for k=1:9
 v=excess(k);if strcmp(names{k},'RP-SS'),v=abs(v);end
 if v==0,label='$0$';else,power=floor(log10(abs(v)));label=sprintf('$%.2f\\times10^{%d}$',v/10^power,power);end
 text(bx,.5,k,label,'Interpreter','latex','HorizontalAlignment','center','FontSize',10);
end
out=fullfile(o.OutputRoot,'intro_comparison');if ~isfolder(out),mkdir(out);end
exportgraphics(f,fullfile(out,'intro_time_accuracy.pdf'),'ContentType','vector');exportgraphics(f,fullfile(out,'intro_time_accuracy.png'),'Resolution',220);
if strcmp(o.Visible,'off'),close(f);end
end
