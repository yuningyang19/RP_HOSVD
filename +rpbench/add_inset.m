function add_inset(fig,data,styles)
%ADD_INSET Four proposed curves in physical error units, thick lines and arrow.
valid=find(any(isfinite(data.y),1));if isempty(valid),return;end
idx=valid(max(1,end-3):end);x=data.x(idx);y=data.y(:,idx);v=y(isfinite(y));if isempty(v),return;end
peak=max(abs(v));power=floor(log10(max(peak,1e-16)));scale=10^power;y=y/scale;
pos=data.ax.Position;bounds=[pos(1)+.45*pos(3),pos(2)+.19*pos(4),.52*pos(3),.37*pos(4)];
z=axes(fig,'Position',bounds,'Color','w','FontName','Times New Roman','FontSize',8,'Box','on','TickDir','in','LineWidth',.6);hold(z,'on');
for k=1:4,plot(z,x,y(k,:),'Color',styles(k).color,'Marker',styles(k).marker,'MarkerFaceColor','w','LineWidth',1.8,'MarkerSize',3);end
if numel(x)>1,xlim(z,[min(x) max(x)]);end
v=y(isfinite(y));span=max(.3,max(v)-min(v));ylim(z,[min(0,min(v))-.08*span,max(v)+.45*span]);
text(z,.5,.96,sprintf('Zoom ($\\times10^{%d}$)',power),'Units','normalized','Interpreter','latex','HorizontalAlignment','center','VerticalAlignment','top','FontSize',8,'BackgroundColor','w','Margin',.2);
if strcmp(data.group,'shapes'),xticks(z,x);xticklabels(z,compose('S%02d',x));end
% A figure-level arrow is drawn after the curves and cannot be hidden by them.
annotation(fig,'arrow',[bounds(1)+.55*bounds(3),pos(1)+.82*pos(3)],[bounds(2)-.005,pos(2)+.035*pos(4)],'LineWidth',1.4,'HeadLength',7,'HeadWidth',7,'Color',[.2 .2 .2]);
end
