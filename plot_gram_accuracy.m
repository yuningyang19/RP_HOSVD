function fig = plot_gram_accuracy(data)
    colors = [0.34,0.38,0.43; 0.77,0.30,0.27; 0.03,0.50,0.55];
    styles = {'--','-','-'};
    markers = {'none','s','o'};
    fig = figure('Color','w', 'Position',[90,150,920,390], ...
        'Name','Gram and RP accuracy', 'NumberTitle','off');
    layout = tiledlayout(fig,1,2, TileSpacing='compact', Padding='compact');
    for panel = 1:2
        ax = nexttile(layout);
        hold(ax,'on');
        set(ax, 'YScale','log', 'FontName','Times New Roman', ...
            'FontSize',14, 'LineWidth',0.8, 'Box','on', ...
            'TickLabelInterpreter','tex', 'XTickLabelRotation',0, 'YGrid','on', ...
            'GridAlpha',0.12, 'XMinorGrid','off', 'YMinorGrid','off');
        if panel == 1
            xAxis = data.prescribedSpectrum.';
            values = data.spectralErrors;
            set(ax, 'XScale','log', 'XDir','reverse');
            xlim(ax,[1e-14,1]);
            ylim(ax,[1e-17,1e5]);
            xticks(ax,10.^(-14:2:0));
            yticks(ax,10.^(-16:4:4));
            xlabel(ax,'Prescribed singular value $\sigma_i$', Interpreter='latex');
            ylabel(ax,'$|\widehat\sigma_i-\sigma_i|/\sigma_i$', Interpreter='latex');
            title(ax,'(a) Singular-value accuracy', FontWeight='normal');
        else
            xAxis = data.ranks;
            values = data.projectionRatios;
            xlim(ax,[data.ranks(1),data.ranks(end)]);
            ylim(ax,[0.8,1e6]);
            xticks(ax,data.ranks);
            yticks(ax,10.^(0:6));
            xlabel(ax,'Target rank $r$', Interpreter='latex');
            ylabel(ax,'$\|A-A\widehat V_r\widehat V_r^{\mathrm{T}}\|_F/\tau_{r+1}(A)$', ...
                Interpreter='latex');
            title(ax,'(b) Low-rank projection accuracy', FontWeight='normal');
        end
        handles = gobjects(1,3);
        plotOrder = 1:3;
        if panel == 2
            plotOrder = [2,3,1]; % Show dashed SVD over the overlapping RP line.
        end
        for method = plotOrder
            bands = empiricalQuantiles(values(:,:,method),[0.2,0.5,0.8]);
            % The floor affects the logarithmic display only, not stored data.
            bands = max(bands,1e-17);
            fill(ax,[xAxis,fliplr(xAxis)], ...
                [bands(1,:),fliplr(bands(3,:))],colors(method,:), ...
                FaceAlpha=0.12, EdgeColor='none', HandleVisibility='off');
            marker = markers{method};
            markerIndices = 1:4:numel(xAxis);
            lineWidth = 1.5;
            if panel == 2
                markerIndices = 1:numel(xAxis);
                if method == 1
                    marker = '^';
                    markerIndices = 1:2:numel(xAxis);
                    lineWidth = 1.3;
                elseif method == 3
                    markerIndices = 2:2:numel(xAxis);
                    lineWidth = 2.1;
                end
            end
            handles(method) = plot(ax,xAxis,bands(2,:), ...
                Color=colors(method,:), LineStyle=styles{method}, ...
                LineWidth=lineWidth, Marker=marker, MarkerSize=5, ...
                MarkerIndices=markerIndices, MarkerFaceColor='white');
        end
        legend(ax,handles,data.methods,Location='northwest', ...
            Box='off', FontSize=13, Interpreter='none');
    end
end

function result = empiricalQuantiles(values, probabilities)
    % Linear interpolation of sorted observations; no statistics toolbox.
    ordered = sort(values,1);
    locations = 1+(size(values,1)-1)*probabilities;
    result = zeros(numel(probabilities),size(values,2));
    for k = 1:numel(probabilities)
        low = floor(locations(k));
        high = ceil(locations(k));
        weight = locations(k)-low;
        result(k,:) = (1-weight)*ordered(low,:)+weight*ordered(high,:);
    end
end
