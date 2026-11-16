function [ratio,table] = rp_mixed_svd_switch_ratio(n,policy)
%RP_MIXED_SVD_SWITCH_RATIO Lookup the direct FP64 econ-SVD / mixed RP aspect-ratio cutoff.
% Default calibration: Apple M3 Ultra, MATLAB R2025a, max threads 32,
% Full-rank double inputs, n=50:50:3000; randPrecondSVD_mixed tall backend
% with default sparse-sign sketch (8 nonzeros, s=min(2n,M)). Includes casts
% and sketch construction. A preconverted-single workload needs its own profile.
% Calibration: MATLAB R2025a, Apple M3 Ultra, 32 threads; see docs/EXPERIMENTS.md.
% Table column 1 is an upper short-side dimension; column 2 is the largest
% aspect ratio assigned to direct SVD. Intermediate n uses the next larger
% calibrated dimension. Above the last row, use the last cutoff as a default.
% A scalar policy overrides lookup; a two-column policy replaces the table.
% These are configurable performance choices, not embedding/error thresholds.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

validateattributes(n,{'numeric'},{'real','scalar','integer','positive','finite'});
if nargin < 2 || isempty(policy)
    table = [
        50 128;
        100 96;
        150 96;
        200 48;
        250 48;
        300 32;
        350 64;
        400 48;
        450 24;
        500 16;
        550 16;
        600 32;
        650 32;
        700 32;
        750 24;
        800 16;
        850 24;
        900 24;
        950 24;
        1000 16;
        1050 24;
        1100 32;
        1150 32;
        1200 24;
        1250 32;
        1300 24;
        1350 24;
        1400 24;
        1450 24;
        1500 24;
        1550 24;
        1600 32;
        1650 24;
        1700 32;
        1750 24;
        1800 16;
        1850 32;
        1900 32;
        1950 24;
        2000 48;
        2050 24;
        2100 16;
        2150 24;
        2200 16;
        2250 24;
        2300 32;
        2350 16;
        2400 24;
        2450 24;
        2500 24;
        2550 24;
        2600 24;
        2650 24;
        2700 16;
        2750 24;
        2800 24;
        2850 24;
        2900 24;
        2950 24;
        3000 16;
    ];
else
    validateattributes(policy,{'numeric'},{'real','nonempty','nonnan'});
    if isscalar(policy)
        validateattributes(policy,{'numeric'},{'nonnegative'});
        ratio = policy;
        table = [];
        return;
    end
    if ~ismatrix(policy) || size(policy,2)~=2 || any(~isfinite(policy(:,1))) || ...
            any(policy(:,1)<=0) || any(diff(policy(:,1))<=0) || any(policy(:,2)<0)
        error('randPrecond:InvalidSwitchTable', ...
            'The switch table must have increasing positive dimensions and nonnegative ratios.');
    end
    table = policy;
end
k = find(n <= table(:,1),1);
if isempty(k)
    k = size(table,1);
end
ratio = table(k,2);
end
