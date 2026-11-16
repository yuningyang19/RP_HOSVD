# Original data sources

Run `download_real_data` to download and extract the datasets.

- **DC Mall**, 1280 x 307 x 191: [Purdue MultiSpec hyperspectral data](https://engineering.purdue.edu/~biehl/MultiSpec/hyperspectral.html), Hyperspectral_Project.zip. Original integer intensities are converted to double without rescaling.
- **Miranda**, 2048 x 256 x 256: [tensor simulation data repository](https://gitlab.com/tensors/tensor_data_miranda_sim), density.mat, used at original resolution without rescaling.
- **CAVE**, 512 x 512 x 31 x 32: [Columbia CAVE multispectral database](https://cave.cs.columbia.edu/repository/Multispectral), complete_ms_data.zip. Scenes are stacked in config/cave_scenes.json order; intensities are divided by the maximum representable value of their PNG storage type.

Download URLs and expected SHA256 hashes are in download_real_data.m. Please follow the original providers' attribution and use conditions. An existing extracted dataset may be provided through `DataRoot`; see +rpbench/load_real.m for its folder layout.
