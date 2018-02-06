import perf_plotter as pp

pp.plotter('../SIMD_scaling.pdf', show=False,
    order='C', vectype='w', vecwidth='16', rates='hybrid', kernel='split',
    minx=0)

pp.plotter('../SIMT_scaling.pdf', show=False,
    order='C', vectype='par', vecwidth='16', rates='hybrid', kernel='split',
    minx=0)