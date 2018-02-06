import perf_plotter as pp

pp.plotter('../SIMD_Vecwidth_comparison.pdf', show=False,
    cores='1', order='C', vectype='w', rates='hybrid', kernel='split')