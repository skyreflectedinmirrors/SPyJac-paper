# a single consolidated place to import
# such that all figures have identical styling (when possible)

import matplotlib.pyplot as plt

# setup latex
plt.rc('text', usetex=True)
plt.rc('font', family='serif')
plt.rc('text.latex',
       preamble=r'\usepackage{amsmath},\usepackage{siunitx},'
                r'\usepackage[version=3]{mhchem}')
plt.rc('font', family='serif')

legend_style = {'loc': 0,
                'fontsize': 16,
                'numpoints': 1,
                'shadow': True,
                'fancybox': True
                }

tick_font_size = 20
minor_tick_font_size = 16
title_font_size = 24

marker_style = {
    'size': 15
}

clear_marker_style = {
    'size': 17
}

default_keys = ['runtime', 'comptime', 'overhead']
marker_wheel = [('o', True), ('>', True), ('s', True),
                ('D', True)]


class wheeler(object):
    def __init__(self, wheel, raise_on_oob=True):
        self.raise_on_oob = raise_on_oob
        self.wheel = wheel[:]

    def __call__(self, key):
        if not self.raise_on_oob and key >= len(self.wheel):
            key = key % len(self.wheel)
        return self.wheel[key]


marker_dict = {x: marker_wheel[i] for i, x in enumerate(default_keys)}


class dummy_formatter(object):
    def __init__(self, choicedict):
        self.choices = choicedict.keys()
        self.values = [choicedict[x] for x in self.choices]

    def __hash__(self):
        return hash(repr(self))

    def format(self, val):
        return next(self.values[i] for i, x in enumerate(self.choices)
                    if x == val)


legend_key = {'H2': r'H$_2$/CO',
              'CH4': r'GRI-Mech 3.0',
              'C2H4': r'USC-Mech II',
              'IC5H11OH': r'IC$_5$H$_{11}$OH'
              }


def pretty_names(pname, short=False):
    pname_dict = {'runtime': 'Runtime',
                  'comptime': 'Compilation time',
                  'overhead': 'Kernel Construction Overhead',
                  'vecwidth': 'Vector Width = {}',
                  'vectype': dummy_formatter({'w': 'Shallow',
                                              'par': 'Unvectorized',
                                              'd': 'Deep',
                                              'openmp': r'OpenMP'}),
                  'order': dummy_formatter({'C': 'C-order',
                                            'F': 'F-order'}),
                  'kernel': dummy_formatter({'single': 'Single Rate Kernel',
                                             'split': 'Split Rate Kernels'}),
                  'rates': dummy_formatter({'fixed': 'Fixed Rate Specialization',
                                            'hybrid': 'Hybrid Rate Specialization',
                                            'full': 'Full Rate Specialization'}),
                  'sparse': dummy_formatter({'sparse': 'Sparse',
                                             'full': 'Dense'}),
                  'conp': dummy_formatter({'conp': 'CONP',
                                           'conv': 'CONV'}),
                  'mechdata.name': dummy_formatter(legend_key),
                  'descriptor': dummy_formatter({'srv2': r'\texttt{sse4.2}',
                                                 'srv2-gpu': r'\texttt{C2075}',
                                                 'haswell': r'\texttt{avx2}',
                                                 'gpu': r'\texttt{K40m}',
                                                 'v1': r'\texttt{sse4.2-v1}',
                                                 'v1-gpu': r'\texttt{C2075-v1}'}),
                  'rtype': dummy_formatter({'jac': 'Analytical',
                                            'fdjac': 'Finite Difference'})
                  }
    if pname in pname_dict:
        return pname_dict[pname]
    return pname


# color schemes
color_wheel = ['r', 'b', 'g', 'k']
color_dict = {x: color_wheel[i] for i, x in enumerate(default_keys)}


def finalize(tight=True):
    # triger tick positioning
    ax = plt.gca()
    if tight:
        plt.tight_layout()

    plt.tick_params(axis='both', which='major', labelsize=tick_font_size)

    for item in (ax.title, ax.xaxis.label, ax.yaxis.label):
        item.set_fontsize(title_font_size)
