from __future__ import print_function, division

from argparse import ArgumentParser
import numpy as np
import cantera as ct
from pyjac.core.mech_interpret import read_mech_ct
from pyjac.core.create_jacobian import determine_jac_inds
from pyjac.loopy_utils.loopy_utils import JacobianType, RateSpecialization
import matplotlib.pyplot as plt


def plot(mech, jac_type, out=''):
    # plot the sparsity patterns of our tested mechanisms

    # get gas
    gas = ct.Solution(mech)
    _, specs, reacs = read_mech_ct(gas=gas)

    # get indicies
    info = determine_jac_inds(reacs, specs, RateSpecialization.fixed, jac_type)
    inds = info['jac_inds']

    # set grid for plotting
    grid = np.zeros((gas.n_species + 1, gas.n_species + 1))
    grid[inds['flat_C'][:, 0], inds['flat_C'][:, 1]] = 1

    print('{}, Density: {:.3}%'.format(
        str(jac_type), 100. * np.where(grid)[0].size / grid.size))

    plt.imshow(grid, cmap='Greys',  interpolation='none')

    if out:
        if out.endswith('.pdf'):
            out = out[:out.index('.pdf')]
        out += '_' + str(jac_type)[str(jac_type).index('.') + 1:] + '.png'
        plt.tight_layout()
        plt.savefig(out, dpi=1000)
    else:
        plt.show()


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('-m', '--mech',
                        type=str,
                        required=True,
                        help='The mechanism to plot')
    parser.add_argument('-o', '--out',
                        type=str,
                        required=False,
                        default='',
                        help='The filename to store the generated plots in. '
                             'If not supplied, the images will only be shown to the '
                             'screen.')
    opts = parser.parse_args()

    plot(opts.mech, JacobianType.exact, opts.out)
    plot(opts.mech, JacobianType.approximate, opts.out)
