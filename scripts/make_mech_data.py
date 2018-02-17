import argparse
import cantera as ct
import yaml
import os
import ntpath

parser = argparse.ArgumentParser()
parser.add_argument('-m', '--mech',
                    type=str,
                    help='The mechanism to generate the data file for')
parser.add_argument('-n', '--name',
                    type=str,
                    default=None,
                    required=False,
                    help='The desired mechanism name for plotting. '
                         'If not specified, the mechanism filename is used')
parser.add_argument('-o', '--outpath',
                    type=str,
                    default='.',
                    required=False,
                    help='The path to place the generated mechanism data file in.')

opts = parser.parse_args()
gas = ct.Solution(opts.mech)
mech = ntpath.basename(opts.mech)
name = opts.name if opts.name is not None else mech[:mech.index('.cti')]

outfile = os.path.join(opts.outpath, name + '.yaml')
with open(outfile, 'w') as file:
    yaml.dump(dict(
        mech=mech,
        name=name,
        n_reactions=gas.n_reactions,
        n_species=gas.n_species,
        n_reversible=len([x for x in gas.reactions() if x.reversible]),
        n_cheb=len([x for x in gas.reactions()
                    if isinstance(x, ct.ChebyshevReaction)]),
        n_plog=len([x for x in gas.reactions()
                    if isinstance(x, ct.PlogReaction)])
        ), file, default_flow_style=False)
