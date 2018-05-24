import os
from argparse import ArgumentParser
import subprocess

import cantera as ct
import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt

from pyjac import create_jacobian
from pyjac.utils import create_dir
from pyjac.libgen import build_type, generate_library
from pyjac.tests.test_utils import data_bin_writer as dbw
from pyjac.tests.test_utils import clean_dir

path = os.path.abspath(os.path.dirname(__file__))


def run(gas, interval, num_states, work_dir, repeats=10):
    def arrhenius(T, A, b, Ea, print_stats=False):
        vals = A * np.power(T, b) * np.exp(-Ea / (ct.gas_constant * T))
        if print_stats:
            print(A, b, Ea, np.max(np.abs(vals - kf) / kf))
        return vals

    # first, convert all reactions to a single rate form
    reacs = gas.reactions()[:]
    for i, reac in enumerate(reacs):
        if isinstance(reac, ct.ChemicallyActivatedReaction):
            reacs[i] = ct.ElementaryReaction(reac.reactants, reac.products)
            reacs[i].rate = reac.high_rate
        elif isinstance(reac, ct.FalloffReaction):
            reacs[i] = ct.ElementaryReaction(reac.reactants, reac.products)
            reacs[i].rate = reac.high_rate
        elif isinstance(reac, ct.ThreeBodyReaction):
            reacs[i] = ct.ElementaryReaction(reac.reactants, reac.products)
            reacs[i].rate = reac.rate
        elif isinstance(reac, ct.PlogReaction):
            reacs[i] = ct.ElementaryReaction(reac.reactants, reac.products)
            reacs[i].rate = reac.rates[-1][1]
        elif isinstance(reac, ct.ChebyshevReaction):
            # fit _something_ to it at a 10 bar, for 600-2200K
            T = np.linspace(600, 2200, num=1000)
            kf = np.zeros_like(T)
            for i in range(T.size):
                kf[i] = reac(T[i], 10 * 10*1e5)
            A = 1e10
            b = 1
            Ea = 1200 * ct.gas_constant
            (A, b, Ea), _ = curve_fit(
                arrhenius, T, kf,
                p0=[A, b, Ea],
                bounds=[(0, -2, 0), (np.inf, 5, np.inf)],
                maxfev=1e6,
                xtol=1e-15)
            if False:
                plt.plot(T, kf, color='b', linestyle='-', label='cheb')
                plt.plot(T, arrhenius(T, A, b, Ea), color='r', linestyle='--',
                         label='fit')
                plt.legend(loc=0)
                plt.show()
            reacs[i] = ct.ElementaryReaction(reac.reactants, reac.products)
            reacs[i].rate = ct.Arrhenius(A, b, Ea)
    # and convert gas
    gas = ct.Solution(thermo='IdealGas', kinetics='GasKinetics',
                      reacs=reacs,
                      species=gas.species())

    # next, order the reactions by the number of distinct species
    def get_reac_and_spec_maps(mygas):
        # first, create rxn->species maps
        reac_nu = mygas.reactant_stoich_coeffs()
        prod_nu = mygas.product_stoich_coeffs()
        # species -> rxn mappings
        spec_masks = np.zeros((mygas.n_species, mygas.n_reactions),
                              dtype=np.bool)
        # the reaction -> species mappings
        reac_masks = []
        for i, reac in enumerate(mygas.reactions()):
            for spec in set(list(reac.reactants.keys()) + list(
                                 reac.products.keys())):
                j = mygas.species_index(spec)
                if prod_nu[j, i] - reac_nu[j, i]:
                    # non-zero species
                    spec_masks[j, i] = True
            reac_masks.append(np.where(spec_masks[:, i])[0])

        # convert to flat, fixed size array
        copy = np.array(reac_masks, copy=True)
        max_size = np.max([x.size for x in reac_masks])
        reac_masks = np.full((len(reac_masks), max_size), -1)
        for i, mask in enumerate(copy):
            reac_masks[i, :mask.size] = mask[:]

        return spec_masks, reac_masks

    # ensure we didn't remove any species
    spec_masks, reac_masks = get_reac_and_spec_maps(gas)
    converted_spec_count = np.where(~np.sum(spec_masks, axis=1))[0].size
    assert converted_spec_count == gas.n_species

    def species_to_rxn_count(reac_list=slice(None)):
        """
        The number of reactions each species is in
        """
        return np.sum(spec_masks[:, reac_list], axis=1)

    def simple(specs, spec_counts):
        """
        Returns 0 if any species in the reaction is unique to that reaction
        otherwise mean of the number of reactions per species in the reaction
        """
        specs = specs[np.where(specs >= 0)]
        if np.any(spec_counts[specs] == 1):
            return 0
        return np.mean(spec_counts[specs])

    def minh(specs, spec_counts):
        """
        The minimum number of reactions any species in the reaction is in
        """

        specs = specs[np.where(specs >= 0)]
        minh = np.min(spec_counts[specs])
        return 0 if minh == 1 else minh

    def rxn_scores(heuristic, reac_list=slice(None)):
        """
        Returns a score from 0--1, where 1 indicates that the reactions is a
        good removal candidate and 0 a bad candidate

        Heuristics correspond to local methods
        """

        reac_list = np.arange(gas.n_reactions)[reac_list]
        s2r = species_to_rxn_count(reac_list)
        scores = np.apply_along_axis(heuristic, 1, reac_masks[reac_list], s2r)
        return scores

    def get_next_removed(heuristic, reac_list=slice(None)):
        """
        Get the index of the next reaction to remove from the current reac_list
        using the given heuristic
        """
        scores = rxn_scores(heuristic, reac_list)
        amax = np.argmax(scores)
        if scores[amax] == 0:
            return -1
        return reac_list[amax]

    def active_reactions(reac_list, return_active=False):
        """
        Returns the number of active reactions in the reac_list
        If return_active is True, return the list of active reactions
        """
        alist = np.where(reac_list >= 0)[0]
        if return_active:
            return alist
        return alist.size

    saved_reaction_lists = []
    reac_list = np.arange(gas.n_reactions)
    saved_reaction_lists.append(active_reactions(reac_list, True))
    while True:
        remove_at = get_next_removed(minh, reac_list=np.where(
            reac_list >= 0)[0])
        if remove_at == -1:
            break
        reac_list[remove_at] = -1
        if (active_reactions(reac_list) <= active_reactions(
                saved_reaction_lists[-1]) - interval):
            # save list
            saved_reaction_lists.append(active_reactions(reac_list, True))

    # get final reaction list and save
    reac_list = active_reactions(reac_list, True)
    saved_reaction_lists.append(reac_list)

    def gas_from_reac_list(reac_list):
        reacs = gas.reactions()[:]
        reacs = [reacs[i] for i in reac_list]
        return ct.Solution(thermo='IdealGas', kinetics='GasKinetics',
                           reactions=reacs,
                           species=gas.species())

    # remap, and ensure the number of removed species is not less than
    # previously
    newgas = gas_from_reac_list(reac_list)
    smap_final, _ = get_reac_and_spec_maps(newgas)
    scount_final = np.where(~np.sum(smap_final, axis=1))[0].size
    assert scount_final == converted_spec_count

    print('Final mechanism size: {} reactions, {} species'.format(
        newgas.n_reactions, scount_final))

    vecsize = 8
    platform = 'intel'
    split_rate_kernels = False
    lang = 'opencl'
    rate_spec = 'hybrid'
    num_cores = 1
    order = 'C'

    def get_filename(wide=False):
        """
        emulate pyjac's naming scheme
        """
        desc = 'spec'
        vsize = vecsize if wide else '1'
        vectype = 'w' if wide else 'par'
        platform = 'intel'
        split = 'split' if split_rate_kernels else 'single'
        conp = 'conp'

        return '{}_{}_{}_{}_{}_{}_{}_{}_{}_{}'.format(
                desc, lang, vsize, order,
                vectype, platform, rate_spec,
                split, num_cores, conp) + '.txt'

    def check_file(file):
        if not os.path.exists(file):
            return repeats
        with open(file, 'r') as f:
            lines = f.readlines()
        import re
        todo = repeats
        for line in lines:
            line = line.split(',')
            if len(line) > 1 and sum(
                    1 if re.search(r'(?:\d+(?:\.\d+e[+-]\d+))', l) else 0
                    for l in line) == 4:
                # four doubles -> good line
                todo -= 1
        return todo

    build = os.path.join(path, 'out')
    obj = os.path.join(path, 'obj')
    lib = os.path.join(path, 'lib')

    for wide in [True, False]:
        vsize = vecsize if wide else None
        # now, go through the various generated reactions lists and run
        # the test on each
        for reac_list in saved_reaction_lists:
            outname = get_filename(wide)
            todo = check_file(outname)
            # clean
            clean_dir(build, remove_dir=False)
            clean_dir(obj, remove_dir=False)
            clean_dir(lib, remove_dir=False)

            subdir = os.path.join(work_dir, str(active_reactions(reac_list)))
            create_dir(subdir)
            # generate the source rate evaluation
            rgas = gas_from_reac_list(reac_list)
            create_jacobian('opencl', gas=rgas, vector_size=vsize,
                            wide=wide, build_path=build,
                            rate_specialization=rate_spec,
                            split_rate_kernels=split_rate_kernels,
                            data_filename=os.path.abspath(
                                os.path.join(work_dir, 'data.bin')),
                            data_order=order,
                            platform=platform,
                            skip_jac=True)

            # first create the executable (via libgen)
            tester = generate_library(lang, build, obj_dir=obj, out_dir=lib,
                                      shared=True,
                                      btype=build_type.species_rates,
                                      as_executable=True)

            # and do runs
            with open(os.path.join(subdir, outname), 'a+') as file:
                for i in range(todo):
                    print(i, "/", todo)
                    subprocess.check_call([os.path.join(lib, tester),
                                           str(num_states), str(1)],
                                          stdout=file)


if __name__ == '__main__':
    parser = ArgumentParser('reaction_scaling_test.py -- tests SIMD '
                            'efficiency scaling of pyJac with differing'
                            ' numbers of reactions.')
    parser.add_argument('-m', '--mech',
                        default='Sarathy_ic5_mech_rev.cti',
                        required=False,
                        type=str,
                        help='The mechanism to test, defaults to the Sarathy '
                             'isopentanol model.')
    parser.add_argument('-i', '--test_interval',
                        default=50,
                        type=int,
                        help='The interval (in # of reactions) at which to '
                             'run the performance tests to produce the '
                             'scaling plot.')
    parser.add_argument('-n', '--num_states',
                        default=None,
                        type=int,
                        required=False,
                        help='The number of states to run in performance '
                             'testing.')
    parser.add_argument('-d', '--data_path',
                        required=True,
                        type=str,
                        help='The path to the ')
    parser.add_argument('-r', '--repeats',
                        default=10,
                        type=int,
                        help='The number of performance runs for each '
                             'mechanism size.')
    parser.add_argument('-w', '--working_directory',
                        type=str,
                        required=False,
                        default=os.getcwd(),
                        help='The directory to work in.')
    args = parser.parse_args()
    gas = ct.Solution(os.path.join(args.data_path, args.mech))

    # get data
    num_conditions, data = dbw.load(
        [], directory=os.path.join(args.data_path))
    # rewrite data to file in 'C' order
    dbw.write(args.working_directory, num_conditions=num_conditions, data=data)

    # normalize for vector width
    num_conditions = (num_conditions // 8) * 8

    run(gas, args.test_interval, num_conditions, args.working_directory,
        repeats=args.repeats)
