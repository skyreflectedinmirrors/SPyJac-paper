import os

import cantera as ct
import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt

file = os.path.abspath(os.path.dirname(__file__))
gas = ct.Solution(os.path.join(file, os.pardir, 'mech_data',
                               'Sarathy_ic5_mech_rev.cti'))


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


# next, order the reactions by the number of distinct species
def get_reac_and_spec_maps(gas):
    # first, create rxn->species maps
    reac_nu = gas.reactant_stoich_coeffs()
    prod_nu = gas.product_stoich_coeffs()
    # species -> rxn mappings
    spec_masks = np.zeros((gas.n_species, gas.n_reactions), dtype=np.bool)
    # the reaction -> species mappings
    reac_masks = []
    for i, reac in enumerate(reacs):
        for spec in set(list(reac.reactants.keys()) + list(
                             reac.products.keys())):
            j = gas.species_index(spec)
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


spec_masks, reac_masks = get_reac_and_spec_maps(gas)
converted_spec_count = np.where(~np.sum(spec_masks, axis=1))[0].size
print('After conversion, {} third-body only species removed'.format(
      converted_spec_count))


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
    scores = rxn_scores(heuristic, reac_list)
    amax = np.argmax(scores)
    if scores[amax] == 0:
        return -1
    return reac_list[amax]


reac_list = np.arange(gas.n_reactions)
while True:
    remove_at = get_next_removed(minh, reac_list=np.where(reac_list >= 0)[0])
    if remove_at == -1:
        break
    reac_list[remove_at] = -1

reac_list = np.where(reac_list >= 0)[0]
reacs = gas.reactions()[:]
reacs = [reacs[i] for i in reac_list]
gas = ct.Solution(thermo='IdealGas', kinetics='GasKinetics',
                  reactions=reacs,
                  species=gas.species())

# remap, and ensure the number of removed species is not less than previously
smap_final, _ = get_reac_and_spec_maps(gas)
scount_final = np.where(~np.sum(smap_final, axis=1))[0].size
assert scount_final == converted_spec_count

print('Final mechanism size: {} reactions, {} species'.format(
    gas.n_reactions, scount_final))
