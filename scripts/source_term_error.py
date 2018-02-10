import os
import numpy as np
from load_error_files import print_error

rtol = 1e-6
atol = 1e-10


def updater(err_dict, err, filename=None, mech_info={}):
    def __get_size(name):
        if 'rop' in name:
            if 'net' in name or 'fwd' in name:
                return mech_info['n_reactions']
            else:
                return mech_info['n_reversible']
        elif 'wdot' in name:
            return mech_info['n_species']
        elif 'phi' in name:
            return mech_info['n_species'] + 1

    for name in err:
        if 'value' in name or 'component' in name or 'store' in name:
            continue
        errs = err[name]
        values = err[name + '_value']
        errs = errs / (atol + rtol * np.abs(values))
        if ('rop_fwd' == name or 'rop_rev' == name) and 'store' in name and np.any(
                errs > 1e-4):
            from time import ctime
            print(filename, ctime(os.path.getmtime(filename)))
            print('Bad data detected...')

        precs = None
        if 'rop_net' in name:
            # calculate the precision norms
            precs = err['rop_component'] / (atol + rtol * np.abs(values))

        if name not in err_dict:
            err_dict[name] = np.zeros((__get_size(name)))

            if ('rop_fwd' in name or 'rop_rev' in name):
                if mech_info['n_cheb']:
                    err_dict[name + '_nocheb'] = np.zeros((__get_size(name)))
                if mech_info['n_plog']:
                    err_dict[name + '_noplog'] = np.zeros((__get_size(name)))

            if precs is not None:
                err_dict['rop_component'] = np.zeros((__get_size(
                    'rop_net')))

        if errs.shape != err_dict[name].shape:
            # check that we have a split
            assert 'C_w' in filename or 'F_d' in filename
            # discard extra zeros resulting from split padding
            errs = errs[:__get_size(name)]

        err_dict[name] = np.maximum(
            err_dict[name], errs)

        def __update_rxn_type(rxn_str):
            if ('rop_fwd' == name or 'rop_rev' == name) and \
                    mech_info['n_' + rxn_str]:
                inds = mech_info[name + '_' + rxn_str + '_inds']
                err_dict[name + '_no' + rxn_str][inds] = np.maximum(
                    err_dict[name + '_no' + rxn_str][inds], errs[inds])

        __update_rxn_type('cheb')
        __update_rxn_type('plog')

        if 'rop_net' in name:
            update_locs = np.where(err_dict[name] == errs)
            # update the precision norms at these locations
            err_dict['rop_component'][
                update_locs] = precs[update_locs]


def format(val):
    return '{:1.2e}'.format(val)


def printer(err_dict):
    keyarr = ['fwd', 'rev', 'net', 'comp', 'phi']
    for name in sorted(err_dict, key=lambda x: keyarr.index(next(
            y for y in keyarr if y in x))):
        err_vals = err_dict[name][np.where(np.logical_not(
            np.isnan(err_dict[name])))]
        if 'phi' in name:
            print('tdot', format(err_vals[0]))
            print('edot', format(err_vals[1]))
            print('species', format(np.linalg.norm(err_vals[2:], ord=np.inf)))
        elif 'rop_net' in name:
            # find prevision range
            maxv = np.linalg.norm(err_vals, ord=np.inf)
            maxind = np.where(err_dict[name] == maxv)[0][0]
            print(name, format(maxv))
            print('rop_component', format(
                err_dict['rop_component'][maxind]))
        elif 'component' not in name:
            print(name, format(np.linalg.norm(err_vals, ord=np.inf)))


print_error('spec', updater, printer)
