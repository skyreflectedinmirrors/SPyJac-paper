import os
import numpy as np
import yaml

script_dir = os.path.dirname(os.path.abspath(__file__))
error_path = os.path.join(script_dir, 'error_checking')
mechs = [os.path.join(error_path, x) for x in os.listdir(
    error_path) if os.path.isdir(os.path.join(error_path, x))]

rtol = 1e-6
atol = 1e-10

err_dicts = {}
for mech in mechs:
    mech_name = os.path.basename(os.path.normpath(mech))
    # get file list
    files = [os.path.join(mech, x) for x in os.listdir(
        mech) if os.path.isfile(os.path.join(mech, x)) if x.endswith('.npz')
        and 'spec' in x]
    err_dicts[mech_name] = {}

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

    # get mech info
    mech_info = os.path.join(mech, mech_name.lower() + '.yaml')
    with open(mech_info, 'r') as file:
        mech_info = yaml.load(file.read())

    for file in files:
        arrs = np.load(file)
        for name in arrs:
            if 'value' in name or 'component' in name or 'store' in name:
                continue
            errs = arrs[name]
            values = arrs[name + '_value']
            errs = errs / (atol + rtol * np.abs(values))

            precs = None
            if 'rop_net' in name:
                # calculate the precision norms
                precs = arrs['rop_component'] / (atol + rtol * np.abs(values))

            if name not in err_dicts[mech_name]:
                err_dicts[mech_name][name] = np.zeros((__get_size(name)))

                if precs is not None:
                    err_dicts[mech_name]['rop_component'] = np.zeros((__get_size(
                        'rop_net')))

            if name in err_dicts[mech_name]:
                if errs.shape != err_dicts[mech_name][name].shape:
                    # check that we have a split
                    assert 'C_w' in file or 'F_d' in file
                    # discard extra zeros resulting from split padding
                    errs = errs[:__get_size(name)]

                err_dicts[mech_name][name] = np.maximum(
                    err_dicts[mech_name][name], errs)
                if 'rop_net' in name:
                    update_locs = np.where(err_dicts[mech_name][name] == errs)
                    # update the precision norms at these locations
                    err_dicts[mech_name]['rop_component'][
                        update_locs] = precs[update_locs]
            else:

                err_dicts[mech_name][name] = np.maximumerrs


def format(val):
    return '{:1.2e}'.format(val)


keyarr = ['fwd', 'rev', 'net', 'comp', 'phi']
mech_arr = ['H2', 'CH4', 'C2H4', 'IC5H11OH']
for mech in mech_arr:
    print(mech)
    for name in sorted(err_dicts[mech], key=lambda x: keyarr.index(next(
            y for y in keyarr if y in x))):
        err_vals = err_dicts[mech][name][np.where(np.logical_not(
            np.isnan(err_dicts[mech][name])))]
        if 'phi' in name:
            print('tdot', format(err_vals[0]))
            print('edot', format(err_vals[1]))
            print('species', format(np.linalg.norm(err_vals[2:], ord=np.inf)))
        elif 'rop_net' in name:
            # find prevision range
            maxv = np.linalg.norm(err_vals, ord=np.inf)
            maxind = np.where(err_dicts[mech][name] == maxv)[0][0]
            print(name, format(maxv))
            print('rop_component', format(
                err_dicts[mech]['rop_component'][maxind]))
        elif 'component' not in name:
            print(name, format(np.linalg.norm(err_vals, ord=np.inf)))
