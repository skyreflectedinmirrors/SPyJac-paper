import os
import numpy as np
import yaml
from collections import defaultdict

script_dir = os.path.dirname(os.path.abspath(__file__))
error_path = os.path.join(script_dir, 'error_checking')


def get_error_files(ftype):
    mechs = [os.path.join(error_path, x) for x in os.listdir(
        error_path) if os.path.isdir(os.path.join(error_path, x))]

    # get file list
    files = {}
    for mech in mechs:
        files[mech] = [os.path.join(mech, x) for x in os.listdir(
            mech) if os.path.isfile(os.path.join(mech, x)) if x.endswith('.npz')
            and ftype in x]

    return files


def run_error_calcs(ftype, updater):
    files = get_error_files(ftype)
    err_dicts = {}
    for mech in files:
        mech_name = os.path.basename(os.path.normpath(mech))
        err_dicts[mech_name] = defaultdict(lambda: 0)

        # get mech info
        mech_info = os.path.join(mech, mech_name.lower() + '.yaml')
        with open(mech_info, 'r') as file:
            mech_info = yaml.load(file.read())

        for file in files[mech]:
            updater(err_dicts[mech_name], np.load(file), filename=file,
                    mech_info=mech_info)

    return err_dicts


def print_error(ftype, updater, printer):
    err_dicts = run_error_calcs(ftype, updater)
    mech_arr = ['H2', 'CH4', 'C2H4', 'IC5H11OH']
    for mech in mech_arr:
        print(mech)
        printer(err_dicts[mech])
