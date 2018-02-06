import os
import numpy as np
from load_error_files import print_error

rtol = 1e-6
atol = 1e-10


def update(err_dict, err, filename=None, **kwargs):
    for name in err:
        if 'amax' in name or 'value' in name:
            continue
        if err[name] > 1e20:
            from time import ctime
            print(os.path.basename(filename), ctime(os.path.getmtime(filename)))
            print('Bad data detected...')
            continue
        err_dict[name] = np.maximum(err_dict[name], err[name])


def printer(err_dict):
    print('\n'.join(
        ['{}: {:.15e}'.format(k, v) for k, v in err_dict.items()]))


print_error('jac', update, printer)
