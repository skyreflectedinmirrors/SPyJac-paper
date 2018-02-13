from __future__ import division

import data_parser
import argparse
import plot_styles as ps
import matplotlib.pyplot as plt
import general_plotting as gp
import numpy as np
import itertools
import functools
import copy
import six
import os
import pickle

run = data_parser.run
rundata = data_parser.rundata
mechdata = data_parser.mechdata
reacs_as_x = False
norm = None

# from http://stackoverflow.com/a/31174427
sentinel = object()


def rgetattr(obj, attr, default=sentinel):
    if default is sentinel:
        _getattr = getattr
    else:
        def _getattr(obj, name):
            return getattr(obj, name, default)
    return functools.reduce(_getattr, [obj] + attr.split('.'))


def __compare(r, name, compare_value, plot_cores=False, strict=False):
    """
    Specialty comparison function to account for differences
    in runtypes
    """
    if six.callable(compare_value):
        return compare_value(rgetattr(r, name))
    if name == 'vecwidth' and r.vectype == 'par' and not strict:
        return True
    if plot_cores and name == 'cores':
        return True
    return rgetattr(r, name) == compare_value


def flatten(data):
    return [x for mech in data for x in data[mech] if x.rundata]


def get_filtered_data(data_clean, warn=True, strict=False, printf=False, **filters):
    data = copy.copy(data_clean)
    # apply filters
    for f in filters:
        if filters[f] is None:
            continue
        if printf:
            print(f, filters[f], sum(len(data[x]) for x in data))
        if warn:
            assert any(data[x] for x in data), 'No data matching all filters'
        try:
            for mech in data:
                data[mech] = [x for x in data[mech]
                              if __compare(x, f, filters[f], strict=strict)]
        except AttributeError:
            pass

    return data


def get_diffs(data):
    diff_check = [x for x in run._fields if x not in ['mechdata', 'rundata']]
    diffs = [set([getattr(x, check) for x in data])
             for check in diff_check]
    # get # with more than 1 option
    diff_locs = [i for i in range(len(diffs)) if len(diffs[i]) > 1]
    diffs = [x for x in diffs if len(x) > 1]
    return diffs, diff_locs, diff_check


def plotter(data_clean, plot_name='', show=True, plot_reacs=True, norm=True,
            legend_handler=None, marker_func=None,
            minx=None, miny=None, maxx=None, maxy=None, ylog=False,
            return_vals=False, **filters):

    # create fig, ax
    plt.figure()
    ax = plt.subplot(1, 1, 1)

    data = get_filtered_data(data_clean, **filters)

    # now plot data
    to_plot = ['runtime']
    if filters.pop('plot_compilation', False):
        to_plot.append('comptime')
    if filters.pop('plot_overhead', False):
        to_plot.append('overhead')
    # get data
    plot_data = flatten(data)
    # get labels

    diffs, diff_locs, diff_check = get_diffs(plot_data)
    plot_cores = False
    if 'cores' in [diff_check[loc] for loc in diff_locs]:
        # can only process one
        plot_cores = len(diff_locs) == 1
        if plot_cores:
            diffs = [sorted(data.keys())]
            diff_locs = [-1]
            diff_check.append('mechdata.mech')
            plot_reacs = False
            plot_cores = True

    retval = None
    # delete diff for vecwidth / par thing
    if 'vectype' in [diff_check[loc] for loc in diff_locs]:
        ind = next((i for i, loc in enumerate(diff_locs)
                    if diff_check[loc] == 'vecwidth'), None)
        if ind is not None:
            diffs.pop(ind)
            diff_locs.pop(ind)

    if len(diff_locs) > 2:
        raise NotImplementedError
    if not diff_locs:
        # regular plot
        for plot in to_plot:
            gp.plot(*gp.process_data(plot_data, plot, reacs_as_x=plot_reacs))
    else:
        # create map dict
        loc_map = {}
        for i, diff in enumerate(diffs):
            for subdiff in diff:
                loc_map[subdiff] = diff_locs[i]

        # sort
        try:
            diffs = [sorted(diff, key=lambda x: float(x)) for diff in diffs]
        except:
            if plot_cores:
                # sort by mech size
                diffs = [sorted(diff, key=lambda x:
                                data[x][0].mechdata.n_reactions) for diff in diffs]
            else:
                diffs = [sorted(diff) for diff in diffs]

        # first pass - process data
        x_vals = []
        y_vals = []
        z_vals = []
        labels = []

        def __get_compound_names(val1, val2):
            c1 = diff_check[loc_map[val1]]
            c2 = diff_check[loc_map[val2]]

            # generic name ordering
            ordering = ['vectype', 'order']

            # sort by order
            check_vals = [None for _ in diff_check]
            check_vals[loc_map[val1]] = c1
            check_vals[loc_map[val2]] = c2
            check_vals = sorted(check_vals,
                                key=lambda x: 100 if x not in ordering
                                else ordering.index(x))

            # remove none
            check_vals = [x for x in check_vals if x is not None]

            # and return str
            return ' - '.join(ps.pretty_names(check).format(
                val1 if check == c1 else val2) for check in check_vals)

        # handle 2 diffs
        if len(diffs) == 1:
            for val in [subdiff for diff in diffs for subdiff in diff]:
                check = diff_check[loc_map[val]]
                match = [x for x in plot_data if __compare(
                    x, check, val, plot_cores=plot_cores)]
                if match:
                    labels.append(ps.pretty_names(check).format(val))
                    x, y, z = gp.process_data(
                        match, 'runtime', reacs_as_x=plot_reacs,
                        plot_cores=plot_cores)
                    x_vals.append(x)
                    y_vals.append(y)
                    z_vals.append(z)
        else:
            iterator = [zip(x, diffs[1])
                        for x in itertools.permutations(diffs[0], len(diffs[0]))]
            iterator = [subiter for i in iterator for subiter in i]
            for val1, val2 in iterator:
                match = [x for x in plot_data if __compare(
                    x, diff_check[loc_map[val1]], val1, plot_cores=plot_cores)
                         and __compare(x, diff_check[loc_map[val2]], val2)]
                if match:
                    labels.append(__get_compound_names(val1, val2))
                    x, y, z = gp.process_data(
                        match, 'runtime', reacs_as_x=plot_reacs,
                        plot_cores=plot_cores)
                    x_vals.append(x)
                    y_vals.append(y)
                    z_vals.append(z)

        if return_vals:
            def __copy_arr(val):
                return [v[:] for v in val]
            retval = [__copy_arr(x_vals), __copy_arr(
                y_vals), __copy_arr(z_vals), copy.copy(labels)]

        # second pass - normalize
        if norm and not plot_cores:
            xlen = len(next(x for x in x_vals if x))
            # find the max y for each x
            for ix in range(xlen):
                y_max = np.max([y_vals[i][ix]
                                for i in range(len(y_vals)) if y_vals[i]])
                # divide
                for i in range(len(y_vals)):
                    z_vals[i][ix] = (z_vals[i][ix] / y_vals[i]
                                     [ix]) * (y_max / y_vals[i][ix])
                    y_vals[i][ix] = y_max / y_vals[i][ix]

        elif norm:
            # parallel scaling eff
            for ix in range(len(x_vals)):
                for i in range(1, len(x_vals[ix])):
                    # scaling eff is t1 / (N * tN)
                    y_vals[ix][i] = y_vals[ix][0] / \
                        (x_vals[ix][i] * y_vals[ix][i])
                    # update uncertainty
                    z_vals[ix][i] = y_vals[ix][i] * np.sqrt(
                        np.power(z_vals[ix][0] / y_vals[ix][0], 2) +
                        np.power(z_vals[ix][i] / y_vals[ix][i], 2))
                # remove first entry (1 core)
                assert x_vals[ix][0] == 1
                x_vals[ix] = x_vals[ix][1:]
                y_vals[ix] = y_vals[ix][1:]
                z_vals[ix] = z_vals[ix][1:]

        if ylog:
            ax.set_yscale('log')

        # and finally plot
        for i in range(len(y_vals)):
            gp.plot(x_vals[i], y_vals[i], z_vals[i],
                    labels=labels, plot_ind=i, marker_func=marker_func)
        ax.set_xlim([minx, maxx])
        ax.set_ylim([miny, maxy])

    ylabel = r'Runtime (\si{\milli\second} / state)'
    xlabel = r'Number of {} in Model'.format(
        'Species' if not plot_reacs else 'Reactions')
    if norm:
        ylabel = 'Speedup'
        if plot_cores:
            ylabel = 'Parallel Scaling Efficiency'
    if plot_cores:
        xlabel = 'Number of Cores'

    plt.ylabel(ylabel)
    plt.xlabel(xlabel)
    if legend_handler:
        plt.legend(*legend_handler, **ps.legend_style).draggable()
    else:
        plt.legend(**ps.legend_style)
    ps.finalize()
    if plot_name:
        plt.savefig(plot_name)
    if show:
        plt.show()
    return retval


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rebuild',
                        default=False,
                        action='store_true')
    parser.add_argument('--lang',
                        required=False,
                        default='opencl',
                        type=str)
    parser.add_argument('--rtype',
                        required=False,
                        default='jac',
                        choices=['jac', 'spec'],
                        type=str)
    parser.add_argument('--vecwidth',
                        required=False,
                        default=None,
                        type=str)
    parser.add_argument('--order',
                        required=False,
                        default=None,
                        type=str,
                        choices=['C', 'F'])
    parser.add_argument('--vectype',
                        required=False,
                        default=None,
                        type=str,
                        choices=['par', 'w', 'd'])
    parser.add_argument('--platform',
                        required=False,
                        default=None,
                        type=str,
                        choices=['intel', 'nvidia', 'amd'])
    parser.add_argument('--rates',
                        required=False,
                        default=None,
                        type=str,
                        choices=['fixed', 'hybrid', 'full'])
    parser.add_argument('--kernel',
                        required=False,
                        default=None,
                        type=str,
                        choices=['single', 'split'])
    parser.add_argument('--cores',
                        required=False,
                        default=None,
                        type=str)
    parser.add_argument('--sparse',
                        default=None,
                        required=False,
                        choices=['sparse', 'full'])
    parser.add_argument('--plot_name',
                        required=False,
                        default='',
                        type=str)
    parser.add_argument('--mech',
                        required=False,
                        default=None,
                        type=str,
                        choices=['H2', 'CH4', 'C2H4', 'IC5H11OH']
                        )
    parser.add_argument('--descriptor',
                        required=False,
                        type=str,
                        default=None)
    parser.add_argument('--conp',
                        required=False,
                        choices=['conp', 'conv'],
                        default='conp')
    parser.add_argument('--plot_compilation',
                        required=False,
                        default=False,
                        action='store_true'
                        )
    parser.add_argument('--plot_overhead',
                        required=False,
                        default=False,
                        action='store_true'
                        )
    parser.add_argument('--no_norm',
                        dest='norm',
                        action='store_false',
                        required=False,
                        default=True)
    opts = vars(parser.parse_args())

    script_dir = os.path.dirname(os.path.normpath(__file__))
    data_clean = None
    try:
        with open(os.path.join(script_dir, 'data.pickle'), 'rb') as file:
            data_clean = pickle.load(file)
    except:
        pass
    finally:
        if data_clean is None or opts['rebuild']:
            data_clean = data_parser.parse_data(rebuild=opts['rebuild'])
            with open(os.path.join(script_dir, 'data.pickle'), 'wb') as file:
                pickle.dump(data_clean, file)

    options = {k: opts[k] for k in opts if opts[k] is not None and k != 'rebuild'}
    plotter(data_clean, **options)
