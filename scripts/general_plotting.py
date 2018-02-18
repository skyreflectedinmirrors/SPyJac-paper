"""Module with
"""
from __future__ import division
import numpy as np
import matplotlib.pyplot as plt
import plot_styles as ps

font_size = 'large'


def process_data(plotdata, plot, reacs_as_x=True,
                 plot_cores=False, plot_scaling=False):
    """
    Process the data into an easily usable form
    """
    def __mechsort(data):
        if reacs_as_x:
            data = sorted(data, key=lambda x: x.mechdata.n_reactions)
            return data, [x.mechdata.n_reactions for x in data]
        else:
            data = sorted(data, key=lambda x: x.mechdata.n_species)
            return data, [x.mechdata.n_species for x in data]

    if plot_cores:
        plotdata = sorted(plotdata, key=lambda x: float(x.cores))
        x_vals = [float(x.cores) for x in plotdata]
    elif plot_scaling:
        # first sort by # mech
        plotdata, _ = __mechsort(plotdata)
        # next sort within mechanism by # of conditions
        for mech in set([x.mechdata.mech for x in plotdata]):
            subdata = [x for x in plotdata if x.mechdata.mech == mech]
            x_vals = []
            y_vals = []
            err_vals = []
            for data in subdata:
                for xv in set(run.num_conditions for run in data.rundata):
                    subruns = [run for run in data.rundata
                               if run.num_conditions == xv]
                    # take mean & std
                    x_vals.append(xv)
                    yv = np.array([getattr(run, plot) for run in subruns])
                    if plot == 'runtime':
                        yv /= xv
                    y_vals.append(np.mean(yv))
                    err_vals.append(np.std(yv))

        return np.array(x_vals), np.array(y_vals), np.array(err_vals)

    else:
        plotdata, x_vals = __mechsort(plotdata)

    y_vals = []
    err_vals = []
    for run in plotdata:
        ys = np.array([getattr(data, plot) for data in run.rundata])
        zs = np.std(ys)
        if plot == 'runtime':
            ys = np.array(
                [getattr(data, plot) / data.num_conditions for data in run.rundata])
            zs /= run.rundata[0].num_conditions
        err_vals.append(zs)
        y_vals.append(np.mean(ys))
    return x_vals, y_vals, err_vals


def get_marker_and_label(plot_ind=None, marker_func=None, label=None, marker=None,
                         labels=[]):
    size = None
    if label is not None and marker is not None:
        name = label
        marker, hollow, color, size = marker
    elif marker_func is not None:
        name = labels[plot_ind]
        marker, hollow, color, size = marker_func(name)
    elif plot_ind is not None:
        assert labels
        marker, hollow = ps.marker_wheel[plot_ind % len(ps.marker_wheel)]
        color = ps.color_wheel[plot_ind % len(ps.marker_wheel)]
        name = labels[plot_ind]
    else:
        marker, hollow = ps.marker_dict[plot]
        color = ps.color_dict[plot]
        name = plot

    if size is None:
        size = ps.marker_style['size'] if not hollow else ps.clear_marker_style[
            'size']
    return marker, hollow, color, name, size


def plot(x_vals, y_vals, err_vals, minx=None, miny=None, maxx=None, maxy=None,
         plot_std=True, return_y=False, labels=[], plot_ind=None, marker_func=None,
         label=None, marker=None):
    """Plot performance as a function of reaction count."""

    marker, hollow, color, name, size = get_marker_and_label(
        plot_ind, marker_func, label, marker, labels)

    argdict = {'x': x_vals,
               'y': y_vals,
               'linestyle': '',
               'marker': marker,
               'label': ps.pretty_names(name)
               }
    argdict['color'] = color
    argdict['markeredgecolor'] = color
    argdict['markersize'] = size
    argdict['markeredgewidth'] = 1.25
    if hollow:
        argdict['markerfacecolor'] = 'None'

    if plot_std:
        argdict['yerr'] = err_vals
    if plot_std:
        plt.errorbar(**argdict)
    else:
        plt.plot(**argdict)

    def __get_min(test, inval):
        return test if inval is None else (
            test if test < inval else inval)

    def __get_max(test, inval):
        return test if inval is None else (
            test if test > inval else inval)
    minx = __get_min(np.min(x_vals), minx)
    miny = __get_min(np.min(y_vals), miny)
    maxx = __get_min(np.max(x_vals), maxx)
    maxy = __get_min(np.max(y_vals), maxy)
    return minx, miny, maxx, maxy
