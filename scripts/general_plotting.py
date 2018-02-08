"""Module with
"""
from __future__ import division
import numpy as np
import matplotlib.pyplot as plt
import plot_styles as ps

font_size = 'large'


def process_data(plotdata, plot, reacs_as_x=True,
                 plot_cores=False):
    """
    Process the data into an easily usable form
    """
    if reacs_as_x:
        plotdata = sorted(plotdata, key=lambda x: x.mechdata.n_reactions)
        x_vals = [x.mechdata.n_reactions for x in plotdata]
    elif plot_cores:
        plotdata = sorted(plotdata, key=lambda x: float(x.cores))
        x_vals = [float(x.cores) for x in plotdata]
    else:
        plotdata = sorted(plotdata, key=lambda x: x.mechdata.n_species)
        x_vals = [x.mechdata.n_species for x in plotdata]

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


def plot(plot, x_vals, y_vals, err_vals, minx=None, miny=None, maxx=None, maxy=None,
         plot_std=True, return_y=False, labels=[], plot_ind=None, marker_func=None,
         label=None, marker=None):
    """Plot performance as a function of reaction count.
    """

    if label is not None and marker is not None:
        name = label
        marker, hollow, color = marker
    elif marker_func is not None:
        name = labels[plot_ind]
        marker, hollow, color = marker_func(name)
    elif plot_ind is not None:
        assert labels
        marker, hollow = ps.marker_wheel[plot_ind % len(ps.marker_wheel)]
        color = ps.color_wheel[plot_ind % len(ps.marker_wheel)]
        name = labels[plot_ind]
    else:
        marker, hollow = ps.marker_dict[plot]
        color = ps.color_dict[plot]
        name = plot

    argdict = {'x': x_vals,
               'y': y_vals,
               'linestyle': '',
               'marker': marker,
               'label': ps.pretty_names(name)
               }
    argdict['color'] = color
    argdict['markeredgecolor'] = color
    if not hollow:
        argdict['markersize'] = ps.marker_style['size']
    else:
        argdict['markerfacecolor'] = 'None'
        argdict['markersize'] = ps.clear_marker_style['size']

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


def plot_scaling(plotdata, markerlist, colorlist, minx=None, miny=None,
                 label_locs=None, plot_std=True, hollow=False, legend_key={}
                 ):
    """Plots performance data with varying number of conditions.
    """
    mset = list(set(x.mechanism for x in plotdata))
    mechs = sorted(mset, key=lambda mech: next(x for x in plotdata
                                               if x.mechanism == mech).num_specs
                   )
    for i, mech in enumerate(mechs):
        name = legend_key[mech]
        data = [x for x in plotdata if x.mechanism == mech]
        x_vals = sorted(list(set(x.x for x in data)))
        y_vals = [next(x.y for x in data if x.x == xval) for xval in x_vals]
        y_vals = [np.mean(x) for x in y_vals]
        err_vals = [np.std(x) for x in y_vals]

        # Find minimum x and y values, or keep manual setting if actually
        # lower than true minimums
        minx = (np.min(x_vals) if minx is None
                else np.min(x_vals) if np.min(x_vals) < minx
                else minx
                )
        miny = (np.min(y_vals) if miny is None
                else np.min(y_vals) if np.min(y_vals) < miny
                else miny
                )

        argdict = {'x': x_vals,
                   'y': y_vals,
                   'linestyle': '',
                   'marker': markerlist[i],
                   'markeredgecolor': colorlist[i],
                   'markersize': 8,
                   'color': colorlist[i],
                   'label': name
                   }
        # use hollow symbols for shared memory results
        if hollow:
            argdict['markerfacecolor'] = 'None'
            argdict['label'] += ' (smem)'
        # plotting error bars for standard deviation
        if plot_std:
            argdict['yerr'] = err_vals
            line = plt.errorbar(**argdict)
        else:
            del argdict['x']
            del argdict['y']
            plt.plot(x_vals, y_vals, **argdict)

        # Rather than legend, place labels above/below series
        if label_locs is not None:
            # get index of first value after specified location
            label_loc, label_off = label_locs[i]
            pos_label = next(x[0]
                             for x in enumerate(x_vals) if x[1] > label_loc)
            # average of points
            label_ypos = 0.5 * (y_vals[pos_label] + y_vals[pos_label - 1])
            plt.text(label_loc, label_ypos * label_off, argdict['label'],
                     fontsize=font_size,
                     horizontalalignment='center', verticalalignment='center'
                     )

    return minx, miny
