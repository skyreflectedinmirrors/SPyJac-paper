pyJac: analytical Jacobian generator for chemical kinetics
==========================================================

This repository contains the source for our paper describing an analytical sparse Jacobian generator for chemical kinetic models, using SIMD and SIMT vectorization.
It makes use of the [`pyJac`](http://github.com/slackha/pyjac/) package, Version 2, which has been developed concurrently. The paper has been submitted to *Combustion and Flame*, and a preprint will soon be available..

To see a current build of the paper from the master branch of this repository, you may use your favorite latex editor to build the paper.tex and derivations.tex source files.

Feel free to submit comments or feedback via the Issues tab [on this repository](https://github.com/arghdos/SPyJac-paper).

Reproducing the Paper
---------------------
The LaTeX source of the paper is in the top directory.

To reproduce all of the figures in the paper, first install packages from the standard Python scientific stack: [numpy](http://numpy.org), [scipy](http://scipy.org), and [matplotlib](http://matplotlib.org) and [jupyter notebook](http://jupyter.org/).
Then, then download the [data used for this paper](https://figshare.com/s/0130c6e0e2e840eefc3b): (doi:10.6084/m9.figshare.6534146) and extract the "scripts" folder into the top level directory.

Finally, start `jupyter notebook` and navigate to the `performance_plots.ipynb` file in the scripts directory where the figures may be reproduced. One exeception this is the Jacobian sparsity plotter, which is a standalone script (`sparse_plotter.py`) that takes a cantera formatted mechanism as an arguement.

Error statistics reported in the paper can be determined by running:

```
python source_term_error.py
python jac_error.py
```

License
-------
<a rel="license" href="http://creativecommons.org/licenses/by/4.0/"><img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by/4.0/88x31.png" /></a><br />This work is licensed under a <a rel="license" href="http://creativecommons.org/licenses/by/4.0/">Creative Commons Attribution 4.0 International License</a>.
See the LICENSE.txt file or follow the link for details.
