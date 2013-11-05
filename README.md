The Boole Interactive Reasoning Assistant
=========================================

Directories:

- boole: the Boole python library
- docs
- examples

To use the Boole library, make sure the boole directory is in your Python path. For example, in Linux, use:

  export PYTHONPATH=[path-to-boole]:$PYTHONPATH

Similarly, if you plan to call Z3 from Boole, make sure the Z3 Python bindings are in your Python path.

To use Boole from Sage, make sure the boole directory is in your Sage path, e.g.

  export SAGE_PATH=[path-to-boole]:$SAGE_PATH

and then run Sage as usual. If you plan to call Z3, make sure the Z3 Python bindings in your Sage path as well.

The files in the examples directory can be executing by typing, e.g.:

  python example.py

The files with extension ipynb are ipython notebooks. With ipython installed, type

  ipython notebook

and then open the corresponding notebook from the browser.

To try the Sage examples, run Sage in the examples directory, and enter:

  attach('sage_examples.py')
  sage_examples()
