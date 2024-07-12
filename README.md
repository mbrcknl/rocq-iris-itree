# Program logics à la carte

This is the Coq code for our paper "Program logics à la carte". A mapping between the
paper and the Coq code can be found in `coq_vs_paper.md`.

**Important note:** the `islaris` folder in the root is a fork of pre-existing
open-source software. Copyright notices and author names in that folder have to do with their
original authors (they were not updated by us).

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for installing the
dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your CPU cores.
