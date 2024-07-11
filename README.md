# Compositional program logics via Iris and ITrees

This is the Coq code associated to our paper "Program logics à la carte".

**Important note:** the `islaris` folder come from a fork of pre-existing open-source software, and
copyright notices and author names they contain have to do with their original authors (they were
not updated by us).

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for installing the
dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile because of outdated
dependencies.  To fix that, please run `opam update` followed by `make build-dep`.
