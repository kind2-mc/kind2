.. DO NOT EDIT, see doc/usr/README.rst for details

.. |develop| image:: https://github.com/kind2-mc/kind2/workflows/Kind2%20CI/badge.svg?branch=develop
   :target: https://github.com/kind2-mc/kind2/actions?query=workflow%3A%22Kind2+CI%22
   :align: middle

.. |release| image:: https://img.shields.io/github/v/release/kind2-mc/kind2?color=blue
   :target: https://github.com/kind2-mc/kind2/releases/latest
   :align: middle

.. |license| image:: https://img.shields.io/github/license/kind2-mc/kind2?color=green
   :target: https://github.com/kind2-mc/kind2/blob/develop/LICENSE.rst
   :align: middle

.. https://stackoverflow.com/a/12145490/8261793

.. |nbsp| unicode:: 0xA0

|develop| |nbsp| |release| |nbsp| |license|

Kind 2
======

`Kind 2 <http://kind.cs.uiowa.edu/>`_ \ is a multi-engine, parallel,
SMT-based automatic model checker for safety properties of Lustre programs.

Kind 2 is a command-line tool. 
It takes as input a Lustre file annotated with properties to be proven
invariant (see `Lustre Input <https://kind.cs.uiowa.edu/kind2_user_doc/2_input/1_lustre.html>`_), and
outputs which of the properties are true for all inputs, as well as an input
sequence for those properties that are falsified. To ease processing by
external tools, Kind 2 can output its results in JSON and XML formats
(see `JSON / XML Output <https://kind.cs.uiowa.edu/kind2_user_doc/3_output/2_machine_readable.html>`_).

By default Kind 2 runs a process for bounded model checking (BMC), two processes
for k-induction (one for a fixed value of k=2, and other for increasing values of k),
several processes for invariant generation, and a process for IC3
in parallel on all properties simultaneously. It incrementally outputs
counterexamples to properties as well as properties proved invariant.

The following command-line options control its operation
(run ``kind2 --help`` for a full list).
See `Techniques <https://kind.cs.uiowa.edu/kind2_user_doc/1_techniques/1_techniques.html>`_ for configuration examples and
more details on each technique.

``--enable {BMC|IND|IND2|IC3|INVGEN|INVGENOS|...}`` Select model checking engines

By default, all four model checking engines are run in parallel.
Give any combination of ``--enable BMC``\ , ``--enable IND``, ``--enable IND2`` and
``--enable IC3`` to select which engines to run. The option ``--enable BMC`` alone
will not be able to prove properties valid, choosing ``--enable IND`` and
``--enable IND2`` only (or either of the two alone) will not produce any results.
Any other combination is sound
(properties claimed to be invariant are indeed invariant) and counterexample-complete
(a counterexample will be produced for each property that is not invariant,
given enough time and resources).

``--timeout <int>`` (default ``0`` = none) -- Run for the given number of seconds of wall clock time

``--smt_solver {Boolector|CVC4|MathSAT|Yices|Yices2|Z3}`` (default ``Z3``\ ) -- Select SMT solver

``--boolector_bin <file>`` -- Executable for Boolector

``--cvc4_bin <file>`` -- Executable for CVC4

``--mathsat_bin <file>`` -- Executable for MathSAT 5

``--yices_bin <file>`` -- Executable for Yices 1 (native input)

``--yices2_bin <file>`` -- Executable for Yices 2 (SMT input)

``--z3_bin <file>`` -- Executable for Z3

``-v`` Output informational messages

``-json`` Output in JSON format

``-xml`` Output in XML format


Try Kind 2 Online
-----------------

Visit our `web interface <https://kind.cs.uiowa.edu/app/>`_ to try Kind 2 from your browser.

Download
--------

If you use a Linux or a macOS computer, you can download an executable of the latest version
of Kind 2 from `here <https://github.com/kind2-mc/kind2/releases/latest/>`_\.
First make sure though that you have the required software described next.

Required Software
-----------------

To run Kind 2 the following software must be installed on your computer:

* Linux or macOS
* `ZeroMQ (C library) 4.x or later <https://zeromq.org>`_\, and
* a supported SMT solver

  * `Boolector <https://boolector.github.io/>`_
    (`5d18baa <https://github.com/Boolector/boolector/commit/5d18baa>`_ or later,
    for inputs with only machine integers),
  * `CVC4 <http://cvc4.cs.stanford.edu/>`_\ ,
  * `MathSAT 5 <http://mathsat.fbk.eu/index.html>`_\ ,
  * `Yices 2 <http://yices.csl.sri.com/>`_\ ,
  * `Yices 1 <http://yices.csl.sri.com/old/download-yices1-full.shtml>`_\ , or
  * `Z3 <https://github.com/Z3Prover/z3>`_ (presently recommended)

Docker
------

Kind 2 is also available on `Docker Hub <https://hub.docker.com/r/kind2/kind2/>`_.

Retrieving / updating the image
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Install docker <https://www.docker.com/products/docker>`_ and then run

.. code-block:: none

   docker pull kind2/kind2:dev

Docker will retrieve the *layers* corresponding to the latest version of the
Kind 2 repository, ``develop`` version. If you are interested in the latest
release, run

.. code-block:: none

   docker pull kind2/kind2

instead.

If you want to update your Kind 2 image to latest one, simply re-run the
``docker pull`` command.

Running Kind 2 through docker
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To run Kind 2 on a file on your system, it is recommended to mount the folder
in which this file is as a `volume <https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume>`_.
In practice, run

.. code-block:: none

   docker run -v <absolute_path_to_folder>:/lus kind2/kind2:dev <options> /lus/<your_file>

where


* ``<absolute_path_to_folder>`` is the absolute path to the folder your file is in,
* ``<your_file>`` is the lustre file you want to run Kind 2 on, and
* ``<options>`` are some Kind 2 options of your choice.

**N.B.**


* the fact that the path to your folder must be absolute is
  `a docker constraint <https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume>`_\ ;
* mount point ``/lus`` is arbitrary and does not matter as long as it is
  consistent with the last argument ``/lus/<your_file>``. To avoid name clashes
  with folders already present in the container however, it is recommended to
  use ``/lus``\ ;
* replace ``kind2:dev`` by ``kind2`` if you want to run the latest release of Kind2
  instead of the ``develop`` version;
* ``docker run`` does **not** update your local Kind 2 image to the latest one:
  the appropriate ``docker pull`` command does.

Packaging your local version of Kind 2
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the ``docker`` directory at the top level of the Kind 2 repository,
there is a ``Dockerfile`` you can use to
build your own Kind 2 image. To do so, just run

.. code-block:: none

   docker build -t kind2-local -f ./docker/Dockerfile .

at the root of the repository. ``kind2-local`` is given here as an example, feel
free to call it whatever you want.

Note that building your own local Kind 2 image **does require access to the
Internet**. This is because of the packages the build process needs to
retrieve, as well as for downloading the z3 and cvc4 solvers.

Building and installing
-----------------------

If you prefer, you can build Kind 2 directly from sources, 
either through the OPAM package manager (recommended) or
directly using dune.


Using OPAM
^^^^^^^^^^

Start by installing `OPAM 2.x <https://opam.ocaml.org/>`_
following the instructions on the website.
If you want to build the development version of Kind 2
that includes the most recent changes, as opposed to
the latest release, then run

.. code-block:: none

   opam pin add -n kind2 https://github.com/kind2-mc/kind2.git

(You can always undo this change later using this command ``opam unpin kind2``).

Otherwise, skip the step above and run

.. code-block:: none

   opam depext kind2
   opam install kind2

The first command installs the ZeroMQ C library
and any other external dependencies required using
the default package manager for your OS
(may require sudo permission).
The second command builds and installs ``kind2``.
By default, ``kind2`` will be installed into
the bin directory of your current OPAM switch. Run

.. code-block:: none

   opam install kind2 --destdir=<DIR>

to install the Kind 2 binary into ``<DIR>/bin``.
This will also create directories ``<DIR>/doc`` and ``<DIR>/lib``.

In alternative, you can clone https://github.com/kind2-mc/kind2.git,
move to its top-level directory, and run

.. code-block:: none

   make install

to have OPAM install ``kind2`` and its dependencies.

Note that z3 is available in OPAM so it is possible to install it too with OPAM by running:

.. code-block:: none

   opam install z3

Be aware, however, that this takes quite a bit of time (up to 25 minutes).


Direct Installation Using Dune 
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To build directly from sources you will also need the following software 
first:

* OCaml 4.07 or later,
* `Dune 2.0 or later <https://github.com/ocaml/dune>`_\,
* dune-build-info,
* `OCaml bindings for ZMQ <https://github.com/issuu/ocaml-zmq>`_\,
* `Yojson <https://github.com/ocaml-community/yojson>`_\,
* `num <https://github.com/ocaml/num>`_\,
* `Menhir <http://gallium.inria.fr/~fpottier/menhir/>`_ parser generator

First install this software on your system using your preferred method.
Then clone the `Kind 2 git repository <https://github.com/kind2-mc/kind2>`_, 
move to the top-level directory of the repository, and run

.. code-block:: none

   dune build src @install
   dune install --sections=bin --prefix <DIR>

to install the Kind 2 binary into ``<DIR>/bin``.

You need a supported SMT solver in your PATH environment variable when running ``kind2``.


Development
-----------

With OPAM 2.x you can create a local switch which will install all dependencies automatically.

.. code-block:: none

   opam switch create .
   make

Alternatively, you can install all dependencies in your current switch by running:

.. code-block:: none

   opam install . --deps-only
   make

For running the unit tests for front end, you can install ounit2 library using opam by running:

.. code-block:: none

   opam install ounit2

To run the ounit tests, you can use the following dune command:

.. code-block:: none

   dune test

Documentation
-------------

Documentation is available online in `HTML <http://kind.cs.uiowa.edu/kind2_user_doc/>`_
or `PDF <http://kind.cs.uiowa.edu/kind2_user_doc/doc.pdf>`_ forms.

In order to generate the documentation locally, you need:

* A GNU version of ``sed`` (``gsed`` on OSX)
* `Python v3.5 or later <https://www.python.org/downloads/>`_
* `Sphinx <https://www.sphinx-doc.org/en/master/usage/installation.html>`_

For HTML documentation, you additionally need:

* `sphinx-press-theme <https://pypi.org/project/sphinx-press-theme/>`_

For PDF documentation, you additionally need:

* `latexmk <https://packages.ubuntu.com/xenial/latexmk>`_
* `XeTeX <https://packages.debian.org/sid/texlive-xetex>`_
* `lmodern <https://packages.debian.org/sid/lmodern>`_

If you're on Debian/Ubuntu, assuming you have Python 3 installed,
you can run the following:

.. code-block:: bash

    sudo apt-get install python3-sphinx latexmk texlive-xetex lmodern
    pip3 install sphinx_press_theme

See ``doc/usr/README.rst`` for more information.
