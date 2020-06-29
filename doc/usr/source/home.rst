Kind 2
======

`Kind 2 <http://kind.cs.uiowa.edu/>`_ \ is a multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs.

Kind 2 takes as input a Lustre file annotated with properties to be proven
invariant (see :ref:`Lustre Input <2_input/1_lustre>`), and
outputs which of the properties are true for all inputs, as well as an input
sequence for those properties that are falsified. To ease processing by external tools,
Kind 2 can output its results in JSON and XML formats (see :ref:`JSON / XML Output <3_output/2_machine_readable>`).

By default Kind 2 runs a process for bounded model checking (BMC), a process
for k-induction, two processes for invariant generation, and a process for IC3
in parallel on all properties simultaneously. It incrementally outputs
counterexamples to properties as well as properties proved invariant.

The following command-line options control its operation (run ``kind2 --help`` for a full list). See :ref:`Techniques <1_techniques/1_techniques>` for configuration examples and more details on each technique.

``--enable {BMC|IND|INVGEN|INVGENOS|IC3}`` Select model checking engines

By default, all three model checking engines are run in parallel. Give any combination of ``--enable BMC``\ , ``--enable IND`` and ``--enable IC3`` to select which engines to run. The option ``--enable BMC`` alone will not be able to prove properties valid, choosing ``--enable IND`` only will not produce any results. Any other combination is sound (properties claimed to be invariant are indeed invariant) and counterexample-complete (a counterexample will be produced for each property that is not invariant, given enough time and resources).

``--timeout_wall <int>`` (default ``0`` = none) -- Run for the given number of seconds of wall clock time

``--timeout_virtual <int>`` (default ``0`` = none) -- Run for the given number of seconds of CPU time

``--smtsolver {CVC4|Yices|Yices2|Z3}`` (default ``Z3``\ ) -- Select SMT solver

The default is ``Z3``\ , but see options of the ``./build.sh`` script to override at compile time

``--cvc4_bin <file>`` -- Executable for CVC4

``--yices_bin <file>`` -- Executable for Yices 1

``--yices2_bin <file>`` -- Executable for Yices 2 (SMT input)

``--z3_bin <file>`` -- Executable for Z3

``-v`` Output informational messages

``-json`` Output in JSON format

``-xml`` Output in XML format

Requirements
------------

* Linux or Mac OS X,
* `OPAM <http://opam.ocaml.org>`_\,
* `libzmq (c lib) 4.x or later <https://zeromq.org>`_\,
* OCaml 4.07 or later,
* `Yojson <https://github.com/ocaml-community/yojson>`_\ ,
* `num <https://github.com/ocaml/num>`_ (part of OCaml distribution until 4.06),
* `Menhir <http://gallium.inria.fr/~fpottier/menhir/>`_ parser generator, and
* a supported SMT solver

  * `CVC4 <http://cvc4.cs.stanford.edu/>`_\ ,
  * `Yices 2 <http://yices.csl.sri.com/>`_\ ,
  * `Yices 1 <http://yices.csl.sri.com/old/download-yices1-full.shtml>`_\ , or
  * `Z3 <https://github.com/Z3Prover/z3>`_ (presently recommended)

Building and installing
-----------------------

Move to the top-level directory of the Kind 2 distribution, Then, run

.. code-block:: none

   opam install kind2

By default, ``kind2`` will be installed into the bin directory of your current OPAM switch. Run 

.. code-block:: none

   opam install kind2 --destdir=DIR

to install the Kind 2 binary into ``<DIR>/bin``.

You need a supported SMT solver on your path when running ``kind2``.

Development
-----------

With OPAM 2.x you can create a local switch which will install all dependencies automatically.

.. code-block:: none

   opam switch create .
   make

Documentation
-------------

Documentation is available online in `HTML <http://kind.cs.uiowa.edu/kind2_user_doc/>`_ or `PDF <http://kind.cs.uiowa.edu/kind2_user_doc/doc.pdf>`_ forms.

.. include:: doc_requirements.rst

See ``doc/usr/README.rst`` for more information.


Online Web Application
----------------------

You can try `Kind 2 from your browser <https://kind.cs.uiowa.edu/app/>`_ if you are not ready to install it.


Docker
------

Kind 2 is available on `docker <https://hub.docker.com/r/kind2/kind2/>`_.

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

To run Kind 2 on a file on your system, it is recommended to mount the folder in which this file is as a `volume <https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume>`_.
In practice, run

.. code-block:: none

   docker run -v <absolute_path_to_folder>:/lus kind2/kind2:dev <options> /lus/<your_file>

where


* ``<absolute_path_to_folder>`` is the absolute path to the folder your file is
  in,
* ``<your_file>`` is the lustre file you want to run Kind 2 on, and
* ``<options>`` are some Kind 2 options of your choice.

**N.B.**


* the fact that the path to your folder must be absolute is `a docker constraint <https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume>`_\ ;
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
