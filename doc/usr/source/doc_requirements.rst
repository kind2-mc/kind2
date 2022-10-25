In order to generate the documentation locally, you need:

* A GNU version of ``sed`` (``gsed`` on OSX)
* `Python v3.5 or later <https://www.python.org/downloads/>`_
* `Sphinx <https://www.sphinx-doc.org/en/master/usage/installation.html>`_

For HTML documentation, you additionally need:

* `sphinx-press-theme <https://pypi.org/project/sphinx-press-theme/>`_

For PDF documentation, you additionally need:

* `latexmk <https://personal.psu.edu/~jcc8/software/latexmk/>`_
* `XeTeX <https://xetex.sourceforge.net>`_
* `lmodern <https://www.gust.org.pl/projects/e-foundry/latin-modern>`_

If you're on Debian/Ubuntu, assuming you have Python 3 installed,
you can run the following:

.. code-block:: bash

    sudo apt-get install python3-sphinx latexmk texlive-xetex lmodern
    pip3 install sphinx_press_theme
