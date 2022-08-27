# The Blueprint For Formalizing Geometric Algebra in Lean

* [Lean Code](https://github.com/pygae/lean-ga/)
* [Blueprint](https://pygae.github.io/lean-ga/blueprint/)
* [Blueprint Source](https://github.com/pygae/lean-ga/docs/blueprint)
* [Dependency Graph](https://pygae.github.io/lean-ga/blueprint/dep_graph.html)
* Slides
  - [ICCA2020](https://pygae.github.io/lean-ga/ICCA2020/)
  - [Noncommutative algebras, computer algebra systems, and theorem provers](https://eric-wieser.github.io/divf-2022)
  - [The Universal Property of the Clifford Algebra](https://eric-wieser.github.io/brno-2021/)

Much of the project infrastructure has been adapted from the [liquid tensor experiment](https://leanprover-community.github.io/liquid/) and [Unit Fractions](https://github.com/b-mehta/unit-fractions).

## Dependencies

If you simply want to produce the `pdf` version of the blueprint, you don't
need anything beyond your usual TeX installation, or you may install and use [tectonic](https://tectonic-typesetting.github.io/en-US/install.html).

In order to build the `html` version you need 
[plasTeX](https://github.com/plastex/plastex/) and its 
[blueprint plugin](https://github.com/PatrickMassot/leanblueprint) and a few extra dependencies. 

You first need to install Graphviz and PyGraphviz:

```bash
# On Ubuntu:
apt-get install graphviz libgraphviz-dev
# On Mac:
brew install graphviz
/opt/homebrew/Cellar/graphviz/5.0.1
# change `GV_PATH` to the path shown by `brew info graphviz`
export GV_PATH=/opt/homebrew/Cellar/graphviz/5.0.1/
pip install --global-option=build_ext \
              --global-option="-I$GV_PATH/include/" \
              --global-option="-L$GV_PATH/lib/" \
              pygraphviz
```

and some other Python packages:

```bash
pip install -r requirements.txt
```

Then some minimal LaTex related packages if you use tectonic and don't have a usual TeX installation:

```bash
# On Ubuntu:
apt-get install dvisvgm texlive-binaries pdf2svg
# On Mac:

```

## Building

NOTE: The following file paths are relative to `blueprint/`.

The source for the blueprint is in `src`. 
If you only want to build it as a `pdf` file then you can simply run 
`xelatex print.tex` or `tectonic print.tex` depending on your TeX choice.

More complicated goals are easier to handle using [python invoke](https://www.pyinvoke.org/).
You can run `inv -l` to see the available actions and their functions.

In particular `inv bp` will build the PDF file, `inv web` will build the website,
and `inv dev` will serve the website locally on http://localhost:8080/ and rebuild PDF and the website on file changes. 

Note that the dependency graph using graph-viz won't work if you simply open `web/dep_graph.html` in 
a browser because of browser paranoia. It has to be accessed through a web server. 

## Authoring

The main TeX file to edit is `content.tex`. It is a normal TeX file except that
each definition and statement must have a `\label` and there are four special LaTeX macros:
* `\lean{name}` indicates the fully namespaced Lean declaration that formalizes
  the current definition or statement.
* `\leanok` means the current definition, statement or proof has been fully formalized (in particular
  a lemma can have `\leanok` in its statement without having it in its proof environment.
* `\uses{refs}` where `refs` is a comma-separated list of LaTeX label can be
  put inside a definition, statement or proof environment. It means each of
  those labels is used by the current environment. This is what creates edges
  in the dependency graph. This mechanism is completely independent from
  `\ref`. With `leanok` this is the most important command to organize work.
  Note that `\uses` in proofs don't need to repeat those in the statement.
* `\proves{label}` can be put in a `proof` environment to indicate which
  statement is proved if this is not obvious (ie it is not proving the
  preceding statement).
