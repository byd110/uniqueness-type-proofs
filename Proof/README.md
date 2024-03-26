## Acknowledements

The mechanizations based on lists (env.v) reuse some libraries by [Reachability types](https://github.com/TiarkRompf/reachability) from Purdue University.

## Installation

https://coq.inria.fr/download

Visual Studio Extension can be installed by searching `VSCoq' in Visual Studio Marketplace.

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

To clean up the generated files:

`make -f CoqMakefile clean` 

Compatibility tested with Coq `8.15.0`.

## supportive materials (old version)

Coq_formalization.pdf rewrite all the definitions and the main theroem in the form of inference rules for quick lookup.