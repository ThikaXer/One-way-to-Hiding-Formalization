## Installation of Isabelle 2024 - How to get the theories running

1) Install Isabelle2024 from https://isabelle.in.tum.de/
2) Download the current AFP from https://www.isa-afp.org/download/ 
3) Unpack to any location `my_location/afp`
4) Add the afp-unruh-edits to Isabelle with `isabelle components -u my_location/afp/thys` (for linux, else please search https://www.isa-afp.org/help/)
5) Open Isabelle.  You can select the entry `Registers` in the `Theories` window's drop down bar (default is `default (HOL)`). This makes loading the files easier. When changing the base entry, remember to close and re-open Isabelle. When re-opening, a small window opens building the heap image. This may take a while.
6) Open the file `O2H_Theorem.thy` from this directory. This load all relevant theories. You can browse the other files using the theories window or the files window.
7) The folders `Registers_Updated` and `Hilbert_Space_Tensor_Product` are additional theories that are not part of this formalization. They are developed by Dominique Unruh and are not yet part in the AFP. They are publicly available at https://github.com/dominique-unruh/afp/tree/unruh-edits/thys,          subfolders Registers and Hilbert_Space_Tensor_Product. We include them here for the reviewers' convenience.

