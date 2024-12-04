## Installation of Isabelle 2024 - How to get the theories running

1) Install Isabelle2024 from https://isabelle.in.tum.de/
2) Download the current AFP from https://www.isa-afp.org/download/ 
3) Unpack to any location `my_location/afp`
4) Edit file `.isabelle/Isabelle2024/ROOTS` in your home directory and add the lines `my_location/afp/thys` and `THIS_DIR` to it.
   (Here `THIS_DIR` is the directory containing this README.)
5) Open Isabelle.  You can select the entry `Registers_Updated` in the `Theories` window's drop down bar
   (default is `default (HOL)`). This makes loading the files easier. 
   When changing the base entry, remember to close and re-open Isabelle.
   When re-opening, a small window opens building the heap image. This may take a while.
6) Open the file `O2H_Theorem.thy` from this directory. This load all relevant theories. 
   You can browse the other files using the theories window or the files window.
7) The folder `Registers_Updated` is an additional session that are not part of this formalization.
   It is an updated version of the `Registers` session contained in the AFP.
   We include it here because until the AFP version has been updated.
