#!/bin/bash
eval $(opam env --safe)
dune build --release
dune install --release
mkdir binaries
cp $(which gen_fma) $(which monpoly) binaries
