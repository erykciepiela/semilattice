#!/bin/bash
ghcid --command "stack ghci semilattice:semilattice-exe --ghci-options=-fobject-code" --test "main"