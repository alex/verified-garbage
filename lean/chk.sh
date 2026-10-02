#!/bin/bash
# Elaborate a file with the lakefile's options.
cd /home/user/verified-garbage/lean
export PATH=$HOME/.elan/bin:$PATH
opts=$(grep -oE "^weak\.[A-Za-z_.]+ = (true|false)" lakefile.toml | sed -E 's/ = /=/; s/^/-D/' | tr '\n' ' ')
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true $opts "$@" 2>&1 | grep -v "^Note:\|^Hint:\|linter can be disabled\|^$\|^  \[apply\]" | head -${N:-60}
