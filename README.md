# sparch-coq
Reconstruct SpArch from Coq/Gallina

## How to install

I tested it only from Linux (Ubuntu/Arch).

1. Install OCaml compiler and OPAM (OCaml Package manager)
2. Install Coq and Libraries (this requires quite a long time)
3. Make

``` sh
# 1. Ocaml
## install OPAM
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

opam init
eval `opam env`
opam switch create 4.10.0
eval `opam env`

## check ocaml is installed
ocaml -version # 4.10.0
opam -version  # 2.0.7

# 2. Coq & VST
## Check Coq dependency
opam install opam-depext
opam-depext coq

## This shows the required dependencies for Coq.
## m4 and findutils might be required in Ubuntu, then install it.
sudo apt-get install m4

## Install Coq and dependencies
opam pin add coq 8.12.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-vst # this requires a long time. (almost 30 min)

# 3. build project
make
```

