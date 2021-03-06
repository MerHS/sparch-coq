# sparch-coq
Reconstruct SpArch from C-light && Coq/Gallina

## tl;dr

```sh
make main
./sparch --print --random 10 10 10
```

## How to install

I tested it on Linux only (Ubuntu/Arch).

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
opam pin add coq 8.12.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-vst # this requires a long time. (30 min)

## Install CompCert
wget -O compcert.tar.gz https://github.com/AbsInt/CompCert/archive/v3.8.tar.gz 
tar xf compcert.tar.gz
mv CompCert-3.8 compcert
cd compcert
./configure -clightgen x86_32-linux; make # this also requires very long time.
cd ..
rm compcert.tag.gz

# 3. build project
make main # build executable SpGEMM program
./sparch # generate random two 1000*1000 matrices and multply it.

make # verify sparch.c by Coq/VST.
```

## How to run

``` sh
# multiply two matrices from `./test.mat` and compare with normal matrix multiplication
./sparch --print

# multiply random matrix (30 x 50, 50 x 70)
# it first generates random dense matrix and convert to sparse matrix.
./sparch --random 30 50 70

# multiply random sparse matrix (do not print comparison)
./sparch --sparse --random 30 50 70
```

