# Dr. Y's Ethereum Contract Analyzer

[An online version](http://dr-y.no-ip.net)

## How to use

* Install OCaml (4.02.3 works) and [opam](https://opam.ocaml.org/)
* `opam install lwt cohttp coq getopt batteries`
* `make`
* `./main.native -p 9999`
* access [localhost:9999](http://localhost:9999)

## LICENSE

* `big.ml` comes from the Coq development team under LGPL version 2.1
* The other files are currently distributed with LGPL version 2.1.