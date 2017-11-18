# Dr. Y's Ethereum Contract Analyzer

[Online version](http://dry.yoichihirai.com/)

## How to use

* Install OCaml (4.02.3 works) and [opam](https://opam.ocaml.org/)
* `opam install lwt cohttp coq getopt batteries ocamlnet`
* `make`
  * Depending on where you installed OPAM packages, you may need to
    prefix the `make` command with `PATH` and `LD_LIBRARY_PATH`
    variable settings. For example, when OPAM packages are installed
    in `~/.opam`, execute the following command instead:
    ```
    PATH=$HOME/.opam/system/bin:$PATH LD_LIBRARY_PATH=$HOME/.opam/system/lib/stublibs make
    ```
* `./main.native -p 9999`
* access [localhost:9999](http://localhost:9999)
* paste some EVM bytecode (beginning from 0x) in the text box
* hit "Analyze" button
* the analyzer tells what the bytecode does, to some point

## LICENSE

* `big.ml` comes from the Coq development team under LGPL version 2.1
* The other files are currently distributed with LGPL version 2.1.

