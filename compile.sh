#!/bin/bash
ocamlbuild -use-ocamlfind -pkgs batteries,getopt,lwt,cohttp,cohttp.lwt -cflag -ppopt -cflag -lwt-debug main.native main.byte
