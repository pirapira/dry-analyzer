Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZBigInt.

Require Import evm2.


Extract Inductive unit => "unit" [ "()" ].
(* Extract Inductive bool => "bool" [ "true" "false" ].*)
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Recursive Extraction Library evm2.
