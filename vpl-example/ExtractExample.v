Require Import Example.
Require Import Vpl.ImpureConfig.
Require Import ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extraction Blacklist List String Nat.

Extraction Library Example.
