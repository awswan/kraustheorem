This is a more general version of Kraus' theorem that we can in a certain weak sense "invert" propositional truncation maps, from section 8.4 of https://doi.org/10.23638/LMCS-13(1:15)2017. In this generalisation we show the result for any cofibration, from which the original can be recovered by noting that propositional truncation is a cofibration.

In order to state the result cleanly, we use two level type theory, interpreting definitional equality as strict equality. Semantically, we typically interpret definitional equality as strict equality. Similarly, it is consistent to add a rewrite rule that makes any strict equality into a definitional equality, although we don't actually do this.

Files are layed out as follows:

- `Basics.agda` Some basic propositions in type theory
- `StrictBasics.agda` Some basic propositions for dealing with strict equality in 2 level type theory
- `Cofibrations.agda` Definition of cofibration
- `KrausTheorem.agda` Contains main result
- `CofibrationExamples.agda` A mostly independent file that uses the Cubical Agda library to give a couple of examples of cofibration, including truncation.

A recent version of Agda that supports two level type theory is needed. Cubical Agda is only used for the last file, so although it is listed as a dependency in `kraustheorem.agda-lib`, you can remove it and most things will still work.