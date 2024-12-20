Theorem 1 from NFM2025 is encoded at line 217 of `UTPANNProofs.thy`.

The verification condition for Marabou are encoded at line 311 of `UTPANNProofs.thy`.

We encode the predicate ANNController as CircANN at line 214 of `UTP_ANN_Defs.thy`, and StandardController as CyclicRCController at line 23 of the same file.

We encode our pattern for describing HiddenLayers || OutputLayer, supporting the definition of ANNController, 
at line 209 of UTP_ANN_Defs.thy.

The file `conf.thy` contains an implementation of our conformance relation, used by `UTPANNProofs.thy`

In the directory `Marabou_Scripts` we have a shell script that automates conformance proof between AnglePID and AnglePIDANN: `anglepid_conformance_testing.sh`.

We have also included a log of a succesful run in `anglepid_conformance_testing.txt`.
