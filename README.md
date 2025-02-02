	
# Contents 
This repository includes the following artifacts:
	- Formal models: Executable, publicly available transition system
representations of Floodsub (fn.lisp) and Broadcastsub (bn.lisp).
	- Formalized notions of correctness: The formalization of the WEB
refinement which includes defining the refinement map, an
equivalence relation among related states of Floodsub and
Broadcastsub, well founded functions and the formalized WEB
 conditions, in f2b-commit.lisp and f2b-ref2.lisp.
	- Mechanized refinement proof: A formally verified proof of the WEB
  conditions in ACL2s demonstrating that Floodsub refines Broadcastsub
  under connected network assumptions.
  
# Build
 The proofs of refinement, along with the Broadcastsub and Floodsub
 models can be built by running ./make.sh in this folder. Makesure
 that cert.pl is in the path.
 
# Demo
A demo.lisp file has been provided that contains a top level
description of the included models and properties. Once the artifacts
have been certified, go through each of the forms given in demo.lisp.
  
  
  
