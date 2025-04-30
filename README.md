	
# Contents 
This repository includes the following artifacts:
1. **Formal models**: Executable, publicly available transition system
representations of Floodnet (fn-trx.lisp) and Broadcastnet
(bn-trx.lisp).
2. **Transition Relations**: Transition relations expressed as boolean
   functions over Floodnet and Broadcastnet states in trx-rels.lisp.
3. **Formalized notions of correctness**: The formalization of the WFS
refinement which includes defining the refinement map and rel-B
relation in f2b-sim-ref.lisp.
4. **Good Floodnet States**: Definitions and properties of good
   floodnet states.
5. **Mechanized refinement proof**: A formally verified proof of the WFS
  conditions in ACL2s demonstrating that Floodnet refines its
  specification: Broadcastnet.
  
# Build
 The proofs of refinement, along with the Broadcastnet and Floodnet
 models can be built by running ./make.sh in this folder. Make sure
 that [cert.pl](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=BUILD____CERT.PL&path=4360/152) is in the path.
 
# Demo
A demo.lisp file has been provided that contains a top level
description of the included models and properties. Once the artifacts
have been certified, go through each of the forms given in demo.lisp.
  
  
  
