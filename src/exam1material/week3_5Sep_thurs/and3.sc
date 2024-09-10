// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Prove the sequent:
//p ∧ q ∧ r ⊢ q


@pure def and3(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p & q & r) |- (q)
      Proof(

      //PROOF GOES HERE
      //        * Top level operator
      1 ( p ^ q ^ r) by Premise,
      2 ( p ^ q ) by AndE1(1),
      3 ( q ) by AndE2(2),

    )
    //@formatter:on
  )
}