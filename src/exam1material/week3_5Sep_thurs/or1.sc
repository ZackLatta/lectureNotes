// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Prove OR is commutative:
//p ∨ q ⊢ q ∨ p


@pure def or1(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    (p | q) |- (q | p)
      Proof(

      //PROOF GOES HERE
      1 ( p | q) Premise,
      2 SubProof(
        3 Assume (p),
        4 ( q | p ) by OrI2(3),
      )
      5 SubProof(
        6 Assume(q),
        7 ( q | p ), OrI1(6),
      8 ( q v p ), OrE(1, 2, 5)
      )



    )
    //@formatter:on
  )
}