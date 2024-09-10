// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//First part proof of distributive law:
//p ∨ (q ∧ r)     is equivalent to
// (p ∨ q) ∧ (p ∨ r)


@pure def orDist1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p | (q & r)) |- ((p | q) & (p | r))
      Proof(

      //PROOF GOES HERE
      1 ((p | q) & (p | r)) Premise,
      2 ( p | q ) AndE1(1),
      3 ( p | r) AndE2(2),
      4 SubProof(
        5 Assume(p),
        6 ( p | (q & r)) by OrI1(5)
      )
      7 SubProof(
        8 Assume(q),
        9 SubProof(
          10 Assume(p)
          11( p | (q & r) ) by OrI1(10),
        )
        12 SubProof(
          13 Assume(r),
          14 ( q & r ) by AndI(8,13)
        )
      )

    )
    //@formatter:on
  )
}