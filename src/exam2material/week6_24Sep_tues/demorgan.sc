// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//¬p ∨ ¬q     and     ¬(p ∧ q)

//prove equivalence

@pure def demorgan1(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    ( !p | !q ) |- ( !(p & q) )
      Proof(
        1 ( !p | !q  ) by Premise,
        2 SubProof(
          3 Assume(p & q),
          4 ( p ) by AndE1(3),
          5 ( q ) by AndE2(3),

          6 SubProof(
            7 Assume( !p ),
            8 (F) by NegE(4, 7)
            //goal: F
          ),
          9 SubProof(
            10 Assume ( !q ),
            11 (F) by NegE(5, 10),
            //goal: F
          ),
          12 ( F ) by OrE(1, 6, 9)
          //goal: F
        ),
        13 ( !(p & q) ) by NegI(2)
    )
    //@formatter:on
  )
}

@pure def demorgan2(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    ( !(p & q) ) |- ( !p | !q )
      Proof(
        1 ( !(p & q) ) by Premise,
        2 SubProof(
          3 Assume(!(!p | !q)),

          //Try to contradict with premise
          //would need p&q
          //try to prove p (try with pbc
          4 SubProof(
            5 Assume (!p),
            6 (!p | !q) by OrI1(5),
            7 (F) by NegE(6,3),
          ),
          8 (p) by PbC(4),

          //try to prove q (very similar to 4)
          //then put p & q together, will contradict premise
        )

    )
    //@formatter:on
  )
}