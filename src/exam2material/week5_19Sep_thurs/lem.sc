// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def lem(p: B): Unit = {
  Deduce(
    //@formatter: off

    |- ( p | !p )
      Proof(
      1 SubProof(
        2 Assume(!(p | !p)),
        3 SubProof(
          4 Assume(p),
          5 (p | !p) by OrI1(4),
          6 (F) by NegE(5,2),
        ),
        7 (!p) by NegI(3),
        8 (p | !p) by OrI2(7),
        9 (F) by NegE(8,2)

        //if we got p | !p, could contradict with line p

        //goal F
      ),
      10 (p | !p) by PbC(1),
      //use pbc

    )
    //@formatter:on
  )
}