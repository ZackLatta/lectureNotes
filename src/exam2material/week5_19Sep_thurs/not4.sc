// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not4(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

      ( !q __>: !p )|- ( p __>: q )
      Proof(
      1 (  !q __>: !p ) by Premise,
      2 SubProof(
        3 Assume (p),

        4 SubProof(
          5 Assume(!q),
          6 (!p) by ImplyE(1,5),
          7 (F) by NegE (3,6),
        ),
        8 (q) by PbC(4),
      ),
        9 ( p __>: q) by ImplyI(2, 8),
    )
    //@formatter:on
  )
}