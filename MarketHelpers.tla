--------------------------- MODULE MarketHelpers ---------------------------
EXTENDS Integers
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) == a[1]*b[2] > a[2]*b[1]

GTE(a, b) == a[1]*b[2] >= a[2]*b[1] 

LT(a, b) == a[1]*b[2] < a[2]*b[1]

LTE(a, b) == a[1]*b[2] <= a[2]*b[1]

(***************************************************************************)
(* Max amount that pool may sell of ask coin without                       *)
(* executing the most adjacent order                                       *)
(*                                                                         *)
(* Differential Invariant:                                                 *)
(* d(poolAsk) / d(poolBid) = d(erate)                                      *)
(* d(poolAsk) = d(poolBid) * d(erate)                                      *)
(*                                                                         *)
(* Integrate over poolAsk on lhs and poolBid & erate on rhs then           *)
(* substitute and simplify                                                 *)
(*                                                                         *)
(* MaxPoolBid ==    [(BidBalanceInitial * exchrateFinal^2) \               *)
(*                  (2 * exchrateFinal + exchrateInitial)] -               *)
(*                  AskBalanceInitial                                      *)
(***************************************************************************)
MaxPoolBid(bidBalInit, askBalInit, erateInit, erateFinal) ==

(
    bidBalInit * erateFinal * erateFinal) \div
    (
        (
            (
                (2 * erateFinal[1]) \div
                erateFinal[2]
            ) * erateInit[2] +
        erateInit[1]
    ) \div erateInit[2]
)
 - askBalInit

=============================================================================