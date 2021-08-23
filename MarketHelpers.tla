----------------------------- MODULE MarketHeplers -------------------------
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
MaxPoolBid(erateInitial, erateFinal) ==
\* AskBalInit / BidBalInit = erateInit[1] / erateInit[2]
LET a == erateInitial[1]
    b == erateInitial[2]
    c == erateInitial[1]
    d == erateFinal[2]
IN
    (
        (
            b * c^2
        ) \div (
            2 * c + a
        )   
    ) - a