--------------------------- MODULE MarketHelpers ---------------------------
EXTENDS Integers, Sequences, SequencesExt, FiniteSets
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
EQ(a, b) == a[1]*b[2] = a[2]*b[1]

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
MaxPoolBid(askBalInit, bidBalInit, erateFinal) ==

(
    bidBalInit * erateFinal * erateFinal) \div
    (
        (
            (
                (2 * erateFinal[1]) \div
                erateFinal[2]
            ) * bidBalInit +
        askBalInit
    ) \div bidBalInit
)
 - askBalInit

\* Given a sequence of positions `seq \in Seq(PositionType)`, sum up
\* all of the position amounts. Returns 0 if seq is empty.
SumSeqPos(seq) == FoldLeft( LAMBDA p,q: p + q.amount, 0, seq )

SelectAcctSeq(acct, book) == SelectSeq(book, LAMBDA pos: pos.account = acct)

TruncateAcctSeq(acct, bal, askCoin, bidCoin, limits, stops) ==
LET limitBook == limits[askCoin, bidCoin]
    stopBook == stops[bidCoin, askCoin]
IN
    LET F[i \in 0 .. Len(stopBook)] ==
        LET G[j \in 0 .. Len(limitBook)] ==
            IF SumSeqPos(SelectAcctSeq(acct, F[i])) +
                SumSeqPos(SelectAcctSeq(acct, G[i])) <=
                bal 
            THEN    << stopBook, limitBook >>
            ELSE
                IF  SumSeqPos(SelectAcctSeq(acct, F[i-1])) +
                    SumSeqPos(SelectAcctSeq(acct, G[i])) <=
                    bal
                THEN    <<F[i-1], G[i]>> 
                ELSE
                    IF  SumSeqPos(SelectAcctSeq(acct, F[i])) +
                        SumSeqPos(SelectAcctSeq(acct, G[i-1])) <=
                        bal
                    THEN    <<F[i], G[i-1]>>
                    ELSE    <<F[i-1], G[i-1]>>
        IN  G[Len(limitBook)]
    IN  F[Len(stopBook)]
                    
=============================================================================