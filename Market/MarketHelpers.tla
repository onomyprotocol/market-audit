--------------------------- MODULE MarketHelpers ---------------------------
EXTENDS Naturals, Sequences, SequencesExt, FiniteSets
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
EQ(a, b) == a[1]*b[2] = a[2]*b[1]

GT(a, b) == a[1]*b[2] > a[2]*b[1]

GTE(a, b) == a[1]*b[2] >= a[2]*b[1] 

LT(a, b) == a[1]*b[2] < a[2]*b[1]

LTE(a, b) == a[1]*b[2] <= a[2]*b[1]

ADDRatio(a, b) == <<(a[1]*b[2] + b[2]*a[1]), a[2] * b[2]>>

(***************************************************************************)
(* Max amount that pool may sell of ask coin without                       *)
(* executing the most adjacent order                                       *)
(***************************************************************************)
BidCoinBalFinal(memberABal, memberBBal, positionRate) ==
(((positionRate[1] * 100) \div (positionRate[1] + positionRate[0])) * (memberABal + memberBBal)) \div 100

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

\* Asserts that balance covers the sum of all position amounts in limitsSeq and stopsSeq
PositionInv( limitsSeq, stopsSeq, balance ) ==
    SumSeqPos( limitsSeq ) + SumSeqPos(stopsSeq) <= balance


TruncatePositions( limitsSeq, stopsSeq, balance ) == 
    \* we use CHOOSE to get one pair, but the cutoff pair is not necessarily unique:
    \* consider: balance = 1, limtsSeq (amounts) = << 1,1 >>, stopsSeq (amounts) = << 1, 1 >>
    \* Truncation returns either << <<>>, <<1>> >> or << <<1>>, <<>> >>
    \* It is up to the implementation to define a deterministic way of resolving 
    \* cases with multiple solutions. 
    \* For example, the implementation could prefer to truncate limits over stops whenever possible
    LET cutoffs == CHOOSE pair \in (DOMAIN limitsSeq \union {0}) \X (DOMAIN stopsSeq \union {0}):
        LET i == pair[1]
            j == pair[2] 
        IN 
        /\ PositionInv( SubSeq(limitsSeq, 1, i) , SubSeq(stopsSeq, 1, j), balance )
        /\ i < Len(limitsSeq) => 
            ~PositionInv( SubSeq(limitsSeq, 1, i+1) , SubSeq(stopsSeq, 1, j), balance ) 
        /\ j < Len(stopsSeq) =>
            ~PositionInv( SubSeq(limitsSeq, 1, i) , SubSeq(stopsSeq, 1, j +1 ), balance ) 
    IN << 
        SubSeq(limitsSeq, 1, cutoffs[1]), 
        SubSeq(stopsSeq, 1, cutoffs[2])
        >>
=============================================================================