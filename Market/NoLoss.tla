------------------------------ MODULE NoLoss ------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt,
            MarketHelpers

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
            \* Drops are proportional entitlements to the AMM liquidity pools
            drops,
            \* Limit Books
            limits,
            \* Pools hold the AMM liquidity
            pools,
            \* The reserve holds the initial amounts
            reserve,
            \* Stop Books
            stops

-----------------------------------------------------------------------------

NoLoss(askCoin, bidCoin, limitsUpd, stopsUpd) ==
\* Getting to this point means that both an Ask Stop and a Bid
\* Limit are equal and enabled.
LET limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    stopBook  == stopsUpd[bidCoin, askCoin]
    stopHead == Head(stopBook)
    
    \* Strike Exchrate either limit or stop as equal
    strikeExchrate ==
        CASE Len(limitBook) = 1 /\ Len(stopBook) = 1 ->
                limitHead.exchrate
        []   Len(limitBook) > 1 /\ Len(stopBook) = 1 ->
                limitBook[2].exchrate
        []   Len(limitBook) = 1 /\ Len(stopBook) > 1 ->
                << 
                    stopBook[2].exchrate[2],
                    stopBook[2].exchrate[1]
                >>
        []   Len(limitBook) > 1 /\ Len(stopBook) > 1 ->
                \* Strike price is based on the most adjacent
                \* order based on price.
                IF LTE(
                        limitBook[2].exchrate,
                        <<
                            stopBook[2].exchrate[2],
                            stopBook[2].exchrate[1]
                        >>
                    )
                THEN limitBook[2].exchrate
                ELSE <<
                        stopBook[2].exchrate[2],
                        stopBook[2].exchrate[1]
                    >>
    stopHeadBidAmt == 
        (stopHead.amount * strikeExchrate[2]) \div
        strikeExchrate[1]
    strikeBidAmt ==
        IF limitBook[1].amount <= stopHeadBidAmt
        THEN    limitBook[1].amount
        ELSE    stopHeadBidAmt
    limitHeadAskAmt ==
        (limitHead.amount * strikeExchrate[1]) \div
        strikeExchrate[2]
    strikeAskAmt == 
        IF stopHead.amount <= limitHeadAskAmt
        THEN    limitHeadAskAmt
        ELSE    stopHead.amount
IN

    /\  accounts' = 
        [ accounts EXCEPT 
            ![limitHead.account, bidCoin] = @ - strikeBidAmt,
            ![limitHead.account, askCoin] = @ + strikeAskAmt,
            ![stopHead.account, bidCoin] = @ + strikeBidAmt,
            ![stopHead.account, askCoin] = @ - strikeAskAmt
        ]

    /\  IF limitHead.amount = strikeBidAmt
            THEN limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
            ELSE limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = 
                        <<[
                            account |-> limitBook[1].account,
                            exchrate |-> limitBook[1].exchrate,
                            amount |-> limitBook[1].amount - strikeBidAmt
                        ]>> \o Tail(@)
                 ]
    /\  IF stopHead.amount = strikeAskAmt
            THEN stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = Tail(@)]
            ELSE stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = 
                        <<[
                            account |-> stopBook[1].account,
                            exchrate |-> stopBook[1].exchrate,
                            amount |-> stopBook[1].amount - strikeAskAmt
                        ]>> \o Tail(@)
                 ]


=============================================================================