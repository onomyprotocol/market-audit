------------------------------- MODULE Limit --------------------------------
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

Limit(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    stopBook == stopsUpd[bidCoin, askCoin]    
    limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    poolExchrate == << pools[bidCoin, askCoin], pools[askCoin, bidCoin] >>
    strikeExchrate ==
        CASE Len(stopBook) = 0 /\ Len(limitBook) = 1 ->
                Head(limitBook).exchrate
        []   Len(stopBook) = 0 /\ Len(limitBook) > 1 ->
                limitBook[2].exchrate
        []   Len(stopBook) > 0 /\ Len(limitBook) = 1 ->
                <<
                    Head(stopBook).exchrate[2],
                    Head(stopBook).exchrate[1]
                >>
        []   Len(stopBook) > 0 /\ Len(limitBook) > 1 ->
                LET stopHeadInvExchrate == <<
                        Head(stopBook).exchrate[2],
                        Head(stopBook).exchrate[1]
                    >>
                IN
                    IF LT(limitBook[2].exchrate, stopHeadInvExchrate)
                    THEN limitBook[2].exchrate
                    ELSE stopHeadInvExchrate

    IN
        LET
            maxPoolAmt == MaxPoolBid(
                poolExchrate[1], 
                poolExchrate[2], 
                strikeExchrate
            )
        IN  
            LET strikeBidAmt ==
                    IF limitHead.amount <= maxPoolAmt
                    THEN limitHead.amount
                    ELSE maxPoolAmt

                    strikeAskAmt == (
                        strikeBidAmt *
                        strikeExchrate[1]
                    ) \div strikeExchrate[2]
            IN
                /\  IF limitHead.amount <= maxPoolAmt
                    THEN limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
                    ELSE limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Append(
                                Tail(@), 
                                [
                                    account |-> limitBook[1].account,
                                    exchrate |-> limitBook[1].exchrate,
                                    amount |-> limitBook[1].amount - strikeBidAmt
                                ]
                            )
                         ]
                /\  accounts' = 
                    [ accounts EXCEPT 
                        ![limitBook[1].account, bidCoin] = @ - strikeBidAmt,
                        ![limitBook[1].account, askCoin] = @ + strikeAskAmt
                    ] 
                /\  pools' = 
                    [ pools EXCEPT
                        ![askCoin, bidCoin] = @ + strikeBidAmt,
                        ![bidCoin, askCoin] = @ - strikeAskAmt 
                    ]
                /\  UNCHANGED <<drops, reserve, stops>>
=============================================================================
