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
    askCoinPoolBalInit == pools[bidCoin, askCoin]
    bidCoinPoolBalInit == pools[askCoin, bidCoin]
    poolExchrate == << askCoinPoolBalInit,  bidCoinPoolBalInit >>

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
            maxBidCoinPoolBalFinal == BidCoinBalFinal(
                poolExchrate[1], 
                poolExchrate[2], 
                strikeExchrate
            )
            maxPoolBid == maxBidCoinPoolBalFinal - bidCoinPoolBalInit
        IN  
            LET strikeBidAmt ==
                    IF limitHead.amount <= maxPoolBid
                    THEN limitHead.amount
                    ELSE maxPoolBid

                strikeAskAmt == (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) \div strikeExchrate[2]
            IN
                /\  IF limitHead.amount <= maxPoolBid
                    THEN limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
                    ELSE limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = 
                                <<[
                                    account |-> limitHead.account,
                                    exchrate |-> limitHead.exchrate,
                                    amount |-> limitHead.amount - strikeBidAmt
                                ]>> \o Tail(@)
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
