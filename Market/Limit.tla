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


LET stopBook == stopsUpd[bidCoin, askCoin]    
    limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    askCoinPoolBalInit == pools[bidCoin, askCoin]
    bidCoinPoolBalInit == pools[askCoin, bidCoin]
    poolExchrate == << askCoinPoolBalInit,  bidCoinPoolBalInit >>
    stopHeadInvExchrate == <<
        Head(stopBook).exchrate[2],
        Head(stopBook).exchrate[1]
    >>

    strikeExchrate ==
        CASE Len(stopBook) = 0 /\ Len(limitBook) = 1 ->
             poolExchrate
        []   Len(stopBook) = 0 /\ Len(limitBook) > 1 ->
            IF GT(poolExchrate, limitBook[2].exchrate)
            THEN poolExchrate
            ELSE limitBook[2].exchrate
        []   Len(stopBook) > 0 /\ Len(limitBook) = 1 ->
            IF GT(poolExchrate, stopHeadInvExchrate)
            THEN poolExchrate
            ELSE stopHeadInvExchrate
        []   Len(stopBook) > 0 /\ Len(limitBook) > 1 ->
            \* Determine the most adjacent order which is the
            \* lesser of the next limit or stop head
            IF LT(limitBook[2].exchrate, stopHeadInvExchrate)    
            THEN \* IF Pool Exchrate is Greater than
                 \* Second Limit Book Order 
                IF GT(poolExchrate, limitBook[2].exchrate)
                THEN poolExchrate
                ELSE limitBook[2].exchrate
            ELSE \* If Pool Exchrate is Greater than
                 \* Ask Stop Head Inverse Exchange Rate
                 IF GT(poolExchrate, stopHeadInvExchrate)
                 THEN poolExchrate
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
