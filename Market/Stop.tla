-------------------------------- MODULE Stop  -------------------------------
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

Stop(askCoin, bidCoin, limitsUpd, stopsUpd) ==
LET 
    stopBook == stopsUpd[bidCoin, askCoin]    
    stopHead == Head(stopBook)
    stopHeadInvExchrate == << stopHead.exchrate[2], stopHead.exchrate[1] >>
    limitBook == limitsUpd[askCoin, bidCoin]
    askCoinPoolBalInit == pools[bidCoin, askCoin]
    bidCoinPoolBalInit == pools[askCoin, bidCoin]
    poolExchrate == << askCoinPoolBalInit,  bidCoinPoolBalInit >>
    stopSecondInvExchrate ==
        <<
            stopBook[2].exchrate[2],
            stopBook[2].exchrate[1]
        >>
    
    strikeExchrate ==
        CASE Len(limitBook) = 0 /\ Len(stopBook) = 1 ->
                poolExchrate
        []   Len(limitBook) = 0 /\ Len(stopBook) > 1 ->
                IF GT(poolExchrate, stopSecondInvExchrate)
                THEN poolExchrate
                ELSE stopSecondInvExchrate
        []   Len(limitBook) > 0 /\ Len(stopBook) = 1 ->
                IF GT(poolExchrate, Head(limitBook).exchrate)
                THEN poolExchrate
                ELSE Head(limitBook).exchrate
        []   Len(limitBook) > 0 /\ Len(stopBook) > 1 ->
                
                    \* Determine the most adjacent order which is the
                    \* lesser of the next stop or limit head
                    IF LT(stopSecondInvExchrate, Head(limitBook).exchrate)    
                    THEN \* IF Pool Exchrate is Greater than
                        \* Second Limit Book Order 
                        IF GT(poolExchrate, stopSecondInvExchrate)
                        THEN poolExchrate
                        ELSE stopSecondInvExchrate
                    ELSE \* If Pool Exchrate is Greater than
                        \* Ask Stop Head Inverse Exchange Rate
                        IF GT(poolExchrate, Head(limitBook).exchrate)
                        THEN poolExchrate
                        ELSE Head(limitBook).exchrate
    IN
        LET
            maxAskCoinPoolBalFinal == BidCoinBalFinal(
                poolExchrate[2], 
                poolExchrate[1], 
                << 
                    strikeExchrate[2],
                    strikeExchrate[1]
                >>  
            )
            maxPoolAsk == maxAskCoinPoolBalFinal - askCoinPoolBalInit
        IN  
            LET strikeAskAmt ==
                    IF stopHead.amount <= maxPoolAsk
                    THEN stopHead.amount
                    ELSE maxPoolAsk

                strikeBidAmt == (
                    strikeAskAmt *
                    strikeExchrate[2]
                ) \div strikeExchrate[1]
            IN
                /\  IF stopHead.amount <= strikeAskAmt
                    THEN stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = Tail(@)]
                    ELSE stops' = [stopsUpd EXCEPT ![bidCoin, askCoin] = 
                                <<[
                                    account |-> stopBook[1].account,
                                    exchrate |-> stopBook[1].exchrate,
                                    amount |-> stopBook[1].amount - strikeAskAmt
                                ]>> \o Tail(@)
                         ]
                /\  accounts' = 
                    [ accounts EXCEPT 
                        ![stopBook[1].account, bidCoin] = @ + strikeBidAmt,
                        ![stopBook[1].account, askCoin] = @ - strikeAskAmt
                    ] 
                /\  pools' = 
                    [ pools EXCEPT
                        ![askCoin, bidCoin] = @ - strikeBidAmt,
                        ![bidCoin, askCoin] = @ + strikeAskAmt 
                    ]
                /\  UNCHANGED <<drops, reserve, limits>>
=============================================================================