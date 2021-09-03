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
        CASE Len(stopBook) = 0 /\ Len(stopBook) = 1 ->
             Head(stopBook).exchrate
        []   Len(stopBook) > 0 /\ Len(limitBook) > 1 ->
            LET stopHeadExchrate == <<
                    Head(stopBook).exchrate[2],
                    Head(stopBook).exchrate[1]
                >>
            IN
                IF LT(limitBook[2].exchrate, stopHeadExchrate)
                THEN limitBook[2].exchrate
        LET
            maxPoolAmt == MaxPoolBid(
                poolExchrate[1], 
                poolExchrate[2], 
                strikeExchrate
            )
        IN
            IF limitHead.amount <= maxPoolAmt
    THEN \* Fulfill entire limit order
        LET strikeBidAmt == limitHead.amount
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) \div strikeExchrate[2]
        IN
            /\  limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![limitBook[1].acct, bidCoin] = @ - strikeBidAmt,
                    ![limitBook[1].acct, askCoin] = @ + strikeAskAmt
                ] 
            /\  pools' = 
                [ pools EXCEPT
                    ![askCoin, bidCoin] = @ + strikeBidAmt,
                    ![bidCoin, askCoin] = @ - strikeAskAmt 
                ]
            /\  UNCHANGED <<drops, reserve, stops>>
    ELSE \* Partial fill limit order
        LET strikeBidAmt == MaxPoolBid(
                pools[bidCoin, askCoin], 
                pools[askCoin, bidCoin],
                strikeExchrate
            )
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
        /\  limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = 
                Append(
                    Tail(@), [
                        account |-> limitBook[1].account,
                        exchrate |-> limitBook[1].exchrate,
                        amount |-> (limitBook[1].amount - strikeBidAmt)
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
    [] OTHER ->
        LET
            stopBook  == stopsUpd[bidCoin, askCoin]
            stopHead == Head(stopBook)
    
    strikeExchrate ==
        IF Len(limitBook) > 1
        THEN 
            IF Len(stopBook) > 0
            THEN
                \* Strike price is based on the most adjacent
                \* order based on price.
                IF LTE(
                        limitBook[2].exchrate,
                        <<
                            stopHead.exchrate[2],
                            stopHead.exchrate[1]
                        >>
                    )
                THEN limitBook[2].exchrate
                ELSE <<
                        stopHead.exchrate[2],
                        stopHead.exchrate[1]
                    >>
            ELSE << stopBook[2].exchrate[2], stopBook[2].exchrate[1] >>
        ELSE 
            IF Len(stopBook) > 0
            THEN <<
                stopHead.exchrate[2],
                stopHead.exchrate[1]
            >>
            ELSE limitHead.exchrate
    maxPoolAmt == MaxPoolBid(pools[bidCoin, askCoin], pools[askCoin, bidCoin], strikeExchrate)
IN
    IF limitHead.amount <= maxPoolAmt
    THEN \* Fulfill entire limit order
        LET strikeBidAmt == limitHead.amount
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) \div strikeExchrate[2]
        IN
            /\  limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = Tail(@)]
            /\  accounts' = 
                [ accounts EXCEPT 
                    ![limitBook[1].acct, bidCoin] = @ - strikeBidAmt,
                    ![limitBook[1].acct, askCoin] = @ + strikeAskAmt
                ] 
            /\  pools' = 
                [ pools EXCEPT
                    ![askCoin, bidCoin] = @ + strikeBidAmt,
                    ![bidCoin, askCoin] = @ - strikeAskAmt 
                ]
            /\  UNCHANGED <<drops, reserve, stops>>
    ELSE \* Partial fill limit order
        LET strikeBidAmt == MaxPoolBid(
                pools[bidCoin, askCoin], 
                pools[askCoin, bidCoin],
                strikeExchrate
            )
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
        /\  limits' = [limitsUpd EXCEPT ![askCoin, bidCoin] = 
                Append(
                    Tail(@), [
                        account |-> limitBook[1].account,
                        exchrate |-> limitBook[1].exchrate,
                        amount |-> (limitBook[1].amount - strikeBidAmt)
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
