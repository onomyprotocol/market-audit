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

vars == <<accounts, drops, limits, pools, reserve, stops>>

-----------------------------------------------------------------------------

Limit(askCoin, bidCoin)

LET limitBook == limits[askCoin, bidCoin]
    stopBook  == stops[bidCoin, askCoin]
    poolExchrate == pools[bidCoin, askCoin] /
                    pools[askCoin, bidCoin]
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
                            stopBook[1].exchrate[2],
                            stopBook[1].exchrate[1]
                        >>
                    )
                THEN limitBook[2].exchrate
                ELSE <<
                        stopBook[1].exchrate[2],
                        stopBook[1].exchrate[1]
                    >>
            ELSE limitBook[2].exchrate
        ELSE 
            IF Len(stopBook) > 0
            THEN <<
                stopBook[1].exchrate[2],
                stopBook[1].exchrate[1]
            >>
            ELSE limitBook[1].exchrate
            
IN
    IF limitBook[1]amount <= stopBook[1].amount
    THEN \* Fulfill entire limit order
        LET strikeBidAmt == limitBook[1].amount
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
            /\  limits' = [limits EXCEPT ![askCoin, bidCoin] = Tail(@)]
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
    ELSE \* Partial fill limit order
        LET strikeBidAmt == maxPoolAmt
            strikeAskAmt == 
                (
                    strikeBidAmt *
                    strikeExchrate[1]
                ) * strikeExchrate[2]
        IN
        /\  limits' = [limits EXCEPT ![askCoin, bidCoin] = 
                Append(
                    Tail(@), <<[
                        account: limitBook[1].accounts,
                        exchrate: limitBook[1].exchrate,
                        amount: limitBook[1].amount - strikeBidAmt
                    ]>>
                )
            ]
        /\  accounts' = 
            [ accounts EXCEPT 
                ![acct, bidCoin] = @ - strikeBidAmt,
                ![acct, askCoin] = @ + strikeAskAmt
            ] 
        /\  pools' = 
            [ pools EXCEPT
                ![askCoin, bidCoin] = @ + strikeBidAmt,
                ![bidCoin, askCoin] = @ - strikeAskAmt 
            ]
