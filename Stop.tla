-------------------------------- MODULE Stop  -------------------------------
EXTENDS     FiniteSets, FiniteSetsExt, Naturals, Sequences, SequencesExt

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
\* Nat tuple (numerator/denominator) inequality helper functions
\* All equalities assume Natural increments
GT(a, b) == a[1]*b[2] > a[2]*b[1]

GTE(a, b) == a[1]*b[2] >= a[2]*b[1] 

LT(a, b) == a[1]*b[2] < a[2]*b[1]

LTE(a, b) == a[1]*b[2] <= a[2]*b[1]

Stop(acct, askCoin, askAmount, bidCoin, bidAmount)
\* Getting to this point means that both an Ask Stop and a Bid
\* Limit are equal and enabled.
LET limitBook == limits[askCoin, bidCoin]
    limitHead == Head(limitBook)
    stopBook  == stops[bidCoin, askCoin]
    stopHead == Head(stopBook)
    \* Strike Exchrate either limit or stop as equal
    strikeExchrate == limitHead.exchrate
IN
    \* IF TRUE then amount traded is equal to limitHead amount
    \* stopHead amount must be equal to or greater than limitHead
    \* amount in this case.
    CASE limitHead.amount <= stopHead.amount ->
            
    /\  accounts' = 
        [ accounts EXCEPT 
            ![acct, bidCoin] = @ - strikeBidAmount,
            ![acct, askCoin] = @ + strikeAskAmount
        ]

    /\  limits' =
        [ limits EXCEPT
            ![askCoin, bidCoin]
        ]

LET
    bidLimits = limits[askCoin, bidCoin]
    askStops = stops[bidCoin, askCoin]
IN
    (***************************************************************)
    (*  In this case, the next order to be enabled will be the head*) 
    (*  of the bid limits.                                         *)
    (*  Order execution will fill order until bid limit head       *)
    (*  exchange rate is reached.                                  *)
    (***************************************************************)
    CASE LTE(bidLimits[1].exchrate, askStops[2].exchrate) ->
        LET strikeExchRate == bidLimitExchRate
            \*  Pool bid coin is the order ask coin
            maxPoolBid ==   MaxPoolBid(poolExchRate, strikeExchRate)
            maxPoolAsk ==   maxBid * 
                            strikeExchRate[1] / 
                            strikExchRate[2]
        IN  IF maxPoolAsk > bidLimitAmount
            THEN
                LET strikeBidAmount ==  bidLimitAmount
                    strikeAskAmount ==  strikeBidAmount *
                                        strikeExchRate[1] / 
                                        strikeExchRate[2] 
                IN
                

LET stopBook == stops[bidCoin, askCoin]
    stopHead
/\  stops' = [stops EXCEPT ![<<pair>>] = Tail(@)]
/\  accounts' = 
    [ accounts EXCEPT 
        ![acct, bidCoin] = @ - strikeBidAmount,
        ![acct, askCoin] = @ + strikeAskAmount
    ] 
/\  pools' = 
    [ pools EXCEPT
        ![askCoin, bidCoin] = @ + strikeBidAmount,
        ![bidCoin, askCoin] = @ - strikeAskAmount 
    ]