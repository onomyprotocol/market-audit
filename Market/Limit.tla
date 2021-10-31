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

LET limitBook == limitsUpd[askCoin, bidCoin]
    limitHead == Head(limitBook)
    askCoinPoolBalInit == pools[bidCoin, askCoin]
    bidCoinPoolBalInit == pools[askCoin, bidCoin]
    poolExchrate == << askCoinPoolBalInit,  bidCoinPoolBalInit >>
IN
\* Enabling Condition
\* AMM Pool Exchange Rate must be Greater than Limit Book Head
/\  GT(poolExchrate, limitHead)
/\  LET
    maxMemberBBal == bidCoinBalFinal(
        askCoinPoolBalInit, 
        bidCoinPoolBalInit,
        limitHead.rate
    )
    
    
    IN
        LET
            maxBidCoinPoolBalFinal == BidCoinBalFinal(
                poolExchrate[1], 
                poolExchrate[2], 
                limitHead.exchrate
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
