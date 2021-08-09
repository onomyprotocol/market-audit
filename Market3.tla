------------------------------- MODULE Market3 -------------------------------
EXTENDS     FiniteSets, Naturals, Sequences

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
\* Ask coin
            ask,
            \* Bid coin
            bid,
            \* Limit Books
            limits,
            \* The reserve holds the initial amounts
            reserve,
            \* Stop Books
            stops

-----------------------------------------------------------------------------
\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}


Amounts == 0..MaxAmount

NomCoins == {"NOM"}     \X Amounts
ACoins   == {"Denom_A"} \X Amounts
BCoins   == {"Denom_B"} \X Amounts

\* A coinamount holds coins of exactly one of NOM, Denom_A, Denom_B
CoinAmount == NomCoins \union ACoins \union BCoins

\* amounts are pairs <<type, amount>>
AmountType(b) == b[1]  
AmountAmount(b) == b[2]

PairTypePre == {{a, b} : a \in CoinType, b \in CoinType}
PairType == { ptp \in PairTypePre : Cardinality(ptp) > 1 }
PairPlusCoin == { <<pair, coin>> \in PairType \X CoinType : coin \in pair }

ExchRateType == {<<a, b>> : a \in CoinAmount, b \in CoinAmount}

PositionType == 
[
    acct: ExchAccount,
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: ExchRateType,
    \* cardinality of amount is the amount
    amount: CoinAmount
]

CoinRecords(ct) == [
                \* Holds a amount (set) of coins
                \* Balances are represented by Cardinality of amount
                \* So, in implementation, consider this balance
                amount: CoinAmount,
                positions: [CoinType -> Seq(Seq(PositionType) \X Seq(PositionType))]
                    
              ]

CoinRecord == CoinRecords("Denom_A") \union CoinRecords("Denom_B") \union CoinRecords("NOM") 

TypeInvariant ==     
/\  accounts \in [
        ExchAccount -> {
          f \in [CoinType -> CoinRecord]:
          \A ct \in CoinType: f[ct] \in CoinRecords(ct)
        }
      ]
/\  ask \in CoinType
    \* Bid Coin
/\  bid \in CoinType
    \* [<< -> Limits]]
/\  limits \in [Seq(PairType \X CoinType) -> Seq(PositionType)]
/\  reserve \in [CoinType -> CoinAmount]
/\  stops \in [Seq(PairType \X CoinType) -> Seq(PositionType)]

INIT ==     
/\  accounts = [
        ea \in ExchAccount |-> [ 
            ct \in CoinType |-> [
                amount |-> << ct, 0 >>, 
                positions |-> [c \in CoinType \ {ct} |-> << <<>>, <<>> >>]
            ]
        ]
    ]
/\  ask = "NOM"
/\  bid = "Coin_A"
/\  limits = [ppc \in PairPlusCoin |-> <<>>]
/\  reserve = [type \in CoinType |->
        CASE    type = "Denom_A" -> MaxAmount        
        []      type = "Denom_B" -> MaxAmount
        []      type = "NOM" -> MaxAmount
    ]
/\  stops =[ppc \in PairPlusCoin |-> <<>>] 


(***************************************************************************)
(* Deposit(acct, amount, type)                                                *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, amount) ==
LET type == amount[1]
    amt == amount[2]
IN  /\  amt <= reserve[type]
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                amount |-> << type, @.amount[2] + amt >>,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ - amt]
    /\  UNCHANGED << ask, bid, limits, stops >>

Withdraw(acct, amount) ==
LET type == amount[1]
    amt == amount[2]
IN
    /\  amt <= accounts[acct][type].amount[2]
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                amount |-> << type, @.amount[2] - amt >>,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ + amt]
    /\  UNCHANGED << ask, bid, limits, stops >>

NEXT == \/  \E acct \in ExchAccount :
            \E type \in CoinType :
                \/  \E amount \in Amounts :
                    IF amount > 0 THEN
                        Deposit(acct, <<type, amount>>)
                    ELSE UNCHANGED <<
                            accounts, 
                            ask,
                            bid,
                            limits, 
                            reserve,
                            stops
                        >>
                \/  \E amount \in Amounts :
                    IF amount > 0 THEN
                        Withdraw(acct, <<type, amount>>)
                    ELSE UNCHANGED <<
                            accounts, 
                            ask,
                            bid,
                            limits, 
                            reserve,
                            stops
                        >>
         
Spec == INIT /\ 
        [][NEXT]_<<
            accounts,
            ask,
            bid,
            limits, 
            reserve,
            stops
          >>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
