------------------------------- MODULE Market3 -------------------------------
EXTENDS     FiniteSets, Naturals, Sequences

CONSTANT    ExchAccount,    \* Set of all accounts
            MaxAmount       \* Max amount of coins in circulation

VARIABLE    accounts,
            \* The reserve holds the initial bags
            reserve

-----------------------------------------------------------------------------
\* Three Coin Types. Two Denoms and NOM
CoinType == {"Denom_A", "Denom_B", "NOM"}

\* A coinbag holds coins of exactly one of NOM, Denom_A, Denom_B

Amounts == 0..MaxAmount

NomCoins == {"NOM"}     \X Amounts
ACoins   == {"Denom_A"} \X Amounts
BCoins   == {"Denom_B"} \X Amounts

CoinBag == NomCoins \union ACoins \union BCoins

\* bags are pairs <<type, amount>>
BagType(b) == b[1]  
BagAmount(b) == b[2]

Position == 
[
    \* Exchange Rate is defined as
    \* Cardinality(exchrate[0]) / Cardinality(exchrate[1])
    exchrate: Seq(CoinBag \X CoinBag),
    \* cardinality of bag is the amount
    bag: CoinBag
]

CoinRecords(ct) == [
                \* Holds a bag (set) of coins
                \* Balances are represented by Cardinality of bag
                \* So, in implementation, consider this balance
                bag: CoinBag,
                positions: [CoinType -> Seq(Seq(Position) \X Seq(Position))]
                    
              ]

CoinRecord == CoinRecords("Denom_A") \union CoinRecords("Denom_B") \union CoinRecords("NOM") 

TypeInvariant ==     
/\  accounts \in [
        ExchAccount -> {
          f \in [CoinType -> CoinRecord]:
          \A ct \in CoinType: f[ct] \in CoinRecords(ct)
        }
      ]
/\  reserve \in [CoinType -> CoinBag]

INIT ==     
/\  accounts = [
        ea \in ExchAccount |-> [ 
            ct \in CoinType |-> [
                bag |-> << ct, 0 >>, 
                positions |-> [c \in CoinType \ {ct} |-> << <<>>, <<>> >>]
            ]
        ]
    ]
/\  reserve = [type \in CoinType |->
        CASE    type = "Denom_A" -> MaxAmount        
        []      type = "Denom_B" -> MaxAmount
        []      type = "NOM" -> MaxAmount
    ]

(***************************************************************************)
(* Deposit(acct, bag, type)                                                *)
(*                                                                         *)
(* The Deposit function takes a SUBSET of coins from a single type and     *)
(* the reserve and places it into an exchange account.                     *)
(***************************************************************************)
Deposit(acct, bag) ==
LET type == bag[1]
    amount == bag[2]
IN  /\  amount <= reserve[type]
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                bag |-> << type, @.bag[2] + amount >>,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ - amount]

Withdraw(acct, bag) ==
LET type == bag[1]
    amount == bag[2]
IN
    /\  amount <= accounts[acct][type].bag[2]
    /\  accounts' = [accounts EXCEPT ![acct][type] = 
            [
                bag |-> << type, @.bag[2] - amount >>,
                positions |-> @.positions
            ]
        ]
    /\  reserve' = [reserve EXCEPT ![type] = @ + amount]

NEXT == \/  \E acct \in ExchAccount :
            \E type \in CoinType :
                \/  \E bagAmount \in Amounts :
                    IF bagAmount > 0 THEN
                        Deposit(acct, <<type, bagAmount>>)
                    ELSE UNCHANGED <<accounts, reserve>>
                \/  \E bagAmount \in Amounts :
                    IF bagAmount > 0 THEN
                        Withdraw(acct, <<type, bagAmount>>)
                    ELSE UNCHANGED <<accounts, reserve>>
         
Spec == INIT /\ [][NEXT]_<<accounts, reserve>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
