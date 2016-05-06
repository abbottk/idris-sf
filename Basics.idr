module Basics

trivial : Elab ()
trivial = do compute
             g <- snd <$> getGoal
             case g of
                  `((=):Type) => do fill `(Var (UN "Refl"))
                                    solve
                  `(():Type) => do fill `(():())
                                   solve
                  otherGoal  => fail [TermPart otherGoal,
                                      TextPart "is not trivial"
                                     ]

|||
||| Enumerated Types
|||

||| Days of the Week
|||
data Day : Type where
     Monday    : Day
     Tuesday   : Day
     Wednesday : Day
     Thursday  : Day
     Friday    : Day
     Saturday  : Day
     Sunday    : Day

next_weekday : (d : Day) -> Day
next_weekday d = case d of
             Monday    => Tuesday
             Tuesday   => Wednesday
             Wednesday => Thursday
             Thursday  => Friday
             Friday    => Monday
             Saturday  => Monday
             Sunday    => Monday

||| next_weekeday assertions
is_next_weekday1 : (d : Day) -> next_weekday Friday = Monday
is_next_weekday1 d = Refl

is_next_weekday2 : (d : Day) -> next_weekday (next_weekday Saturday) = Tuesday
is_next_weekday2 d = Refl

test_next_weekday : (next_weekday (next_weekday Saturday)) = Tuesday
test_next_weekday = Refl


||| Booleans
|||
data Boolean : Type where
     Top : Boolean
     Bot : Boolean

negb : (b : Boolean) -> Boolean
negb b = case b of
     Top => Bot
     Bot => Top

andb : (b1,b2 : Boolean) -> Boolean
andb b1 b2 = case b1 of
     Top => b2
     Bot => Bot

orb : (b1,b2 : Boolean) -> Boolean
orb b1 b2 = case b1 of
    Top => Top
    Bot => b2

||| orb assertions
test_orb1 : (orb Top Bot) = Top
test_orb1 = Refl

test_orb2 : (orb Bot Bot) = Bot
test_orb2 = Refl

test_orb3 : (orb Bot Top) = Top
test_orb3 = Refl

test_orb4 : (orb Top Top) = Top
test_orb4 = Refl


||| Exercise: 1 star (nandb)
||| Complete the definition of the following function, then make sure that the
|||   assertions below can each be verified by Idris.
|||
||| This function should return true if either or both of its inputs are false.
|||
nandb : (b1,b2 : Boolean) -> Boolean
nandb b1 b2 = (negb (andb b1 b2))

||| nandb assertions
test_nandb1 : (nandb Top Bot) = Top
test_nandb1 = Refl

test_nandb2 : (nandb Bot Bot) = Top
test_nandb2 = Refl

test_nandb3 : (nandb Bot Top) = Top
test_nandb3 = Refl

test_nandb4 : (nandb Top Top) = Bot
test_nandb4 = Refl


||| Exercise: 1 star (andb3)
||| Do the same for the andb3 function below. This function should return true
|||   when all of its inpouts are true, and false otherwise.
|||
andb3 : (b1,b2,b3 : Boolean) -> Boolean
andb3 b1 b2 b3 = (andb b1 (andb b2 b3))

||| andb3 assertions
test_andb31 : (andb3 Top Top Top) = Top
test_andb31 = Refl

test_andb32 : (andb3 Bot Top Top) = Bot
test_andb32 = Refl

test_andb33 : (andb3 Top Bot Top) = Bot
test_andb33 = Refl

test_andb34 : (andb3 Top Top Bot) = Bot
test_andb34 = Refl


|||
||| Function Types
|||

||| Numbers
|||

||| data Nats : Type where
|||      O : Nats
|||      S : Nats -> Nats
pred : (n : Nat) -> Nat
pred n = case n of
     Z   => Z
     S k => k

minusTwo : (n : Nat) -> Nat
minusTwo n = case n of
         Z       => Z
         S Z     => Z
         S (S k) => k

evenb : (n : Nat) -> Boolean
evenb n = case n of
      Z       => Top
      S Z     => Bot
      S (S k) => Top

oddb : (n : Nat) -> Boolean
oddb n = negb (evenb n)

||| oddb assertions
test_oddb1 : (oddb (S Z)) = Top
test_oddb1 = Refl

test_oddb2 : (oddb (S (S (S (S Z))))) = Bot
test_oddb2 = Refl

plus' : (n,m : Nat) -> Nat
plus' n m = case n of
      Z   => m
      S k => S (plus' k m)

mult' : (n,m : Nat) -> Nat
mult' n m = case n of
      Z   => Z
      S k => plus m (mult' k m)

minus' : (n,m : Nat) -> Nat
minus' n m = case (n,m) of
       (Z,   _  ) => Z
       (S _, Z  ) => n
       (S k, S j) => minus k j

exp : (base,power : Nat) -> Nat
exp base power = case power of
    Z   => S Z
    S p => mult' base (exp base p)


||| Exercise: 1 star (factorial)
||| Translate the standard factorial function into Idris.
|||
factorial : (n : Nat) -> Nat
factorial n = case n of
          Z   => S Z
          S Z => S Z
          S k => (mult' n (factorial k))

||| factorial assertions
test_factorial1 : (factorial 3) = 6
test_factorial1 = Refl

test_factorial2 : (factorial 5) = (mult' 10 12)
test_factorial2 = Refl

beq_nat : (n,m : Nat) -> Boolean
beq_nat n m = case n of
        Z => case m of
          Z   => Top
          S j => Bot
        S k => case m of
          Z   => Bot
          S j => beq_nat k j

ble_nat : (n,m : Nat) -> Boolean
ble_nat n m = case n of
        Z   => Top
        S k => case m of
            Z   => Bot
            S j => ble_nat k j

||| ble_nat assertions
test_ble_nat1 : (ble_nat 2 2) = Top
test_ble_nat1 = Refl

test_ble_nat2 : (ble_nat 2 4) = Top
test_ble_nat2 = Refl

test_ble_nat3 : (ble_nat 4 2) = Bot
test_ble_nat3 = Refl


||| Exercise: 2 stars (blt_nat)
||| The blt_nat function test natural numbers for less-than, yielding a boolean.
|||
blt_nat : (n,m : Nat) -> Boolean
blt_nat n m = case (beq_nat n m) of
        Top => Bot
        Bot => (ble_nat n m)

||| blt_nat assertions
test_blt_nat1 : (blt_nat 2 2) = Bot
test_blt_nat1 = Refl

test_blt_nat2 : (blt_nat 2 4) = Top
test_blt_nat2 = Refl

test_blt_nat3 : (blt_nat 4 2) = Bot
test_blt_nat3 = Refl


|||
||| Proof by Simplification
|||

plus_Z_n : {n : Nat} -> 0 + n = n
plus_Z_n = ?plus_Z_n
