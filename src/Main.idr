module Main
import Data.Vect
import Data.Nat

||| Vect is defined in the standard library as:
||| ```
||| data Vect : Nat -> Type -> Type
|||   Nil : Vect 0 elem
|||   (::) : elem -> Vect len elem -> Vect (S len) elem
||| ```
||| Vect is a list that keeps track of its length at compile time using dependent types.
|||
||| You can write a vect `[1, 2, 3]` as `1::(2::(3::Nil))`. We will use both of these syntaxes
||| in our descriptions.
|||
||| We use `Vect` instead of the simpler `List` to ensure that different permutationss of our
||| lists are the same length, so we don't misakenly think [1, 2, 3] is a permutation of [2, 1].
||| However, we will refer to vects as lists most of the time because the difference isn't super
||| relevant.
|||
||| Currently, we only allow `Vect` to contain natural numbers. We will extend this to any ordered
||| objects later.

||| Sorted provides a proof that a list of natural numbers `xs` is sorted.
data Sorted : (xs : Vect n Nat) -> Type where
  ||| An empty list is sorted.
  SortedZero:
    Sorted Nil
  ||| A list with one element is sorted.
  SortedOne:
    (x:Nat) ->
    Sorted (x::Nil)
  ||| A list with structure `x::(y::ys)`, where
  ||| - The `x`, `y` are in order, or in other words `x` <= `y`
  ||| - `y::ys` is sorted
  ||| is also sorted.
  SortedMany:
    (x : Nat) -> (y : Nat) -> (ys : Vect n Nat) ->
    (LTE x y) -> Sorted (y :: ys) ->
    Sorted (x :: (y :: ys))

||| Elem provides a proof that an element `x` of type `a` is in a list `xs`.
data Elem : (x : a) -> (xs : Vect n a) -> Type where
  ||| If `x` equals the first element of the list, `x` is in the list.
  Here  : Elem x (x :: xs)
  ||| If we know that `x` is in xs, we know that `x` is also in the bigger list `y::xs`.
  There : Elem x xs -> Elem x (y :: xs)


||| Permutation provides a proof that a list `xs` has the same elements as `ys`, or in other words
||| that `xs` is a reordering of `ys`
data Permutation : (xs: Vect n Nat) -> (ys: Vect n Nat) -> Type where
    ||| Two empty lists are permutations of each other.
    PermutationZero: Permutation [] []
    ||| If we know that `as` and `bs` are permutations of each other, then we know that
    ||| x::as and x::bs are permutations of each other.
    PermutationGrow: (as, bs: Vect n Nat) -> (x : Nat) ->
      Permutation as bs -> Permutation (x::as) (x::bs)
    ||| If we know that `as` and `bs` are permutations of each other, then we know that
    ||| a::(b::as) and b::(a::bs) are permutations of each other.
    PermutationSwap: (as, bs : Vect n Nat) -> (a, b : Nat) -> Permutation as bs ->
      Permutation (a::(b::as)) (b::(a::bs))
    ||| If we know that `as` and `bs` are permutations of each other, and we know that `bs`
    ||| and `cs` are permutations of each other, then we know that `as` and `cs` are
    ||| permutations of each other.
    PermutationTrans : (as, bs, cs : Vect n Nat) ->
      Permutation as bs -> Permutation bs cs -> Permutation as cs

||| In dependently typed languages, functions correspond to theorems.
||| For every function, we will state what theorem it is proving in english after the "Theorem"
||| label, and also describe the function after "Function" label if relevant. We won't describe
||| the function label for all functions because many are only useful as theorems.

||| Theorem: If a list of the form `x::xs` is sorted, the smaller list `xs` is also sorted
sortedImpliesSortedSmaller : (x: Nat) -> (xs : Vect n Nat) -> (Sorted (x::xs)) -> Sorted xs
-- Base case: If `x::xs` has only one element, then `xs` will be the empty list [], which is sorted
-- by SortedZero
sortedImpliesSortedSmaller x [] _ = SortedZero
-- Inductive step: If `x::xs` has at least two elements, then our `Sorted` proof will be of the form
-- SortedMany, so we can extract the inner proof that xs is sorted
-- You can also think of extracting the inner proof as accessing the inductive hypothesis
sortedImpliesSortedSmaller x (y::ys) (SortedMany x y ys _ sor) = sor

||| Theorem: All lists are permutations of themselves
permutationId : (xs : Vect n Nat) -> Permutation xs xs
-- Base case: The empty list is a permutation of itself by PermutationZero
permutationId [] = PermutationZero
-- Inductive step: Let our list be of the form x::xs. By the inductive hypothesis,
-- xs is a permutation of itself. By PermutationGrow, x::xs is a permutation of itself.
permutationId (x::xs) = PermutationGrow xs xs x (permutationId xs)

||| Theorem: If `xs` is a permutation of `ys`, `ys` is a permutation of `xs`
permutationRev : (xs, ys: Vect n Nat) -> Permutation xs ys -> Permutation ys xs
permutationRev [] [] (PermutationZero) = PermutationZero
permutationRev (x::as) (x::bs) (PermutationGrow as bs x p) =
  (PermutationGrow bs as x (permutationRev as bs p))
permutationRev (a::(b::as)) (b::(a::bs)) (PermutationSwap as bs a b p) =
  PermutationSwap bs as b a (permutationRev as bs p)
permutationRev as cs (PermutationTrans as bs cs perm1 perm2) =
  PermutationTrans cs bs as (permutationRev bs cs perm2) (permutationRev as bs perm1)

||| Theorem: If an element `a` is in a list `as`, and `as` is a permutation of `cs`, then
||| `a` is in the list `cs`
elOfListIsInPermOfList: (as, cs : Vect n Nat) -> (a : Nat) -> Permutation as cs -> Elem a as
  -> Elem a cs
elOfListIsInPermOfList (a::(b::xs)) (b::(a::ys)) c (PermutationSwap xs ys a b p) elem = case elem of
  Here => There (Here)
  There (Here) => Here
  There (There pos) => There (There (elOfListIsInPermOfList xs ys c p pos))
elOfListIsInPermOfList (x::xs) (x::ys) l (PermutationGrow xs ys x p1) elem = case elem of
  Here => Here
  There elem => There (elOfListIsInPermOfList xs ys l p1 elem)
elOfListIsInPermOfList as cs a (PermutationTrans as bs cs p1 p2) aElemAs = let
  aElemBs : (Elem a bs) = elOfListIsInPermOfList as bs a p1 aElemAs
  in elOfListIsInPermOfList bs cs a p2 aElemBs

||| Theorem: If an element `y` is the first element of a list `y::ys`, and `y::ys` is a permutation of `x::xs`,
||| then either y = x or y is an element of xs
firstElOfListIsHeadOrInTailOfPerm: (Permutation (x::xs) (y::ys)) -> Either (y = x) (Elem y xs)
firstElOfListIsHeadOrInTailOfPerm (PermutationSwap xs ys a b p) = Right (Here)
firstElOfListIsHeadOrInTailOfPerm (PermutationGrow as bs x p1) = Left Refl
firstElOfListIsHeadOrInTailOfPerm (PermutationTrans (a::as) (b::bs) (c::cs) perm1 perm2) = let
  cInBs : Elem c (b::bs) =
    elOfListIsInPermOfList (c::cs) (b::bs) c (permutationRev (b::bs) (c::cs) perm2) Here
  cInAs : Elem c (a::as) =
    elOfListIsInPermOfList (b::bs) (a::as) c (permutationRev (a::as) (b::bs) perm1) cInBs
  in case cInAs of
    Here => Left Refl
    There x => Right x

||| Theorem: If an element `y` is in a list `xs`, and the list `x::xs` is sorted, then `x <= y`
yAfterXInSortedListImpliesXLtY: (x, y : Nat) -> (xs : Vect n Nat) -> (Sorted (x::xs)) -> (Elem y xs)
  -> (LTE x y)
yAfterXInSortedListImpliesXLtY x y (y::xs) (SortedMany x y xs prfLte sor) Here = prfLte
yAfterXInSortedListImpliesXLtY x y (f::xs) (SortedMany x f xs prfLte sor) (There n) = let
  fLteY : LTE f y = yAfterXInSortedListImpliesXLtY f y xs sor n
  xLteF : LTE x f = prfLte
  in transitive xLteF fLteY

||| Theorem: Let `x`, `y` be elements and `ys` be a list. Let `x_ys` be a list that contains `x` and
||| all elements in `ys` in some order. If `y` <= `x` and `y::ys` is sorted (which means that `y` <=
||| all elements in `ys`), then the list `y::x_ys` is sorted.
yLtXAndYsImpliesYLtXYs:
  (x, y: Nat) -> (ys: Vect n Nat) -> (x_ys : Vect (S n) Nat) ->
  (LTE y x) -> (Sorted (y::ys)) -> (Sorted x_ys) -> (Permutation (x::ys) x_ys) -> (Sorted (y::x_ys))
yLtXAndYsImpliesYLtXYs x y ys (f::x_ysTail) yLteX y'ysSor x_ysTailSor x'ysPermX_ys =
  -- Let `f::x_ysTail` be the list that contains `x` and all elements in `ys` in some order.
  -- Note that `f::x_ysTail` = `x_ys` we discussed in the theorem.
  -- By theorem `firstElOfListIsHeadOrInTailOfPerm`, we know the first element `f`
  -- of `f::x_ysTail` is either equal to `x`, or is an element of `ys`.
  case firstElOfListIsHeadOrInTailOfPerm x'ysPermX_ys of
    -- Assume `f` is equal to `x`.
    Left fEqX => let
      -- We know that `y <= x`, so by substitution `y <= f`.
      yLteF = replace {p=(\k => LTE y k)} (sym fEqX) yLteX
      -- By definition of SortedMany, because `y` <= `f` and `f::x_ysTail` is sorted,
      -- `y::(f::x_ysTail)` is sorted
      in SortedMany y f x_ysTail yLteF x_ysTailSor
    -- Assume `f` is in `ys`.
    Right fElemYs => let
      -- We know that `y::ys` is sorted, so `yAfterXInSortedListImpliesXLtY`,
      -- `y` <= `f`
      yLteF = yAfterXInSortedListImpliesXLtY y f ys y'ysSor fElemYs
      -- By definition of SortedMany, because `y` <= `f` and `f::x_ysTail` is sorted,
      -- `y::(f::x_ysTail)` is sorted
      in SortedMany y f x_ysTail yLteF x_ysTailSor

||| Theorem: The binary relation "less than or equal to" is total, or in other words forall `x`, `y`,
||| either `x` <= `y` or `y` <= `x`.
lteTotal : (x, y : Nat) -> Either (LTE x y) (LTE y x)
lteTotal Z Z = Left LTEZero
lteTotal Z (S m) = Left LTEZero
lteTotal (S n) Z = Right LTEZero
lteTotal (S n) (S m) =
  case lteTotal n m of
    Left p => Left (LTESucc p)
    Right p => Right (LTESucc p)


||| Theorem: Let `x` be an element and `inList` be a sorted list. There exists another list `outList`
||| that contains `x` and all elements in `inList` and is sorted.
||| Function: Takes a list `inList`, a proof that `inList` is sorted, and an element `x`. Creates
||| a new list `outList` by inserting `x` into `inList`. Returns `outList`, a proof that `outList` is sorted,
||| and a proof that `outList` is a permutation of `x::inList`.
insert : (inList : Vect n Nat) -> (Sorted inList) -> (x : Nat)
  -> (outList : Vect (S n) Nat ** (Sorted outList, Permutation (x::inList) outList))
-- Base case: We can insert an element into an empty list to get a sorted list.
insert [] sor x = ([x] ** (SortedOne x, permutationId [x]))
-- Inductive step: We want to show that there exists a permutation of x::(y::ys)
-- that is sorted. We proceed by cases:
insert (y::ys) sor x =
  case lteTotal x y of
    -- If `x` is less than or equal to `y`, we want to insert here.
    Left prf =>
      let
        -- By definition of SortedMany, because `x` <= `y` and `y::ys` is sorted,
        -- x::(y::ys) is sorted
        retSor = SortedMany x y ys prf sor
        -- By theorem `permutationId`, `x::(y::ys)` is a permutation of itself. Thus,
        -- `x::(y::ys)` is a sorted permutation of `x::(y::ys)`
        ret = (x::(y::ys) ** (retSor, permutationId (x::(y::ys)) ))
      in ret
    -- If `y` is less than or equal to `x`, we want to insert later.
    Right prf =>
      let
        ysSorted = sortedImpliesSortedSmaller y ys sor
        -- By the inductive hypothesis, there exists a sorted version of x::ys
        recursiveCase = insert ys ysSorted x
        (x_ys ** (sor1, perm1)) = recursiveCase
        -- By theorem `yLtXAndYsImpliesYLtXYs`, we know `y::x_ys` is sorted
        y_x_ysSorted = yLtXAndYsImpliesYLtXYs x y ys x_ys prf sor sor1 perm1
        -- By PermutationGrow, because `x::ys` is a permutation of `x_ys`, `y::(x::ys)` is
        -- a permutation of `y::x_ys`
        intermediatePerm: Permutation (y::(x::ys)) (y::x_ys) = PermutationGrow (x::ys) (x_ys) y perm1
        -- By PermutationSwap, `y::(x::ys)` is a permutation of `x::(y::ys)`. By transitive property
        -- of permutations, `x::(y::ys)` is a permutation of `y::x_ys`.
        retPerm: Permutation (x::(y::ys)) (y::x_ys) =
          PermutationTrans
            (x::(y::ys)) (y::(x::ys)) (y::x_ys)
            (PermutationSwap ys ys x y (permutationId ys)) intermediatePerm
        -- Thus, `y::x_ys` is a sorted permutation of `x::(y::ys)`
        ret = (y::x_ys ** (y_x_ysSorted, retPerm))
      in ret

||| Theorem: Let `inList` be a list. There exists a sorted list `outList` with the same elements.
||| Function: Takes a list `inList`. Creates a new list `outList` by sorting `inList`. Returns `outList`,
||| a proof that `outList` is sorted, and a proof that `inList` is a permutation of `outList`
insertionSort : (inList : Vect n Nat)
  -> (outList : Vect n Nat ** (Sorted outList, Permutation inList outList))
-- Base case: An empty list is sorted.
insertionSort [] = ([] ** (SortedZero, PermutationZero))
-- Inductive step: We want to show that there exists a permutation of that x::xs is sorted.
insertionSort (x::xs) =
  let
    -- By the inductive hypothesis, there exists a sorted version of `xs`, let's call it `xsSorted`.
    recursiveCase : (xsSorted : Vect _ Nat ** (Sorted xsSorted, Permutation xs xsSorted)) = insertionSort xs
    (xsSorted ** (sor1, perm1)) = recursiveCase
    -- By theorem `insert`, there exists a sorted list that contains `x` and all elements in `xsSorted`,
    -- let's call it `xsSortedInserted`.
    insertRet : (xsSortedInserted : Vect _ Nat ** (Sorted xsSortedInserted, Permutation (x::xsSorted) xsSortedInserted))
      = insert xsSorted sor1 x
    (xsSortedInserted ** (sor2, perm2)) = insertRet
    -- By PermutationGrow, because xs is a permutation of xsSorted, x::xs is a permutation of x::xsSorted.
    perm3 : Permutation (x :: xs) (x :: xsSorted) =
      PermutationGrow xs xsSorted x perm1
    -- Because`xsSortedInserted` is a permutation of `x::xsSorted`, and because `x::xsSorted` is a permutation of `x::xs`,
    -- by transitivity of permutation we know `xsSortedInserted` is a permutation of `x::xs`.
    permRet : Permutation (x::xs) (xsSortedInserted) =
      PermutationTrans (x::xs) (x::xsSorted) xsSortedInserted perm3 perm2
    -- Thus, `xsSortedInserted` is a sorted permutation of `x::xs`.
  in (xsSortedInserted ** (sor2, permRet))

||| Theorem: There exists an IO monad
||| Function: Sorts a list using insertionSort, and prints the original and final list.
main : IO ()
main = do
  let vect = [23, 23, 4352, 532, 123, 143, 214, 2, 142, 412]
  let (sortedList ** (prfSorted, prfPermutation)) = insertionSort vect

  putStrLn $ show vect
  putStrLn $ show sortedList