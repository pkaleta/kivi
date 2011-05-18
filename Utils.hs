module Utils where

import Debug.Trace

type Addr = Int
type Assoc a b = [(a, b)]
type Heap a = (Int, [Addr], Assoc Addr a)

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, addr : free, assoc) obj = ((size + 1, free, (addr, obj) : assoc), addr)

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, assoc) addr obj = (size, free, (addr, obj) : remove addr assoc)

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, assoc) addr = (size, addr:free, remove addr assoc)

hLookup :: Heap a -> Addr -> a
hLookup (size, free, assoc) addr =
    case lookup addr assoc of
        Just x -> x
        _      -> error $ "Cannot find node: " ++ showAddr addr ++ " in the heap."

hAddresses :: Heap a -> [Addr]
hAddresses (size, free, assoc) = [addr | (addr, _) <- assoc]

hSize :: Heap a -> Int
hSize (size, _, _) = size

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull addr = addr == hNull

showAddr :: Addr -> [Char]
showAddr addr = "#" ++ show addr

-- private helper functions
remove :: Addr -> [(Addr, a)] -> [(Addr, a)]
remove addr [] = error $ "Attempt to update or free non-existent address: " ++ showAddr addr ++ " from heap."
remove addr ((a, obj) : assoc) | addr == a = assoc
                               | otherwise = (a, obj) : remove addr assoc

aLookup :: (Eq a) => Assoc a b -> a -> b -> b
aLookup [] key def = def
aLookup ((k, v) : xs) key def | k == key = v
                              | otherwise = aLookup xs key def

aDomain :: Assoc a b -> [a]
aDomain xs = [k | (k, _) <- xs]

aHasKey :: Eq a => Assoc a b -> a -> Bool
aHasKey env k = k `elem` aDomain env

aRange :: Assoc a b -> [b]
aRange xs = [v | (_, v) <- xs]

aEmpty = []

bindersOf :: [(a, b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

rhssOf :: [(a, b)] -> [b]
rhssOf defns = [rhs | (_, rhs) <- defns]

