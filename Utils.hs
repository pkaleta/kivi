module Utils where


type Addr   = Int
type Heap a = (Int, [Addr], [(Addr, a)])

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc   :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, addr:free, assoc) obj = ((size+1, free, (addr, obj) : assoc), addr)

--shouldn't it also remove the addr from free addresses?
hUpdate  :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, assoc) addr obj = (size, free, (addr, obj) : remove addr assoc)

-- what if addr was not present in the assoc?
hFree    :: Heap a -> Addr -> Heap a
hFree (size, free, assoc) addr = (size, addr:free, remove addr assoc)

hLookup  :: Heap a -> Addr -> a
hLookup (size, free, assoc) addr =
    case lookup addr assoc of
        Just x -> x
        _      -> error "Cannot find node: " ++ showAddr a ++ " in the heap."

hAddresses :: Heap a -> [Addr]
hAddresses (size, free, assoc) = [addr | (addr, _) <- assoc]

hSize    :: Heap a -> Int
hSize (size, _, _) = size

hNull    :: Addr
hNull = 0

hIsNull  :: Addr -> Bool
hIsNull addr = addr == hNull

showAddr :: Addr -> [Char]
showAddr addr = "#" ++ show addr

-- private helper functions
remove :: Addr -> [(Addr, a)] -> [(Addr, a)]
remove addr [] = error "Attempt to update or free non-existent address: " ++ showAddr addr ++ " from heap."
remove addr (a, obj) : assoc | addr == a = assoc
                             | addr /= a = a : remove addr assoc

