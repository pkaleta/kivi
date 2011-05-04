module Gc where

import Utils
import Defs

gc :: TiState -> TiState
gc state = (stack, dump, heap', globals, stats, output)
    where
        heap' = scanHeap $ foldl markFrom heap $ findRoots state
        (stack, dump, heap, globals, stats, output) = state

markFrom :: TiHeap -> Addr -> TiHeap
markFrom heap addr =
    case node of
        NMarked node -> heap
        NAp a1 a2 -> heap2
            where
                heap1 = markFrom heap' a1
                heap2 = markFrom heap1 a2
        NSc name vars expr -> heap'
        NNum n -> heap'
        NInd addr -> heap'
            where
                heap' = markFrom heap addr
        NPrim name primitive -> heap'
        NData tag addrs -> newHeap
            where
                newHeap = foldl markFrom heap' addrs
    where
        node = hLookup heap addr
        heap' = hUpdate heap addr $ NMarked node

scanHeap :: TiHeap -> TiHeap
scanHeap heap =
    foldl analyse heap addrs
    where
        addrs = hAddresses heap
        analyse heap addr =
            case node of
                NMarked node ->
                    hUpdate heap addr node
                _ ->
                    hFree heap addr
            where
                node = hLookup heap addr

findRoots (stack, dump, heap, globals, stats, output) =
    findStackRoots stack ++ findDumpRoots dump ++ findGlobalRoots globals

findStackRoots :: TiStack -> [Addr]
findStackRoots stack = stack

findDumpRoots :: TiDump -> [Addr]
findDumpRoots dump = foldl (++) [] dump

findGlobalRoots :: TiGlobals -> [Addr]
findGlobalRoots globals = map snd globals
