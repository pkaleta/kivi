module Gc where

import Common
import Utils

gc :: GmState -> GmState
gc state = state { gmheap = heap' }
    where
        heap' = scanHeap $ foldl markFrom heap $ findRoots state
        heap = gmheap state

markFrom :: GmHeap -> Addr -> GmHeap
markFrom heap addr =
    case node of
        NMarked node -> heap
        NAp a1 a2 -> heap2
            where
                heap1 = markFrom heap0 a1
                heap2 = markFrom heap1 a2
        NGlobal arity code -> heap0
        NNum n -> heap0
        NChar c -> heap0
        NInd addr -> heap1
            where
                heap1 = markFrom heap0 addr
        NConstr tag args -> heap1
            where
                heap1 = foldl markFrom heap0 args
    where
        node = hLookup heap addr
        heap0 = hUpdate heap addr $ NMarked node

scanHeap :: GmHeap -> GmHeap
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

findRoots state =
    findStackRoots (gmstack state) ++
    findDumpRoots (gmdump state) ++
    findGlobalRoots (gmglobals state)

findStackRoots :: GmStack -> [Addr]
findStackRoots stack = stack

findDumpRoots :: GmDump -> [Addr]
findDumpRoots dump = foldl collectRoots [] dump
    where
        collectRoots roots (code, stack, vstack) = roots ++ findStackRoots stack

findGlobalRoots :: GmGlobals -> [Addr]
findGlobalRoots globals = map snd globals
