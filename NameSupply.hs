module NameSupply where


type NameSupply = Int

initialNameSupply :: NameSupply
initialNameSupply = 0

getName :: NameSupply -> [Char] -> (NameSupply, [Char])
getName ns prefix = (ns + 1, makeName ns prefix)

getNames :: NameSupply -> [[Char]] -> (NameSupply, [[Char]])
getNames ns ps = (ns + length ps, zipWith makeName [ns..] ps)

makeName :: NameSupply -> [Char] -> [Char]
makeName ns prefix = prefix ++ (show ns)
