module IntMap

import IntSet

Prefix : Type
Prefix = Int

Mask : Type
Mask = Int

data IntMap a = Bin Prefix
                    Mask
                    (IntMap a)
                    (IntMap a)
              | Tip Key a
              | Nil



