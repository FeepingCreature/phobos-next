module sso_hashset;

import sso_hashmap_or_hashset;
public import sso_hashmap_or_hashset : removeAllMatching, filtered, byElement, intersectedWith;

/** Hash map storing keys of type `K`.
 */
alias HashSet(K,
              alias Allocator = null,
              alias hasher = hashOf,
              uint smallBinMinCapacity = 1) = HashMapOrSet!(K, void,
                                                            Allocator,
                                                            hasher,
                                                            smallBinMinCapacity);