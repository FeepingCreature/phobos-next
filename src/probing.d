module probing;

/** Do...

   See also: https://fgiesen.wordpress.com/2015/02/22/triangular-numbers-mod-2n/
 */
size_t triangularFindIndex(alias hasher = hashOf, T, K)(const scope T[] haystack,
                                                        const scope auto ref K key)
    @safe pure nothrow @nogc
{
    size_t isKeyForIx(const scope K key,
                      const scope size_t ix) const
    {
        return (haystack[ix] is key || // hit slot
                haystack[ix].isNull); // free slot
    }

    immutable typeof(return) mask = haystack.length - 1;
    assert((~mask ^ mask) == size_t.max); // isPowerOf2(haystack.length)

    import digestion : hashOf2;
    size_t ix = hashOf2!(hasher)(key) & mask;

    if (isKeyForIx(key, ix))
    {
        return ix;
    }

    // if not yet decided

    ix = (ix + 1) & mask;   // modulo power of two
    dln("ix:", ix);

    size_t inc = 1;
    while (!isKeyForIx(key, ix) &&
           inc != haystack.length)
    {
        ix = (ix + inc) & mask;
        dln("ix:", ix);
        inc *= 2;
    }

    if (isKeyForIx(key, ix))
    {
        return ix;
    }
    else
    {
        return haystack.length;
    }
}

@safe pure nothrow unittest
{
    import digestx.fnv : FNV;
    import std.typecons : Nullable;
    import dbgio;

    alias T = Nullable!int;

    foreach (immutable lengthPower; 0 .. 20)
    {
        immutable length = 2^^lengthPower;
        dln(length);

        // allocate and perpare haystack
        auto haystack = new T[length];
        haystack[] = T(17);
        immutable key = T(42);
        haystack[0] = key;

        assert(haystack.triangularFindIndex!(FNV!(64, true))(key) != haystack.length);
    }
}

version(unittest)
{
    import dbgio;
}