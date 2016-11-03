module setops_ex;

/** Generalization for `std.algorithm.setopts.setUnion` with optimized
    special-handling of hash-set/map support.
 */
auto setUnion(T1, T2)(T1 a, T2 b)
    @trusted
{
    import std.range : CommonType, ElementType;
    import std.traits : hasMember;
    alias E = CommonType!(ElementType!T1,
                          ElementType!T2);
    static if (isAA!T1 &&
               isAA!T2)
    {
        if (a.length < b.length)
        {
            return setUnionHelper(a, b);
        }
        else
        {
            return setUnionHelper(b, a);
        }
    }
    else
    {
        import std.algorithm.sorting : merge;
        return merge(a, b);
    }
}

/** Helper function for `setUnion` that assumes `small` has shorter length than
    `large` .
*/
private static auto setUnionHelper(Small, Large)(const Small small, Large large)
{
    Large united = large.dup;
    foreach (const ref e; small.byKeyValue)
    {
        if (auto hitPtr = e.key in large)
        {
            (*hitPtr) = e.value;
        }
        else
        {
            united[e.key] = e.value;
        }
    }
    return united;
}

/** Is `true` if `Set` is set-like container, that is provides membership
    checking via the `in` operator or `contains`.
    TODO Move to Phobos std.traits
*/
template hasContains(Set)
{
    import std.traits : hasMember;
    enum isSetOf = hasMember!(Set, "contains"); // TODO extend to check `in` operator aswell
}

/** Is `true` if `Map` is map-like container, that is provides membership
    checking via the `in` operator or `contains`.
    TODO Move to Phobos std.traits
*/
template isAA(Map)
{
    import std.traits : isAssociativeArray;
    enum isAA = isAssociativeArray!Map; // TODO check if in operator returns reference to value
}

version(unittest)
{
    import std.algorithm.comparison : equal;
}

/// union of arrays
@safe pure unittest
{
    assert(setUnion([1, 2], [2, 3]).equal([1, 2, 2, 3]));
}

/// union of associative array (via keys)
@safe pure unittest
{
    alias Map = string[int];

    Map a = [0 : "a", 1 : "b"];
    Map b = [2 : "c"];

    Map c = [0 : "a", 1 : "b", 2 : "c"];

    import dbgio : dln;
    // test associativity
    assert(setUnion(a, b) == c);
    assert(setUnion(b, a) == c);
}
