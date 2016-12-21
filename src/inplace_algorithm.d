module inplace_algorithm;

import std.functional : unaryFun;

import typecons_ex : hasIndexing;

version(unittest)
{
    import std.algorithm.comparison : equal;
    import dbgio : dln;
}

/** Returns: `r` eagerly in-place filtered on `predicate`.
    TODO Move to array_ex.d to get access to private members in Array such as _mptr
 */
C filteredInplace(alias predicate, C)(C r) @trusted
    if (is(typeof(unaryFun!predicate)) &&
        hasIndexing!C)          // TODO extend to isArrayContainer!C
{
    import std.typecons : Unqual;
    import std.traits : hasElaborateDestructor, isMutable, hasIndirections;
    import std.range.primitives : ElementType;
    import std.algorithm.mutation : move;
    import traits_ex : ownsItsElements;

    alias pred = unaryFun!predicate;
    alias E = ElementType!C;
    alias MutableC = Unqual!C;

    size_t dstIx = 0;           // destination index

    // skip leading passing elements
    // TODO reuse .indexOf!(_ => !pred(_)) algorithm in `Array`
    while (dstIx < r.length && pred(r.ptr[dstIx]))
    {
        dstIx += 1;
    }

    // inline filtering
    foreach (immutable srcIx; dstIx + 1 .. r.length)
    {
        // TODO move this into @trusted member of Array
        if (pred(r.ptr[srcIx]))
        {
            static if (isMutable!E &&
                       !hasIndirections!E)
            {
                move(r.ptr[srcIx], r.ptr[dstIx]); // TODO reuse function in array
            }
            else static if (ownsItsElements!C)
            {
                move(r.ptr[srcIx], r.ptr[dstIx]); // TODO reuse function in array
            }
            else
            {
                static assert(false, "Cannot move elements in instance of " ~ C.stringof);
            }
            dstIx += 1;
        }
        else
        {
            static if (hasElaborateDestructor!E)
            {
                .destroy(e);
            }
        }
    }

    r.shrinkTo(dstIx);

    return move(r);
}

@safe pure nothrow @nogc unittest
{
    import std.algorithm.mutation : move;
    import std.meta : AliasSeq;
    import unique_range : intoUniqueRange;
    import array_ex : UncopyableArray, SortedSetUncopyableArray;

    alias E = int;
    foreach (C; AliasSeq!(UncopyableArray, SortedSetUncopyableArray))
    {
        alias A = C!E;

        static assert(is(A == typeof(A().filteredInplace!(_ => _ & 1))));

        // empty case
        immutable E[0] c0 = [];
        assert(A.withCapacity(0)
                .filteredInplace!(_ => _ & 1)
                .intoUniqueRange()
                .equal(c0[]));

        // few elements triggers small-array optimization
        immutable E[2] c2 = [3, 11];
        auto a2 = A.withElements(2, 3, 11, 12);
        assert(a2.isSmall);
        assert(move(a2).filteredInplace!(_ => _ & 1)
                       .intoUniqueRange()
                       .equal(c2[]));

        // odd elements
        immutable E[6] c6 = [3, 11, 13, 15, 17, 19];
        auto a6 = A.withElements(3, 11, 12, 13, 14, 15, 16, 17, 18, 19);
        assert(a6.isLarge);
        assert(move(a6).filteredInplace!(_ => _ & 1)
                       .intoUniqueRange()
                       .equal(c6[]));

        // elements less than or equal to limit
        immutable E[7] c7 = [3, 11, 12, 13, 14, 15, 16];
        auto a7 = A.withElements(3, 11, 12, 13, 14, 15, 16, 17, 18, 19);
        assert(a7.isLarge);
        assert(move(a7).filteredInplace!(_ => _ <= 16)
                       .intoUniqueRange()
                       .equal(c7[]));
    }
}
