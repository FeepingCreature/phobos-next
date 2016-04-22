#!/usr/bin/env rdmd-dev-module

/** Extensions to std.algorithm.sort.
    License: $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0).
*/

module sort_ex;

import std.traits: isAggregateType;
import std.range: ElementType, isRandomAccessRange, isInputRange;

private template xtorFun(alias xtor)
{
    import std.traits: isIntegral;
    static if (is(typeof(xtor) : string))
    {
        auto ref xtorFun(T)(auto ref T a)
        {
            mixin("with (a) { return " ~ xtor ~ "; }");
        }
    }
    else static if (isIntegral!(typeof(xtor)))
    {
        auto ref xtorFun(T)(auto ref T a)
        {
            import std.conv: to;
            mixin("return a.tupleof[" ~ xtor.to!string ~ "];");
        }
    }
    else
    {
        alias xtorFun = xtor;
    }
}

/* private alias makePredicate(alias xtor) = (a, b) => (xtorFun!xtor(a) < xtorFun!xtor(b)); */

/* auto sortBy(xtors..., R)(R r) { */
/*     alias preds = staticMap!(makePredicate, xtors); */
/*     return r.sort!preds; */
/* } */

/** Sort Random Access Range $(D R) of Aggregates on Value of Calls to $(D xtor).
    See also: http://forum.dlang.org/thread/nqwzojnlidlsmpunpqqy@forum.dlang.org#post-dmfvkbfhzigecnwglrur:40forum.dlang.org
 */
void sortBy(alias xtor, R)(R r) if (isRandomAccessRange!R &&
                                    isAggregateType!(ElementType!R))
{
    import std.algorithm : sort;
    import std.functional: unaryFun;
    r.sort!((a, b) => (xtorFun!xtor(a) <
                       xtorFun!xtor(b)));
}

/** Reverse Sort Random Access Range $(D R) of Aggregates on Value of Calls to $(D xtor).
    See also: http://forum.dlang.org/thread/nqwzojnlidlsmpunpqqy@forum.dlang.org#post-dmfvkbfhzigecnwglrur:40forum.dlang.org
*/
void rsortBy(alias xtor, R)(R r) if (isRandomAccessRange!R &&
                                     isAggregateType!(ElementType!R))
{
    import std.algorithm : sort;
    import std.functional: unaryFun;
    r.sort!((a, b) => (xtorFun!xtor(a) >
                       xtorFun!xtor(b)));
}

@safe pure nothrow unittest
{
    static struct X { int x, y, z; }

    auto r = [ X(1, 2, 1),
               X(0, 1, 2),
               X(2, 0, 0) ];

    r.sortBy!(a => a.x);
    assert(r == [ X(0, 1, 2),
                  X(1, 2, 1),
                  X(2, 0, 0) ]);
    r.sortBy!(a => a.y);
    assert(r == [ X(2, 0, 0),
                  X(0, 1, 2),
                  X(1, 2, 1)] );
    r.sortBy!(a => a.z);
    assert(r == [ X(2, 0, 0),
                  X(1, 2, 1),
                  X(0, 1, 2) ]);

    r.sortBy!"x";
    assert(r == [ X(0, 1, 2),
                  X(1, 2, 1),
                  X(2, 0, 0) ]);
    r.sortBy!"y";
    assert(r == [ X(2, 0, 0),
                  X(0, 1, 2),
                  X(1, 2, 1)] );
    r.sortBy!"z";
    assert(r == [ X(2, 0, 0),
                  X(1, 2, 1),
                  X(0, 1, 2) ]);

    r.sortBy!0;
    assert(r == [ X(0, 1, 2),
                  X(1, 2, 1),
                  X(2, 0, 0) ]);
    r.sortBy!1;
    assert(r == [ X(2, 0, 0),
                  X(0, 1, 2),
                  X(1, 2, 1)] );
    r.sortBy!2;
    assert(r == [ X(2, 0, 0),
                  X(1, 2, 1),
                  X(0, 1, 2) ]);
}

/** Returns: $(D r) sorted.
    If needed a GC-copy of $(D r) is allocated, sorted and returned.
    See also: http://forum.dlang.org/thread/tnrvudehinmkvbifovwo@forum.dlang.org#post-tnrvudehinmkvbifovwo:40forum.dlang.org
    TODO Add to Phobos
*/
auto sorted(R, E = ElementType!R)(R r)
{
    import std.traits : isNarrowString;
    import std.range: hasLength;
    import range_ex : isSortedRange;

    static if (isSortedRange!R)
    {
        return r;
    }
    else
    {
        static if (isRandomAccessRange!R)
        {
            auto s = r.dup;
        }
        else static if (isNarrowString!R)
        {
            import std.conv : to;
            auto s = r.to!(dchar[]); // need dchar for random access
        }
        else static if (hasLength!R)
        {
            import std.algorithm: copy;
            auto s = new E[r.length];
            static if (is(typeof(r[]))) // TODO unpretty
            {
                r[].copy(s);
            }
            else
            {
                r.copy(s);
            }
        }
        else
        {
            E[] s; // TODO use Appender?
            foreach (const ref e; r[])
            {
                s ~= e;             // TODO optimize?
            }
        }

        import std.algorithm.sorting : sort;
        return sort(s);
    }
}

version(unittest) import std.algorithm.comparison : equal;

///
@safe pure unittest
{
    assert(equal("öaA".sorted, "Aaö"));
    assert(equal("öaA"w.sorted, "Aaö"));
    assert(equal("öaA"d.sorted, "Aaö"));
}

///
@safe pure unittest
{
    import std.algorithm.sorting : sort;
    auto x = "öaA"d;
    auto y = sort(x.dup).sorted; // parameter to sorted is a SortedRange
    assert(equal(y, "Aaö"));
}

///
@safe pure unittest
{
    import std.algorithm.sorting : sort;
    immutable x = [3, 2, 1];
    auto y = x.dup;
    sort(y);
    assert(equal(x.sorted, y));
}

///
unittest
{
    import std.container: Array;
    auto x = Array!int(3, 2, 1);
    assert(equal(x.sorted, [1, 2, 3]));
}

///
unittest
{
    import std.container: SList;
    auto x = SList!int(3, 2, 1);
    assert(equal(x.sorted, [1, 2, 3]));
}

import std.random : Random;

/** Functional version of `std.random.randomShuffle`.

    Returns: $(D r) randomly shuffled.

    If needed a GC-copy of $(D r) is allocated, sorted and returned.
*/
auto randomlyShuffled(Range, RandomGen)(Range r, ref RandomGen gen)
{
    import std.random : randomShuffle;
    r.randomShuffle(gen);
    // TODO reuse copying logic in `sorted`
    return r;
}

///
auto randomlyShuffled(Range)(Range r)
{
    import std.random : randomShuffle;
    r.randomShuffle();
    // TODO reuse copying logic in `sorted`
    return r;
}

///
@safe pure unittest
{
    immutable x = [3, 2, 1];
    auto y = x.dup;
    Random random;
    y.randomlyShuffled(random);
}
