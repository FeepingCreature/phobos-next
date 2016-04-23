module math_ex;

import std.traits : isIntegral;

/** Check if `x` is an exact (binary) power of 2.
    See also: http://forum.dlang.org/post/hloonbgclzloqemycnth@forum.dlang.org
    TODO Move to Phobos std.math.
*/
bool isPow2(T)(T x)
    if (isIntegral!T)
{
    import core.bitop : popcnt;
    return popcnt(x) == 1;
}

@safe pure nothrow @nogc unittest
{
    // run-time
    assert(!7.isPow2);
    assert(8.isPow2);
    assert(!9.isPow2);

    // compile-time
    static assert(!7.isPow2);
    static assert(8.isPow2);
    static assert(!9.isPow2);
}
