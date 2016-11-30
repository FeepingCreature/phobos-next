#!/usr/bin/env rdmd-dev-module

/** Various extensions to core.bitop and std.bitmanip.
    Copyright: Per Nordlöw 2016-.
    License: $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0).
    Authors: $(WEB Per Nordlöw)

    TODO Add range checking of bit indexes.
*/
module bitop_ex;

import std.traits : isIntegral;
import std.meta : allSatisfy;

pure @nogc nothrow:

/** Get an Unsigned Type of size as $(D T) if possible. */
template UnsignedOfSameSizeAs(T)
{
    enum nBits = 8*T.sizeof;
    static      if (nBits ==  8) alias UnsignedOfSameSizeAs = ubyte;
    else static if (nBits == 16) alias UnsignedOfSameSizeAs = ushort;
    else static if (nBits == 32) alias UnsignedOfSameSizeAs = uint;
    else static if (nBits == 64) alias UnsignedOfSameSizeAs = ulong;
    else static if (nBits == 128) alias UnsignedOfSameSizeAs = ucent;
    else {
        import std.conv: to;
        static assert(false, "No Unsigned type of size " ~ to!string(nBits) ~ " found");
    }
}

/** Returns: Zero Instance T with $(D bix):th Bit set. */
T makeBit(T, I...)(I bixs) @safe
    if (isIntegral!T &&
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
in
{
    foreach (const bix; bixs)
    {
        assert(0 <= bix && bix < 8*T.sizeof);
    }
}
body
{
    T x = 0;
    foreach (const bix; bixs)
    {
        x |= cast(T)((cast(T)1) << bix);
    }
    return x;
}
alias btm = makeBit;

/** Returns: Check if all $(D bix):th Bits Of $(D a) are set. */
bool testBit(T, I...)(in T a, I bixs) @safe
    if (isIntegral!T &&
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
{
    return a & makeBit!T(bixs) ? true : false;
}
/** Returns: Check if all $(D bix):th Bits Of $(D a) are set. */
bool testBit(T, I...)(in T a, I bixs) @trusted
    if ((!(isIntegral!T)) &&
        allSatisfy!(isIntegral, I))
{
    return (*(cast(UnsignedOfSameSizeAs!T*)&a)).testBit(bixs); // reuse integer variant
}
/** Returns: Check if all $(D bix):th Bits Of $(D *a) are set. */
bool testBit(T, I...)(in T* a, I bixs)
    if ((!(isIntegral!T)) &&
        !is(T == size_t) &&     // avoid stealing `core.bitop.bt`
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
{
    return testBit(*a, bixs);
}
alias bt = testBit;

///
unittest
{
    static void test(T)()
    {
        const mn = T.min, mx = T.max;
        enum nBits = 8*T.sizeof;
        foreach (const ix; 0 .. nBits-1)
        {
            assert(!mn.bt(ix));
        }
        assert(mn.bt(nBits - 1));
        foreach (const ix; 0 .. T.sizeof)
        {
            assert(mx.bt(ix));
        }
    }
    test!byte;
    test!short;
    test!int;
    test!long;
}

/** Test and sets the $(D bix):th Bit Of $(D a) to one.
    Returns: A non-zero value if the bit was set, and a zero if it was clear.
*/
void setBit(T, I...)(ref T a, I bixs) @safe
    if (isIntegral!T &&
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
{
    a |= makeBit!T(bixs);
}

/** Test and sets the $(D bix):th Bit Of $(D *a) to one.
    Returns: A non-zero value if the bit was set, and a zero if it was clear.
*/
void setBit(T, I...)(T* a, I bixs) @safe
    if (isIntegral!T &&
        !is(T == size_t) && // avoid stealing core.bitop.bt
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
{
    *a |= makeBit!T(bixs);
}

/** Returns: Check if all $(D bix):th Bits Of $(D a) are set. */
void setBit(T, I...)(ref T a, I bixs) @trusted
    if ((!(isIntegral!T)) &&
        allSatisfy!(isIntegral, I) &&
        I.length >= 1)
{
    alias U = UnsignedOfSameSizeAs!T;
    (*(cast(U*)&a)) |= makeBit!U(bixs); // reuse integer variant
}
alias bts = setBit;

/* alias btc = complementBit; */
/* alias btr = resetBit; */

/** Set lowest bit of `a` to one. */
void setLowestBit(T)(ref T a) @safe
    if (isIntegral!T)
{
    setBit(a, 0);
}
alias setBottomBit = setLowestBit;

/** Set highest bit of `a` to one. */
void setHighestBit(T)(ref T a) @safe
    if (isIntegral!T)
{
    setBit(a, 8*T.sizeof - 1);
}
alias setTopBit = setHighestBit;

/** Get lowest bit of `a`. */
bool getLowBit(T)(in T a) @safe
    if (isIntegral!T)
{
    return (a & 1) != 0;
}
alias getBottomBit = getLowBit;

/** Get highest bit of `a`. */
bool getHighBit(T)(in T a) @safe
    if (isIntegral!T)
{
    // TODO use core.bitop.bt when T is a size_t
    return (a & (cast(T)1 << 8*T.sizeof - 1)) != 0;
}
alias getTopBit = getHighBit;

///
unittest
{
    const ubyte x = 1;
    assert(!x.getTopBit);
    assert(x.getLowBit);
}

///
unittest
{
    const ubyte x = 128;
    assert(x.getTopBit);
    assert(!x.getLowBit);
}

/** Reset bits `I` of `a` (to zero). */
void resetBit(T, I...)(ref T a, I bixs) @safe
    if (isIntegral!T &&
        allSatisfy!(isIntegral, I))
{
    a &= ~makeBit!T(bixs);
}
/** Reset bits `I` of `*a` (to zero). */
void resetBit(T, I...)(T* a, I bixs) @safe
    if (isIntegral!T &&
        !is(T == size_t) && // avoid stealing core.bitop.bt
        allSatisfy!(isIntegral, I))
{
    *a &= ~makeBit!T(bixs);
}

/** Reset bits `I` of `a` (to zero). */
void resetBit(T, I...)(ref T a, I bixs)
    if ((!(isIntegral!T)) &&
        allSatisfy!(isIntegral, I))
{
    alias U = UnsignedOfSameSizeAs!T;
    (*(cast(U*)&a)) &= ~makeBit!U(bixs); // reuse integer variant
}

/** Reset lowest bit of `a` (to zero). */
void resetLowestBit(T)(ref T a) @safe
    if (isIntegral!T)
{
    resetBit(a, 0);
}
alias resetBottomBit = resetLowestBit;

/** Reset highest bit of `a` (to zero). */
void resetHighestBit(T)(ref T a) @safe
    if (isIntegral!T)
{
    resetBit(a, 8*T.sizeof - 1);
}
alias resetTopBit = resetHighestBit;

alias btr = resetBit;

///
unittest
{
    alias T = int;
    enum nBits = 8*T.sizeof;
    T a = 0;

    a.bts(0); assert(a == 1);
    a.bts(1); assert(a == 3);
    a.bts(2); assert(a == 7);

    a.btr(0); assert(a == 6);
    a.btr(1); assert(a == 4);
    a.btr(2); assert(a == 0);

    (&a).bts(0); assert(a == 1);
    (&a).bts(1); assert(a == 3);
    (&a).bts(2); assert(a == 7);

    (&a).btr(0); assert(a == 6);
    (&a).btr(1); assert(a == 4);
    (&a).btr(2); assert(a == 0);

    (&a).bts(0, 1, 2); assert(a == 7);
    (&a).btr(0, 1, 2); assert(a == 0);

    a.bts(8*T.sizeof - 1); assert(a != 0);
    a.btr(8*T.sizeof - 1); assert(a == 0);

    T b = 0;
    b.bts(nBits - 1);
    assert(b == T.min);
}

///
unittest
{
    static void test(T)()
    {
        enum nBits = 8*T.sizeof;
        T x = 0;
        x.bts(0);
    }

    test!float;
    test!double;
}

///
unittest
{
    assert(makeBit!int(2) == 4);
    assert(makeBit!int(2, 3) == 12);
    assert(makeBit!uint(0, 31) == 2^^31 + 1);

    import std.meta : AliasSeq;
    foreach (T; AliasSeq!(ubyte, ushort, uint, ulong))
    {
        foreach (const n; 0 .. 8*T.sizeof)
        {
            const x = makeBit!T(n);
            assert(x == 2UL^^n);

            T y = x;
            y.resetBit(n);
            assert(y == 0);

            y.setBit(n);
            assert(y == x);
        }
    }
}
