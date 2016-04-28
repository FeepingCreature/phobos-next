module modulo;                  // haha ;)

import std.traits : isIntegral;

/** Module type within inclusive value range (0 .. `m`-1).

    Similar to Ada's modulo type `0 mod m`.

    See also: https://forum.dlang.org/post/hmrpwyqfoxwtywbznbrr@forum.dlang.org
    See also: http://codeforces.com/contest/628/submission/16212299

    TODO Allow assignment from Mod!N = Mod!M when N >= M

    TODO reuse ideas from bound.d

    TODO Add function limit()
    static if (isPow2!m)
    {
    return x & 2^^m - 1;
    }
    else
    {
    return x % m;
    }

    called after opBinary opUnary etc similar to what is done
    http://codeforces.com/contest/628/submission/16212299

    TODO Move to Phobos std.typecons
 */
template Mod(size_t m, T = void)
    if (is(T == void) || isIntegral!T)
{
    import math_ex : isPow2;

    static assert(m > 0, "m must be greater than zero");

    static if (!is(T == void)) // check if type `T` was explicitly required
    {
        static assert(m - 1 <= 2^^(8*T.sizeof) - 1); // if so, check that it matches `s`
        alias S = T;
    }
    // otherwise, infer it from `m`
    else static if (m - 1 <= ubyte.max)  { alias S = ubyte; }
    else static if (m - 1 <= ushort.max) { alias S = ushort; }
    else static if (m - 1 <= uint.max)   { alias S = uint; }
    else                                 { alias S = ulong; }

    struct Mod
    {
        this(U)(U value)
            if (isIntegral!U)
        in
        {
            assert(value < m, "value too large"); // TODO use enforce instead?
        }
        body
        {
            this.x = cast(S)value; // TODO ok to cast here?
        }

        auto ref opAssign(U)(U value)
            if (isIntegral!U)
        in
        {
            assert(value < m, "value too large"); // TODO use enforce instead?
        }
        body
        {
            this.x = cast(S)value; // TODO ok to cast here?
        }

        /// Construct from Mod!n, where `m >= n`.
        this(size_t n, U)(Mod!(n, U) rhs)
            if (m >= n && isIntegral!U)
        {
            this.x = rhs.x;
        }

        /// Assign from Mod!n, where `m >= n`.
        auto ref opAssign(size_t n, U)(Mod!(n, U) rhs)
            if (m >= n && isIntegral!U)
        {
            this.x = rhs.x;
        }

        @property size_t _prop() const { return x; } // read-only access
        alias _prop this;

        private S x;
    }
}

/// Instantiator for `Mod`.
auto mod(size_t m, T)(T value)
    if (is(T == void) || isIntegral!T)
{
    return Mod!(m, T)(value);
}

///
@safe pure nothrow @nogc unittest
{
    // check size logic
    static assert(Mod!(ubyte.max + 1).sizeof == 1);
    static assert(Mod!(ubyte.max + 2).sizeof == 2);
    static assert(Mod!(ushort.max + 1).sizeof == 2);
    static assert(Mod!(ushort.max + 2).sizeof == 4);
    static assert(Mod!(cast(size_t)uint.max + 1).sizeof == 4);
    static assert(Mod!(cast(size_t)uint.max + 2).sizeof == 8);

    Mod!(8, ubyte) x = 6;
    Mod!(8, ubyte) y = 7;

    assert(x < y);

    y = 5;
    y = 5L;

    assert(y < x);

    assert(y == 5);
    assert(y != 0);

    Mod!(8, uint) ui8 = 7;
    Mod!(256, ubyte) ub256 = 255;

    Mod!(258, ushort) ub258 = ub256;

    // copy construction to smaller modulo is disallowed
    static assert(!__traits(compiles, { Mod!(255, ubyte) ub255 = ub258; }));

    auto a = 7.mod!10;
    auto b = 8.mod!256;
    auto c = 257.mod!1000;

    assert(a < b);
    assert(a < c);

    b = a;
    c = a;
    c = b;

    // assignment to smaller modulo is disallowed
    static assert(!__traits(compiles, { a = b; }));
    static assert(!__traits(compiles, { a = c; }));
}
