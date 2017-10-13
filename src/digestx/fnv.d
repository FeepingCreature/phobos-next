/**
   FNV(Fowler-Noll-Vo) hash implementation. This module conforms to the APIs defined in std.digest.digest.
*/
module digestx.fnv;

public import std.digest.digest;

/**
 * Template API FNV-1(a) hash implementation.
 */
struct FNV(ulong bitLength, bool fnv1a = false)
{
    static if (bitLength == 32)
    {
        alias Element = uint;
    }
    else static if (bitLength == 64)
    {
        alias Element = ulong;
    }
    else
    {
        static assert(0, "Unsupported hash length " ~ bitLength.stringof);
    }

    pragma(inline, true):

    /// Initializes the digest calculation.
    void start() @safe pure nothrow @nogc
    {
        _hash = fnvOffsetBasis;
    }

    /// Feeds the digest with data.
    void put(scope const(ubyte)[] data...) @trusted pure nothrow @nogc
    {
        foreach (immutable ubyte i; data)
        {
            static if (fnv1a)
            {
                _hash ^= i;
                _hash *= fnvPrime;
            }
            else
            {
                _hash *= fnvPrime;
                _hash ^= i;
            }
        }
    }

    /// Returns the finished FNV digest. This also calls start to reset the internal state.
    ubyte[bitLength / 8] finish() @trusted pure nothrow @nogc
    {
        import std.bitmanip : nativeToBigEndian;
        _result = _hash;
        start();
        return nativeToBigEndian(_result); // TODO can avoid this calculation?
    }

    Element get() const
    {
        return _result;
    }

private:

    // FNV-1 hash parameters
    static if (bitLength == 32)
    {
        enum Element fnvPrime = 0x1000193U;
        enum Element fnvOffsetBasis = 0x811C9DC5U;
    }
    else static if (bitLength == 64)
    {
        enum Element fnvPrime = 0x100000001B3UL;
        enum Element fnvOffsetBasis = 0xCBF29CE484222325UL;
    }
    else
    {
        static assert(0, "Unsupported hash length " ~ bitLength.stringof);
    }

    Element _hash;
    Element _result;
}

alias FNV32 = FNV!32; /// 32bit FNV-1, hash size is ubyte[4]
alias FNV64 = FNV!64; /// 64bit FNV-1, hash size is ubyte[8]
alias FNV32A = FNV!(32, true); /// 32bit FNV-1a, hash size is ubyte[4]
alias FNV64A = FNV!(64, true); /// 64bit FNV-1a, hash size is ubyte[8]

///
unittest
{
    // alias FNV32Digest = WrapperDigest!FNV32; /// OOP API for 32bit FNV-1
    // alias FNV64Digest = WrapperDigest!FNV64; /// OOP API for 64bit FNV-1
    alias FNV32ADigest = WrapperDigest!FNV32A; /// OOP API for 32bit FNV-1a
    // alias FNV64ADigest = WrapperDigest!FNV64A; /// OOP API for 64bit FNV-1a

    FNV64 fnv64;
    fnv64.start();
    fnv64.put(cast(ubyte[]) "hello");
    assert(toHexString(fnv64.finish()) == "7B495389BDBDD4C7");

    // Template API
    assert(digest!FNV32("abc") == x"439C2F4B");
    assert(digest!FNV64("abc") == x"D8DCCA186BAFADCB");
    assert(digest!FNV32A("abc") == x"1A47E90B");
    assert(digest!FNV64A("abc") == x"E71FA2190541574B");

    // OOP API
    Digest fnv = new FNV32ADigest;
    ubyte[] d = fnv.digest("1234");
    assert(d == x"FDC422FD");
}

/// Convenience aliases for std.digest.digest.digest using the FNV implementation.
auto fnv32Of(T...)(in T data)
{
    return digest!(FNV32, T)(data);
}
/// ditto
auto fnv64Of(T...)(in T data)
{
    return digest!(FNV64, T)(data);
}
/// ditto
auto fnv32aOf(T...)(in T data)
{
    return digest!(FNV32A, T)(data);
}
/// ditto
auto fnv64aOf(T...)(in T data)
{
    return digest!(FNV64A, T)(data);
}

///
@safe pure nothrow @nogc unittest
{
    assert(fnv32Of("") == x"811C9DC5");
    assert(fnv64Of("") == x"CBF29CE484222325");
    assert(fnv32aOf("") == x"811C9DC5");
    assert(fnv64aOf("") == x"CBF29CE484222325");
}
