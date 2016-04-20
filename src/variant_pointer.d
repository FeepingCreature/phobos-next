module variant_pointer;

version(unittest)
{
    import dbg : dln;
}

/** A variant pointer to either of `Types`.

    Realizes a very lightweight version of polymorphism packed inside one single
    pointer. Typically the three least significant bits are used to store type
    information.
 */
struct VariantPointer(Types...)
{
    alias S = size_t;
    private enum N = Types.length; // useful local shorthand

    enum typeBits = 8;               // number of bits used to represent type
    enum maxTypeCount = 2^^typeBits; // maximum of different types
    enum typeShift = 8*S.sizeof - typeBits;
    enum typeMask = cast(S)(maxTypeCount - 1) << typeShift;

    import std.meta : staticIndexOf;
    enum tixOf(T) = staticIndexOf!(T, Types); // TODO cast to ubyte if N is <= 256

    enum bool allows(T) = tixOf!T >= 0;
    static assert(N <= maxTypeCount, "Can only represent 8 different types");

    static assert(this.sizeof == (void*).sizeof); // should have same size as pointer

    extern (D) S toHash() const @trusted pure nothrow
    {
        import core.internal.hash : hashOf;
        return _raw.hashOf;
    }

    pure nothrow @nogc:

    this(T)(T* value)
        if (allows!T)
    {
        init(value);
    }

    auto opAssign(T)(T* that)
        if (allows!T)
    {
        init(that);
        return this;
    }

    private void init(T)(T* that)
    in
    {
        assert(!(cast(S)that & typeMask));
    }
    body
    {
        _raw = (cast(S)that | // pointer in lower part
                (cast(S)(tixOf!T) << typeShift)); // use higher bits for type information
    }

    private bool isOfType(T)() const nothrow @nogc
    {
        return ((_raw & typeMask) >> typeShift) == tixOf!T;
    }

    @property inout(T)* peek(T)() inout @trusted @nogc nothrow
    {
        static if (!is(T == void))
            static assert(allows!T, "Cannot store a " ~ T.stringof ~ " in a " ~ name);
        if (!isOfType!T) return null;
        return cast(inout T*)(cast(S)_raw & ~typeMask);
    }

    private S _raw;
}

pure nothrow unittest
{
    import std.meta : AliasSeq;

    alias Types = AliasSeq!(byte, short, int, long,
                            float, double, real, char);

    alias VP = VariantPointer!Types;

    VP x;

    foreach (T; Types)
    {
        T a = 73;

        x = &a;

        foreach (U; Types)
        {
            static if (is(T == U))
            {
                assert(x.peek!U);
                assert(*(x.peek!U) == a);
            }
            else
            {
                assert(!x.peek!U);
            }
        }
    }
}
