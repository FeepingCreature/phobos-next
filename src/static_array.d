module static_array;

/** Statically allocated `E`-array of fixed pre-allocated length.
    Similar to Rust's `fixedvec`: https://docs.rs/fixedvec/0.2.3/fixedvec/
*/
struct StaticArrayN(E, uint capacity)
{
    E[capacity] _store;

    static      if (capacity < ubyte.max + 1)  ubyte _length;
    else static if (capacity < ushort.max + 1) ushort _length;
    else static assert("Too large capacity " ~ capacity);

    alias ElementType = E;

    @safe pure nothrow @nogc:

    /// Construct with elements `ixs`.
    this(Es...)(Es ixs)
        if (Es.length >= 1 &&
            Es.length <= capacity)
    {
        foreach (const i, const ix; ixs)
        {
            _store[i] = ix;
        }
        _length = ixs.length;
    }

    /** Get length. */
    auto length() const { return _length; }
}

///
@safe pure unittest
{
    alias E = char;
    enum capacity = 3;

    alias A = StaticArrayN!(E, capacity);
    static assert(A.sizeof == E.sizeof*capacity + 1);

    auto ab = A('a', 'b');
    assert(ab.length == 2);

    const abc = A('a', 'b', 'c');
    assert(abc.length == 3);

    static assert(!__traits(compiles, { const abc = A('a', 'b', 'c', 'd'); }));
}
