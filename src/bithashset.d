module bithashset;

/// Growable flag.
enum Growable { no, yes }

/// Copyable flag.
enum Copyable { no, yes }

/** Store presence of elements of type `E` in a set in the range `0 .. length`. */
struct DenseSetFilter(E,
                      Growable growable = Growable.no,
                      Copyable copyable = Copyable.no)
    if (is(typeof(cast(size_t)E.init))) // is castable to size_t
{
    import core.memory : malloc = pureMalloc, calloc = pureCalloc, realloc = pureRealloc;
    import core.bitop : bts, btr, btc, bt;

    @safe pure nothrow @nogc pragma(inline):

    /// Construct set to store at most `length` number of bits.
    this(size_t length) @trusted
    {
        _blocksPtr = null;
        static if (growable == Growable.yes)
        {
            _length = length;
            _capacity = 0;
            assureCapacity(length);
        }
        else
        {
            _capacity = length;
            _blocksPtr = cast(Block*)calloc(blockCount, Block.sizeof);
        }
    }

    ~this() @trusted
    {
        import qcmeman : free;
        free(_blocksPtr);
    }

    static if (copyable)
    {
        this(this) @trusted
        {
            Block* srcBlocksPtr = _blocksPtr;
            _blocksPtr = cast(Block*)malloc(blockCount * Block.sizeof);
            _blocksPtr[0 .. blockCount] = srcBlocksPtr[0 .. blockCount];
        }
    }
    else
    {
        @disable this(this);

        /// Returns: shallow (and deep) duplicate of `this`.
        typeof(this) dup() @trusted
        {
            typeof(this) copy;
            static if (growable == Growable.yes)
            {
                copy._length = this._length;
            }
            copy._capacity = this._capacity;
            copy._blocksPtr = cast(Block*)malloc(blockCount * Block.sizeof);
            copy._blocksPtr[0 .. blockCount] = this._blocksPtr[0 .. blockCount];
            return copy;
        }
    }

    @property:

    static if (growable == Growable.yes)
    {
        /// Expand to capacity to make room for at least `newLength`.
        private void assureCapacity(size_t newLength) @trusted
        {
            if (_capacity < newLength)
            {
                const oldBlockCount = blockCount;
                import std.math : nextPow2;
                this._capacity = newLength.nextPow2;
                _blocksPtr = cast(Block*)realloc(_blocksPtr, blockCount * Block.sizeof);
                _blocksPtr[oldBlockCount .. blockCount] = 0;
            }
        }
    }

    /** Insert element `e`.
        Returns: precense status of element before insertion.
    */
    bool insert(E e) @trusted
    {
        const ix = cast(size_t)e;
        static if (growable == Growable.yes) { assureCapacity(ix + 1); _length = ix + 1; } else { assert(ix < _capacity); }
        return bts(_blocksPtr, ix) != 0;
    }
    alias put = insert;         // OutputRange compatibility

    /** Remove element `e`.
        Returns: precense status of element before removal.
     */
    bool remove(E e) @trusted
    {
        const ix = cast(size_t)e;
        static if (growable == Growable.yes) { assureCapacity(ix + 1); _length = ix + 1; } else { assert(ix < _capacity); }
        return btr(_blocksPtr, ix) != 0;
    }

    /** Insert element `e` if it's present otherwise remove it.
        Returns: `true` if elements was zeroed, `false` otherwise.
     */
    bool complement(E e) @trusted
    {
        const ix = cast(size_t)e;
        static if (growable == Growable.yes) { assureCapacity(ix + 1); _length = ix + 1; } else { assert(ix < _capacity); }
        return btc(_blocksPtr, ix) != 0;
    }

    /// Check if element `e` is stored/contained.
    bool contains(E e) @trusted const
    {
        const ix = cast(size_t)e;
        static if (growable == Growable.yes)
        {
            return ix < _length && bt(_blocksPtr, ix) != 0;
        }
        else
        {
            return ix < _capacity && bt(_blocksPtr, ix) != 0;
        }
    }

    /// ditto
    auto opBinaryRight(string op)(E e) const
        if (op == "in")
    {
        return contains(e);
    }

    /** Get current capacity in number of elements (bits).
        If `growable` is `Growable.yes` then capacity is variable, otherwise it's constant.
    */
    @property size_t capacity() const
    {
        return _capacity;
    }

private:
    @property size_t blockCount() const
    {
        return _capacity / Block.sizeof + (_capacity % Block.sizeof ? 1 : 0);
    }

    alias Block = size_t;       /// Allocated block type.
    Block* _blocksPtr;          /// Pointer to blocks of bits.
    static if (growable == Growable.yes)
    {
        size_t _length;         /// Offset + 1 of highest set bit.
        size_t _capacity;       /// Number of bits allocated.
    }
    else
    {
        size_t _capacity;       /// Number of bits allocated.
    }
}

///
@safe pure nothrow @nogc unittest
{
    alias E = uint;

    import std.range : isOutputRange;
    alias Set = DenseSetFilter!(E, Growable.no);
    static assert(isOutputRange!(Set, E));

    const set0 = Set();
    assert(set0.capacity == 0);

    const length = 2^^6;
    auto set = DenseSetFilter!E(2*length);
    const y = set.dup;
    assert(y.capacity == 2*length);

    foreach (ix; 0 .. length)
    {
        assert(!set.contains(ix));
        assert(ix !in set);

        assert(!set.insert(ix));
        assert(set.contains(ix));
        assert(ix in set);

        assert(set.complement(ix));
        assert(!set.contains(ix));
        assert(ix !in set);

        assert(!set.complement(ix));
        assert(set.contains(ix));
        assert(ix in set);

        assert(!set.contains(ix + 1));
    }

    auto z = set.dup;
    foreach (ix; 0 .. length)
    {
        assert(z.contains(ix));
        assert(ix in z);
    }

    foreach (ix; 0 .. length)
    {
        assert(set.contains(ix));
        assert(ix in set);
    }

    foreach (ix; 0 .. length)
    {
        assert(set.contains(ix));
        set.remove(ix);
        assert(!set.contains(ix));
    }
}

///
@safe pure nothrow @nogc unittest
{
    alias E = uint;

    auto set = DenseSetFilter!(E, Growable.yes)();
    assert(set._length == 0);

    const length = 2^^16;
    foreach (ix; 0 .. length)
    {
        assert(!set.contains(ix));
        assert(ix !in set);

        assert(!set.insert(ix));
        assert(set.contains(ix));
        assert(ix in set);

        assert(set.complement(ix));
        assert(!set.contains(ix));
        assert(ix !in set);

        assert(!set.complement(ix));
        assert(set.contains(ix));
        assert(ix in set);

        assert(!set.contains(ix + 1));
    }
}

/// test `RefCounted` storage
nothrow @nogc unittest          // TODO pure when https://github.com/dlang/phobos/pull/4692/files has been merged
{
    import std.typecons : RefCounted;
    alias E = int;

    RefCounted!(DenseSetFilter!(E, Growable.yes)) set;

    assert(set._length == 0);
    assert(set.capacity == 0);

    assert(!set.insert(0));
    assert(set._length == 1);
    assert(set.capacity == 2);

    const y = set;

    foreach (const e; 1 .. 1000)
    {
        assert(!set.insert(e));
        assert(set._length == e + 1);
        assert(y._length == e + 1);
    }

    const set1 = RefCounted!(DenseSetFilter!(E, Growable.yes))(42);
    assert(set1._length == 42);
    assert(set1.capacity == 64);
}

///
@safe pure nothrow @nogc unittest
{
    enum E:ubyte { a, b, c, d, dAlias = d }

    auto set = DenseSetFilter!(E, Growable.yes)();

    assert(set._length == 0);

    import std.traits : EnumMembers;
    foreach (lang; [EnumMembers!E])
    {
        assert(!set.contains(lang));
    }
    foreach (lang; [EnumMembers!E])
    {
        set.insert(lang);
        assert(set.contains(lang));
    }

}
