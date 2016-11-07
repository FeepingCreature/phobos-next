/** Ownership and borrwoing á lá Rust.

    TODO:

    <ul>
    <li> TODO Move to typecons_ex.

    <li> TODO Perhaps disable all checking (and unittests) in release mode (when
    debug is not active), but preserve overloads sliceRO and sliceRW. If not use
    `enforce` instead.

    <li> TODO Implement and use trait `hasUnsafeSlicing`

    <li> TODO Add WriteBorrowedPointer, ReadBorrowedPointer to wrap `ptr` access to Container

    <li> TODO Is sliceRW and sliceRO good names?

    <li> TODO can we make the `_range` member non-visible but the alias this
    public in ReadBorrowedSlice and WriteBorrowedSlice

    </ul>
 */
module borrown;

version(unittest)
{
    import dbgio;
}

/** Return wrapper around container `Container` that can be safely sliced, by
    tracking number of read borrowed ranges and whether it's currently write
    borrowed.

    Only relevant when `Container` implements referenced access over
    <ul>
    <li> `opSlice` and
    <li> `opIndex`
    </ul>

    TODO Iterate and wrap all @unsafe accessors () and wrapped borrow
    checks for all modifying members of `Container`?
*/
struct Owned(Container)
    if (needsOwnership!Container)
{
    import std.range.primitives : hasSlicing;
    import std.traits : isMutable;

    /// Type of range of `Container`.
    alias Range = typeof(Container.init[]);

pragma(inline):

    // TODO can we somehow disallow move construction for `this`?

    ~this()
    {
        assert(!_writeBorrowed, "This is still write-borrowed, cannot release!");
        assert(_readBorrowCount == 0, "This is still read-borrowed, cannot release!");
    }

    /// Move `this` into a returned r-value.
    typeof(this) move()
    {
        assert(!_writeBorrowed, "This is still write-borrowed, cannot move!");
        assert(_readBorrowCount == 0, "This is still read-borrowed, cannot move!");
        import std.algorithm.mutation : move;
        return move(this);
    }

    /** Checked overload for `std.algorithm.mutation.move`. */
    void move(ref typeof(this) dst) pure nothrow @nogc
    {
        assert(!this._writeBorrowed, "Source is still write-borrowed, cannot move!");
        assert(this._readBorrowCount == 0, "Source is still read-borrowed, cannot move!");

        assert(!dst._writeBorrowed, "Destination is still write-borrowed, cannot move!");
        assert(dst._readBorrowCount == 0, "Destination is still read-borrowed, cannot move!");

        import std.algorithm.mutation : move;
        move(this, dst);
    }

    /** Checked overload for `std.algorithm.mutation.moveEmplace`. */
    void moveEmplace(ref typeof(this) dst) pure nothrow @nogc
    {
        assert(!this._writeBorrowed, "Source is still write-borrowed, cannot moveEmplace!");
        assert(this._readBorrowCount == 0, "Source is still read-borrowed, cannot moveEmplace!");

        import std.algorithm.mutation : moveEmplace;
        moveEmplace(this, dst);
    }

    static if (true/*TODO hasUnsafeSlicing!Container*/)
    {
        import std.typecons : Unqual;

        /// Get full read-only slice.
        ReadBorrowedSlice!(Range, Owned) sliceRO() const @trusted
        {
            assert(!_writeBorrowed, "This is already write-borrowed");
            return typeof(return)(_container.opSlice,
                                  cast(Unqual!(typeof(this))*)(&this)); // trusted unconst casta
        }

        /// Get read-only slice in range `i` .. `j`.
        ReadBorrowedSlice!(Range, Owned) sliceRO(size_t i, size_t j) const @trusted
        {
            assert(!_writeBorrowed, "This is already write-borrowed");
            return typeof(return)(_container.opSlice[i .. j],
                                  cast(Unqual!(typeof(this))*)(&this)); // trusted unconst cast
        }

        /// Get full read-write slice.
        WriteBorrowedSlice!(Range, Owned) sliceRW() @trusted
        {
            assert(!_writeBorrowed, "This is already write-borrowed");
            assert(_readBorrowCount == 0, "This is already read-borrowed");
            return typeof(return)(_container.opSlice, &this);
        }

        /// Get read-write slice in range `i` .. `j`.
        WriteBorrowedSlice!(Range, Owned) sliceRW(size_t i, size_t j) @trusted
        {
            assert(!_writeBorrowed, "This is already write-borrowed");
            assert(_readBorrowCount == 0, "This is already read-borrowed");
            return typeof(return)(_container.opSlice[i .. j], &this);
        }

        /// Get read-only slice in range `i` .. `j`.
        auto opSlice(size_t i, size_t j) const
        {
            return sliceRO(i, j);
        }
        /// Get read-write slice in range `i` .. `j`.
        auto opSlice(size_t i, size_t j)
        {
            return sliceRW(i, j);
        }

        /// Get read-only slice.
        auto opSlice() const
        {
            return sliceRO();
        }
        /// Get read-write slice.
        auto opSlice()
        {
            return sliceRW();
        }
    }

    @safe pure nothrow @nogc:

    @property:

    /// Returns: `true` iff owned container is borrowed.
    bool isBorrowed() const { return _writeBorrowed || _readBorrowCount >= 1; }

    /// Returns: `true` iff owned container is write borrowed.
    bool isWriteBorrowed() const { return _writeBorrowed; }

    /// Returns: number of read-only borrowers of owned container.
    uint readBorrowCount() const { return _readBorrowCount; }

    Container _container;            /// wrapped container
    alias _container this;
private:
    bool _writeBorrowed = false; /// `true' if _container is currently referred to
    uint _readBorrowCount = 0; /// number of readable borrowers. TODO use `size_t` minus one bit instead in `size_t _stats`
}

/** Checked overload for `std.algorithm.mutation.move`.

    TODO Can we somehow prevent users of Owned from accidentally using
    `std.algorithm.mutation.move` instead of this wrapper?
 */
void move(Owner)(ref Owner src, ref Owner dst) @safe pure nothrow @nogc
    if (isInstanceOf!(Owned, Owner))
{
    src.move(dst);              // reuse member function
}

/** Checked overload for `std.algorithm.mutation.moveEmplace`.

    TODO Can we somehow prevent users of Owned from accidentally using
    `std.algorithm.mutation.moveEmplace` instead of this wrapper?
*/
void moveEmplace(Owner)(ref Owner src, ref Owner dst) @safe pure nothrow @nogc
    if (isInstanceOf!(Owned, Owner))
{
    src.moveEmplace(dst);   // reuse member function
}

/** Write-borrowed access to range `Range`. */
private static struct WriteBorrowedSlice(Range, Owner)
    // if (isInstanceOf!(Owned, Owner))
{
    this(Range range, Owner* owner)
    {
        assert(owner);
        _range = range;
        _owner = owner;
        owner._writeBorrowed = true;
    }

    @disable this(this);        // cannot be copied

    ~this()
    {
        debug assert(_owner._writeBorrowed, "Write borrow flag is already false, something is wrong with borrowing logic.");
        _owner._writeBorrowed = false;
    }

    Range _range;                   /// range
    alias _range this;              /// behave like range

private:
    Owner* _owner = null;           /// pointer to container owner
}

/** Read-borrowed access to range `Range`. */
private static struct ReadBorrowedSlice(Range, Owner)
    // if (isInstanceOf!(Owned, Owner))
{
    this(const Range range, Owner* owner)
    {
        assert(owner);
        _range = range;
        _owner = owner;

        assert(_owner._readBorrowCount != typeof(_owner._readBorrowCount).max, "Cannot have more borrowers.");
        _owner._readBorrowCount += 1;
    }

    this(this)
    {
        assert(_owner._readBorrowCount != typeof(_owner._readBorrowCount).max, "Cannot have more borrowers.");
        _owner._readBorrowCount += 1;
    }

    ~this()
    {
        debug assert(_owner._readBorrowCount != 0, "Read borrow counter is already zero, something is wrong with borrowing logic.");
        _owner._readBorrowCount -= 1;
    }

    /// Get read-only slice in range `i` .. `j`.
    auto opSlice(size_t i, size_t j)
    {
        return typeof(this)(_range[i .. j], _owner);
    }

    /// Get read-only slice.
    auto opSlice() inout
    {
        return this;            // same as copy
    }

    const Range _range;         /// constant range
    alias _range this;          /// behave like range

private:
    Owner* _owner = null;       /// pointer to container owner
}

template needsOwnership(Container)
{
    import std.range.primitives : hasSlicing;
    // TODO activate when array_ex : UncopyableArray
    // enum needsOwnership = hasSlicing!Container; // TODO extend to check if it's not @safe
    enum needsOwnership = is(Container == struct);
}

version(unittest)
{
    import array_ex : UncopyableArray, CopyableArray;
}

pure unittest
{
    alias A = UncopyableArray!int;
    const Owned!A co;          // const owner

    import std.traits : isMutable;
    static assert(!isMutable!(typeof(co)));

    const cos = co[];
}

@safe pure unittest
{
    alias A = UncopyableArray!int;
    A a = A.init;
    a = A.init;
    // TODO a ~= A.init;
}

@safe pure unittest
{
    alias A = CopyableArray!int;
    A a = A.init;
    A b = A.init;
    a = b;
    a ~= b;
}

pure unittest
{
    import std.traits : isInstanceOf;
    import std.exception: assertThrown;
    import core.exception : AssertError;

    alias A = UncopyableArray!int;

    Owned!A oa;

    Owned!A ob;
    oa.move(ob);                // ok to move unborrowed

    Owned!A od = void;
    oa.moveEmplace(od);         // ok to moveEmplace unborrowed

    static assert(oa.sizeof == 4*size_t.sizeof);

    oa ~= 1;
    oa ~= 2;
    assert(oa[] == [1, 2]);
    assert(oa[0 .. 1] == [1]);
    assert(oa[1 .. 2] == [2]);
    assert(oa[0 .. 2] == [1, 2]);
    assert(!oa.isWriteBorrowed);
    assert(!oa.isBorrowed);
    assert(oa.readBorrowCount == 0);

    {
        const wb = oa.sliceRW;

        Owned!A oc;
        assertThrown!AssertError(oa.move()); // cannot move write borrowed

        assert(wb.length == 2);
        static assert(!__traits(compiles, { auto wc = wb; })); // write borrows cannot be copied
        assert(oa.isBorrowed);
        assert(oa.isWriteBorrowed);
        assert(oa.readBorrowCount == 0);
        assertThrown!AssertError(oa.opSlice); // one more write borrow is not allowed
    }

    // ok to write borrow again in separate scope
    {
        const wb = oa.sliceRW;

        assert(wb.length == 2);
        assert(oa.isBorrowed);
        assert(oa.isWriteBorrowed);
        assert(oa.readBorrowCount == 0);
    }

    // ok to write borrow again in separate scope
    {
        const wb = oa.sliceRW(0, 2);
        assert(wb.length == 2);
        assert(oa.isBorrowed);
        assert(oa.isWriteBorrowed);
        assert(oa.readBorrowCount == 0);
    }

    // multiple read-only borrows are allowed
    {
        const rb1 = oa.sliceRO;

        Owned!A oc;
        assertThrown!AssertError(oa.move(oc)); // cannot move read borrowed

        assert(rb1.length == oa.length);
        assert(oa.readBorrowCount == 1);

        const rb2 = oa.sliceRO;
        assert(rb2.length == oa.length);
        assert(oa.readBorrowCount == 2);

        const rb3 = oa.sliceRO;
        assert(rb3.length == oa.length);
        assert(oa.readBorrowCount == 3);

        const rb_ = rb3;
        assert(rb_.length == oa.length);
        assert(oa.readBorrowCount == 4);
        assertThrown!AssertError(oa.sliceRW); // single write borrow is not allowed
    }

    // test modification via write borrow
    {
        auto wb = oa.sliceRW;
        wb[0] = 11;
        wb[1] = 12;
        assert(wb.length == oa.length);
        assert(oa.isWriteBorrowed);
        assert(oa.readBorrowCount == 0);
        assertThrown!AssertError(oa.sliceRO);
    }
    assert(oa[] == [11, 12]);
    assert(oa.sliceRO(0, 2) == [11, 12]);

    // test mutable slice
    static assert(isInstanceOf!(WriteBorrowedSlice, typeof(oa.sliceRW())));
    static assert(isInstanceOf!(WriteBorrowedSlice, typeof(oa[])));
    foreach (ref e; oa.sliceRW)
    {
        assertThrown!AssertError(oa.sliceRO); // one more write borrow is not allowed
        assertThrown!AssertError(oa.sliceRW); // one more write borrow is not allowed
        assertThrown!AssertError(oa[]); // one more write borrow is not allowed
    }

    // test readable slice
    static assert(isInstanceOf!(ReadBorrowedSlice, typeof(oa.sliceRO())));
    foreach (const ref e; oa.sliceRO)
    {
        assert(oa.sliceRO.length == oa.length);
        assert(oa.sliceRO[0 .. 0].length == 0);
        assert(oa.sliceRO[0 .. 1].length == 1);
        assert(oa.sliceRO[0 .. 2].length == oa.length);
        assertThrown!AssertError(oa.sliceRW); // write borrow during iteration is not allowed
        assertThrown!AssertError(oa.move());  // move not allowed when borrowed
    }

    // move semantics
    auto oaMove1 = oa.move();
    auto oaMove2 = oaMove1.move();
    assert(oaMove2[] == [11, 12]);

    // constness propagation from owner to borrower
    Owned!A mo;          // mutable owner
    assert(mo.sliceRO.ptr == mo.ptr);
    assert(mo.sliceRO(0, 0).ptr == mo.ptr);
    static assert(isInstanceOf!(ReadBorrowedSlice, typeof(mo.sliceRO())));

    const Owned!A co;          // const owner
    assert(co.sliceRO.ptr == co.ptr);
    static assert(isInstanceOf!(ReadBorrowedSlice, typeof(co.sliceRO())));
}

nothrow unittest
{
    import std.algorithm.sorting : sort;
    alias E = int;
    alias A = UncopyableArray!E;
    A a;
    sort(a[]);         // TODO make this work
}

// y = sort(x.move()), where x and y are instances of unsorted Array
@safe nothrow unittest
{
    import std.algorithm.sorting : sort;
    import std.range : isRandomAccessRange, hasSlicing;

    alias E = int;
    alias A = UncopyableArray!E;
    alias O = Owned!A;

    const O o;
    auto os = o[];
    auto oss = os[];            // no op

    static assert(is(typeof(os) == typeof(oss)));
    // static assert(hasSlicing!(typeof(os)));
    // TODO make these work:
    version(none)
    {
        static assert(isRandomAccessRange!S);
        import std.algorithm.sorting : sort;
        sort(a[]);
    }
}
