module basic_array;

import std.traits : Unqual;
import container_traits : NoGc, mustAddGCRange, needsMove;

/** Array type with deterministic control of memory. The memory allocated for
    the array is reclaimed as soon as possible; there is no reliance on the
    garbage collector. Array uses malloc, realloc and free for managing its own
    memory.

    Use `std.bitmanip.BitArray` for array container storing boolean values.

    TODO optimize by making members templates. 0.579s before, eval-dwim: 0.67s

    TODO add members keys() and values()

    TODO Add OutputRange.writer support as
    https://github.com/burner/StringBuffer/blob/master/source/stringbuffer.d#L45

    TODO Use `std.traits.areCopyCompatibleArrays`

    See also: https://github.com/facebook/folly/blob/master/folly/docs/FBVector.md
*/
struct BasicArray(T,
                  alias Allocator = null, // null means means to qcmeman functions
                  CapacityType = size_t)  // see also https://github.com/izabera/s
    if (!is(Unqual!T == bool) &&             // use `BitArray` instead
        (is(CapacityType == ulong) ||        // 3 64-bit words
         is(CapacityType == uint)))          // 2 64-bit words
{
    import std.range : isInputRange, isIterable, ElementType, isInfinite;
    import std.traits : Unqual, hasElaborateDestructor, hasIndirections, hasAliasing,
        isMutable, TemplateOf, isArray, isAssignable, isCopyable;
    import std.algorithm : move, moveEmplace, moveEmplaceAll;
    import std.conv : emplace;

    import qcmeman : malloc, calloc, realloc, free, gc_addRange, gc_removeRange;

    /// Mutable element type.
    private alias MutableE = Unqual!T;

    /// Is `true` if `U` can be assign to the element type `T` of `this`.
    enum isElementAssignable(U) = isAssignable!(MutableE, U);

    pragma(inline):

    /// Returns: an array of length `initialLength` with all elements default-initialized to `ElementType.init`.
    pragma(inline, true)
    static typeof(this) withLength()(size_t initialLength)
    {
        return withCapacityLengthZero(initialLength, initialLength, true);
    }

    /// Returns: an array with initial capacity `initialCapacity`.
    pragma(inline, true)
    static typeof(this) withCapacity()(size_t initialCapacity)
    {
        return withCapacityLengthZero(initialCapacity, 0, false);
    }

    /** Construct using
     * - initial capacity `capacity`,
     * - initial length `Length`,
     * - and zeroing-flag `zero`.
     */
    pragma(inline)              // DMD cannot inline
    private static typeof(this) withCapacityLengthZero()(size_t capacity,
                                                         size_t length,
                                                         bool zero) @trusted
    {
        assert(capacity >= length);
        assert(capacity <= CapacityType.max);
        return typeof(return)(Store(typeof(this).allocate(capacity, zero),
                                    cast(CapacityType)capacity,
                                    cast(CapacityType)length));
    }

    /** Emplace `thatPtr` with elements moved from `elements`. */
    static ref typeof(this) emplaceWithMovedElements()(typeof(this)* thatPtr,
                                                       T[] elements) @system
    {
        immutable length = elements.length;
        thatPtr._store.ptr = typeof(this).allocate(length, false);
        thatPtr._store.capacity = cast(CapacityType)length;
        thatPtr._store.length = cast(CapacityType)length;
        foreach (immutable i, ref e; elements[])
        {
            moveEmplace(e, thatPtr._mptr[i]);
        }
        return *thatPtr;
    }

    pragma(inline, true)
    private this(Store store)
    {
        _store = store;
    }

    /// Construct from uncopyable element `value`.
    this()(T value) @trusted
        if (!isCopyable!T)
    {
        _store.ptr = typeof(this).allocate(1, false);
        _store.capacity = 1;
        _store.length = 1;
        moveEmplace(value, _mptr[0]); // TODO remove `moveEmplace` when compiler does it for us
    }

    /// Construct from uncopyable element `value`.
    this(U)(U value) @trusted
        if (isCopyable!U &&
            isElementAssignable!U)
    {
        _store.ptr = typeof(this).allocate(1, false);
        _store.capacity = 1;
        _store.length = 1;
        emplace(&_mptr[0], value);
    }

    static if (isCopyable!T &&
               !is(T == union)) // forbid copying of unions such as `HybridBin` in hashmap.d
    {
        static typeof(this) withElements()(in T[] elements)
        {
            immutable length = elements.length;
            auto ptr = typeof(this).allocate(length, false);

            foreach (immutable i, const e; elements[])
            {
                ptr[i] = e;
            }

            // ptr[0 .. length] = elements[];
            return typeof(return)(Store(ptr,
                                        cast(CapacityType)length,
                                        cast(CapacityType)length));
        }

        /// Returns: shallow duplicate of `this`.
        pragma(inline)          // DMD cannot inline
        @property BasicArray!(Unqual!T, Allocator, CapacityType) dup() const @trusted
        {
            return typeof(this).withElements(this[]);
        }
    }


    /// Construct from element(s) `values`.
    this(U)(U[] values...) @trusted
        if (isCopyable!U &&
            isElementAssignable!U) // prevent accidental move of l-value `values` in array calls
    {
        if (values.length == 1) // TODO branch should be detected at compile-time
        {
            // twice as fast as array assignment below
            _store.ptr = typeof(this).allocate(1, false);
            _store.capacity = 1;
            _store.length = 1;
            emplace(&_mptr[0], values[0]);
            return;
        }
        reserve(values.length);
        _store.length = cast(CapacityType)values.length;
        import emplace_all : moveEmplaceAllNoReset;
        moveEmplaceAllNoReset(values,
                              _mptr[0 .. _store.length]);
    }

    /// Construct from `n` number of element(s) `values` (in a static array).
    this(uint n)(T[n] values...) @trusted
    {
        reserve(values.length);
        _store.length = cast(CapacityType)values.length;
        // TODO use import emplace_all instead
        import static_iota : iota;
        foreach (immutable i; iota!(0, values.length))
        {
            _mptr[i] = values[i];
        }
    }

    /** Is `true` iff constructable from the iterable (or range) `I`.
     */
    enum isAssignableFromElementsOfRefIterableStruct(I) = (is(I == struct) && // exclude class ranges for aliasing control
                                                           isRefIterable!I && // elements may be non-copyable
                                                           !isInfinite!I &&
                                                           isElementAssignable!(ElementType!I));

    /// Construct from the elements `values`.
    this(R)(R values) @trusted
        if (isAssignableFromElementsOfRefIterableStruct!R)
    {
        import std.range : hasLength, hasSlicing;

        static if (hasLength!R &&
                   hasSlicing!R &&
                   isCopyable!(ElementType!R) &&
                   !hasElaborateDestructor!(ElementType!R))
        {
            reserve(values.length);
            import std.algorithm : copy;
            copy(values[0 .. values.length],
                 _mptr[0 .. values.length]); // TODO better to use foreach instead?
            _store.length = values.length;
        }
        else
        {
            static if (hasLength!R)
            {
                reserve(values.length);
                size_t i = 0;
                foreach (ref value; move(values)) // TODO remove `move` when compiler does it for us
                {
                    static if (needsMove!(typeof(value)))
                    {
                        moveEmplace(value, _mptr[i++]);
                    }
                    else
                    {
                        _mptr[i++] = value;
                    }
                }
                _store.length = values.length;
            }
            else
            {
                /* TODO optimize with `moveEmplaceAll` that does a raw copy and
                 * zeroing of values */
                foreach (ref value; move(values)) // TODO remove `move` when compiler does it for us
                {
                    static if (needsMove!(ElementType!R))
                    {
                        insertBackMove(value); // steal element
                    }
                    else
                    {
                        insertBack1(value);
                    }
                }
            }
        }
    }
    /// No default copying.
    @disable this(this);

    /// Destruct.
    ~this()
    {
        release();
    }

    /// Empty.
    void clear()
    {
        release();
        resetInternalData();
    }

    /// Release internal store.
    private void release() @trusted
    {
        static if (hasElaborateDestructor!T)
        {
            destroyElements();
        }
        static if (mustAddGCRange!T)
        {
            gc_removeRange(_store.ptr);
        }
        free(_mptr);
    }

    /// Destroy elements.
    static if (hasElaborateDestructor!T)
    {
        private void destroyElements() @trusted
        {
            foreach (const i; 0 .. _store.length)
            {
                .destroy(_mptr[i]);
            }
        }
    }

    /// Reset internal data.
    pragma(inline, true)
    private void resetInternalData()
    {
        _store.ptr = null;
        _store.capacity = 0;
        _store.length = 0;
    }

    /** Allocate heap regionwith `initialCapacity` number of elements of type `T`.
        If `zero` is `true` they will be zero-initialized.
    */
    private static MutableE* allocate(size_t initialCapacity, bool zero)
    {
        typeof(return) ptr = null;

        if (zero) { ptr = cast(typeof(return))calloc(initialCapacity, T.sizeof); }
        else      { ptr = cast(typeof(return))malloc(initialCapacity * T.sizeof); }
        assert(ptr, "Allocation failed");

        static if (mustAddGCRange!T)
        {
            gc_addRange(ptr, initialCapacity * T.sizeof);
        }
        return ptr;
    }

    /** Comparison for equality. */
    pragma(inline, true)
    bool opEquals()(in typeof(this) rhs) const
    {
        return slice() == rhs.slice();
    }
    /// ditto
    pragma(inline, true)
    bool opEquals()(in ref typeof(this) rhs) const
    {
        return slice() == rhs.slice();
    }
    /// ditto
    pragma(inline, true)
    bool opEquals(U)(in U[] rhs) const
        if (is(typeof(T[].init == U[].init)))
    {
        return slice() == rhs;
    }

    /// Calculate D associative array (AA) key hash.
    size_t toHash()() const @trusted
    {
        import core.internal.hash : hashOf;
        static if (isCopyable!T)
        {
            return this.length ^ hashOf(slice());
        }
        else
        {
            typeof(return) hash = this.length;
            foreach (immutable i; 0 .. this.length)
            {
                hash ^= this.ptr[i].hashOf;
            }
            return hash;
        }
    }

    static if (isCopyable!T)
    {
        /** Construct a string representation of `this` at `sink`.
         */
        void toString()(scope void delegate(const(char)[]) sink) const
        {
            sink("[");
            foreach (const ix, ref value; slice())
            {
                import std.format : formattedWrite;
                sink.formattedWrite("%s", value);
                if (ix + 1 < length) { sink(", "); } // separator
            }
            sink("]");
        }
    }

    /// Check if empty.
    pragma(inline, true)
    bool empty()() const { return _store.length == 0; }

    /// Get length.
    pragma(inline, true)
    @property size_t length()() const { return _store.length; }
    alias opDollar = length;    /// ditto

    /// Set length to `newLength`.
    @property void length()(size_t newLength) @trusted
    {
        if (newLength < length)
        {
            static if (hasElaborateDestructor!T)
            {
                foreach (const i; newLength .. _store.length)
                {
                    .destroy(_mptr[i]);
                }
            }
        }
        else
        {
            reserve(newLength);
            static if (hasElaborateDestructor!T)
            {
                // TODO remove when compiles does it for us
                foreach (const i; _store.length .. newLength)
                {
                    // TODO remove when compiler does it for us:
                    static if (isCopyable!T)
                    {
                        emplace(&_mptr[i], T.init);
                    }
                    else
                    {
                        auto _ = T.init;
                        moveEmplace(_, _mptr[i]);
                    }
                }
            }
            else
            {
                _mptr[_store.length .. newLength] = T.init;
            }
        }

        assert(newLength <= CapacityType.max);
        _store.length = cast(CapacityType)newLength;
    }

    /// Get capacity.
    pragma(inline, true)
    @property size_t capacity()() const { return _store.capacity; }

    /** Ensures sufficient capacity to accommodate for requestedCapacity number
        of elements. If `requestedCapacity` < `capacity`, this method does
        nothing.
     */
    void reserve()(size_t requestedCapacity) @trusted
    {
        assert(requestedCapacity <= CapacityType.max);

        if (requestedCapacity <= capacity) { return; }

        static if (mustAddGCRange!T)
        {
            gc_removeRange(_mptr);
        }

        // growth factor
        // Motivation: https://github.com/facebook/folly/blob/master/folly/docs/FBVector.md#memory-handling
        reallocateAndSetCapacity(3*requestedCapacity/2); // use 1.5 like Facebook's `fbvector` does
        // import std.math : nextPow2;
        // reallocateAndSetCapacity(requestedCapacity.nextPow2);

        static if (mustAddGCRange!T)
        {
            gc_addRange(_mptr, _store.capacity * T.sizeof);
        }
    }

    /// Index support.
    pragma(inline, true)
    scope ref inout(T) opIndex()(size_t i) inout return
    {
        return slice()[i];
    }

    /// Slice support.
    pragma(inline, true)
    scope inout(T)[] opSlice()(size_t i, size_t j) inout return
    {
        return slice()[i .. j];
    }
    /// ditto
    pragma(inline, true)
    scope inout(T)[] opSlice()() inout return
    {
        return slice();
    }

    /// Index assignment support.
    scope ref T opIndexAssign(U)(U value, size_t i) @trusted return
    {
        static if (hasElaborateDestructor!T)
        {
            move(*(cast(MutableE*)(&value)), _mptr[i]); // TODO is this correct?
        }
        else static if (hasIndirections!T && // TODO `hasAliasing` instead?
                        !isMutable!T)
        {
            static assert("Cannot modify constant elements with indirections");
        }
        else
        {
            slice()[i] = value;
        }
        return slice()[i];
    }

    /// Slice assignment support.
    pragma(inline, true)
    scope T[] opSliceAssign(U)(U value) return
    {
        return slice()[] = value;
    }

    /// ditto
    pragma(inline, true)
    scope T[] opSliceAssign(U)(U value, size_t i, size_t j) return
    {
        return slice()[i .. j] = value;
    }

    /// Get reference to front element.
    pragma(inline, true)
    scope ref inout(T) front()() inout return @property
    {
        // TODO use?: enforce(!empty); emsi-containers doesn't, std.container.Array does
        return slice()[0];
    }

    /// Get reference to back element.
    pragma(inline, true)
    scope ref inout(T) back()() inout return @property
    {
        // TODO use?: enforce(!empty); emsi-containers doesn't, std.container.Array does
        return slice()[_store.length - 1];

    }

    /** Move `value` into the end of the array.
     */
    void insertBackMove()(ref T value) @trusted
    {
        reserve(_store.length + 1);
        moveEmplace(value, _mptr[_store.length]);
        _store.length += 1;
    }

    /** Insert `value` into the end of the array.

        TODO rename to `insertBack` and make this steal scalar calls over
        insertBack(U)(U[] values...) overload below
     */
    void insertBack1()(T value) @trusted
    {
        reserve(_store.length + 1);
        static if (needsMove!T)
        {
            insertBackMove(*cast(MutableE*)(&value));
        }
        else
        {
            _mptr[_store.length] = value;
        }
        _store.length += 1;
    }

    /** Insert unmoveable `value` into the end of the array.
     */
    pragma(inline)              // DMD cannot inline
    void insertBack()(T value) @trusted
        if (!isCopyable!T)
    {
        insertBackMove(value);
    }

    /** Insert the elements `values` into the end of the array.
     */
    void insertBack(U)(U[] values...) @trusted
        if (isElementAssignable!U &&
            isCopyable!U)       // prevent accidental move of l-value `values`
    {
        if (values.length == 1) // TODO branch should be detected at compile-time
        {
            // twice as fast as array assignment below
            return insertBack1(values[0]);
        }
        static if (is(T == immutable(T)))
        {
            /* An array of immutable values cannot overlap with the `this`
               mutable array container data, which entails no need to check for
               overlap.
            */
            reserve(_store.length + values.length);
            _mptr[_store.length .. _store.length + values.length] = values;
        }
        else
        {
            import overlapping : overlaps;
            if (_store.ptr == values.ptr) // called for instances as: `this ~= this`
            {
                reserve(2*_store.length); // invalidates `values.ptr`
                foreach (immutable i; 0 .. _store.length)
                {
                    _mptr[_store.length + i] = _store.ptr[i];
                }
            }
            else if (overlaps(this[], values[]))
            {
                assert(false, `TODO Handle overlapping arrays`);
            }
            else
            {
                reserve(_store.length + values.length);
                _mptr[_store.length .. _store.length + values.length] = values;
            }
        }
        _store.length += values.length;
    }

    /** Insert the elements `values` into the end of the array.
     */
    void insertBack(R)(R values)
        if (isAssignableFromElementsOfRefIterableStruct!R)
    {
        import std.range : hasLength;
        static if (isInputRange!R &&
                   hasLength!R)
        {
            reserve(_store.length + values.length);
            import std.algorithm : copy;
            copy(values, _mptr[_store.length .. _store.length + values.length]);
            _store.length += values.length;
        }
        else
        {
            foreach (ref value; move(values)) // TODO remove `move` when compiler does it for us
            {
                static if (isCopyable!(ElementType!R))
                {
                    insertBack(value);
                }
                else
                {
                    insertBackMove(value);
                }
            }
        }
    }

    /// ditto
    alias put = insertBack;

    /** Remove last value fromm the end of the array.
     */
    pragma(inline, true)
    void popBack()()
    {
        assert(!empty);
        _store.length -= 1;
        static if (hasElaborateDestructor!T)
        {
            .destroy(_mptr[_store.length]);
        }
    }

    /** Pop back element and return it. */
    pragma(inline, true)
    T backPop()() @trusted
    {
        assert(!empty);
        _store.length -= 1;
        static if (needsMove!T)
        {
            return move(_mptr[_store.length]); // move is indeed need here
        }
        else
        {
            return _mptr[_store.length]; // no move needed
        }
    }

    /** Pop element at `index`. */
    void popAt()(size_t index)
        @trusted
        @("complexity", "O(length)")
    {
        assert(index < this.length);
        .destroy(_mptr[index]);
        shiftToFrontAt(index);
        _store.length -= 1;
    }

    /** Move element at `index` to return. */
    T moveAt()(size_t index)
        @trusted
        @("complexity", "O(length)")
    {
        assert(index < this.length);
        auto value = move(_mptr[index]);
        shiftToFrontAt(index);
        _store.length -= 1;
        return move(value); // TODO remove `move` when compiler does it for us
    }

    /** Move element at front. */
    pragma(inline, true)
    T frontPop()()
        @("complexity", "O(length)")
    {
        return moveAt(0);
    }

    private void shiftToFrontAt()(size_t index)
        @trusted
    {
        // TODO use this instead:
        // immutable si = index + 1;   // source index
        // immutable ti = index;       // target index
        // immutable restLength = this.length - (index + 1);
        // moveEmplaceAll(_mptr[si .. si + restLength],
        //                _mptr[ti .. ti + restLength]);
        foreach (immutable i; 0 .. this.length - (index + 1)) // each element index that needs to be moved
        {
            immutable si = index + i + 1; // source index
            immutable ti = index + i; // target index
            moveEmplace(_mptr[si], // TODO remove `move` when compiler does it for us
                        _mptr[ti]);
        }
    }

    /** Forwards to $(D insertBack(values)).
     */
    pragma(inline, true)
    void opOpAssign(string op)(T value)
        if (op == "~")
    {
        insertBackMove(value);
    }

    /// ditto
    pragma(inline, true)
    void opOpAssign(string op, U)(U[] values...) @trusted
        if (op == "~" &&
            isElementAssignable!U &&
            isCopyable!U)       // prevent accidental move of l-value `values`
    {
        insertBack(values);
    }

    /// ditto
    pragma(inline, true)
    void opOpAssign(string op, R)(R values)
        if (op == "~" &&
            isInputRange!R &&
            !isInfinite!R &&
            !isArray!R &&
            isElementAssignable!(ElementType!R))
    {
        insertBack(values);
    }

    pragma(inline, true)
    void opOpAssign(string op)(const auto ref typeof(this) values)
        if (op == "~")
    {
        insertBack(values[]);
    }

    // typeof(this) opBinary(string op, R)(R values)
    //     if (op == "~")
    // {
    //     // TODO: optimize
    //     typeof(this) result;
    //     result ~= this[];
    //     assert(result.length == length);
    //     result ~= values[];
    //     return result;
    // }

    /// Helper slice.
    pragma(inline, true)
    scope private inout(T)[] slice() inout return @trusted
    {
        return _store.ptr[0 .. _store.length];
    }

    /// Unsafe access to pointer.
    pragma(inline, true)
    scope inout(T)* ptr()() inout return @system
    {
        return _store.ptr;
    }

    /// Reallocate storage.
    private void reallocateAndSetCapacity()(size_t newCapacity) @trusted
    {
        assert(newCapacity <= CapacityType.max);
        _store.capacity = cast(CapacityType)newCapacity;

        _store.ptr = cast(T*)realloc(_mptr, T.sizeof * _store.capacity);
        assert(_store.ptr, "Reallocation failed");
    }

    /// Mutable pointer.
    pragma(inline, true)
    scope private MutableE* _mptr() const return @trusted
    {
        return cast(typeof(return))_store.ptr;
    }

private:
    /** For more convenient construction. */
    struct Store
    {
        // defined here https://dlang.org/phobos/std_experimental_allocator_gc_allocator.html#.GCAllocator
        // import std.experimental.allocator.gc_allocator : GCAllocator;
        static if (is(Allocator == std.experimental.allocator.gc_allocator.GCAllocator))
        {
            T* ptr;             // GC-allocated store pointer
        }
        else
        {
            @NoGc T* ptr;       // non-GC-allocated store pointer
        }

        CapacityType capacity; // store capacity
        CapacityType length;   // store length
    }

    Store _store;
}

/// construct and append from slices
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T, null, uint);
    static if (size_t.sizeof == 8) // only 64-bit
    {
        static assert(A.sizeof == 2 * size_t.sizeof); // only two words
    }

    auto a = A([10, 11, 12].s);

    a ~= a[];
    assert(a[] == [10, 11, 12,
                   10, 11, 12].s);

    a ~= false;
    assert(a[] == [10, 11, 12,
                   10, 11, 12, 0].s);
}

@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    A a;

    a.length = 1;
    assert(a.length == 1);
    assert(a.capacity >= 1);

    a[0] = 10;

    a.insertBack(11, 12);

    a ~= T.init;
    a.insertBack([3].s);
    assert(a[] == [10, 11, 12, 0, 3].s);

    import std.algorithm : filter;

    a.insertBack([42].s[].filter!(_ => _ is 42));
    assert(a[] == [10, 11, 12, 0, 3, 42].s);

    a.insertBack([42].s[].filter!(_ => _ !is 42));
    assert(a[] == [10, 11, 12, 0, 3, 42].s);

    a ~= a[];
    assert(a[] == [10, 11, 12, 0, 3, 42,
                   10, 11, 12, 0, 3, 42].s);
}

@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    A a;                        // default construction allowed
    assert(a.empty);
    assert(a.length == 0);
    assert(a.capacity == 0);
    assert(a[] == []);

    auto b = BasicArray!int.withLength(3);
    assert(!b.empty);
    assert(b.length == 3);
    assert(b.capacity == 3);
    b[0] = 1;
    b[1] = 2;
    b[2] = 3;
    assert(b[] == [1, 2, 3].s);

    b[] = [4, 5, 6].s;
    assert(b[] == [4, 5, 6].s);

    const c = BasicArray!int.withCapacity(3);
    assert(c.empty);
    assert(c.capacity == 3);
    assert(c[] == []);

    // TODO this should fail with -dip1000
    auto f() @safe
    {
        A a;
        return a[];
    }
    auto d = f();

    const e = BasicArray!int([1, 2, 3, 4].s);
    assert(e.length == 4);
    assert(e[] == [1, 2, 3, 4].s);
}

@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    auto a = A([1, 2, 3].s);
    A b = a.dup;                // copy construction enabled

    assert(a[] == b[]);          // same content
    assert(a[].ptr !is b[].ptr); // but not the same

    assert(b[] == [1, 2, 3].s);
    assert(b.length == 3);

    b ~= 4;
    assert(a != b);
    a.clear();
    assert(a != b);
    b.clear();
    assert(a == b);

    auto c = A([1, 2, 3].s);

    auto d = A(1, 2, 3);
}

/// scope checking
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!T;

    scope T[] leakSlice() @safe return
    {
        A a;
        return a[];             // TODO shouldn't compile with -dip1000
    }

    scope T* leakPointer() @safe return
    {
        A a;
        return a._store.ptr;          // TODO shouldn't compile with -dip1000
    }

    auto lp = leakPointer();    // TODO shouldn't compile with -dip1000
    auto ls = leakSlice();      // TODO shouldn't compile with -dip1000
    T[] as = A(1, 2)[];         // TODO shouldn't compile with -dip1000
    auto bs = A(1, 2)[];        // TODO shouldn't compile with -dip1000
}

version(unittest)
{
    /// uncopyable struct
    private static struct US
    {
        @disable this(this);
        int x;
    }
}

/// construct and insert from non-copyable element type passed by value
@safe pure nothrow /*@nogc*/ unittest
{
    alias A = BasicArray!(US);

    A a = A(US(17));
    assert(a[] == [US(17)]);

    a.insertBack(US(18));
    assert(a[] == [US(17),
                   US(18)]);

    a ~= US(19);
    assert(a[] == [US(17),
                   US(18),
                   US(19)]);
}

/// construct from slice of uncopyable type
@safe pure nothrow @nogc unittest
{
    alias A = BasicArray!(US);
    // TODO can we safely support this?: A a = [US(17)];
}

// construct from array with uncopyable elements
@safe pure nothrow @nogc unittest
{
    alias A = BasicArray!(US);

    A a;
    assert(a.empty);

    a.insertBack(A.init);
    assert(a.empty);
}

// construct from ranges of uncopyable elements
@safe pure nothrow @nogc unittest
{
    alias T = US;
    alias A = BasicArray!T;

    A a;
    assert(a.empty);

    import std.algorithm : map, filter;

    const b = A([10, 20, 30].s[].map!(_ => T(_^^2))); // hasLength
    assert(b.length == 3);
    assert(b == [T(100), T(400), T(900)].s);

    const c = A([10, 20, 30].s[].filter!(_ => _ == 30).map!(_ => T(_^^2))); // !hasLength
    assert(c == [T(900)].s);
}

// construct from ranges of copyable elements
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!T;

    A a;
    assert(a.empty);

    import std.algorithm : map, filter;

    const b = A([10, 20, 30].s[].map!(_ => T(_^^2))); // hasLength
    assert(b.length == 3);
    assert(b == [T(100), T(400), T(900)].s);

    const c = A([10, 20, 30].s[].filter!(_ => _ == 30).map!(_ => T(_^^2))); // !hasLength
    assert(c == [T(900)].s);
}

/// construct with string as element type that needs GC-range
@safe pure nothrow @nogc unittest
{
    alias T = string;
    alias A = BasicArray!(T);

    A a;
    a ~= `alpha`;
    a ~= `beta`;
    a ~= [`gamma`, `delta`].s;
    assert(a[] == [`alpha`, `beta`, `gamma`, `delta`].s);

    const b = [`epsilon`].s;

    a.insertBack(b);
    assert(a[] == [`alpha`, `beta`, `gamma`, `delta`, `epsilon`].s);

    a ~= b;
    assert(a[] == [`alpha`, `beta`, `gamma`, `delta`, `epsilon`, `epsilon`].s);
}

/// convert to string
unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    BasicArray!char sink;
    // TODO make this work: A([1, 2, 3]).toString(sink.put);
}

/// foreach
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    auto a = A([1, 2, 3].s);

    foreach (const i, const e; a)
    {
        assert(i + 1 == e);
    }
}

/// removal
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    auto a = A([1, 2, 3].s);
    assert(a == [1, 2, 3].s);

    assert(a.frontPop() == 1);
    assert(a == [2, 3].s);

    a.popAt(1);
    assert(a == [2].s);

    a.popAt(0);
    assert(a == [].s);

    a.insertBack(11);
    assert(a == [11].s);

    assert(a.backPop == 11);

    a.insertBack(17);
    assert(a == [17].s);
    a.popBack();
    assert(a.empty);

    a.insertBack([11, 12, 13, 14, 15].s[]);
    a.popAt(2);
    assert(a == [11, 12, 14, 15].s);
    a.popAt(0);
    assert(a == [12, 14, 15].s);
    a.popAt(2);

    assert(a == [12, 14].s);

    a ~= a;
}

/// removal
@safe pure nothrow unittest
{
    size_t mallocCount = 0;
    size_t freeCount = 0;

    struct S
    {
        @safe pure nothrow @nogc:

        import qcmeman : malloc, free;

        this(int x) @trusted
        {
            // dln("ctor:");
            _ptr = cast(int*)malloc(1);
            mallocCount += 1;
            // dln("malloc: _ptr=", _ptr);
            *_ptr = x;
        }

        @disable this(this);

        ~this() @trusted
        {
            // dln("dtor:");
            free(_ptr);
            freeCount += 1;
            // dln("free: _ptr=", _ptr);
        }

        @NoGc int* _ptr;
    }

    // TODO static assert(!mustAddGCRange!S);

    /* D compilers cannot currently move stuff efficiently when using
     * std.algorithm.mutation.move. A final dtor call to the cleared sourced is
     * always done. */
    size_t extraDtor = 1;

    alias A = BasicArray!(S);
    static assert(!mustAddGCRange!A);
    alias AA = BasicArray!(A);
    static assert(!mustAddGCRange!AA);

    assert(mallocCount == 0);

    {
        A a;
        a.insertBack(S(11));
        assert(mallocCount == 1);
        assert(freeCount == extraDtor + 0);
    }

    assert(freeCount == extraDtor + 1);

    // assert(a.front !is S(11));
    // assert(a.back !is S(11));
    // a.insertBack(S(12));
}

/// test `OutputRange` behaviour with std.format
@safe pure /*TODO nothrow @nogc*/ unittest
{
    import std.format : formattedWrite;
    const x = "42";
    alias A = BasicArray!(char);
    A a;
    a.formattedWrite!("x : %s")(x);
    assert(a == "x : 42");
}

/// test emplaceWithMovedElements
@trusted pure nothrow @nogc unittest
{
    const x = "42";
    alias A = BasicArray!(char);

    auto ae = ['a', 'b'].s;

    A a = void;
    A.emplaceWithMovedElements(&a, ae[]);

    assert(a.length == ae.length);
    assert(a.capacity == ae.length);
    assert(a[] == ae);
}

@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T, null, uint);
    const a = A(17);
    assert(a[] == [17].s);
}

/// check duplication
@safe pure nothrow @nogc unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    static assert(!__traits(compiles, { A b = a; })); // copying disabled

    auto a = A([10, 11, 12].s);
    auto b = a.dup;
    assert(a == b);
    assert(a[].ptr !is b[].ptr);
}

/// construct from map range
@safe pure nothrow unittest
{
    import std.algorithm : map;
    alias T = int;
    alias A = BasicArray!(T);
    auto a = A([10, 20, 30].s[].map!(_ => _^^2));
    assert(a[] == [100, 400, 900].s);
}

/// construct from map range
@trusted pure nothrow unittest
{
    alias T = int;
    alias A = BasicArray!(T);

    import std.typecons : RefCounted;
    RefCounted!A x;

    auto z = [1, 2, 3].s;
    x ~= z[];

    auto y = x;
    assert(y == z);
}

/// TODO Move to Phobos.
private enum bool isRefIterable(T) = is(typeof({ foreach (ref elem; T.init) {} }));

version(unittest)
{
    import array_help : s;
}

import dbgio;