module open_hashmap_or_hashset;

import container_traits : isNullableType, defaultNullKeyConstantOf, mustAddGCRange, isNull, nullify;
import pure_mallocator : PureMallocator;

@safe:

/** Hash set (or map) with open-addressing, storing (key) elements of type `K`
 * and values of type `V`.
 *
 * Uses open-addressing with quadratic probing (using triangular numbers) and
 * lazy deletion/removal.
 *
 * Params:
 *      K = key type.
 *      V = value type.
 *      hasher = hash function or std.digest Hash.
 *      Allocator = memory allocator for bin array
 *
 * See also: https://en.wikipedia.org/wiki/Lazy_deletion
 * See also: https://probablydance.com/2017/02/26/i-wrote-the-fastest-hashtable/
 *
 * TODO when K is a class or pointer use use void*.max or 0x1 as deleted value
 *
 * TODO extend opBinaryRight to return a reference to a free slot when assigned to sets value in slot and does _count += 1;
 *
 * TODO add extractElement that moves it out similar to
 * http://en.cppreference.com/w/cpp/container/unordered_set/extract
 *
 * TODO benchmark against https://github.com/greg7mdp/sparsepp
 *
 * TODO add merge or union algorithm here or into container_algorithm.d. See
 * also: http://en.cppreference.com/w/cpp/container/unordered_set/merge. this
 * algorithm moves elements from source if they are not already in `this`
 *
 * TODO robin hood hashing
 */
struct OpenHashMapOrSet(K, V = void,
                        alias hasher = hashOf,
                        alias Allocator = PureMallocator.instance)
    if (isNullableType!K
        //isHashable!K
        )
{
    import std.algorithm.mutation : move;
    import std.math : nextPow2;
    import std.traits : hasElaborateCopyConstructor, hasElaborateDestructor, isCopyable, isMutable, hasIndirections, Unqual;
    import std.typecons : Nullable;

    import qcmeman : gc_addRange, gc_removeRange;
    import digestion : hashOf2;
    import probing : triangularProbeFromIndex;

    enum removalFlag = true;

    /** In the hash map case, `V` is non-void, and a value is stored alongside
     * the key of type `K`.
     */
    enum hasValue = !is(V == void);

    alias MutableThis = Unqual!(typeof(this));
    alias ConstThis = const(MutableThis);

    static if (isInstanceOf!(Nullable, K))
    {
        alias WrappedKey = Unqual!(typeof(K.get));
    }

    pragma(inline):

    /// Element type.
    static if (hasValue)
    {
        /** Map insertion status.
         */
        enum InsertionStatus
        {
            added,                      // element was added
            modified,                   // value of element was changed (map only). TODO only for Map-case
            unmodified                  // element was left unchanged
        }

        /// Constant element reference with both constant key and value.
        struct T
        {
            K key;
            V value;
        }

        /// Mutable element reference with constant key and mutable value.
        struct CT
        {
            const K key;
            V value;
        }

        /// Get key part of element.
        pragma(inline, true)
        static auto ref inout(K) keyOf()(auto ref return inout(T) element)
        {
            return element.key;
        }

        /// Get value part of element.
        pragma(inline, true)
        static auto ref inout(V) valueOf()(auto ref return inout(T) element)
        {
            return element.value;
        }

        /** Type of key stored. */
        alias KeyType = K;

        /** Type of value stored. */
        alias ValueType = V;

        enum keyEqualPred = "a.key is b";

        enum nullKeyElement = T(defaultNullKeyConstantOf!K, V.init);
    }
    else                        // HashSet
    {
        /** Set insertion status.
         */
        enum InsertionStatus
        {
            added,                      // element was added
            unmodified                  // element was left unchanged
        }


        alias T = K;

        /// Get key part of element.
        pragma(inline, true)
        static auto ref inout(K) keyOf()(auto ref return inout(T) element)
        {
            return element;
        }

        enum keyEqualPred = "a is b";

        enum nullKeyElement = defaultNullKeyConstantOf!K;
    }

    alias ElementType = T;

    /** Make with room for storing at least `capacity` number of elements.
     *
     * See also:
     * https://forum.dlang.org/post/nyngzsaeqxzzuumivtze@forum.dlang.org
     */
    pragma(inline, true)
    static typeof(this) withCapacity(size_t capacity) // template-lazy
    {
        return typeof(return)(makeBins(capacity), 0);
    }

    pragma(inline, true)
    private static T[] makeBins(size_t capacity_) @trusted
    {
        immutable powerOf2Capacity = nextPow2(capacity_);

        import std.traits : isPointer;

        // TODO cannot use makeArray here because it cannot handle uncopyable types
        // import std.experimental.allocator : makeArray;
        // auto bins = Allocator.makeArray!T(powerOf2Capacity, nullKeyElement);

        immutable byteCount = T.sizeof*powerOf2Capacity;

        static if (is(K == class) ||
                   isPointer!K ||
                   (isInstanceOf!(Nullable, K) &&
                    is(Unqual!K == Nullable!(WrappedKey,
                                             WrappedKey.init)))) // init value is always zero bits only
        {
            /* prefer call to calloc before malloc+memset:
             * https://stackoverflow.com/questions/2688466/why-mallocmemset-is-slower-than-calloc */
            static if (__traits(hasMember, Allocator, "zeroallocate"))
            {
                auto bins = cast(T[])Allocator.instance.zeroallocate(byteCount);
            }
            else
            {
                auto bins = cast(T[])Allocator.instance.zeroallocate(byteCount);
                import core.stdc.string : memset;
                memset(bins.ptr, 0, byteCount);
            }
        }
        else
        {
            auto bins = cast(T[])Allocator.instance.allocate(byteCount);
            foreach (ref element; bins)
            {
                nullifyElement(element);
            }
        }

        static if (mustAddGCRange!T)
        {
            gc_addRange(bins.ptr, byteCount);
        }

        return bins;
    }

    private pragma(inline, true)
    void[] allocateUninitializedBins(size_t capacity) const pure nothrow @nogc @system
    {
        immutable byteCount = T.sizeof*capacity;
        auto bins = Allocator.instance.allocate(byteCount);
        static if (mustAddGCRange!T)
        {
            gc_addRange(bins.ptr, byteCount);
        }
        return bins;
    }

    import std.range : StdElementType = ElementType;
    import std.traits : isIterable, isAssignable;

    /** Make with `elements`. */
    static typeof(this) withElements(R)(R elements)
        if (isIterable!R &&
            isAssignable!(T, StdElementType!R))
    {
        import std.range : hasLength;
        static if (hasLength!R)
        {
            typeof(this) that = withCapacity(elements.length);
            foreach (ref element; elements)
            {
                that.insertWithoutGrowth(element);
            }
        }
        else
        {
            typeof(this) that;
            foreach (ref element; elements)
            {
                that.insert(element);
            }
        }
        return that;
    }

    /// Destruct.
    ~this()
    {
        release();
    }

    /// No copying.
    @disable this(this);

    static if (isCopyable!T)
    {
        /// Returns: a shallow duplicate of `this`.
        typeof(this) dup()() const // template-lazy
            @trusted
        {
            T[] binsCopy = cast(T[])allocateUninitializedBins(_bins.length);
            foreach (immutable elementIndex, ref element; _bins)
            {
                /** TODO functionize to `emplaceAll` in emplace_all.d. See also:
                 * http://forum.dlang.org/post/xxigbqqflzwfgycrclyq@forum.dlang.org
                 */
                if (keyOf(element).isNull)
                {
                    binsCopy[elementIndex] = T.init;
                }
                else
                {
                    static if (hasElaborateDestructor!T)
                    {
                        import std.conv : emplace;
                        emplace(&binsCopy[elementIndex], element);
                    }
                    else
                    {
                        binsCopy[elementIndex] = element;
                    }
                }
            }
            static if (removalFlag)
            {
                if (_holesPtr)
                {
                    auto holesPtrCopy = allocateHoles(binBlockBytes(_bins.length));
                    immutable wordCount = holesWordCount(_bins.length);
                    holesPtrCopy[0 .. wordCount] = _holesPtr[0 .. wordCount];
                    return typeof(return)(binsCopy, _count, holesPtrCopy);
                }
            }
            return typeof(return)(binsCopy, _count);
        }
    }

    /// Equality.
    bool opEquals()(const scope auto ref typeof(this) rhs) const
    {
        if (_count != rhs._count) { return false; } // quick discardal
        foreach (immutable ix; 0 .. _bins.length)
        {
            if (!keyOf(_bins[ix]).isNull)
            {
                static if (hasValue)
                {
                    auto hitPtr = _bins[ix].key in rhs;
                    if (!hitPtr) { return false; }
                    if ((*hitPtr) !is _bins[ix].value) { return false; }
                }
                else
                {
                    if (!rhs.contains(_bins[ix])) { return false; }
                }
            }
        }
        return true;
    }

    static if (removalFlag)
    {
    pragma(inline, true):
    private:

        enum wordBytes = size_t.sizeof;
        enum wordBits = 8*wordBytes;

        static size_t* allocateHoles(size_t byteCount) @trusted
        {
            return cast(typeof(return))Allocator.instance.allocate(byteCount);
        }

        static size_t* zeroallocateHoles(size_t byteCount) @trusted
        {
            return cast(typeof(return))Allocator.instance.zeroallocate(byteCount);
        }

        version(none)
        static size_t* reallocateHoles(size_t[] holes, size_t byteCount) @trusted
        {
            auto rawHoles = cast(void[])holes;
            const ok = Allocator.instance.reallocate(rawHoles, byteCount);
            assert(ok, "couldn't reallocate holes");
            return cast(typeof(return))rawHoles.ptr;
        }

        void deallocateHoles() @trusted
        {
            if (_holesPtr)
            {
                Allocator.instance.deallocate(_holesPtr[0 .. holesWordCount(_bins.length)]);
            }
        }

        /** Returns: number of words (`size_t`) needed to represent
         * `_bins.length` holes.
         */
        static size_t holesWordCount(size_t binCount)
        {
            return (binCount / wordBits +
                    (binCount % wordBits ? 1 : 0));
        }

        static size_t binBlockBytes(size_t binCount)
        {
            return wordBytes*holesWordCount(binCount);
        }

        size_t* lazyHolesPtr() @trusted
        {
            if (_holesPtr is null)
            {
                // lazy allocation
                _holesPtr = zeroallocateHoles(binBlockBytes(_bins.length));
            }
            return _holesPtr;
        }

        void setHole(size_t index) @trusted
        {
            assert(index < 8*size_t.max*holesWordCount(_bins.length));
            import core.bitop : bts;
            bts(lazyHolesPtr, index);
        }
    }

    /// Empty.
    void clear()()              // template-lazy
    {
        release();
        _bins = typeof(_bins).init;
        static if (removalFlag)
        {
            _holesPtr = null;
        }
        _count = 0;
    }

    /// Release internal allocations.
    private void release()
    {
        releaseBinElements();
        releaseBinsAndHolesSlices();
    }

    /// Release bin elements.
    private void releaseBinElements()
        @trusted
    {
        foreach (immutable ix; 0 .. _bins.length)
        {
            static if (hasElaborateDestructor!T)
            {
                .destroy(_bins[ix]);
            }
        }
    }

    /// Release bin slice.
    private void releaseBinsAndHolesSlices()
        @trusted
    {
        releaseBinsSlice(_bins);
        static if (removalFlag)
        {
            deallocateHoles();
        }
    }

    static private void releaseBinsSlice(T[] bins)
        @trusted
    {
        static if (mustAddGCRange!T)
        {
            gc_removeRange(bins.ptr);
        }
        Allocator.instance.deallocate(bins);
    }

    version(LDC) { pragma(inline, true): } // needed for LDC to inline this, DMD cannot
    pragma(inline, true):                  // LDC must have this

    /** Check if `element` is stored.
        Returns: `true` if element is present, `false` otherwise.
    */
    pragma(inline, true)
    bool contains()(const scope K key) const // template-lazy, auto ref here makes things slow
    {
        assert(!key.isNull);
        return isOccupiedIndex(tryFindIndexOfKey(key));
    }
    static if (isInstanceOf!(Nullable, K))
    {
        pragma(inline, true)
        bool contains(const scope WrappedKey wrappedKey) const // template-lazy, auto ref here makes things slow
        {
            return contains(K(wrappedKey));
        }
    }

    /** Insert `element`, being either a key-value (map-case) or a just a key (set-case).
     */
    pragma(inline, true)
    InsertionStatus insert(T element)
    {
        assert(!keyOf(element).isNull); // TODO needed?
        reserveExtra(1);
        return insertWithoutGrowth(move(element));
    }
    static if (!hasValue &&
               isInstanceOf!(Nullable, K))
    {
        pragma(inline, true)
        InsertionStatus insert(WrappedKey wrappedElement)
        {
            return insert(K(wrappedElement));
        }
    }

    /** Insert `elements`, all being either a key-value (map-case) or a just a key (set-case).
     */
    void insertN(R)(R elements) @trusted
        if (isIterable!R &&
            isCopyable!T)       // TODO support uncopyable T?
    {
        import std.range : hasLength;
        static if (hasLength!R)
        {
            reserveExtra(elements.length);
        }
        foreach (element; elements)
        {
            static if (hasIndirections!T)
            {
                insertWithoutGrowth(element);
            }
            else
            {
                insertWithoutGrowth(*cast(Unqual!T*)&element);
            }
        }
    }

    /// Is `true` iff in-place rehashing during growth should be performed.
    enum bool doInPlaceGrow = false;

    /// Numerator for grow scale.
    enum growScaleP = 3;
    /// Denominator for grow scale.
    enum growScaleQ = 2;

    /** Reserve rom for `extraCapacity` number of extra buckets. */
    void reserveExtra(size_t extraCapacity) // not template-lazy
    {
        immutable newCapacity = (_count + extraCapacity)*growScaleP/growScaleQ;
        if (newCapacity > _bins.length)
        {
            growWithNewCapacity(newCapacity);
        }
    }

    /// Grow (rehash) to make for `newCapacity` number of elements.
    pragma(inline, true)
    private void growWithNewCapacity(size_t newCapacity) // not template-lazy
    {
        assert(newCapacity > _bins.length);
        static if (__traits(hasMember, PureMallocator, "reallocate"))
        {
            if (doInPlaceGrow)
            {
                growInPlaceWithNewCapacity(newCapacity);
            }
            else
            {
                growStandardWithNewCapacity(newCapacity);
            }
        }
        else
        {
            growStandardWithNewCapacity(newCapacity);
        }
    }

    /** Nullify `element`. */
    static private void nullifyElement(scope ref T element)
    {
        keyOf(element).nullify(); // moveEmplace doesn't init source of type Nullable
        static if (hasValue &&
                   hasElaborateDestructor!V)
        {
            valueOf(element) = V.init;
            // TODO instead do only .destroy(valueOf(_bins[hitIndex])); and emplace values
        }
    }

    /** Rehash elements in-place. */
    private void rehashInPlace()() // template-lazy
        @trusted
    {
        import bitarray : BitArray;
        auto dones = BitArray!().withLength(_bins.length); // TODO use size_t[] and core.bitop instead
        foreach (immutable doneIndex; 0 .. dones.length)
        {
            if (!dones[doneIndex] && // if _bins[doneIndex] not yet ready
                !keyOf(_bins[doneIndex]).isNull) // and non-null
            {
                import std.algorithm.mutation : moveEmplace;

                T currentElement = void;

                // TODO functionize:
                moveEmplace(_bins[doneIndex], currentElement);
                static if (isInstanceOf!(Nullable, K))
                {
                    nullifyElement(_bins[doneIndex]); // `moveEmplace` doesn't init source of type Nullable
                }

                while (true)
                {
                    alias predicate = (index, const auto ref element) => (keyOf(element).isNull || // free slot or
                                                                          !dones[index]); // or a not yet replaced element
                    immutable hitIndex = _bins[].triangularProbeFromIndex!(predicate)(keyToIndex(keyOf(currentElement)));
                    assert(hitIndex != _bins.length, "no free slot");

                    dones[hitIndex] = true; // _bins[hitIndex] will be at it's correct position

                    if (!keyOf(_bins[hitIndex]).isNull()) // if free slot found
                    {
                        T nextElement = void;

                        // TODO functionize:
                        moveEmplace(_bins[hitIndex], nextElement); // save non-free slot
                        static if (isInstanceOf!(Nullable, K))
                        {
                            nullifyElement(_bins[hitIndex]);           // `moveEmplace` doesn't init source of type Nullable
                        }

                        moveEmplace(currentElement, _bins[hitIndex]);
                        moveEmplace(nextElement, currentElement);
                    }
                    else // if no free slot
                    {
                        moveEmplace(currentElement, _bins[hitIndex]);
                        break; // inner iteration is finished
                    }
                }
                dones[doneIndex] = true; // _bins[doneIndex] is at it's correct position
            }
        }
    }

    /** Grow (including rehash) store in-place to make room for `newCapacity` number of
     * elements.
     */
    private void growInPlaceWithNewCapacity(size_t newCapacity) // not template-lazy
        @trusted
    {
        assert(newCapacity > _bins.length);
        immutable powerOf2newCapacity = nextPow2(newCapacity);

        static if (mustAddGCRange!T)
        {
            gc_removeRange(_bins.ptr);
        }

        immutable oldLength = _bins.length;
        auto rawBins = cast(void[])_bins;
        if (Allocator.instance.reallocate(rawBins, T.sizeof*powerOf2newCapacity))
        {
            _bins = cast(T[])rawBins;
            static if (mustAddGCRange!T)
            {
                immutable byteCount = T.sizeof*_bins.length;
                gc_addRange(_bins.ptr, byteCount);
            }
            static if (removalFlag)
            {
                deallocateHoles();
                _holesPtr = allocateHoles(binBlockBytes(_bins.length));
            }

            // TODO make this an array operation `nullifyAll` or `nullifyN`
            foreach (ref bin; _bins[oldLength .. powerOf2newCapacity])
            {
                keyOf(bin).nullify(); // move this `init` to reallocate() above?
            }

            rehashInPlace();
        }
        else
        {
            assert(0, "couldn't reallocate bin");
        }
    }

    /** Grow (rehash) store to make room for `newCapacity` number of elements.
     */
    private void growStandardWithNewCapacity(size_t newCapacity) // not template-lazy
        @trusted
    {
        assert(newCapacity > _bins.length);
        T[] oldBins = _bins;
        debug immutable oldCount = _count;

        _bins = makeBins(newCapacity); // replace with new bins
        static if (removalFlag)
        {
            deallocateHoles();
            _holesPtr = allocateHoles(binBlockBytes(_bins.length));
        }
        _count = 0;

        // move elements to copy
        foreach (ref oldBin; oldBins)
        {
            if (!keyOf(oldBin).isNull)
            {
                insertMoveWithoutGrowth(oldBin);
            }
        }
        debug assert(oldCount == _count);

        releaseBinsSlice(oldBins);

        assert(_bins.length);
    }

    /** Insert `element`, being either a key-value (map-case) or a just a key (set-case).
     */
    pragma(inline, true)
    private InsertionStatus insertWithoutGrowth(T element)
    {
        assert(!keyOf(element).isNull);

        immutable hitIndex = _bins[].triangularProbeFromIndex!((const auto ref _) => (keyOf(_) is keyOf(element) ||
                                                                                      keyOf(_).isNull))(keyToIndex(keyOf(element)));
        assert(hitIndex != _bins.length, "no free slot");

        if (keyOf(_bins[hitIndex]).isNull) // key missing
        {
            move(element,
                 _bins[hitIndex]);
            _count += 1;
            return InsertionStatus.added;
        }
        static if (hasValue)
        {
            if (valueOf(element) !is
                valueOf(_bins[hitIndex])) // only value changed
            {
                move(valueOf(element),
                     valueOf(_bins[hitIndex]));
                return InsertionStatus.modified;
            }
        }
        return InsertionStatus.unmodified;
    }

    /** Insert `element`, being either a key-value (map-case) or a just a key (set-case).
     */
    pragma(inline, true)
    private InsertionStatus insertMoveWithoutGrowth(ref T element)
    {
        return insertWithoutGrowth(move(element));
    }

    static if (hasValue)
    {
        /** Insert or replace `value` at `key`. */
        pragma(inline, true)    // LDC must have this
        InsertionStatus insert(K key, V value)
        {
            return insert(T(move(key),
                            move(value)));
        }
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)    // LDC must have this
            InsertionStatus insert(WrappedKey wrappedKey, V value)
            {
                return insert(K(wrappedKey), move(value));
            }
        }
    }

    /** L-value element reference (and in turn range iterator).
     */
    static private struct LvalueElementRef(SomeOpenHashMapOrSet)
    {
        SomeOpenHashMapOrSet* table;
        size_t iterationIndex;  // index to bin inside `table`
        size_t iterationCounter; // counter over number of elements popped

        pragma(inline, true):

        /// Check if empty.
        @property bool empty() const @safe pure nothrow @nogc
        {
            return iterationIndex == table.binCount;
        }

        /// Get number of element left to pop.
        @property size_t length() const @safe pure nothrow @nogc
        {
            return table.length - iterationCounter;
        }

        pragma(inline)
        void popFront()
        {
            assert(!empty);
            iterationIndex += 1;
            findNextNonEmptyBin();
            iterationCounter += 1;
        }

        @property typeof(this) save() // ForwardRange
        {
            return this;
        }

        private void findNextNonEmptyBin()
        {
            while (iterationIndex != (*table).binCount &&
                   keyOf((*table)._bins[iterationIndex]).isNull)
            {
                iterationIndex += 1;
            }
        }
    }

    /** R-value element reference (and in turn range iterator).
     */
    static private struct RvalueElementRef(SomeOpenHashMapOrSet)
    {
        SomeOpenHashMapOrSet table; // owned
        size_t iterationIndex;  // index to bin inside table
        size_t iterationCounter; // counter over number of elements popped

        pragma(inline, true):

        /// Check if empty.
        @property bool empty() const @safe pure nothrow @nogc
        {
            return iterationIndex == table.binCount;
        }

        /// Get number of element left to pop.
        @property size_t length() const @safe pure nothrow @nogc
        {
            return table.length - iterationCounter;
        }

        pragma(inline)
        void popFront()
        {
            assert(!empty);
            iterationIndex += 1;
            findNextNonEmptyBin();
            iterationCounter += 1;
        }

        private void findNextNonEmptyBin()
        {
            while (iterationIndex != table.binCount &&
                   keyOf(table._bins[iterationIndex]).isNull)
            {
                iterationIndex += 1;
            }
        }
    }

    static if (!hasValue)       // HashSet
    {
        pragma(inline, true)
        scope const(K)* opBinaryRight(string op)(const scope K key) const return
            if (op == "in")
        {
            assert(!key.isNull);
            immutable hitIndex = tryFindIndexOfKey(key);
            return isOccupiedIndex(hitIndex) ? &_bins[hitIndex] : null;
        }
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)    // LDC must have this
            scope const(K)* opBinaryRight(string op)(const scope WrappedKey wrappedKey) const return
                if (op == "in")
            {
                return opBinaryRight!"in"(K(wrappedKey));
            }
        }

        /// Range over elements of l-value instance of this.
        static private struct ByLvalueElement(SomeOpenHashMapOrSet)
        {
        pragma(inline, true):
            static if (is(T == class))
            {
                /// Get reference to front element (key and value).
                @property scope auto front()() return
                {
                    /* cast away const from `SomeOpenHashMapOrSet` for classes
                     * because class elements are currently hashed and compared
                     * compared using their identity (pointer value) `is`
                     */
                    return cast(T)table.binElementsAt(ix)[elementOffset];
                }
            }
            else
            {
                /// Get reference to front element (key and value).
                @property scope auto front()()
                {
                    return table._bins[iterationIndex];
                }
            }
            public LvalueElementRef!SomeOpenHashMapOrSet _elementRef;
            alias _elementRef this;
        }

        /// Range over elements of r-value instance of this.
        static private struct ByRvalueElement(SomeOpenHashMapOrSet)
        {
        pragma(inline, true):
            static if (is(T == class))
            {
                /// Get reference to front element (key and value).
                @property scope auto front()() return
                {
                    /* cast away const from `SomeOpenHashMapOrSet` for classes
                     * because class elements are currently hashed and compared
                     * compared using their identity (pointer value) `is`
                     */
                    return cast(T)table.binElementsAt(iterationIndex)[elementOffset];
                }
            }
            else
            {
                /// Get reference to front element (key and value).
                @property scope auto front()()
                {
                    return table._bins[iterationIndex];
                }
            }
            public RvalueElementRef!SomeOpenHashMapOrSet _elementRef;
            alias _elementRef this;
        }

        /// ditto
        version(none)           // cannot be combined
        {
        pragma(inline, true)
        scope auto opSlice()() inout return // template-lazy
        {
            return byElement();
        }
        }
    }

    static if (hasValue)        // HashMap
    {
        scope inout(V)* opBinaryRight(string op)(const scope K key) inout return // auto ref here makes things slow
            if (op == "in")
        {
            immutable hitIndex = tryFindIndexOfKey(key);
            if (hitIndex != _bins.length)
            {
                return cast(typeof(return))&_bins[hitIndex].value;
            }
            else                    // miss
            {
                return null;    // TODO return reference to where element should be placed
            }
        }
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)    // LDC must have this
            scope inout(V)* opBinaryRight(string op)(const scope WrappedKey wrappedKey) inout return // auto ref here makes things slow
                if (op == "in")
            {
                return opBinaryRight!"in"(K(wrappedKey));
            }
        }

        static private struct ByKey(SomeOpenHashMapOrSet)
        {
            pragma(inline, true):
            /// Get reference to key of front element.
            @property scope const auto ref front()() return // key access must be const
            {
                return table._bins[iterationIndex].key;
            }
            public LvalueElementRef!SomeOpenHashMapOrSet _elementRef;
            alias _elementRef this;
        }

        /// Returns forward range that iterates through the keys of `this` in undefined order.
        @property scope auto byKey()() inout return // template-lazy property
        {
            alias This = ConstThis;
            auto result = ByKey!This((LvalueElementRef!This(cast(This*)&this)));
            result.findNextNonEmptyBin();
            return result;
        }

        static private struct ByValue(SomeOpenHashMapOrSet)
        {
            pragma(inline, true):
            /// Get reference to value of front element.
            @property scope auto ref front()() return @trusted // template-lazy property
            {
                return *(cast(ValueType*)&table._bins[iterationIndex].value);
            }
            public LvalueElementRef!SomeOpenHashMapOrSet _elementRef;
            alias _elementRef this;
        }

        /// Returns forward range that iterates through the values of `this` in undefined order.
        @property scope auto byValue()() inout return // template-lazy property
        {
            alias This = ConstThis;
            auto result = ByValue!This((LvalueElementRef!This(cast(This*)&this)));
            result.findNextNonEmptyBin();
            return result;
        }

        static private struct ByKeyValue(SomeOpenHashMapOrSet)
        {
            pragma(inline, true):
            /// Get reference to front element (key and value).
            @property scope auto ref front()() return @trusted
            {
                static if (isMutable!(SomeOpenHashMapOrSet))
                {
                    alias E = CT;
                }
                else
                {
                    alias E = const(T);
                }
                return *(cast(E*)&table._bins[iterationIndex]);
            }
            public LvalueElementRef!SomeOpenHashMapOrSet _elementRef;
            alias _elementRef this;
        }

        /// Returns forward range that iterates through the keys and values of `this`.
        @property scope auto byKeyValue()() return // template-lazy property
        {
            alias This = MutableThis;
            auto result = ByKeyValue!This((LvalueElementRef!This(cast(This*)&this)));
            result.findNextNonEmptyBin();
            return result;
        }
        /// ditto
        @property scope auto byKeyValue()() const return // template-lazy property
        {
            alias This = ConstThis;
            auto result = ByKeyValue!This((LvalueElementRef!This(cast(This*)&this)));
            result.findNextNonEmptyBin();
            return result;
        }

        /// ditto
        pragma(inline, true)
        scope auto opSlice()() return  // template-lazy
        {
            return byKeyValue();
        }

        /// Indexing.
        pragma(inline, true)    // LDC must have this
        scope ref inout(V) opIndex()(const scope K key) inout return // auto ref here makes things slow
        {
            immutable hitIndex = tryFindIndexOfKey(key);
            if (hitIndex != _bins.length)
            {
                return _bins[hitIndex].value;
            }
            else
            {
                import core.exception : RangeError;
                throw new RangeError("Key not in table");
            }
        }
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)    // LDC must have this
            scope ref inout(V) opIndex()(const scope WrappedKey wrappedKey) inout return // auto ref here makes things slow
            {
                return opIndex(K(wrappedKey));
            }
        }

        /** Get value of `key` or `defaultValue` if `key` not present (and
         * therefore `nothrow`).
         *
         * Returns: value reference iff `defaultValue` is an l-value.
         *
         * TODO make `defaultValue` `lazy` when that can be `nothrow`
         */
        auto ref V get()(const scope K key, // template-lazy
                         const scope V defaultValue)
        {
            auto value = key in this;
            if (value !is null)
            {
                return *value;
            }
            else
            {
                return defaultValue;
            }
        }
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)
            auto ref V get()(const scope WrappedKey wrappedKey, // template-lazy
                             const scope V defaultValue)
            {
                return get(K(wrappedKey),
                           defaultValue);
            }
        }

	/** Supports $(B aa[key] = value;) syntax.
	 */
        pragma(inline, true)
        void opIndexAssign()(V value, K key) // template-lazy
	{
            insert(T(move(key),
                     move(value)));
            // TODO return reference to value
	}
        static if (isInstanceOf!(Nullable, K))
        {
            pragma(inline, true)
            void opIndexAssign()(V value, WrappedKey wrappedKey) // template-lazy
            {
                insert(T(K(move(wrappedKey)),
                         move(value)));
                // TODO return reference to value
            }
        }
    }

    static if (removalFlag)
    {
        /** Remove `element`.
            Returns: `true` if element was removed, `false` otherwise.
        */
        bool remove()(const scope K key) // template-lazy
        {
            immutable hitIndex = tryFindIndexOfKey(key);
            if (hitIndex != _bins.length) // if hit
            {
                nullifyElement(_bins[hitIndex]);
                static if (removalFlag)
                {
                    setHole(hitIndex);
                }
                _count -= 1;
                return true;
            }
            return false;
        }
        static if (isInstanceOf!(Nullable, K))
        {
            bool remove()(const scope WrappedKey wrappedKey) // template-lazy
            {
                return remove(K(wrappedKey));
            }
        }
    }

    import traits_ex : isRefIterable;
    import std.range : front;

    /** Remove all elements matching `keys` followed by a rehash.
        Returns: `true` if element was removed, `false` otherwise.
    */
    bool rehashingRemoveN(Keys)(const scope Keys keys) // template-lazy
        if (isRefIterable!Keys &&
            is(typeof(Keys.front == K.init)))
    {
        rehash!("!a.isNull && keys.canFind(a)")(); // TODO make this work
    }

    /// Check if empty.
    pragma(inline, true)
    @property bool empty() const { return _count == 0; }

    /// Get length (read-only).
    pragma(inline, true)
    @property size_t length() const { return _count; }

    /// Get bin count.
    pragma(inline, true)
    @property size_t binCount() const { return _bins.length; }

private:
    T[] _bins;            // bin elements
    size_t _count;        // total number of non-null elements stored in `_bins`
    static if (removalFlag)
    {
        size_t* _holesPtr; // bit array describing which bin elements that has been removed (holes)
    }

    /** Returns: bin index of `key`. */
    pragma(inline, true)
    private size_t keyToIndex(const scope K key) const
    {
        return hashOf2!(hasher)(key) & powerOf2Mask;
    }

    /** Returns: current index mask from bin count. */
    pragma(inline, true)
    private size_t powerOf2Mask() const
    {
        immutable typeof(return) mask = _bins.length - 1;
        assert((~mask ^ mask) == typeof(mask).max); // isPowerOf2(_bins.length)
        return mask;
    }

    pragma(inline, true)
    private size_t tryFindIndexOfKey(const scope K key) const
    {
        static if (removalFlag)
        {
            // may contain holes
            alias predicate = (const auto ref element) => keyOf(element) is key;
        }
        else
        {
            // cannot contain holes
            static if (isCopyable!T)
            {
                /* don't use `auto ref` for copyable `T`'s to prevent
                 * massive performance drop for small elements when compiled
                 * with LDC. TODO remove when LDC is fixed. */
                alias predicate = (element) => (keyOf(element) is key ||
                                                keyOf(element).isNull);
            }
            else
            {
                alias predicate = (const auto ref element) => (keyOf(element) is key ||
                                                               keyOf(element).isNull);
            }
        }
        return _bins[].triangularProbeFromIndex!(predicate)(keyToIndex(key));
    }

    /** Returns: `true` iff `index` indexes a non-null element. */
    pragma(inline, true)
    private bool isOccupiedIndex(size_t index) const
    {
        return (index != _bins.length &&
                !keyOf(_bins[index]).isNull);
    }

    /** Returns: `true` iff `index` indexes a vacant (either null or deleted) element. */
    pragma(inline, true)
    private bool isVacantIndex(size_t index) const
    {
        return (index != _bins.length &&
                (keyOf(_bins[index]).isNull)); // TODO check for holes
    }
}

/** Immutable hash set storing keys of type `K`.
 */
alias OpenHashSet(K, alias hasher = hashOf,
                  alias Allocator = PureMallocator.instance) = OpenHashMapOrSet!(K, void, hasher, Allocator);

/** Immutable hash map storing keys of type `K` and values of type `V`.
 */
alias OpenHashMap(K, V, alias hasher = hashOf,
                  alias Allocator = PureMallocator.instance) = OpenHashMapOrSet!(K, V, hasher, Allocator);

import std.traits : isInstanceOf;

/** Remove (reset) all elements in `x` matching `predicate`.
 */
void removeAllMatching(alias predicate, SomeOpenHashMapOrSet)(auto ref SomeOpenHashMapOrSet x)
    if (isInstanceOf!(OpenHashMapOrSet,
                      SomeOpenHashMapOrSet))
{
    size_t count = 0;
    alias E = typeof(SomeOpenHashMapOrSet._bins.init[0]);
    foreach (immutable i; 0 .. x._bins.length)
    {
        import std.functional : unaryFun;
        if (!x._bins[i].isNull &&
            unaryFun!predicate(x._bins[i]))
        {
            count += 1;
            x._bins[i].nullify();
        }
    }
    x._count -= count;
}

/** Returns: `x` eagerly filtered on `predicate`.
    TODO move to container_algorithm.d.
*/
SomeOpenHashMapOrSet filtered(alias predicate, SomeOpenHashMapOrSet)(SomeOpenHashMapOrSet x)
    if (isInstanceOf!(OpenHashMapOrSet,
                      SomeOpenHashMapOrSet))
{
    import std.functional : not;
    x.removeAllMatching!(not!predicate); // `x` is a singleton (r-value) so safe to mutate
    import std.algorithm.mutation : move;
    return move(x);             // functional
}

/** Returns: `x` eagerly intersected with `y`.
    TODO move to container_algorithm.d.
 */
auto intersectedWith(C1, C2)(C1 x, auto ref C2 y)
    if (isInstanceOf!(OpenHashMapOrSet, C1) &&
        isInstanceOf!(OpenHashMapOrSet, C2))
{
    import std.algorithm.mutation : move;
    static if (__traits(isRef, y)) // y is l-value
    {
        // @("complexity", "O(x.length)")
        return move(x).filtered!(_ => y.contains(_)); // only x can be reused
    }
    else
    {
        /* both are r-values so reuse the shortest */
        // @("complexity", "O(min(x.length), min(y.length))")
        if (x.length <
            y.length)
        {
            return move(x).filtered!(_ => y.contains(_)); // functional
        }
        else
        {
            return move(y).filtered!(_ => x.contains(_)); // functional
        }
    }
}

/// r-value and l-value intersection
@safe pure nothrow @nogc unittest
{
    alias K = Nullable!(uint, uint.max);
    alias X = OpenHashMapOrSet!(K, void, FNV!(64, true));

    auto x0 = X.init;
    assert(x0.length == 0);
    assert(x0._bins.length == 0);
    assert(!x0.contains(K(1)));

    auto x1 = X.withElements([K(12)].s);
    assert(x1.length == 1);
    assert(x1.contains(12));
    assert(x1.contains(K(12)));

    auto x2 = X.withElements([K(10), K(12)].s);
    assert(x2.length == 2);
    assert(x2.contains(K(10)));
    assert(x2.contains(K(12)));

    auto x3 = X.withElements([K(12), K(13), K(14)].s);
    assert(x3.length == 3);
    assert(x3.contains(K(12)));
    assert(x3.contains(K(13)));
    assert(x3.contains(K(14)));

    auto z = X.withElements([K(10), K(12), K(13), K(15)].s);
    assert(z.length == 4);
    assert(z.contains(K(10)));
    assert(z.contains(K(12)));
    assert(z.contains(K(13)));
    assert(z.contains(K(15)));

    import std.algorithm.mutation : move;
    auto y = move(z).intersectedWith(x2);
    assert(y.length == 2);
    assert(y.contains(K(10)));
    assert(y.contains(K(12)));
}

/// r-value and r-value intersection
@safe pure nothrow @nogc unittest
{
    alias K = Nullable!(uint, uint.max);
    alias X = OpenHashMapOrSet!(K, void, FNV!(64, true));

    auto y = X.withElements([K(10), K(12), K(13), K(15)].s).intersectedWith(X.withElements([K(12), K(13)].s));
    assert(y.length == 2);
    assert(y.contains(K(12)));
    assert(y.contains(K(13)));
}

/** Returns: `x` eagerly intersected with `y`.
    TODO move to container_algorithm.d.
 */
auto intersectWith(C1, C2)(ref C1 x,
                           auto ref const(C2) y)
    if (isInstanceOf!(OpenHashMapOrSet, C1) &&
        isInstanceOf!(OpenHashMapOrSet, C2))
{
    return x.removeAllMatching!(_ => !y.contains(_));
}

/// r-value and l-value intersection
@safe pure nothrow @nogc unittest
{
    alias K = Nullable!(uint, uint.max);
    alias X = OpenHashMapOrSet!(K, void, FNV!(64, true));

    auto x = X.withElements([K(12), K(13)].s);
    auto y = X.withElements([K(10), K(12), K(13), K(15)].s);
    y.intersectWith(x);
    assert(y.length == 2);
    assert(y.contains(K(12)));
    assert(y.contains(K(13)));
}

/** Returns forward range that iterates through the elements of `c` in undefined
 * order.
 */
auto byElement(SomeOpenHashMapOrSet)(auto ref inout(SomeOpenHashMapOrSet) c)
    @trusted
    if (isInstanceOf!(OpenHashMapOrSet,
                      SomeOpenHashMapOrSet))
{
    alias C = const(SomeOpenHashMapOrSet);
    static if (__traits(isRef, c))
    {
        auto result = C.ByLvalueElement!C((C.LvalueElementRef!C(cast(C*)&c)));
        result.findNextNonEmptyBin();
        return result;
    }
    else
    {
        import std.algorithm.mutation : move;
        auto result = C.ByRvalueElement!C((C.RvalueElementRef!C(move(*(cast(SomeOpenHashMapOrSet*)&c))))); // reinterpret
        result.findNextNonEmptyBin();
        return move(result);
    }
}
alias range = byElement;        // EMSI-container naming

/// make range from l-value and r-value. element access is always const
pure nothrow @nogc unittest
{
    alias K = Nullable!(uint, uint.max);
    alias X = OpenHashMapOrSet!(K, void, FNV!(64, true));

    immutable a = [K(11), K(22), K(33)].s;

    // mutable
    auto x = X.withElements(a);
    assert(x.length == 3);
    assert(x.byElement.count == x.length);
    foreach (e; x.byElement)    // from l-value
    {
        assert(x.contains(e));
        static assert(is(typeof(e) == const(K))); // always const access
    }

    // const
    const y = X.withElements(a);
    foreach (e; y.byElement)    // from l-value
    {
        assert(y.contains(e));
        static assert(is(typeof(e) == const(K)));
    }

    foreach (e; X.withElements([K(11)].s).byElement) // from r-value
    {
        assert(e == K(11));
        static assert(is(typeof(e) == const(K))); // always const access
    }
}

/// test various things
@trusted pure nothrow @nogc unittest
{
    immutable uint n = 600;

    alias K = Nullable!(uint, uint.max);

    import std.meta : AliasSeq;
    foreach (V; AliasSeq!(void, string))
    {
        alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));

        static if (!X.hasValue)
        {
            auto x = X.withElements([K(11), K(12), K(13)].s);

            import std.algorithm : count;
            auto xr = x.byElement;

            alias R = typeof(xr);
            import std.range : isInputRange;
            import std.traits : ReturnType;
            static assert(is(typeof(R.init) == R));
            static assert(is(ReturnType!((R xr) => xr.empty) == bool));
            auto f = xr.front;
            static assert(is(typeof((R xr) => xr.front)));
            static assert(!is(ReturnType!((R xr) => xr.front) == void));
            static assert(is(typeof((R xr) => xr.popFront)));

            static assert(isInputRange!(typeof(xr)));

            assert(x.byElement.count == 3);

            X y;
            foreach (const ref e; x.byElement)
            {
                assert(x.contains(e));
                assert(!y.contains(e));
                y.insert(e);
                assert(y.contains(e));
            }

            assert(y.byElement.count == 3);
            assert(x == y);

            const z = X();
            assert(z.byElement.count == 0);

            immutable w = X();
            assert(w.byElement.count == 0);

            {
                auto xc = X.withElements([K(11), K(12), K(13)].s);
                assert(xc.length == 3);
                assert(xc.contains(K(11)));

                // TODO http://forum.dlang.org/post/kvwrktmameivubnaifdx@forum.dlang.org
                xc.removeAllMatching!(_ => _ == K(11));

                assert(xc.length == 2);
                assert(!xc.contains(K(11)));

                xc.removeAllMatching!(_ => _ == 12);
                assert(!xc.contains(K(12)));
                assert(xc.length == 1);

                xc.removeAllMatching!(_ => _ == 13);
                assert(!xc.contains(K(13)));
                assert(xc.length == 0);

                // this is ok
                foreach (e; xc.byElement) {}

            }

            {
                auto k = X.withElements([K(11), K(12)].s).filtered!(_ => _ != K(11)).byElement;
                static assert(isInputRange!(typeof(k)));
                assert(k.front == 12);
                k.popFront();
                assert(k.empty);
            }

            {
                X q;
                auto qv = [K(11U), K(12U), K(13U), K(14U)].s;
                q.insertN(qv[]);
                foreach (e; qv[])
                {
                    assert(q.contains(e));
                }
                q.clear();
                assert(q.empty);
            }
        }

        import container_traits : mustAddGCRange;
        static if (X.hasValue &&
                   is(V == string))
        {
            static assert(mustAddGCRange!V);
            static assert(mustAddGCRange!(V[1]));
            static assert(mustAddGCRange!(X.T));
        }
        else
        {
            static assert(!mustAddGCRange!(X.T));
        }

        auto x1 = X();            // start empty

        // fill x1

        foreach (immutable key_; 0 .. n)
        {
            const key = K(key_);

            static if (X.hasValue)
            {
                const value = V.init;
                const element = X.ElementType(key, value);
            }
            else
            {
                // no assignment because Nullable.opAssign may leave rhs in null state
                alias element = key;
            }

            assert(key !in x1);

            assert(x1.length == key);
            assert(x1.insert(element) == X.InsertionStatus.added);
            assert(x1.length == key + 1);

            static if (X.hasValue)
            {
                const e2 = X.ElementType(key, "a");
                assert(x1.insert(e2) == X.InsertionStatus.modified);
                assert(x1.contains(key));
                assert(x1.get(key, null) == "a");
                x1.remove(key);
                x1[key] = value;
            }

            assert(x1.length == key + 1);

            const hitPtr = key in x1;
            static if (X.hasValue)
            {
                assert(hitPtr && *hitPtr != "_");
            }
            else
            {
                assert(hitPtr && *hitPtr == key);
            }

            assert(x1.insert(element) == X.InsertionStatus.unmodified);
            static if (X.hasValue)
            {
                assert(x1.insert(key, value) == X.InsertionStatus.unmodified);
            }
            assert(x1.length == key + 1);

            assert(key in x1);
        }

        static if (X.hasValue)
        {
            import basic_array : Array = BasicArray;
            Array!(X.ElementType) a1;

            foreach (const ref key; x1.byKey)
            {
                auto keyPtr = key in x1;
                assert(keyPtr);
                a1 ~= X.ElementType(key, (*keyPtr));
            }

            assert(x1.length == a1.length);

            foreach (aElement; a1[])
            {
                auto keyPtr = aElement.key in x1;
                assert(keyPtr);
                assert((*keyPtr) is aElement.value);
            }
        }

        assert(x1.length == n);

        // duplicate x1

        auto x2 = x1.dup;

        // non-symmetric algorithm so both are needed
        assert(x2 == x1);
        assert(x1 == x2);

        static if (X.hasValue)
        {
            assert(equal(x1.byKey, x2.byKey));
            assert(equal(x1.byValue, x2.byValue));
            assert(equal(x1.byKeyValue, x2.byKeyValue));
            assert(equal(x1[], x2[]));
        }

        static assert(!__traits(compiles, { const _ = x1 < x2; })); // no ordering

        assert(x2.length == n);

        // empty x1

        foreach (immutable key_; 0 .. n)
        {
            const key = K(key_);

            static if (X.hasValue)
            {
                const element = X.ElementType(key, V.init);
            }
            else
            {
                alias element = key;
            }

            assert(x1.length == n - key);

            const hitPtr = key in x1;
            static if (X.hasValue)
            {
                assert(hitPtr && *hitPtr is element.value);
            }
            else
            {
                assert(hitPtr && *hitPtr is element);
            }

            assert(x1.remove(key));
            assert(x1.length == n - key - 1);

            static if (!X.hasValue)
            {
                assert(!x1.contains(key));
            }
            assert(key !in x1);
            assert(!x1.remove(key));
            assert(x1.length == n - key - 1);
        }

        assert(x1.length == 0);

        x1.clear();
        assert(x1.length == 0);

        // empty x2

        assert(x2.length == n); // should be not affected by emptying of x1

        foreach (immutable key_; 0 .. n)
        {
            const key = K(key_);

            static if (X.hasValue)
            {
                const element = X.ElementType(key, V.init);
            }
            else
            {
                const element = key;
            }

            assert(x2.length == n - key);

            assert(key in x2);

            assert(x2.remove(key));
            assert(x2.length == n - key - 1);

            assert(key !in x2);
            assert(!x2.remove(key));
            assert(x2.length == n - key - 1);
        }

        assert(x2.length == 0);

        x2.clear();
        assert(x2.length == 0);
    }
}

/// range checking
@trusted pure unittest
{
    immutable n = 11;

    alias K = Nullable!(uint, uint.max);
    alias V = uint;

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));

    auto s = X.withCapacity(n);

    void dummy(ref V value) {}

    assertThrown!RangeError(dummy(s[K(0)]));

    foreach (immutable uint i; 0 .. n)
    {
        const k = K(i);
        s[k] = V(i);
        assertNotThrown!RangeError(dummy(s[k]));
    }

    foreach (immutable uint i; 0 .. n)
    {
        const k = K(i);
        s.remove(k);
        assertThrown!RangeError(dummy(s[k]));
    }

    s[K(0)] = V.init;
    auto vp = K(0) in s;
    static assert(is(typeof(vp) == V*));
    assert((*vp) == V.init);

    s.remove(K(0));
    assert(K(0) !in s);

    X t;
    t.reserveExtra(4096);

    t.clear();
}

/// class as value
@trusted pure unittest
{
    immutable n = 11;

    alias K = Nullable!(uint, uint.max);
    class V
    {
        this(uint data) { this.data = data; }
        uint data;
    }

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));

    auto s = X.withCapacity(n);

    void dummy(ref V value) {}

    assertThrown!RangeError(dummy(s[K(0)]));

    foreach (immutable uint i; 0 .. n)
    {
        const k = K(i);
        s[k] = new V(i);
        assertNotThrown!RangeError(dummy(s[k]));
    }

    // test range
    auto sr = s.byKeyValue;
    assert(sr.length == n);
    foreach (immutable uint i; 0 .. n)
    {
        sr.popFront();
        assert(sr.length == n - i - 1);
    }

    foreach (immutable uint i; 0 .. n)
    {
        const k = K(i);
        s.remove(k);
        assertThrown!RangeError(dummy(s[k]));
    }

    s[K(0)] = V.init;
    auto vp = K(0) in s;
    static assert(is(typeof(vp) == V*));

    s.remove(K(0));
    assert(K(0) !in s);

    X t;
    t.reserveExtra(4096);
}

/// constness inference of ranges
pure nothrow unittest
{
    alias K = Nullable!(uint, uint.max);
    class V
    {
        this(uint data) { this.data = data; }
        uint data;
    }

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));
    const x = X();

    foreach (e; x.byKey)
    {
        static assert(is(typeof(e) == const(X.KeyType)));
    }

    foreach (e; x.byValue)
    {
        static assert(is(typeof(e) == X.ValueType)); // TODO should be const(X.ValueType)
    }

    foreach (e; x.byKeyValue)
    {
        static assert(is(typeof(e.key) == const(X.KeyType)));
        static assert(is(typeof(e.value) == const(X.ValueType)));
        static assert(is(typeof(e) == const(X.ElementType)));
    }
}

/// range key constness and value mutability with `class` value
pure nothrow unittest
{
    struct S
    {
        uint value;
    }
    alias K = Nullable!(S, S(uint.max));

    class V
    {
        this(uint data) { this.data = data; }
        uint data;
    }

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));
    auto x = X();

    x[K(S(42))] = new V(43);

    assert(x.length == 1);

    foreach (e; x.byValue)      // `e` is auto ref
    {
        static assert(is(typeof(e) == X.ValueType)); // mutable access to value
        assert(e.data == 43);

        // value mutation side effects
        e.data += 1;
        assert(e.data == 44);
        e.data -= 1;
        assert(e.data == 43);
    }

    foreach (ref e; x.byKeyValue)   // `e` is auto ref
    {
        static assert(is(typeof(e.key) == const(X.KeyType))); // const access to key
        static assert(is(typeof(e.value) == X.ValueType)); // mutable access to value

        assert(e.key.value == 42);

        assert(e.value.data == 43);

        // value mutation side effects
        e.value.data += 1;
        assert(e.value.data == 44);
        e.value.data -= 1;
        assert(e.value.data == 43);
    }
}

/// range key constness and value mutability with `class` key and `class` value
pure nothrow unittest
{
    class K
    {
        this(uint value)
        {
            this.value = value;
        }
        uint value;
    }

    class V
    {
        this(uint data) { this.data = data; }
        uint data;
    }

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));
    auto x = X();

    x[new K(42)] = new V(43);

    assert(x.length == 1);

    foreach (e; x.byValue)      // `e` is auto ref
    {
        static assert(is(typeof(e) == X.ValueType)); // mutable access to value
        assert(e.data == 43);

        // value mutation side effects
        e.data += 1;
        assert(e.data == 44);
        e.data -= 1;
        assert(e.data == 43);
    }

    foreach (ref e; x.byKeyValue)   // `e` is auto ref
    {
        static assert(is(typeof(e.key) == const(X.KeyType))); // const access to key
        static assert(is(typeof(e.value) == X.ValueType)); // mutable access to value

        assert(e.key.value == 42);
        assert(e.value.data == 43);

        // value mutation side effects
        e.value.data += 1;
        assert(e.value.data == 44);
        e.value.data -= 1;
        assert(e.value.data == 43);
    }
}

/// range key constness and value mutability with `class` key and `class` value
pure nothrow unittest
{
    class K
    {
        this(uint value)
        {
            this.value = value;
        }
        uint value;
    }

    struct V
    {
        this(uint data) { this.data = data; }
        @disable this(this);
        uint data;
    }

    alias X = OpenHashMapOrSet!(K, V, FNV!(64, true));
    auto x = X();

    x[new K(42)] = V(43);

    assert(x.length == 1);

    foreach (ref e; x.byValue)  // `e` is auto ref
    {
        static assert(is(typeof(e) == X.ValueType)); // mutable access to value
        assert(e.data == 43);

        // value mutation side effects
        e.data += 1;
        assert(e.data == 44);
        e.data -= 1;
        assert(e.data == 43);
    }

    foreach (ref e; x.byKeyValue) // `e` is auto ref
    {
        static assert(is(typeof(e.key) == const(X.KeyType))); // const access to key
        static assert(is(typeof(e.value) == X.ValueType)); // mutable access to value

        assert(e.key.value == 42);
        assert(e.value.data == 43);

        // value mutation side effects
        e.value.data += 1;
        assert(e.value.data == 44);
        e.value.data -= 1;
        assert(e.value.data == 43);
    }
}

version(unittest)
{
    import std.exception : assertThrown, assertNotThrown;
    import core.exception : RangeError;
    import std.algorithm : count;
    import std.algorithm.comparison : equal;
    import std.typecons : Nullable;
    import digestx.fnv : FNV;
    import array_help : s;
}
