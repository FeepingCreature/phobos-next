module hashset;

import std.traits : isIntegral, isUnsigned;

/** Hash set storing elements of type `T`.

    Uses small-size-optimized (SSO) arrays as buckets.
 */
struct HashSet(T,
               alias Allocator = null,
               alias hashFunction = xxhash64Of)
{
    /** Construct with room for storing `capacity` number of elements.
     */
    static typeof(this) withCapacity(size_t capacity)
    {
        typeof(return) that;
        that.initialize(capacity / smallBucketLength);
        return that;
    }

    /** Initialize at least `minimumBucketCount` number of initial buckets.
     */
    private void initialize(size_t minimumBucketCount)
    {
        import std.math : nextPow2;
        // make bucket count a power of two
        immutable bucketCount = nextPow2(minimumBucketCount == 0 ? 0 : minimumBucketCount - 1);
        // so we can use fast bitmask instead of slower division remainder
        hashMask = bucketCount - 1;
        initializeBuckets(bucketCount);
    }

    /** Initialize `bucketCount` number of buckets.
     */
    private void initializeBuckets(size_t bucketCount) @trusted // TODO remove @trusted
    {
        _buckets = Buckets.withLength(bucketCount);
        _largeBucketFlags = LargeBucketFlags.withLength(bucketCount);
    }

    /// Destruct.
    ~this()
    {
        release();
    }

    /// Empty.
    void clear() @safe nothrow
    {
        release();
        resetInternalData();
    }

    /// Release internal store.
    private void release() @trusted
    {
        foreach (const bucketIndex; 0 .. _buckets.length)
        {
            if (_largeBucketFlags[bucketIndex])
            {
                .destroy(_buckets[bucketIndex].large);
            }
            else
            {
                .destroy(_buckets[bucketIndex].small);
            }
        }
    }

    /// Reset internal data.
    private void resetInternalData()
    {
        assert(false, "TODO");
    }

    /** Insert `value`.
        Returns: `true` if value was already present, `false` otherwise. This is
        similar to behaviour of `contains`.
     */
    bool insert(T value) @trusted
    {
        import std.conv : emplace;
        import std.algorithm.searching : canFind;
        immutable bucketIndex = bucketHashIndex(value);
        if (_largeBucketFlags[bucketIndex])
        {
            if (!_buckets[bucketIndex].large[].canFind(value))
            {
                _buckets[bucketIndex].large.insertBackMove(value);
                return false;
            }
        }
        else
        {
            if (!_buckets[bucketIndex].small[].canFind(value))
            {
                const ok = _buckets[bucketIndex].small.insertBackMaybe(value);
                if (!ok)        // if full
                {
                    // expand small to large
                    SmallBucket smallCopy = _buckets[bucketIndex].small;
                    emplace!(LargeBucket)(&_buckets[bucketIndex].large, smallCopy[]);
                    _buckets[bucketIndex].large.insertBackMove(value);
                    _largeBucketFlags[bucketIndex] = true; // bucket is now large
                }
                return false;
            }
        }
        return true;
    }

    /** Check if `value` is stored.
        Returns: `true` if value was already present, `false` otherwise.
     */
    bool contains(in T value) const @trusted
    {
        import std.algorithm.searching : canFind;
        immutable bucketIndex = bucketHashIndex(value);
        if (_largeBucketFlags[bucketIndex])
        {
            return _buckets[bucketIndex].large[].canFind(value);
        }
        else
        {
            return _buckets[bucketIndex].small[].canFind(value);
        }
    }

    /** Remove `value`.
        Returns: `true` if values was removed, `false` otherwise.
     */
    bool remove(in T value)
    {
        import std.algorithm.searching : find;
        immutable bucketIndex = bucketHashIndex(value);
        assert(0, "TODO Implement removeAtIndex in Array and use _buckets[bucketIndex].removeAtIndex() here");
        assert(0, "TODO Check shrinkage to SmallBucket");
    }

    /** Get index into `bucket` for `value`.
     */
    pragma(inline, true)
    size_t bucketHashIndex(in T value) const
    {
        return hashFunction(value) & hashMask; // fast modulo calculation
    }

private:
    import basic_uncopyable_array : Array = UncopyableArray; // TODO change to CopyableArray when
    import basic_bitarray : BitArray;

    alias LargeBucket = Array!(T, Allocator);

    import std.algorithm : max;
    enum smallBucketLength = max(1, // at least one element in small bucket
                                 (LargeBucket.sizeof - 1) / T.sizeof);

    import arrayn : ArrayN;
    alias SmallBucket = ArrayN!(T, smallBucketLength);

    /** Small-size-optimized bucket. */
    union HybridBucket
    {
        SmallBucket small;
        LargeBucket large;
    }

    alias Buckets = Array!(HybridBucket, Allocator);
    alias LargeBucketFlags = BitArray!(Allocator);

    Buckets _buckets;

    // TODO this store currently wastes 1 or 2 words as _bucket already contain
    // same _length and _store. Use MultiArray!(HybridBucket, bool) container to
    // store this.
    LargeBucketFlags _largeBucketFlags;

    size_t hashMask;
}

@safe pure nothrow unittest
{
    const elementCount = 2^^10;
    alias T = uint;
    auto s = HashSet!(T, null, /*identityHashOf*/).withCapacity(elementCount);
    foreach (const i; 0 .. elementCount)
    {
        assert(!s.contains(i));
        assert(!s.insert(i));
        assert(s.contains(i));
        assert(s.insert(i));
        assert(s.contains(i));
    }
}

/** Dummy-hash for benchmarking performance of HashSet. */
pragma(inline, true)
ulong identityHashOf(T)(in T value)
    if (isUnsigned!T &&
        T.sizeof <= size_t.sizeof)
{
    return value;
}

/** xxHash64-variant of `core.internal.hash.hashOf`.
 */
pragma(inline, true)
ulong xxhash64Of(T)(in T value) @trusted // TODO make variadic
    if (isIntegral!T)
{
    import xxhash64 : xxhash64Of;
    return xxhash64Of((cast(const(ubyte)*)(&value))[0 .. value.sizeof]);
}

/** MurmurHash3-variant of `core.internal.hash.hashOf`.
 */
ulong murmurHash3Of(T)(in T value) @trusted // TODO make variadic
    if (isIntegral!T)                       // TODO exnd
{
    import std.digest.digest : makeDigest;
    import std.digest.murmurhash : MurmurHash3;
    auto dig = makeDigest!(MurmurHash3!(128));
    dig.put((cast(const(ubyte)*)(&value))[0 .. value.sizeof]);
    dig.finish();
    const elements = dig.get();
    return elements[0] ^ elements[1];
}

/** fnv64-variant of `core.internal.hash.hashOf`.
 */
pragma(inline, true)
ulong fnv64aOf(T)(in T value) @trusted // TODO make variadic
    if (isIntegral!T)                  // TODO extend
{
    import digestx.fnv : fnv64aOf;
    typeof(return) result;
    cast(ubyte*)&result[0 .. result.sizeof] = fnv64aOf((cast(const(ubyte)*)(&value))[0 .. value.sizeof]);
    return result;
}

/** See also: http://forum.dlang.org/post/o1igoc$21ma$1@digitalmars.com

    Doesn't work: integers are returned as is.
 */
pragma(inline, true)
size_t typeidHashOf(T)(in T value) @trusted
{
    return typeid(T).getHash(&value);
}

// version = show;

version(show)
@safe nothrow /*pure @nogc*/ unittest
{
    const elementCount = 2^^10;
    foreach (const i; 0 .. elementCount)
    {
        dln(typeidHashOf(i));   // doesn't work just prints 0, 1, 2, ...
    }
}

version(unittest)
{
    import array_help : s;
}

version(show)
{
    import dbgio : dln;
}
