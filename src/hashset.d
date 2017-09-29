module hashset;

/** Hash set storing elements of type `T`.

    TODO add union storage for small arrays together with smallArrayFlags BitArray
 */
struct HashSet(T,
               alias Allocator = null,
               alias hashFunction = murmurHash3Of!T)
{
    import basic_uncopyable_array : Array = UncopyableArray; // TODO change to CopyableArray when

    /** Construct with at least `requestedBucketCount` number of initial buckets.
     */
    pragma(inline, true)
    this(size_t requestedBucketCount)
    {
        initialize(requestedBucketCount);
    }

    /** Initialize at least `requestedBucketCount` number of initial buckets.
     */
    pragma(inline)
    private void initialize(size_t requestedBucketCount)
    {
        import std.math : nextPow2;
        immutable bucketCount = nextPow2(requestedBucketCount == 0 ? 0 : requestedBucketCount - 1);
        hashMask = bucketCount - 1;
        initializeBuckets(bucketCount);
    }

    /** Initialize `bucketCount` number of buckets.
     */
    pragma(inline, true)
    private void initializeBuckets(size_t bucketCount) @trusted // TODO remove @trusted
    {
        _buckets = Buckets.withLength(bucketCount);
    }

    /** Insert `value`.
        Returns: `true` if value was already present, `false` otherwise. This is
        similar to behaviour of `contains`.
     */
    bool insert(T value)
    {
        import std.algorithm.searching : canFind;
        immutable bucketIndex = hashFunction(value) & hashMask;
        if (!_buckets[bucketIndex][].canFind(value))
        {
            _buckets[bucketIndex].insertBackMove(value);
            return false;
        }
        return true;
    }

    /** Remove `value`.
        Returns: `true` if values was removed, `false` otherwise.
     */
    bool remove(U)(in U value)
        if (is(typeof(T.init == U.init)))
    {
        import std.algorithm.searching : find;
        immutable bucketIndex = hashFunction(value) & hashMask;
        static assert(0, "TODO Implement removeAtIndex in Array and use _buckets[bucketIndex].removeAtIndex() here");
    }

private:
    alias Bucket = Array!(T, Allocator);
    alias Buckets = Array!(Bucket, Allocator);

    Buckets _buckets;
    size_t hashMask;
}

private size_t murmurHash3Of(T)(in T value)
{
    import std.digest : digest;
    import std.digest.murmurhash : MurmurHash3;
    immutable ubyte[16] hash = digest!(MurmurHash3!(128, 64))([value].s);
    return ((cast(size_t)(hash[0] << 0)) |
            (cast(size_t)(hash[1] << 1)) |
            (cast(size_t)(hash[2] << 2)) |
            (cast(size_t)(hash[3] << 3)) |
            (cast(size_t)(hash[4] << 4)));
}

@safe pure nothrow unittest
{
    const bucketCount = 2^^16;
    const elementCount = bucketCount/2;

    alias T = uint;

    auto s = HashSet!(T)(bucketCount);

    assert(s._buckets.length == bucketCount);

    foreach (i; 0 .. elementCount)
    {
        assert(!s.insert(i));
    }

    foreach (i; 0 .. elementCount)
    {
        assert(s.insert(i));
    }
}

version(unittest)
{
    import array_help : s;
    import dbgio : dln;
}
