/** Tries and Prefix Trees.

    See also: https://en.wikipedia.org/wiki/Trie
    See also: https://en.wikipedia.org/wiki/Radix_tree

    TODO Use variadic list of Tuple!(Ix, Node) in constructors for SparseBr4 and DenseBrM

    TODO Use IxsN.at(ix) and use inplace of IxsN.opIndex

    TODO Make `Key` and Ix[]-array of `immutable Ix` like `string`

    TODO Allow NodeType-constructors to take const and immutable prefixes

    TODO Check for case when expanding to bit-branch instead of SparseBr4 in all `expand()` overloads

    TODO Make array indexing/slicing as @trusted and use .ptr[] instead of [] when things are stable. Especially in IxsN

    TODO Store `isKey` in top-most bit of length part of `IxsN prefix` and use for TwoLf3, TriLf2, and SixLf1.

    TODO Optimize SparseBr4.findSub for specific `subCount`

    TODO Add function reprefix({SparseBr4|DenseBrM) and call after insertAt({SparseBr4|DenseBrM}). Only useful when one single leaf is present?
    TODO Is std.algorithm.countUntil the most suitable function to use in setSub(SparseBr4*, ...)
    TODO Use std.experimental.allocator

    TODO Can we somehow overload opIndex so we can do brM[i] instead of more cumbersome (*brM)[i] when brM is of type DenseBrM*?

    TODO Provide `opIndex` and make `opSlice` for set-case (`Value` is `void`) return `SortedRange`

    TODO Should opBinaryRight return void* instead of bool for set-case?

    TODO Add `struct Range`. Use same construct as in `containers-em/src/containers/ttree.d`.

    - Members:
      - Iterator front()
      - void popFront()
      - bool empty())
      - Iterator it; // Iterator is defined below
    - Reuse RefCounted reference to _root. Add checks with `isSorted`.

    Prefix:
    - `set.prefix("alpha")`                           => `Range` of `Tuple!(string, Lang, PoT, Sense)`.
    - `set.prefix(tuple("alpha"))`                    => `Range` of `Tuple!(Lang, PoT, Sense)`.
    - `set.prefix(tuple("alpha", Lang.en))`           => `Range` of `Tuple!(PoT, Sense)`.
    - `set.prefix(tuple("alpha", Lang.en, PoT.noun))` => `Range` of `Tuple!(Sense)`.

    Returns: a range of elements which are equivalent (though not necessarily equal) to value.
    auto equalRange(this This)(inout T value)

    Returns: a range of elements which are greater than low and smaller than highValue.
    auto bound(this This)(inout T lowValue, inout T highValue)

    Returns: a range of elements which are less than value.
    auto lowerBound(this This)(inout T value)

    Returns: a range of elements which are greater than value.
    auto upperBound(this This)(inout T value)
*/
module trie;

import std.traits : isIntegral, isFloatingPoint, isSomeChar, isSomeString, isScalarType, isArray, allSatisfy, anySatisfy, isPointer;
import std.typecons : tuple, Tuple, Unqual;
import std.range : isInputRange, ElementType;
import std.range.primitives : hasLength;

import bijections : isIntegralBijectableType, bijectToUnsigned;
import variant_ex : WordVariant;
import typecons_ex : IndexedArray, StrictlyIndexed;
import modulo : Mod, mod;

// version = enterSingleInfiniteMemoryLeakTest;
// version = debugAllocations;
version = benchmark;
// version = print;

import dbg;

alias isFixedTrieableKeyType = isIntegralBijectableType;

enum isTrieableKeyType(T) = (isFixedTrieableKeyType!T ||
                             (isInputRange!T &&
                              isFixedTrieableKeyType!(ElementType!T)));

extern(C) pure nothrow @system /* TODO @nogc */
{
    void* malloc(size_t size);
    void* calloc(size_t nmemb, size_t size);
    void* realloc(void* ptr, size_t size);
    void free(void* ptr);
}

/** Mutable Raw Key. */
alias Key(size_t span) = Mod!(2^^span)[]; // TODO use bitset to more naturally support span != 8.
/** Immutable Raw Key. */
alias IKey(size_t span) = immutable(Mod!(2^^span))[]; // TODO use bitset to more naturally support span != 8.
/** Fixed-Length Raw Key. */
alias KeyN(size_t span, size_t N) = Mod!(2^^span)[N];

/** Size of a CPU cache line in bytes.

    Container layouts should be adapted to make use of at least this many bytes
    in its nodes.
 */
enum cacheLineSize = 64;

shared static this()
{
    import core.cpuid : dataCaches;
    assert(cacheLineSize == dataCaches()[0].lineSize, "Cache line is not 64 bytes");
}

enum keySeparator = ',';

/** Statically allocated `Ix`-array of fixed pre-allocated length `capacity` of
    Ix-elements in chunks of elementLength. `ElementType` is
    `Ix[elementLength]`.
 */
struct IxsN(size_t capacity,
            uint elementLength = 1,
            uint span = 8)
    if (capacity*elementLength >= 2) // no use storing less than 2 bytes
{
    enum L = elementLength;
    enum M = 2^^span;   // branch-multiplicity, typically either 2, 4, 16 or 256
    alias Ix = Mod!M;

    static if (L == 1)
        alias E = Ix;
    else
        alias E = Ix[L];

    this(Es...)(Es ixs)
        if (Es.length >= 1 &&
            Es.length <= capacity)
    {
        foreach (const i, const ix; ixs)
        {
            static assert(!is(typeof(ix) == int));
            _ixs[i] = ix;
        }
        _length = ixs.length;
    }

    static if (L == 1)
    {
        this(const Ix[] ixs)
        {
            assert(ixs.length <= capacity);
            _ixs[0 .. ixs.length] = ixs;
            _length = ixs.length;
        }
    }

    @property auto toString() const
    {
        string s;
        foreach (const i, const ix; chunks)
        {
            if (i != 0) { s ~= keySeparator; } // separator
            import std.string : format;
            static if (elementLength == 1)
            {
                s ~= format("%.2X", ix); // in hexadecimal
            }
            else
            {
                foreach (const j, const subIx; ix[])
                {
                    if (j != 0) { s ~= '_'; } // separator
                    s ~= format("%.2X", subIx); // in hexadecimal
                }
            }
        }
        return s;
    }

    @safe pure nothrow @nogc:

    bool empty() const { return _length == 0; }
    bool full() const { return _length == capacity; }

    auto front() inout
    {
        assert(!empty);
        return _ixs[0];
    }

    auto back() inout
    {
        assert(!empty);
        return _ixs[_length - 1];
    }

    /** Pop one front element. */
    auto ref popFront()
    {
        assert(!empty);
        // TODO is there a reusable Phobos function for this?
        foreach (const i; 0 .. _length - 1)
        {
            _ixs[i] = _ixs[i + 1]; // TODO move construct?
        }
        --_length;
        return this;
    }

    /** Pop `n` front elements. */
    auto ref popFrontN(size_t n)
    {
        assert(length >= n);
        // TODO is there a reusable Phobos function for this?
        foreach (const i; 0 .. _length - n)
        {
            _ixs[i] = _ixs[i + n]; // TODO move construct?
        }
        _length -= n;
        return this;
    }

    auto ref popBack()
    {
        assert(!empty);
        --_length;
        return this;
    }

    auto ref pushBack(Es...)(Es moreEs)
        if (Es.length <= capacity)
    {
        assert(length + Es.length <= capacity);
        foreach (const i, const ix; moreEs)
        {
            _ixs[_length + i] = ix;
        }
        _length += Es.length;
        return this;
    }

    bool contains(const Ix[] ix) const @nogc
    {
        import std.algorithm.searching : canFind;
        if (ix.length != L) { return false; }
        return (chunks.canFind(ix)); // TODO use binarySearch
    }

    auto chunks() inout { return _ixs[0 .. _length]; }
    alias chunks this;

    /** Variant of `opIndex` with compile-time range checking. */
    auto ref at(uint ix)() inout
        if (ix < capacity)
    {
        return _ixs[ix];
    }

    auto length() const { return _length; }

private:
    Mod!(capacity + 1) _length; // number of defined elements in `_ixs`
    static if (L == 1)
    {
        Ix[capacity] _ixs;     // byte indexes
    }
    else
    {
        Ix[L][capacity] _ixs;  // byte indexes
    }
}

static assert(IxsN!(6, 1, 8).sizeof == 7);
static assert(IxsN!(3, 2, 8).sizeof == 7);
static assert(IxsN!(2, 3, 8).sizeof == 7);

@safe pure nothrow unittest
{
    import std.algorithm : equal;
    import modulo : mod;

    enum span = 8;
    enum M = 2^^span;

    alias Ix = Mod!(M, ubyte);
    Ix[] ixs = [11.mod!M, 22.mod!M, 33.mod!M, 44.mod!M];
    enum capacity = 7;

    auto x = IxsN!(capacity, 1)(ixs);
    auto y = IxsN!(capacity, 1)(11.mod!M, 22.mod!M, 33.mod!M, 44.mod!M);

    assert(x == y);

    assert(x.length == 4);
    assert(!x.empty);

    assert(x.equal([11, 22, 33, 44]));
    assert(x.front == 11);
    assert(x.back == 44);
    assert(!x.full);
    x.popFront;
    assert(x.equal([22, 33, 44]));
    assert(x.front == 22);
    assert(x.back == 44);
    assert(!x.full);
    x.popBack;
    assert(x.equal([22, 33]));
    assert(x.front == 22);
    assert(x.back == 33);
    assert(!x.full);
    x.popFront;
    assert(x.equal([33]));
    assert(x.front == 33);
    assert(x.back == 33);
    assert(!x.full);
    x.popFront;
    assert(x.empty);
    assert(!x.full);
    assert(x.length == 0);

    x.pushBack(11.mod!M, 22.mod!M, 33.mod!M, 44.mod!M, 55.mod!M, 66.mod!M, 77.mod!M);
    assert(x.equal([11, 22, 33, 44, 55, 66, 77]));
    assert(!x.empty);
    assert(x.full);
}

/** Returns: `true` if `r` and all `ss` all have equal length.
 */
bool equalLength(R, Ss...)(const R r, const Ss ss) @safe pure nothrow @nogc
    if (Ss.length >= 1 &&
        allSatisfy!(hasLength, R, Ss))
{
    foreach (const ref s; ss)
    {
        if (r.length != s.length) { return false; }
    }
    return true;
}

@safe pure nothrow unittest
{
    assert(equalLength([1], [2], [3]));
    assert(!equalLength([1, 1], [2], [3]));
    assert(!equalLength([1], [2, 2], [3]));
    assert(!equalLength([1], [2], [3, 3]));
}

/// Binary power of radix, typically either 1, 2, 4 or 8.
private enum span = 8;
private enum radix = 2^^span; // branch-multiplicity, typically either 2, 4, 16 or 256
alias order = radix;          // tree order

static assert(span == 8, "Radix is currently limited to 8");

/** Raw adaptive radix tree (ART) container storing untyped variable-length `Key`.

    In set-case (`Value` is `void`) this container is especially suitable for
    representing a set of 32 or 64 integers/pointers.

    Radix-trees are suitable for storing variable-keys and provide completion of
    all keys matching a given key prefix. This enables efficient storage of long
    URLs sharing a common prefix, typically a domain and path.

    Branch packing of leaves is more efficiently when `Key.sizeof` is fixed,
    that is `hasFixedKeyLength` returns `true`.

    For optimal performance, the individual bit-chunks should be arranged
    starting with most sparse chunks first. For integers this means most
    significant chunk (byte) first.

    For a good introduction to adaptive radix trees (ART) see also:
    https://infosys.cs.uni-saarland.de/publications/ARCD15.pdf

    See also: https://en.wikipedia.org/wiki/Trie
    See also: https://en.wikipedia.org/wiki/Radix_tree
    See also: https://github.com/npgall/concurrent-trees
    See also: http://code.dogmap.org/kart/
    See also: http://cr.yp.to/critbit.html
    See also: https://gcc.gnu.org/onlinedocs/libstdc++/ext/pb_ds/trie_based_containers.html
    See also: https://github.com/npgall/concurrent-trees
*/
private struct RawRadixTree(Value = void)
{
    import std.bitmanip : bitfields;
    import std.conv : to;
    import std.algorithm : filter;
    import std.meta : AliasSeq, staticMap;
    import std.typecons : ConstOf;
    import bitset : BitSet;

    /** Is `true` if this tree stores values of type `Value` along with keys,
     that is be a map rather than a set */
    enum hasValue = !is(Value == void);

    /// `true` if tree has binary branch.
    enum isBinary = span == 2;

    /** Radix Modulo Index */
    alias Ix = Mod!radix; // restricted index type avoids range checking in array indexing below

    /** `span` least significant bits (LSB) of leaves directly packed into a word.

        TODO Generalize to packing of more than one `Ix` per byte.
        TODO respect byteorder in `SixLf1` to work with `WordVariant`
        TODO implement and use opSlice instead of .key[]
    */
    static if (size_t.sizeof == 8) // 64-bit CPU
    {
        static if (span == 8)
        {
            /// Single/1-Key Leaf with maximum key-length 6.
            struct OneLf6
            {
                enum capacity = (size_t.sizeof - 2) / Ix.sizeof;
                this(Ix[] key) { this.key = key; }

                pragma(inline) bool contains(Key!span key) const @nogc { return this.key == key; }

                @property string toString() const @safe pure
                {
                    import std.string : format;
                    string s;
                    foreach (const i, const ix; key)
                    {
                        const first = i == 0; // first iteration
                        if (!first) { s ~= '_'; }
                        s ~= format("%.2X", ix); // in hexadecimal
                    }
                    return s;
                }

                IxsN!(capacity, 1) key;
            private:
                ubyte _mustBeIgnored = 0; // must be here and ignored because it contains `WordVariant` type of `Node`
            }

            /// Binary/2-Key Leaf with key-length 3.
            struct TwoLf3
            {
                enum keyLength = 3; // fixed length key
                enum capacity = 2; // maximum number of keys stored

                this(Keys...)(Keys keys)
                    if (Keys.length >= 1 && Keys.length <= capacity)
                {
                    this.keys = keys;
                }

                inout(Ix)[] prefix() inout
                {
                    final switch (keys.length)
                    {
                    case 1:
                        return keys.at!0[];
                    case 2:
                        import std.algorithm : commonPrefix;
                        return commonPrefix(keys.at!0[], keys.at!1[]);
                    }
                }

                pragma(inline) bool contains(Key!span key) const @nogc { return keys.contains(key); }

                IxsN!(capacity, keyLength) keys;
            private:
                ubyte _mustBeIgnored = 0; // must be here and ignored because it contains `WordVariant` type of `Node`
            }

            /// Ternary/3-Key Leaf with key-length 2.
            struct TriLf2
            {
                enum keyLength = 2; // fixed length key
                enum capacity = 3; // maximum number of keys stored

                this(Keys...)(Keys keys)
                    if (Keys.length >= 1 && Keys.length <= capacity)
                {
                    this.keys = keys;
                }

                inout(Ix)[] prefix() inout
                {
                    final switch (keys.length)
                    {
                    case 1:
                        return keys.at!0[];
                    case 2:
                        import std.algorithm : commonPrefix;
                        return commonPrefix(keys.at!0[], keys.at!1[]);
                    case 3:
                        import std.algorithm : commonPrefix;
                        return commonPrefix(keys.at!0[],
                                            commonPrefix(keys.at!1[], keys.at!2[])); // TODO make and reuse variadic commonPrefix
                    }
                }

                pragma(inline) bool contains(Key!span key) const @nogc { return keys.contains(key); }

                IxsN!(capacity, keyLength) keys;
            private:
                ubyte _mustBeIgnored = 0; // must be here and ignored because it contains `WordVariant` type of `Node`
            }

            /// Hexa/6-Key Leaf with key-length 1.
            struct SixLf1
            {
                enum keyLength = 1;
                enum capacity = (size_t.sizeof - 2) / Ix.sizeof; // maximum number of elements

                this(Keys...)(Keys keys)
                    if (Keys.length >= 1 && Keys.length <= capacity)
                {
                    this.keys = keys;
                }

                pragma(inline) bool contains(Key!span key) const @nogc { return keys.contains(key); }

                IxsN!(capacity, 1) keys;
            private:
                ubyte _mustBeIgnored = 0; // must be here and ignored because it contains `WordVariant` type of `Node`
            }
        }
    }
    else
    {
        static assert(false, "Currently requires a 64-bit CPU (size_t.sizeof == 8)");
    }

    // TODO make these run-time arguments at different key depths and map to statistics of typed-key
    alias DefaultBr = SparseBr4*; // either SparseBr4*, DenseBrM*

    static if (!hasValue)
    {
        static assert(SixLf1.sizeof == size_t.sizeof); // assert that it's size matches platform word-size
    }

    /** Node types. */
    alias NodeTypes = AliasSeq!(OneLf6,
                                TwoLf3,
                                TriLf2,
                                SixLf1,
                                DenseBrM*,
                                SparseBr4*,
                                DenseLf1*,
                                SparseLf1*,
                                );

    /** Mutable node. */
    alias Node = WordVariant!NodeTypes;
    /** Constant node. */
    // TODO make work with indexNaming alias ConstNodePtr = WordVariant!(staticMap!(ConstOf, NodeTypes));

    static assert(span <= 8*Ix.sizeof, "Need more precision in Ix");

    /** Element (`Key` plus optional `Value`) Reference. */
    struct ElementRef
    {
        Node node;
        Ix ix;
    }

    /** Tree Iterator. */
    alias Iterator = ElementRef[];

    /** Tree Range. Is `isBidirectionalRange`. */
    struct Range
    {
        Iterator front;
        Iterator back;
    }

    /** 256-Branch population histogram.
    */
    alias DenseLf1_PopHist = size_t[radix];

    /** 4-Branch population histogram.
        Index maps to population with value range (1 .. 4).
    */
    alias SparseBr4_PopHist = size_t[4];

    /** radix-Branch population histogram.
        Index maps to population with value range (1 .. `radix`).
    */
    alias DenseBrM_PopHist = size_t[radix];

    /** Tree Population and Memory-Usage Statistics. */
    struct Stats
    {
        DenseLf1_PopHist popHist_DenseLf1;
        SparseBr4_PopHist popHist_SparseBr4; // packed branch population histogram
        DenseBrM_PopHist popHist_DenseBrM; // full branch population histogram

        size_t allOneLf60CountOfSparseBr4; // number of `SparseBr4` which sub-branches are all `OneLf6` of length 0
        size_t allOneLf60CountOfDenseBrM; // number of `DenseBrM` which sub-branches are all `OneLf6` of length 0

        /** Maps `Node` type/index `Ix` to population.

            Used to calculate complete tree memory usage, excluding allocator
            overhead typically via `malloc` and `calloc`.
         */
        IndexedArray!(size_t, Node.Ix) popByNodeType;
        static assert(is(typeof(popByNodeType).Index == Node.Ix));

        /// Number of heap-allocated `Node`s. Should always equal `heapNodeAllocationBalance`.
        size_t heapNodeCount;
    }

    /** Sparsely coded leaves. */
    static private struct SparseLf1
    {
        alias Length = Mod!(radix + 1);
        alias Capacity = Mod!(radix + 1);

        pure nothrow /* TODO @nogc */:

        this(Es...)(Es es) @safe
        {
            import std.math : nextPow2;

            _length = es._length;

            // TODO reuse allocate or reserve
            _capacity = nextPow2(es._length);
            _keys = malloc(_capacity*Ix.sizeof);
            static if (hasValue)
            {
                _values = malloc(_capacity*Value.sizeof);
            }

            foreach (const i, const e; es)
            {
                _keys[i] = e[0];
                static if (hasValue)
                {
                    _values[i] = e[1];
                }
            }
        }

        ~this()
        {
            free(_keys); debug _keys = null;
            static if (hasValue)
            {
                free(_values); debug _values = null;
            }
        }

        pragma(inline) Length length() const @safe @nogc { return _length; }
        pragma(inline) Capacity capacity() const @safe @nogc { return _capacity; }

        /** Reserve room for `newCapacity` number of elements. */
        void reserve(Capacity newCapacity) @trusted
        {
            if (_capacity < newCapacity)
            {
                _keys = cast(typeof(_keys))realloc(_keys, _capacity*Ix.sizeof);
                _values = cast(typeof(_values))realloc(_values, _capacity*Value.sizeof);
            }
            _capacity = newCapacity;
        }

        pragma(inline) bool empty() const @safe @nogc { return _length == 0; }
        pragma(inline) bool full() const @safe @nogc { return _length == radix; }

        pragma(inline) bool contains(Key!span key) const @trusted @nogc
        {
            import std.algorithm.searching : canFind;
            return (key.length == 1 &&
                    _keys[0 .. _length].canFind(key[0]));
        }

        /** Append statistics of tree under `this` into `stats`. */
        void calculate(ref Stats stats) @safe
        {
            dln("TODO");
        }

    private:
        Length _length;
        Capacity _capacity;
        Ix* _keys;
        Value* _values;
    }

    /** Dense Bitset Branch with only bottom-most leaves. */
    static private struct DenseLf1
    {
        enum prefixCapacity = 14; // 6, 14, 22, ...
        enum maxSubCount = 256;

        @safe pure nothrow:

        this(Ixs...)(Ix[] prefix, bool isKey, Ixs subIxs)
            if (Ixs.length <= maxSubCount)
        {
            this.prefix = prefix;
            this.isKey = isKey;
            foreach (subIx; subIxs)
            {
                _keyBits[subIx] = true;
            }
        }

        pragma(inline) bool hasSubAt(Ix ix) const @nogc { return _keyBits[ix]; }
        pragma(inline) bool empty() const @nogc { return _keyBits.empty; }
        pragma(inline) bool full() const @nogc { return _keyBits.full; }

        pragma(inline) bool contains(Key!span key) const @nogc
        {
            import std.algorithm : skipOver;
            return (key.skipOver(prefix[]) &&  // matching prefix
                    ((key.length == 0 && isKey) || // direct match
                     (key.length == 1 && _keyBits[key[0]]))); // sub-match
        }

        /** Append statistics of tree under `this` into `stats`. */
        void calculate(ref Stats stats)
        {
            const count = _keyBits.countOnes; // number of non-zero sub-nodes
            assert(count <= radix);
            ++stats.popHist_DenseLf1[count - 1]; // TODO type-safe indexing
        }

        private:
        BitSet!radix _keyBits;  // 32 bytes
        static if (hasValue)
        {
            Value[radix] values; // values
        }
        IxsN!prefixCapacity prefix; // prefix common to all `subNodes` (also called edge-label)
        bool isKey;
    }

    static if (!hasValue) { static assert(DenseLf1.sizeof == 48); }

    /** Sparse/Packed/Partial 4-way branch. */
    static private struct SparseBr4
    {
        enum subCapacity = 4; // maximum number of sub indexes and nodes preallocated

        enum prefixCapacity = 10; // 2, 10, 18, ...

        @safe pure nothrow:

        this(Ix[] prefix, bool isKey)
        {
            this.prefix = prefix;
            this.isKey = isKey;
        }

        this(Ix[] prefix, bool isKey, Ix subIx, Node subNode)
        {
            this.prefix = prefix;
            this.isKey = isKey;
            this.subIxSlots.at!0 = subIx;
            this.subNodeSlots.at!0 = subNode;
            this.subCount = 1;
        }

        this(Ix[] prefix, bool isKey,
             Ix subIx0, Node subNode0,
             Ix subIx1, Node subNode1)
        {
            assert(subIx0 != subIx1);
            assert(subNode0 != subNode1);

            this.prefix = prefix;
            this.isKey = isKey;

            this.subIxSlots.at!0 = subIx0;
            this.subNodeSlots.at!0 = subNode0;

            this.subIxSlots.at!1 = subIx1;
            this.subNodeSlots.at!1 = subNode1;

            this.subCount = 2;
        }

        void pushBackSub(Tuple!(Ix, Node) sub)
        {
            assert(!full);
            const backIx = subCount.mod!subCapacity;
            subIxSlots[backIx] = sub[0];
            subNodeSlots[backIx] = sub[1];
            subCount = cast(ubyte)(subCount + 1); // TODO remove need for cast
        }

        inout(Node) findSub(Ix ix) inout
        {
            switch (subCount)
            {
            case 0:
                break;
            case 1:
                if (subIxSlots.at!0 == ix) { return subNodeSlots.at!0; }
                break;
            case 2:
                foreach (i; iota!(0, 2))
                {
                    if (subIxSlots.at!i == ix) { return subNodeSlots.at!i; }
                }
                break;
            case 3:
                foreach (i; iota!(0, 3))
                {
                    if (subIxSlots.at!i == ix) { return subNodeSlots.at!i; }
                }
                break;
            case 4:
                foreach (i; iota!(0, 4))
                {
                    if (subIxSlots.at!i == ix) { return subNodeSlots.at!i; }
                }
                break;
            default:
                // TODO do binary search
                foreach (const i_; 0 ..  subCount)
                {
                    const i = i_.mod!subCapacity;
                    if (subIxSlots[i] == ix) { return subNodeSlots[i]; }
                }
                break;
            }
            return Node.init;
        }

        pragma(inline) bool empty() const @nogc { return subCount == 0; }
        pragma(inline) bool full() const @nogc { return subCount == subCapacity; }

        pragma(inline) auto subIxs() inout @nogc
        {
            return subIxSlots[0 .. subCount];
        }
        pragma(inline) auto subNodes() inout @nogc
        {
            return subNodeSlots[0 .. subCount];
        }

        /** Returns `true` if this branch can be packed into a bitset, that is
            contains only sub-nodes of type `OneLf6` of zero length. */
        bool hasMinimumDepth() const /* TODO @nogc */
        {
            foreach (const sub; subNodes)
            {
                if (const subOneLf6Ref = sub.peek!(OneLf6))
                {
                    const subOneLf6 = *subOneLf6Ref;
                    if (subOneLf6.key.length != 0) { return false; }
                }
                else
                {
                    return false;
                }
            }
            return true;
        }

        /** Append statistics of tree under `this` into `stats`. */
        void calculate(ref Stats stats) const
        {
            size_t count = 0; // number of non-zero sub-nodes
            foreach (const sub; subNodes)
            {
                ++count;
                sub.calculate!(Value)(stats);
            }
            assert(count <= radix);
            ++stats.popHist_SparseBr4[count - 1]; // TODO type-safe indexing
            stats.allOneLf60CountOfSparseBr4 += hasMinimumDepth;
        }

        private:

        // members in order of decreasing `alignof`:
        StrictlyIndexed!(Node[subCapacity]) subNodeSlots;
        IxsN!prefixCapacity prefix; // prefix common to all `subNodes` (also called edge-label)
        StrictlyIndexed!(Ix[subCapacity]) subIxSlots;
        mixin(bitfields!(ubyte, "subCount", 7, // counts length of defined elements in subNodeSlots
                         bool, "isKey", 1)); // key at this branch is occupied
    }

    static assert(SparseBr4.sizeof == 48);

    /** Dense/Unpacked `radix`-branch with `radix` number of sub-nodes. */
    static private struct DenseBrM
    {
        enum subCapacity = 256;
        enum prefixCapacity = 15; // 7, 15, 23, ..., we can afford larger prefix here because DenseBrM is so large

        @safe pure nothrow:

        this(Ix[] prefix, bool isKey = false)
        {
            this.prefix = prefix;
            this.isKey = isKey;
        }

        this(Ix[] prefix, bool isKey, Ix subIx, Node subNode)
        {
            this(prefix, isKey);
            this.subNodes[subIx] = subNode;
        }

        this(Ix[] prefix, bool isKey,
             Ix subIx0, Node subNode0,
             Ix subIx1, Node subNode1)
        {
            assert(subIx0 != subIx1);
            assert(subNode0 != subNode1);

            this(prefix, isKey);
            this.subNodes[subIx0] = subNode0;
            this.subNodes[subIx1] = subNode1;
        }

        this(SparseBr4* rhs)
        {
            this.prefix = rhs.prefix;
            this.isKey = rhs.isKey;
            foreach (const i; 0 .. rhs.subCount) // each sub node. TODO use iota!(Mod!N)
            {
                const iN = i.mod!(SparseBr4.subCapacity);
                const subIx = rhs.subIxSlots[iN];
                this.subNodes[subIx] = rhs.subNodes[iN];
            }
        }

        IxsN!prefixCapacity prefix; // prefix (edge-label) common to all `subNodes`
        bool isKey;      // key at this branch is occupied
        StrictlyIndexed!(Node[radix]) subNodes;

        /** Returns `true` if this branch can be packed into a bitset, that is
            contains only subNodes of type `OneLf6` of zero length. */
        bool hasMinimumDepth() const @safe pure nothrow /* TODO @nogc */
        {
            foreach (const subNode; subNodes)
            {
                if (const subOneLf6Ref = subNode.peek!(OneLf6))
                {
                    if ((*subOneLf6Ref).key.length != 0)
                    {
                        return false;
                    }
                }
                else
                {
                    return false;
                }
            }
            return true;
        }

        /// Number of non-null sub-Nodes.
        Mod!(radix + 1) subCount() const
        {
            typeof(return) count = 0; // number of non-zero sub-nodes
            foreach (const subNode; subNodes) // TODO why can't we use std.algorithm.count here?
            {
                if (subNode) { ++count; }
            }
            assert(count <= radix);
            return count;
        }

        /** Append statistics of tree under `this` into `stats`. */
        void calculate(ref Stats stats)  /* TODO @nogc */ const
        {
            size_t count = 0; // number of non-zero sub-nodes
            foreach (const subNode; subNodes)
            {
                if (subNode)
                {
                    ++count;
                    subNode.calculate!(Value)(stats);
                }
            }
            assert(count <= radix);
            ++stats.popHist_DenseBrM[count - 1]; // TODO type-safe indexing
            stats.allOneLf60CountOfDenseBrM += hasMinimumDepth;
        }
    }

    static if (false)
    {
        pragma(msg, "SparseBr4.sizeof:", SparseBr4.sizeof, " SparseBr4.alignof:", SparseBr4.alignof);
        pragma(msg, "SparseBr4.subNodes.sizeof:", SparseBr4.subNodes.sizeof, " SparseBr4.subNodes.alignof:", SparseBr4.subNodes.alignof);
        pragma(msg, "SparseBr4.prefix.sizeof:", SparseBr4.prefix.sizeof, " SparseBr4.prefix.alignof:", SparseBr4.prefix.alignof);
        pragma(msg, "SparseBr4.subIxs.sizeof:", SparseBr4.subIxs.sizeof, " SparseBr4.subIxs.alignof:", SparseBr4.subIxs.alignof);
    }

    /** Set sub-`Node` of branch `Node curr` at index `ix` to `subNode`. */
    pragma(inline) Node setSub(Node curr, Ix subIx, Node subNode, size_t superPrefixLength) @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_DenseLf1Ptr: return setSub(curr.as!(DenseLf1*), subIx, subNode, superPrefixLength);
        case Node.Ix.ix_SparseBr4Ptr: return setSub(curr.as!(SparseBr4*), subIx, subNode, superPrefixLength);
        case Node.Ix.ix_DenseBrMPtr: return setSub(curr.as!(DenseBrM*), subIx, subNode, superPrefixLength);
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }
    /// ditto
    Node setSub(DenseLf1* curr, Ix subIx, Node subNode, size_t superPrefixLength) @safe pure nothrow /* TODO @nogc */
    {
        if (const subNodeRef = subNode.peek!(OneLf6))
        {
            const subNode_ = *subNodeRef;
            if (subNode_.key.empty)
            {
                curr._keyBits[subIx] = true;
                freeNode(subNode); // free it because it's stored inside the bitset itself
                return Node(curr);
            }
        }

        // need to expand
        const extraCount = curr._keyBits[subIx] ? 0 : 1; // if one extra sub-node needes to be added
        Node next;
        if (curr._keyBits.countOnes + extraCount <= SparseBr4.subCapacity) // if `curr` keys plus on extra fit
        {
            auto next_ = construct!(SparseBr4*)(curr.prefix, curr.isKey);
            foreach (const ix; curr._keyBits.oneIndexes)
            {
                setSub(next_, ix, Node(construct!(OneLf6)), superPrefixLength);
            }
            next = next_;
        }
        else
        {
            auto next_ = construct!(DenseBrM*)(curr.prefix, curr.isKey);
            foreach (const ix; curr._keyBits.oneIndexes)
            {
                setSub(next_, ix, Node(construct!(OneLf6)), superPrefixLength);
            }
            next = next_;
        }
        freeNode(curr);
        return setSub(next, subIx, subNode, superPrefixLength); // insert on new
    }
    /// ditto
    Node setSub(SparseBr4* curr, Ix subIx, Node subNode, size_t superPrefixLength) @safe pure nothrow /* TODO @nogc */
    {
        if (const hit = curr.subIxSlots.findIndex(subIx))
        {
            curr.subNodeSlots[hit.index] = subNode; // reuse
        }
        else if (!curr.full)     // if room left in curr
        {
            curr.pushBackSub(tuple(subIx, subNode)); // add one to existing
        }
        else                    // if no room left in curr we need to expand
        {
            auto next = construct!(DenseBrM*)(curr);
            freeNode(curr);
            assert(!getSub(next, subIx)); // key slot should be free
            return setSub(next, subIx, subNode, superPrefixLength); // fast, because directly calls setSub(DenseBrM*, ...)
        }
        return Node(curr);
    }
    /// ditto
    pragma(inline) Node setSub(DenseBrM* curr, Ix subIx, Node subNode, size_t superPrefixLength) @safe pure nothrow /* TODO @nogc */
    {
        try
        {
            debug assert(!curr.subNodes[subIx],
                         "sub-Node at index " ~ subIx.to!string ~
                         " already set to " ~ subNode.to!string);
        }
        catch (Exception e) {}
        curr.subNodes[subIx] = subNode;
        return Node(curr);
    }

    Node getSub(DenseLf1* curr, Ix subIx) @safe pure nothrow
    {
        if (curr.hasSubAt(subIx))
        {
            return Node(OneLf6.init);
        }
        return Node.init;
    }

    Node getSub(SparseBr4* curr, Ix subIx) @safe pure nothrow
    {
        if (auto subNode = curr.findSub(subIx))
        {
            return subNode;
        }
        return Node.init;
    }

    Node getSub(DenseBrM* curr, Ix subIx) @safe pure nothrow
    {
        auto sub = curr.subNodes[subIx];
        curr.subNodes[subIx] = Node.init; // zero it to prevent multiple references
        return sub;
    }

    /** Get sub-`Node` of branch `Node curr` at index `subIx. */
    Node getSub(Node curr, Ix subIx) @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_DenseLf1Ptr: return getSub(curr.as!(DenseLf1*), subIx);
        case Node.Ix.ix_SparseBr4Ptr: return getSub(curr.as!(SparseBr4*), subIx);
        case Node.Ix.ix_DenseBrMPtr: return getSub(curr.as!(DenseBrM*), subIx);
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    /** Returns: `true` if `curr` is occupied, `false` otherwise. */
    pragma(inline) bool isKey(Node curr) const @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_DenseLf1Ptr: return curr.as!(DenseLf1*).isKey;
        case Node.Ix.ix_SparseBr4Ptr: return curr.as!(SparseBr4*).isKey;
        case Node.Ix.ix_DenseBrMPtr: return curr.as!(DenseBrM*).isKey;
            // TODO extend to leaves aswell?
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    pragma(inline) void makeKey(Node curr) const @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_DenseLf1Ptr: curr.as!(DenseLf1*).isKey = true; break;
        case Node.Ix.ix_SparseBr4Ptr: curr.as!(SparseBr4*).isKey = true; break;
        case Node.Ix.ix_DenseBrMPtr: curr.as!(DenseBrM*).isKey = true; break;
            // TODO extend to leaves aswell?
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    /** Get prefix of node `curr`. */
    auto getPrefix(inout Node curr) @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_OneLf6: return curr.as!(OneLf6).key[]; // suffix is the prefix
        // case Node.Ix.ix_TriLf2: return curr.as!(TriLf2).prefix[];
        case Node.Ix.ix_SixLf1: return inout(Ix[]).init; // no prefix
        case Node.Ix.ix_DenseLf1Ptr: return curr.as!(DenseLf1*).prefix[];
        case Node.Ix.ix_SparseBr4Ptr: return curr.as!(SparseBr4*).prefix[];
        case Node.Ix.ix_DenseBrMPtr: return curr.as!(DenseBrM*).prefix[];
            // TODO extend to leaves aswell?
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    /** Set prefix of branch node `curr` to `prefix`. */
    void setPrefix(Node curr, Ix[] prefix) @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_OneLf6:    curr.as!(OneLf6).key  = typeof(curr.as!(OneLf6).key)(prefix); break;
        case Node.Ix.ix_SixLf1:    assert(prefix.length == 0); break;
        case Node.Ix.ix_DenseLf1Ptr: curr.as!(DenseLf1*).prefix = typeof(curr.as!(DenseLf1*).prefix)(prefix); break;
        case Node.Ix.ix_SparseBr4Ptr: curr.as!(SparseBr4*).prefix = typeof(curr.as!(SparseBr4*).prefix)(prefix); break;
        case Node.Ix.ix_DenseBrMPtr: curr.as!(DenseBrM*).prefix = typeof(curr.as!(DenseBrM*).prefix)(prefix); break;
            // TODO extend to leaves aswell?
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    /** Pop `n`  from prefix. */
    void popFrontNPrefix(Node curr, size_t n) @safe pure nothrow
    {
        switch (curr.typeIx)
        {
        case Node.Ix.ix_DenseLf1Ptr: curr.as!(DenseLf1*).prefix.popFrontN(n); break;
        case Node.Ix.ix_SparseBr4Ptr: curr.as!(SparseBr4*).prefix.popFrontN(n); break;
        case Node.Ix.ix_DenseBrMPtr: curr.as!(DenseBrM*).prefix.popFrontN(n); break;
            // TODO extend to leaves aswell?
        default: assert(false, "Unsupported Node type " ~ curr.typeIx.to!string);
        }
    }

    Stats usageHistograms() const
    {
        typeof(return) stats;
        _root.calculate!(Value)(stats);
        return stats;
    }

    this(this)
    {
        if (!_root) return;
        auto rhsRoot = _root;
        debug const oldLength = _length;
        if (rhsRoot)
        {
            _root = null;       // reset
            _length = 0;        // needs reset because insert updates
            // TODO insert(rhsRoot[]);
        }
        assert(false, "TODO calculate tree by branches and leafs and make copies of them");
    }

    ~this()
    {
        if (_root) { release(_root); }
        try
        {
            if (_heapNodeAllocationBalance != 0)
            {
                dln("warning: Memory leak, heap Node allocation balance is not zero, but " ~
                    _heapNodeAllocationBalance.to!string ~
                    ", nodeCountsByIx is " ~ nodeCountsByIx.to!string);
            }
        }
        catch (Exception e) {}
    }

    const @safe pure nothrow /* TODO @nogc */
    {
        /** Returns: `true` if `key` is stored, `false` otherwise. */
        pragma(inline) bool contains(Key!span key)
        {
            return containsAt(_root, key);
        }

        /** Returns: `true` if `key` is stored under `curr`, `false` otherwise. */
        pragma(inline) bool containsAt(Node curr, Key!span key)
        {
            import std.algorithm : skipOver;
            final switch (curr.typeIx) with (Node.Ix)
            {
            case undefined: return false;
            case ix_OneLf6: return curr.as!(OneLf6).contains(key);
            case ix_TwoLf3: return curr.as!(TwoLf3).contains(key);
            case ix_TriLf2: return curr.as!(TriLf2).contains(key);
            case ix_SixLf1: return curr.as!(SixLf1).contains(key);
            case ix_SparseLf1Ptr: return curr.as!(SparseLf1*).contains(key);
            case ix_DenseLf1Ptr: return curr.as!(DenseLf1*).contains(key);
            case ix_SparseBr4Ptr:
                auto curr_ = curr.as!(SparseBr4*);
                return (key.skipOver(curr_.prefix) &&        // matching prefix
                        ((key.length == 0 && curr_.isKey) || // either stored at `curr`
                         (key.length >= 1 && containsAt(curr_.findSub(key[0]), key[1 .. $])))); // recurse
            case ix_DenseBrMPtr:
                auto curr_ = curr.as!(DenseBrM*);
                return (key.skipOver(curr_.prefix) &&        // matching prefix
                        ((key.length == 0 && curr_.isKey) || // either stored at `curr`
                         (key.length >= 1 && containsAt(curr_.subNodes[key[0]], key[1 .. $])))); // recurse
            }
        }

        pragma(inline) size_t countHeapNodes()
        {
            return countHeapNodesAt(_root);
        }

        pragma(inline) size_t countHeapNodesAt(Node curr)
        {
            size_t count = 0;
            final switch (curr.typeIx) with (Node.Ix)
            {
            case undefined: break;
            case ix_OneLf6: break;
            case ix_TwoLf3: break;
            case ix_TriLf2: break;
            case ix_SixLf1: break;

            case ix_SparseLf1Ptr:
            case ix_DenseLf1Ptr:
                ++count;
                break;

            case ix_SparseBr4Ptr:
                auto curr_ = curr.as!(SparseBr4*);
                ++count;
                foreach (subNode; curr_.subNodeSlots[0 .. curr_.subCount])
                {
                    if (subNode) { count += countHeapNodesAt(subNode); }
                }
                break;

            case ix_DenseBrMPtr:
                ++count;
                auto curr_ = curr.as!(DenseBrM*);
                foreach (subNode; curr_.subNodes)
                {
                    if (subNode) { count += countHeapNodesAt(subNode); }
                }
                break;
            }
            return count;
        }
    }

    @safe pure nothrow /* TODO @nogc */
    {
        /** Insert `key` into `this` tree. */
        pragma(inline) Node insert(Key!span key, out Node insertionNode)
        {
            return _root = insertAt(_root, key, 0, insertionNode);
        }

        Node insertNew(Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            switch (key.length)
            {
            case 0: return insertionNode = Node(construct!(OneLf6)());
            case 1: return insertionNode = Node(construct!(SixLf1)(key[0]));
            case 2: return insertionNode = Node(construct!(TriLf2)(key));
            case 3: return insertionNode = Node(construct!(TwoLf3)(key));
            default:
                if (key.length <= OneLf6.capacity)
                {
                    return insertionNode = Node(construct!(OneLf6)(key));
                }
                else if (key.length <= DenseLf1.prefixCapacity) // only if DenseLf1.prefixCapacity > OneLf6.capacity
                {
                    auto prefix = key[0 .. $ - 1];
                    return insertionNode = Node(construct!(DenseLf1*)(prefix, false, key[$ - 1]));
                }
                else                // key doesn't fit in a `OneLf6`
                {
                    import std.algorithm : min;
                    auto brKey = key[0 .. min(key.length, DefaultBr.prefixCapacity)];
                    auto next = insertAt(Node(construct!(DefaultBr)(brKey, false)), // as much as possible of key in branch prefix
                                         key, superPrefixLength, insertionNode);

                    // assert that next branch shouldn't be a bit-packed branch instead
                    debug if (const nextSparseBr4Ref = next.peek!(SparseBr4*))
                    {
                        assert(!(*nextSparseBr4Ref).hasMinimumDepth);
                    }
                    assert(insertionNode);
                    return next;
                }
            }
        }

        /** Insert `key` into sub-tree under root `curr`. */
        pragma(inline) Node insertAt(Node curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            if (!curr)          // if no existing `Node` to insert at
            {
                auto next = insertNew(key, superPrefixLength, insertionNode);
                assert(insertionNode); // must be added to new Node
                return next;
            }
            else
            {
                final switch (curr.typeIx) with (Node.Ix)
                {
                case undefined: return typeof(return).init;
                case ix_OneLf6: return insertAt(curr.as!(OneLf6), key, superPrefixLength, insertionNode);
                case ix_TwoLf3: return insertAt(curr.as!(TwoLf3), key, superPrefixLength, insertionNode);
                case ix_TriLf2: return insertAt(curr.as!(TriLf2), key, superPrefixLength, insertionNode);
                case ix_SixLf1: return insertAt(curr.as!(SixLf1), key, superPrefixLength, insertionNode);

                case ix_SparseLf1Ptr:
                case ix_DenseLf1Ptr:
                case ix_SparseBr4Ptr:
                case ix_DenseBrMPtr: return insertAtBranch(curr, key, superPrefixLength, insertionNode);
                }
            }
        }

        Node insertAtBranch(Node curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            import std.algorithm : commonPrefix;
            auto currPrefix = getPrefix(curr);
            auto matchedKeyPrefix = commonPrefix(key, currPrefix);

            if (willFail) { dln("WILL FAIL: key:", key,
                                " curr:", curr,
                                " currPrefix:", getPrefix(curr),
                                " matchedKeyPrefix:", matchedKeyPrefix,
                                " superPrefixLength:", superPrefixLength); }

            // prefix:"ab", key:"cd"
            if (matchedKeyPrefix.length == 0) // no prefix key match
            {
                if (currPrefix.length == 0) // no current prefix
                {
                    if (key.length == 0)
                    {
                        if (willFail) { dln(""); }
                        // both prefix and key is empty
                        assert(currPrefix == key); // assert exact match
                        if (!isKey(curr))
                        {
                            makeKey(curr);
                            insertionNode = curr;
                        }
                        return curr;
                    }
                    else
                    {
                        if (willFail) { dln(""); }
                        const subIx = key[0];
                        return setSub(curr, subIx,
                                      insertAt(getSub(curr, subIx), // recurse
                                               key[1 .. $],
                                               superPrefixLength + 1,
                                               insertionNode),
                                      superPrefixLength);
                    }
                }
                else
                {
                    const currSubIx = currPrefix[0]; // subIx = 'a'
                    popFrontNPrefix(curr, 1);
                    if (key.length == 0)
                    {
                        if (willFail) { dln(""); }
                        return insertionNode = Node(construct!(DefaultBr)(matchedKeyPrefix,
                                                                          true, // because `key` is empty
                                                                          currSubIx, curr));
                    }
                    else
                    {
                        if (willFail) { dln(""); }
                        return Node(construct!(DefaultBr)(matchedKeyPrefix, false,
                                                          currSubIx, curr,
                                                          key[0],
                                                          insertNew(key[1 .. $], superPrefixLength, insertionNode)));
                    }
                }
            }
            else if (matchedKeyPrefix.length < key.length)
            {
                if (matchedKeyPrefix.length == currPrefix.length)
                {
                    if (willFail) { dln(""); }
                    // most probable: key is an extension of prefix: prefix:"ab", key:"abcd"
                    key = key[matchedKeyPrefix.length .. $]; // strip `currPrefix from beginning of `key`
                    superPrefixLength += matchedKeyPrefix.length;
                    const subIx = key[0];
                    return setSub(curr, subIx,
                                  insertAt(getSub(curr, subIx), // recurse
                                           key[1 .. $],
                                           superPrefixLength + 1,
                                           insertionNode),
                                  superPrefixLength);
                }
                else
                {
                    if (willFail) { dln(""); }
                    // prefix and key share beginning: prefix:"ab11", key:"ab22"

                    const currSubIx = currPrefix[matchedKeyPrefix.length]; // need index first
                    popFrontNPrefix(curr, matchedKeyPrefix.length + 1); // drop matchedKeyPrefix plus index to next super branch

                    return Node(construct!(DefaultBr)(matchedKeyPrefix, false, // key is not occupied
                                                      currSubIx,
                                                      curr,
                                                      key[matchedKeyPrefix.length],
                                                      insertNew(key[matchedKeyPrefix.length + 1.. $], superPrefixLength, insertionNode)));
                }
            }
            else // if (matchedKeyPrefix.length == key.length)
            {
                assert(matchedKeyPrefix.length == key.length);
                if (matchedKeyPrefix.length < currPrefix.length)
                {
                    if (willFail) { dln(""); }
                    // prefix is an extension of key: prefix:"abcd", key:"ab"
                    const subIx = currPrefix[matchedKeyPrefix.length]; // need index first
                    popFrontNPrefix(curr, matchedKeyPrefix.length + 1); // drop matchedKeyPrefix plus index to next super branch
                    return insertionNode = Node(construct!(DefaultBr)(matchedKeyPrefix, true, // `true` because `key` occupies this node
                                                                      subIx, curr));
                }
                else // if (matchedKeyPrefix.length == currPrefix.length)
                {
                    if (willFail) { dln(""); }
                    assert(matchedKeyPrefix.length == currPrefix.length);
                    // prefix equals key: prefix:"ab", key:"ab"
                    assert(currPrefix == key); // assert exact match
                    if (!isKey(curr))
                    {
                        makeKey(curr);
                        insertionNode = curr;
                    }
                    return curr;
                }
            }
        }

        Node insertAt(OneLf6 curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            import std.algorithm : commonPrefix;
            auto matchedKeyPrefix = commonPrefix(key, curr.key);
            if (curr.key.length == key.length)
            {
                if (matchedKeyPrefix.length == key.length) // curr.key, key and matchedKeyPrefix all equal
                {
                    return Node(curr); // already stored in `curr`
                }
                else if (matchedKeyPrefix.length + 1 == key.length) // key and curr.key are both matchedKeyPrefix plus one extra
                {
                    Node next;
                    switch (matchedKeyPrefix.length)
                    {
                    case 0: next = construct!(SixLf1)(curr.key[0], key[0]); break;
                    case 1: next = construct!(TriLf2)(curr.key, key); break;
                    case 2: next = construct!(TwoLf3)(curr.key, key); break;
                    default:
                        if (willFail) { dln("matchedKeyPrefix:", matchedKeyPrefix); }
                        next = construct!(DenseLf1*)(matchedKeyPrefix, false,
                                                    curr.key[$ - 1],
                                                    key[$ - 1]);
                        break;
                    }
                    freeNode(curr);
                    return insertionNode = next;
                }
            }
            return insertAt(split(curr, matchedKeyPrefix, key, superPrefixLength),
                            key, superPrefixLength, insertionNode);
        }

        Node insertAt(TwoLf3 curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || curr.keyLength == key.length);
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            if (willFail) { dln("WILL FAIL: key:", key, " curr:", curr, " superPrefixLength:", superPrefixLength); }
            if (curr.keyLength == key.length)
            {
                if (curr.contains(key)) { return Node(curr); }
                if (!curr.keys.full)
                {
                    curr.keys.pushBack(key);
                    return insertionNode = Node(curr);
                }

                // TODO Use variadic commonPrefix(curr.keys.at!0, curr.keys.at!1, key)
                enum PL = curr.keyLength - 1;    // searched prefix length
                if (curr.keys.at!0[0 .. PL] ==          key[0 .. PL] &&
                    curr.keys.at!0[0 .. PL] == curr.keys.at!1[0 .. PL]) // `curr.keys` and `key` share all but last Ix
                {
                    // if `curr` and `key` can be combined into a `DenseLf1`
                    auto next = construct!(DenseLf1*)(key[0 .. PL], false);
                    foreach (const currKey; curr.keys)
                    {
                        next._keyBits[currKey[PL]] = true;
                    }
                    next._keyBits[key[PL]] = true;
                    freeNode(curr);
                    return insertionNode = Node(next);
                }
            }
            return insertAt(expand(curr, superPrefixLength), key, superPrefixLength, insertionNode); // NOTE stay at same (depth)
        }

        Node insertAt(TriLf2 curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || curr.keyLength == key.length);
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            if (willFail) { dln("WILL FAIL: key:", key, " curr:", curr, " superPrefixLength:", superPrefixLength); }
            if (curr.keyLength == key.length)
            {
                if (curr.contains(key)) { return Node(curr); }
                if (!curr.keys.full)
                {
                    curr.keys.pushBack(key);
                    return insertionNode = Node(curr);
                }

                if (curr.keys.at!0[0] == key[0] &&
                    curr.keys.at!0[0] == curr.keys.at!1[0] &&
                    curr.keys.at!1[0] == curr.keys.at!2[0]) // `curr.keys` and `key` share all but last Ix
                {
                    // if `curr` and `key` can be combined into a `DenseLf1`
                    auto next = construct!(DenseLf1*)(key[0 .. 1], false);
                    foreach (const currKey; curr.keys)
                    {
                        next._keyBits[currKey[1]] = true;
                    }
                    next._keyBits[key[1]] = true;
                    freeNode(curr);
                    return insertionNode = Node(next);
                }
            }
            return insertAt(expand(curr, superPrefixLength),
                            key, superPrefixLength, insertionNode); // NOTE stay at same (depth)
        }

        Node insertAt(SixLf1 curr, Key!span key, size_t superPrefixLength, out Node insertionNode)
        {
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);
            if (!(hasVariableKeyLength || curr.keyLength == key.length))
            {
                dln(curr);
                dln(key);
            }
            assert(hasVariableKeyLength || curr.keyLength == key.length);

            if (willFail) { dln("WILL FAIL: key:", key, " curr:", curr, " superPrefixLength:", superPrefixLength); }
            if (curr.keyLength == key.length)
            {
                if (curr.contains(key)) { return Node(curr); }
                if (!curr.keys.full)
                {
                    curr.keys.pushBack(key[0]);
                    return insertionNode = Node(curr);
                }

                if (willFail) { dln("prefix empty"); }
                auto next = construct!(DenseLf1*)(Ix[].init, false);
                foreach (const currKey; curr.keys)
                {
                    next._keyBits[currKey] = true;
                }
                next._keyBits[key[0]] = true;
                freeNode(curr);
                return insertionNode = Node(next);
            }
            if (willFail) { dln("curr:", curr, " key:", key, " superPrefixLength:", superPrefixLength); }
            return insertAt(expand(curr, superPrefixLength),
                            key, superPrefixLength, insertionNode); // NOTE stay at same (depth)
        }

        /** Split `curr` using `prefix`. */
        Node split(OneLf6 curr, Key!span prefix, Key!span key, size_t superPrefixLength) // TODO key here is a bit malplaced
        {
            assert(hasVariableKeyLength || curr.key.length == key.length);
            assert(hasVariableKeyLength || superPrefixLength + key.length == fixedKeyLength);

            Node next;
            if (curr.key.length == key.length) // balanced tree possible
            {
                switch (curr.key.length)
                {
                case 1:
                    if (prefix.length == 0)
                    {
                        freeNode(curr);
                        return Node(construct!(SixLf1)(curr.key)); // TODO removing parameter has no effect. why?
                    }
                    else if (prefix.length == 1)
                    {
                        assert(false, "Use P1Lf with single-length prefix and a maximum of 4 ");
                    }
                    else
                    {
                        if (willFail) { dln("prefix:", prefix); }
                        next = construct!(DenseLf1*)(prefix, false);
                    }
                    break;
                case 2:
                    freeNode(curr);
                    return Node(construct!(TriLf2)(curr.key));
                case 3:
                    freeNode(curr);
                    return Node(construct!(TwoLf3)(curr.key));
                default:
                    break;
                }
            }

            // default case
            if (!next) { next = construct!(DefaultBr)(prefix, false); }

            Node insertionNodeCurr;      // dummy
            auto superNext = insertAt(next, curr.key, superPrefixLength, insertionNodeCurr);
            assert(insertionNodeCurr); // assure that `curr` was reinserted
            freeNode(curr);   // remove old current

            return superNext;
        }

        /** Destructively expand `curr` and return it. */
        Node expand(TwoLf3 curr, size_t superPrefixLength)
        {
            assert(hasVariableKeyLength || superPrefixLength + curr.keyLength == fixedKeyLength);

            if (willFail) { dln("WILL FAIL: curr:", curr, " superPrefixLength:", superPrefixLength); }

            Node next;
            if (curr.keys.length == 1) // only one key
            {
                next = construct!(DefaultBr)(Ix[].init, false); // so no prefix
                Node insertionNodeCurr;
                next = insertAtBranch(next,
                                      curr.keys.at!0,
                                      superPrefixLength,
                                      insertionNodeCurr);
                assert(insertionNodeCurr);
            }
            else
            {
                auto next_ = construct!(DefaultBr)(curr.prefix, false);
                immutable prefixLength = next_.prefix.length;
                next = next_;
                // TODO functionize:
                foreach (key; curr.keys)
                {
                    Node insertionNodeCurr;
                    next = setSub(next, key[prefixLength],
                                  insertNew(key[prefixLength + 1 .. $], superPrefixLength, insertionNodeCurr),
                                  superPrefixLength);
                    assert(insertionNodeCurr);
                }
            }
            freeNode(curr);
            return next;
        }

        /** Destructively expand `curr` and return it. */
        Node expand(TriLf2 curr, size_t superPrefixLength)
        {
            assert(hasVariableKeyLength || superPrefixLength + curr.keyLength == fixedKeyLength);

            // TODO functionize:
            Node next;
            if (curr.keys.length == 1) // only one key
            {
                next = construct!(DefaultBr)(Ix[].init, false); // so no prefix
                Node insertionNodeCurr;
                next = insertAtBranch(next,
                                      curr.keys.at!0,
                                      superPrefixLength,
                                      insertionNodeCurr);
                assert(insertionNodeCurr);
            }
            else
            {
                auto next_ = construct!(DefaultBr)(curr.prefix, false);
                immutable prefixLength = next_.prefix.length;
                next = next_;
                // TODO functionize:
                foreach (key; curr.keys)
                {
                    Node insertionNodeCurr;
                    next = setSub(next, key[prefixLength], insertNew(key[prefixLength + 1 .. $], superPrefixLength, insertionNodeCurr),
                                  superPrefixLength);
                    assert(insertionNodeCurr);
                }
            }
            freeNode(curr);
            return next;
        }

        /** Destructively expand `curr` making room for `nextKey` and return it. */
        Node expand(SixLf1 curr, size_t superPrefixLength)
        {
            assert(hasVariableKeyLength || superPrefixLength + curr.keyLength == fixedKeyLength);

            auto next = construct!(DenseLf1*);
            foreach (const ixM; curr.keys)
            {
                assert(!next._keyBits[ixM]); // assert no duplicates in keys
                next._keyBits[ixM] = true;
            }
            freeNode(curr);
            return Node(next);
        }

    }

    /** Returns: `true` iff tree is empty (no elements stored). */
    bool empty() const @safe pure nothrow /* TODO @nogc */ { return !_root; }

    /** Returns: number of elements store. */
    size_t length() const @safe pure nothrow /* TODO @nogc */ { return _length; }

    private:

    /** Allocate (if pointer) and Construct a `Node`-type of value type `NodeType`
        using constructor arguments `args` of `Args`. */
    auto construct(NodeType, Args...)(Args args) @trusted
    {
        version(debugAllocations) { dln("constructing ", NodeType.stringof, " from ", args); }
        debug ++nodeCountsByIx[NodeType.stringof];
        static if (isPointer!NodeType)
        {
            debug ++_heapNodeAllocationBalance;
            import std.conv : emplace;
            return emplace(cast(NodeType)malloc((*NodeType.init).sizeof), args);
            // TODO ensure alignment of node at least that of NodeType.alignof
        }
        else
        {
            return NodeType(args);
        }
    }

    void freeNode(NodeType)(NodeType nt) @trusted
    {
        version(debugAllocations) { dln("freeing ", NodeType.stringof, " ", nt); }
        static if (isPointer!NodeType)
        {
            free(cast(void*)nt);  // TODO Allocator.free
            debug --_heapNodeAllocationBalance;
        }
        debug --nodeCountsByIx[NodeType.stringof];
    }

    @safe pure nothrow /* TODO @nogc */
    {
        void release(SparseLf1* curr)
        {
            freeNode(curr);
        }
        void release(DenseLf1* curr)
        {
            freeNode(curr);
        }

        void release(SparseBr4* curr)
        {
            foreach (sub; curr.subNodes[0 .. curr.subCount])
            {
                release(sub); // recurse
            }
            freeNode(curr);
        }

        void release(DenseBrM* curr)
        {
            foreach (sub; curr.subNodes[].filter!(sub => sub)) // TODO use static foreach
            {
                release(sub); // recurse
            }
            freeNode(curr);
        }

        void release(OneLf6 curr) { freeNode(curr); }
        void release(TwoLf3 curr) { freeNode(curr); }
        void release(TriLf2 curr) { freeNode(curr); }
        void release(SixLf1 curr) { freeNode(curr); }

        void release(Node curr)
        {
            version(debugAllocations) { dln("releasing Node ", curr); }
            final switch (curr.typeIx) with (Node.Ix)
            {
            case undefined: break; // ignored
            case ix_OneLf6: return release(curr.as!(OneLf6));
            case ix_TwoLf3: return release(curr.as!(TwoLf3));
            case ix_TriLf2: return release(curr.as!(TriLf2));
            case ix_SixLf1: return release(curr.as!(SixLf1));
            case ix_SparseLf1Ptr: return release(curr.as!(SparseLf1*));
            case ix_DenseLf1Ptr: return release(curr.as!(DenseLf1*));
            case ix_SparseBr4Ptr: return release(curr.as!(SparseBr4*));
            case ix_DenseBrMPtr: return release(curr.as!(DenseBrM*));
            }
        }

        bool isHeapAllocatedNode(Node curr) const
        {
            final switch (curr.typeIx) with (Node.Ix)
            {
            case undefined: return false;
            case ix_OneLf6: return false;
            case ix_TwoLf3: return false;
            case ix_TriLf2: return false;
            case ix_SixLf1: return false;
            case ix_SparseLf1Ptr: return true;
            case ix_DenseLf1Ptr: return true;
            case ix_SparseBr4Ptr: return true;
            case ix_DenseBrMPtr: return true;
            }
        }
    }

    /** Returns: `true` if all keys in tree are of fixed length/size, `false` otherwise. */
    bool hasFixedKeyLength() const @safe pure nothrow @nogc
    {
        return (fixedKeyLength !=
                fixedKeyLengthUndefined);
    }
    /** Returns: `true` if keys in tree may be of variable length/size, `false` otherwise. */
    bool hasVariableKeyLength() const @safe pure nothrow @nogc
    {
        return !hasFixedKeyLength;
    }

    /// Returns: number of nodes used in `this` tree. Should always equal `Stats.heapNodeCount`.
    pragma(inline) debug size_t heapNodeAllocationBalance() @safe pure nothrow /* TODO @nogc */
    {
        return _heapNodeAllocationBalance;
    }

    void print() @safe const
    {
        printAt(_root, 0);
    }

    void printAt(Node curr, size_t depth, uint subIx = uint.max) @safe const
    {
        import std.range : repeat;
        import std.stdio : write, writeln;

        if (!curr) { return; }

        foreach (const i; 0 .. depth) { write('-'); } // prefix
        if (subIx != uint.max)
        {
            import std.string : format;
            write(format("%.2X ", subIx));
        }

        final switch (curr.typeIx) with (Node.Ix)
        {
        case undefined: break;
        case ix_OneLf6:
            auto curr_ = curr.as!(OneLf6);
            writeln(typeof(curr_).stringof, "#", curr_.key.length, ": ", curr_.to!string);
            break;
        case ix_TwoLf3:
            auto curr_ = curr.as!(TwoLf3);
            writeln(typeof(curr_).stringof, "#", curr_.keys.length, ": ", curr_.keys);
            break;
        case ix_TriLf2:
            auto curr_ = curr.as!(TriLf2);
            writeln(typeof(curr_).stringof, "#", curr_.keys.length, ": ", curr_.keys);
            break;
        case ix_SixLf1:
            auto curr_ = curr.as!(SixLf1);
            writeln(typeof(curr_).stringof, "#", curr_.keys.length, ": ", curr_.keys);
            break;
        case ix_SparseLf1Ptr:
            auto curr_ = curr.as!(SparseLf1*);
            dln("TODO");
            break;
        case ix_DenseLf1Ptr:
            auto curr_ = curr.as!(DenseLf1*);
            write(typeof(*curr_).stringof, "#", curr_._keyBits.countOnes, (curr_.isKey ? " X" : " _"), " @", curr_);
            if (!curr_.prefix.empty) { write(" prefix=", curr_.prefix); }
            write(": ");

            // keys
            size_t ix = 0;
            bool other = false;
            foreach (const value;  curr_._keyBits[])
            {
                string s;
                if (value)
                {
                    if (other)
                    {
                        s ~= keySeparator;
                    }
                    else
                    {
                        other = true;
                    }
                    import std.string : format;
                    s ~= format("%.2X", ix);
                }
                ++ix;
                write(s);
            }

            writeln();
            break;
        case ix_SparseBr4Ptr:
            auto curr_ = curr.as!(SparseBr4*);
            write(typeof(*curr_).stringof, "#", curr_.subCount, (curr_.isKey ? " X" : " _"), " @", curr_);
            if (!curr_.prefix.empty) { write(" prefix=", curr_.prefix); }
            writeln(":");
            foreach (const i, const subNode; curr_.subNodes)
            {
                printAt(subNode, depth + 1, cast(uint)curr_.subIxs[i]);
            }
            break;
        case ix_DenseBrMPtr:
            auto curr_ = curr.as!(DenseBrM*);
            write(typeof(*curr_).stringof, "#", curr_.subCount, (curr_.isKey ? " X" : " _"), " @", curr_);
            if (!curr_.prefix.empty) { write(" prefix=", curr_.prefix); }
            writeln(":");
            foreach (const i, const subNode; curr_.subNodes)
            {
                printAt(subNode, depth + 1, cast(uint)i);
            }

            break;
        }
    }

    private:
    Node _root;                 ///< tree root node
    size_t _length = 0; ///< number of elements (keys or key-value-pairs) currently stored under `_root`
    immutable fixedKeyLength = fixedKeyLengthUndefined; ///< maximum length of key if fixed, otherwise 0
    enum fixedKeyLengthUndefined = 0;

    // debug stuff
    debug long _heapNodeAllocationBalance = 0;
    debug size_t[string] nodeCountsByIx;
    debug bool willFail;

}

/** Append statistics of tree under `Node` `sub.` into `stats`.
 */
static private void calculate(Value)(RawRadixTree!(Value).Node sub,
                                     ref RawRadixTree!(Value).Stats stats)
    @safe pure nothrow /* TODO @nogc */
{
    alias RT = RawRadixTree!(Value);
    ++stats.popByNodeType[sub.typeIx];

    with (RT.Node.Ix)
    {
        final switch (sub.typeIx)
        {
        case undefined: break;
        case ix_OneLf6: break; // TODO calculate()
        case ix_TwoLf3: break; // TODO calculate()
        case ix_TriLf2: break; // TODO calculate()
        case ix_SixLf1: break; // TODO calculate()
        case ix_SparseLf1Ptr: ++stats.heapNodeCount; sub.as!(RT.SparseLf1*).calculate(stats); break;
        case ix_DenseLf1Ptr: ++stats.heapNodeCount; sub.as!(RT.DenseLf1*).calculate(stats); break;
        case ix_SparseBr4Ptr: ++stats.heapNodeCount; sub.as!(RT.SparseBr4*).calculate(stats); break;
        case ix_DenseBrMPtr: ++stats.heapNodeCount; sub.as!(RT.DenseBrM*).calculate(stats); break;
        }
    }
}

/** Remap typed key `typedKey` to untype key of `Key`. */
static private Key!span remapKey(TypedKey)(in TypedKey typedKey)
    @trusted pure nothrow /* TODO @nogc */
    if (allSatisfy!(isTrieableKeyType, TypedKey))
{
    import std.traits : isArray;
    enum radix = 2^^span;     // branch-multiplicity, typically either 2, 4, 16 or 256
    alias Ix = Mod!radix;

    static if (isFixedTrieableKeyType!TypedKey)
    {
        const ukey = typedKey.bijectToUnsigned;

        enum nbits = 8*ukey.sizeof; // bitsize of ukey
        enum chunkCount = nbits/span; // number of chunks in ukey
        static assert(chunkCount*span == nbits, "Bitsize of TypedKey must be a multiple of span:" ~ span.stringof);

        KeyN!(span, TypedKey.sizeof) key;

        static if (span == 8)
        {
            foreach (bix; 0 .. chunkCount)
            {
                const bitShift = (chunkCount - 1 - bix)*span; // most significant bit chunk first (MSBCF)
                key[bix] = (ukey >> bitShift) & (radix - 1); // part of value which is also an index
            }
        }

        return key.dup; // TODO avoid this GC-allocation
    }
    else static if (isArray!TypedKey &&
                    is(Unqual!(typeof(TypedKey.init[0])) == char))
    {
        import std.string : representation;
        const ubyte[] key = typedKey.representation; // lexical byte-order
        return cast(Ix[])key;
    }
    else static if (is(Unqual!TypedKey == wstring))
    {
        const ushort[] rKey = typedKey.representation; // lexical byte-order.
        // TODO MSByte-order of elements in rKey for ordered access and good branching performance
        const ubyte[] key = (cast(const ubyte*)rKey.ptr)[0 .. rKey[0].sizeof * rKey.length]; // TODO @trusted functionize. Reuse existing Phobos function?
        return key;
    }
    else static if (is(Unqual!TypedKey == dstring))
    {
        const uint[] rKey = typedKey.representation; // lexical byte-order
        // TODO MSByte-order of elements in rKey for ordered access and good branching performance
        const ubyte[] key = (cast(const ubyte*)rKey.ptr)[0 .. rKey[0].sizeof * rKey.length]; // TODO @trusted functionize. Reuse existing Phobos function?
        return key;
    }
    else
    {
        static assert(false, "TODO Handle typed key " ~ TypedKey.stringof);
    }
}

/// Radix-Tree with key-type `TypedKey` and value-type `Value`.
struct RadixTree(TypedKey, Value)
    if (allSatisfy!(isTrieableKeyType, TypedKey))
{
    this(bool unusedDummy)      // TODO how do we get rid of the need for `unusedDummy`?
    {
        this.fixedKeyLength = isFixedTrieableKeyType!TypedKey ? TypedKey.sizeof : fixedKeyLengthUndefined;
    }

    /** Insert `key`.
        Returns: `true` if `key` wasn't previously inserted, `false` otherwise.
     */
    bool insert(in TypedKey key)
        @safe pure nothrow /* TODO @nogc */
    {
        _tree.Node insertionNode; // indicates that key was added
        _tree.insert(key.remapKey, insertionNode);
        _length += !insertionNode.isNull;
        return !insertionNode.isNull;
    }

    static if (!_tree.hasValue)
    {
        const nothrow:

        /** Returns: `true` if `key` is stored, `false` otherwise. */
        bool contains(in TypedKey typedKey)
        {
            return _tree.contains(typedKey.remapKey);
        }
    }

    static if (_tree.hasValue)
    {
        /** Insert `key`.
            Returns: `false` if key was previously already inserted, `true` otherwise.
        */
        bool insert(in TypedKey key, Value value)
        {
            _tree.Node insertionNode; // indicates that key was added
            _tree.insert(key.remapKey, insertionNode);
            if (insertionNode)
            {
                dln("TODO Set value:", value, " at insertionNode:", insertionNode);
            }
            _length += !insertionNode.isNull;
            return !insertionNode.isNull;
        }

        /** Returns: pointer to value if `key` is contained in set, null otherwise. */
        Value* contains(in TypedKey key) const
        {
            return null;
        }
    }

    /** Supports $(B `TypedKey` in `this`) syntax. */
    auto opBinaryRight(string op)(in TypedKey key) const if (op == "in") { return contains(key); }

    void print() @safe const
    {
        _tree.print();
    }

    private RawRadixTree!(Value) _tree;
    alias _tree this;
}
alias PatriciaTrie = RadixTree;
alias RadixTrie = RadixTree;
alias CompactPrefixTree = RadixTree;

/// Instantiator of set-version of `RadixTree` where value-type is `void` (unused).
auto radixTreeSet(Key)()
{
    static if (is(Key == string))
    {
        alias MutableKey = const(char)[];
    }
    else
    {
        alias MutableKey = Key;
    }
    return RadixTree!(MutableKey, void)(false);
}

/// Instantiator of map-version of `RadixTree` where value-type is `Value`.
auto radixTreeMap(Key, Value)() { return RadixTree!(Key, Value)(false); }

// @safe pure nothrow /* TODO @nogc */
unittest
{
    auto set = radixTreeSet!(ulong);

    assert(set.insert(0));
    assert(!set.insert(0));
    assert(set.heapNodeAllocationBalance == 1);

    assert(set.insert(1));
    assert(!set.insert(1));
    assert(set.heapNodeAllocationBalance == 1);

    foreach (const i; 2 .. 256)
    {
        assert(set.insert(i));
        assert(!set.insert(i));
        assert(set.heapNodeAllocationBalance == 1);
    }

    assert(set.insert(256));
    assert(!set.insert(256));

    assert(set.heapNodeAllocationBalance == 2);
}

@safe pure nothrow /* TODO @nogc */
unittest
{
    auto set = radixTreeSet!(ubyte);
    alias Set = typeof(set);

    foreach (const i; 0 .. Set.SixLf1.capacity)
    {
        assert(!set.contains(i));
        assert(set.insert(i));
        assert(!set.insert(i));
        assert(set.contains(i));
        assert(set.heapNodeAllocationBalance == 0);
        const rootRef = set._root.peek!(Set.SixLf1);
        assert(rootRef);
    }

    foreach (const i; Set.SixLf1.capacity .. 256)
    {
        assert(!set.contains(i));
        assert(set.insert(i));
        assert(!set.insert(i));
        assert(set.contains(i));
        assert(set.heapNodeAllocationBalance == 1);
        const rootRef = set._root.peek!(Set.DenseLf1*);
        assert(rootRef);
    }

    const rootRef = set._root.peek!(Set.DenseLf1*);
    assert(rootRef);

    const root = *rootRef;
    assert(!root.empty);
    assert(root.full);
}

@safe pure nothrow /* TODO @nogc */
unittest
{
    import std.meta : AliasSeq;
    foreach (T; AliasSeq!(ushort, uint))
    {
        auto set = radixTreeSet!(T);
        alias Set = typeof(set);

        assert(!set.contains(0));
        assert(set.insert(0));
        assert(!set.insert(0));
        assert(set.contains(0));
        assert(set.heapNodeAllocationBalance == 0);

        foreach (const i; 1 .. 256)
        {
            assert(!set.contains(i));
            assert(set.insert(i));
            assert(!set.insert(i));
            assert(set.contains(i));
        }

        assert(!set.contains(256));
        assert(set.insert(256));
        assert(!set.insert(256));
        assert(set.contains(256));
        assert(set.heapNodeAllocationBalance == 2);

        assert(!set.contains(257));
        assert(set.insert(257));
        assert(!set.insert(257));
        assert(set.contains(257));

        const rootRef = set._root.peek!(Set.DefaultBr);
        assert(rootRef);
        const root = *rootRef;
        assert(root.prefix.length == T.sizeof - 2);
    }
}

/** Calculate and print statistics of `tree`. */
void showStatistics(RT)(const ref RT tree) // why does `in`RT tree` trigger a copy ctor here
{
    import std.stdio : writeln;
    auto stats = tree.usageHistograms;
    writeln("DenseLf1 Population Histogram: ", stats.popHist_DenseLf1);
    writeln("SparseBr4 Population Histogram: ", stats.popHist_SparseBr4);
    writeln("DenseBrM Population Histogram: ", stats.popHist_DenseBrM);
    writeln("Population By Node Type: ", stats.popByNodeType);

    // these should be zero
    writeln("Number of SparseBr4 with OneLf6-0 only subNodes: ", stats.allOneLf60CountOfSparseBr4);
    writeln("Number of DenseBrM with OneLf6-0 only subNodes: ", stats.allOneLf60CountOfDenseBrM);

    size_t totalBytesUsed = 0;
    foreach (RT.Node.Ix ix, pop; stats.popByNodeType) // TODO use stats.byPair when added to typecons_ex.d
    {
        size_t bytesUsed = 0;
        with (RT.Node.Ix)
        {
            final switch (ix)
            {
            case undefined: break;
            case ix_OneLf6: bytesUsed = pop*RT.OneLf6.sizeof; break;
            case ix_TwoLf3: bytesUsed = pop*RT.TwoLf3.sizeof; break;
            case ix_TriLf2: bytesUsed = pop*RT.TriLf2.sizeof; break;
            case ix_SixLf1: bytesUsed = pop*RT.SixLf1.sizeof; break;
            case ix_SparseLf1Ptr: bytesUsed = pop*RT.SparseLf1.sizeof; totalBytesUsed += bytesUsed; break;
            case ix_DenseLf1Ptr: bytesUsed = pop*RT.DenseLf1.sizeof; totalBytesUsed += bytesUsed; break;
            case ix_SparseBr4Ptr: bytesUsed = pop*RT.SparseBr4.sizeof; totalBytesUsed += bytesUsed; break;
            case ix_DenseBrMPtr: bytesUsed = pop*RT.DenseBrM.sizeof; totalBytesUsed += bytesUsed; break;
            }
        }
        if (bytesUsed)
        {
            writeln(pop, " number of ", ix, " uses ", bytesUsed/1e6, " megabytes");
        }
    }
    writeln("Tree uses ", totalBytesUsed/1e6, " megabytes");
}

/// Create a set of words from /usr/share/dict/words
unittest
{
    immutable path = "/usr/share/dict/words";
    import std.stdio : File, writeln;
    auto set = radixTreeSet!(string);
    assert(set.empty);
    size_t count = 0;
    foreach (const line; File(path).byLine())
    {
        import std.algorithm.searching : endsWith;
        import std.range : empty;
        if (!line.empty &&
            !line.endsWith(`'s`)) // skip genitive forms
        {
            if (line.length <= 15)
            {
                // version(print) dln(line);
                assert(!set.contains(line));
                assert(set.insert(line));
                assert(set.contains(line));
                ++count;
            }
        }
    }
    // version(print) dln("Added ", count, " words from ", path);
    version(print) set.showStatistics();
    // version(print) set.print();
}

/** Generate `count` number of random unique strings of minimum length 1 and
    maximum length `capacity`.
 */
private static auto randomUniqueStrings(size_t count = 1_000_000,
                                        uint capacity = 16)
    @trusted
{
    import std.random : Random, uniform;
    auto gen = Random();

    bool[string] stringSet;  // set of strings using D's builtin associative array
    while (stringSet.length < count)
    {
        const length = uniform(1, capacity, gen);
        auto key = new char[length];
        foreach (ix; 0 .. length)
        {
            key[ix] = cast(char)('a' + 0.uniform(26, gen));
        }
        stringSet[key[].idup] = true;
    }
    import std.array : array;
    return stringSet.byKey.array;
}

auto checkString(Keys...)()
    if (Keys.length >= 1)
{
    import std.range : iota;
    foreach (Key; Keys)
    {
        auto set = radixTreeSet!(Key);
        alias Set = set;
        assert(set.empty);

        foreach (const key; randomUniqueStrings)
        {
            // dln(`key:`, key);
            import std.conv : to;
            immutable failMessage = `Failed for key: "` ~ key.to!string ~ `"`;

            import std.string : representation;
            // set.willFail = (key == `iex`);
            // if (set.willFail) { set.print(); }

            // if (set.willFail) dln(`key:`, key, ` (`, key.representation, `)`);

            // if (set.willFail) dln(`assert(!set.contains(key)) ################################ : `);
            assert(!set.contains(key), failMessage);

            // if (set.willFail) dln(`assert(set.insert(key)) ################################ : `);
            assert(set.insert(key), failMessage);

            // if (set.willFail) dln(`assert(set.contains(key)) ################################ :`);
            assert(set.contains(key), failMessage);

            // if (set.willFail) dln(`assert(!set.insert(key)) ################################ :`);
            assert(!set.insert(key), failMessage);

            // if (set.willFail) dln(`assert(set.contains(key)) ################################ :`);
            assert(set.contains(key), failMessage);
        }
    }
}

@safe pure /* TODO @nogc */
unittest
{
    checkString!(string);
}

/// Check correctness when span is `span` and for each `Key` in `Keys`.
auto checkNumeric(Keys...)()
    if (Keys.length >= 1)
{
    import std.range : iota;
    foreach (const it; 0.iota(1))
    {
        import std.algorithm : equal;
        struct TestValueType { int i; float f; char ch; }
        alias Value = TestValueType;
        import std.meta : AliasSeq;
        foreach (Key; Keys)
        {
            dln("Key: ", Key.stringof);
            alias Tree = radixTreeSet!(Key);
            auto set = Tree;
            assert(set.hasFixedKeyLength == isFixedTrieableKeyType!Key);
            assert(set.empty);

            static assert(!set.hasValue);

            import std.algorithm : min, max;

            const useContains = true;

            static if (isIntegral!Key ||
                       isFloatingPoint!Key)
            {
                static if (isIntegral!Key)
                {
                    const low = max(Key.min, -98900); // chosen to minimize number of lines of debug output before bug in contains happens
                    const high = min(Key.max, 100_000);
                    const length = high - low + 1;
                }
                else static if (isFloatingPoint!Key)
                {
                    const low = -100_000;
                    const high = 100_000;
                    const length = high - low + 1;
                }

                size_t cnt = 0;
                foreach (const uk; low.iota(high + 1))
                {
                    const Key key = cast(Key)uk;
                    // debug set.willFail = (key == -32639);
                    if (useContains)
                    {
                        if (set.willFail) dln("before check no contains yet");
                        assert(!set.contains(key)); // key should not yet be in set
                        assert(key !in set);        // alternative syntax
                    }

                    if (set.willFail) dln("before first insert()");
                    assert(set.insert(key));  // insert new value returns `true` (previously not in set)
                    if (useContains)
                    {
                        if (set.willFail) dln("before check passing contains()");
                        assert(set.contains(key)); // key should now be in set
                    }
                    if (set.willFail) dln("before second insert()");
                    assert(!set.insert(key)); // reinsert same value returns `false` (already in set)

                    if (useContains)
                    {
                        assert(set.contains(key)); // key should now be in set
                        assert(key in set);        // alternative syntax
                        if (key != Key.max)        // except last value
                        {
                            assert(!set.contains(cast(Key)(key + 1))); // next key is not yet in set
                        }
                    }
                    ++cnt;
                }
                assert(set.length == length);
            }
            else
            {
                static assert(false, `Handle type: "` ~ Key.stringof ~ `"`);
            }

            auto map = radixTreeMap!(Key, Value);
            assert(map.hasFixedKeyLength == isFixedTrieableKeyType!Key);
            static assert(map.hasValue);

            map.insert(Key.init, Value.init);
        }
    }
}

/// Benchmark performance and memory usage when span is `span`.
void benchmark()()
{
    import core.thread : sleep;
    import std.range : iota;
    import std.stdio : writeln;

    import std.algorithm : equal;
    struct TestValueType { int i; float f; char ch; }
    alias Value = TestValueType;
    import std.meta : AliasSeq;
    foreach (Key; AliasSeq!(uint)) // just benchmark uint for now
    {
        auto set = radixTreeSet!(Key);
        alias Set = set;
        assert(set.empty);

        static assert(!set.hasValue);

        import std.conv : to;
        import std.datetime : StopWatch, AutoStart, Duration;

        enum n = 10_000_000;

        import std.array : array;
        import std.random : randomShuffle;

        const useUniqueRandom = false;

        // TODO functionize to randomIota in range_ex.d
        auto randomIotaSamples = 0.iota(n).array; randomIotaSamples.randomShuffle;

        import std.range : generate, take;
        import std.random : uniform;
        auto randomSamples = generate!(() => uniform!Key).take(n);

        {
            auto sw = StopWatch(AutoStart.yes);

            foreach (Key k; randomSamples)
            {
                if (useUniqueRandom)
                {
                    assert(set.insert(k));
                }
                else
                {
                    set.insert(k);
                }

                /* second insert of same key should always return `false` to
                   indicate that key was already stored */
                static if (false) { assert(!set.insert(k)); }
            }

            writeln("trie: Added ", n, " ", Key.stringof, "s of size ", n*Key.sizeof/1e6, " megabytes in ", sw.peek().to!Duration, ". Sleeping...");

            set.showStatistics();

            sleep(2);
            writeln("Sleeping done");
        }

        {
            auto sw = StopWatch(AutoStart.yes);
            bool[int] aa;

            foreach (Key k; randomSamples) { aa[k] = true; }

            writeln("D-AA: Added ", n, " ", Key.stringof, "s of size ", n*Key.sizeof/1e6, " megabytes in ", sw.peek().to!Duration, ". Sleeping...");
            sleep(2);
            writeln("Sleeping done");
        }

        // version(print)
        set.print();

        auto map = radixTreeMap!(Key, Value);
        assert(map.empty);
        static assert(map.hasValue);

        map.insert(Key.init, Value.init);
    }
}

/// leak test
version(enterSingleInfiniteMemoryLeakTest)
@safe pure nothrow /* TODO @nogc */
unittest
{
    while (true)
    {
        checkNumeric!(float);
    }
}

@safe pure nothrow /* TODO @nogc */
unittest
{
    checkNumeric!(float, double,
                  long, int, short, byte,
                  ulong, uint, ushort, ubyte);
}

auto testPrint(uint span, Keys...)()
    if (Keys.length >= 1)
{
    import std.range : iota;
    foreach (const it; 0.iota(1))
    {
        foreach (Key; Keys)
        {
            dln("Key: ", Key.stringof);
            alias Tree = radixTreeSet!(Key);
            auto set = Tree;

            import std.algorithm : min, max;

            static if (isIntegral!Key)
            {
                const low = max(Key.min, -100_000);
                const high = min(Key.max, 100_000);
            }
            else static if (isFloatingPoint!Key)
            {
                const low = -100_000;
                const high = 100_000;
            }

            foreach (const uk; low.iota(high + 1))
            {
                const Key key = cast(Key)uk;
                assert(set.insert(key));  // insert new value returns `true` (previously not in set)
                assert(!set.insert(key)); // reinsert same value returns `false` (already in set)
            }

            version(print) set.print();
        }
    }
}

version(print) @safe unittest
{
    testPrint!(8,
               double, float,
               long, int, short, byte,
               ulong, uint, ushort, ubyte);
}

/** Static Iota.
    TODO Move to Phobos std.range.
 */
template iota(size_t from, size_t to)
    if (from <= to)
{
        alias iota = iotaImpl!(to - 1, from);
}
private template iotaImpl(size_t to, size_t now)
{
    import std.meta : AliasSeq;
    static if (now >= to) { alias iotaImpl = AliasSeq!(now); }
    else                  { alias iotaImpl = AliasSeq!(now, iotaImpl!(to, now + 1)); }
}

version(benchmark)
void main(string[] args)
{
    benchmark;
}
