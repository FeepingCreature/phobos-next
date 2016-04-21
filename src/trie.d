/** Tries and PrefixTrees.

    See also: https://en.wikipedia.org/wiki/Trie

    TODO if `Value` is a `isScalarType` store it in Value[M]
    TODO if `Value` is a `bool` store it in bitset

    TODO Andrei!: Provide `opIndex` and make `opSlice` for set-case (`Value` is `void`) return `SortedRange`

    TODO Andrei!: Provide RandomAccess `opIndex` and `opSlice`! for variable-length keys aswell?

    TODO Andrei!: Provide in operator for fixed-length keys!?

    TODO Add RadixTreeRange.{front,popFront,empty}. Reuse RefCounted reference
    to _rootPtr. Add checks with `isSorted`.

    TODO Name members so they indicate that range isSorted.

    TODO Andrei!: Name members to indicate complexity

    TODO Benchmark `contains()` and compare it to to builtin AAs.in.

    TODO Extend bitop_ex.d with {set,get}{Bit,Qit,Bytes} and reuse

    TODO RadixTree: Assigning a void pointer to a class

    TODO Should opBinaryRight return void* instead of bool for set-case?

    TODO Replace
    - if (auto currBranchM = currPtr.peek!BranchM)
    - else if (const currLeafM = currPtr.peek!LeafM)
    with some compacter logic perhaps using mixins or pattern matching using
    switch-case on internally store type in `VariantPointer`.

    I've just started working on a RadixTree implementation in D here:

    https://github.com/nordlow/phobos-next/blob/master/src/trie.d

    The current solution is very generic as it CT-specializes to either a
    `RadixTreeMap` and `RadixTreeSet`. These provide very memory-efficient
    replacements for a `HashMap` and a `HashSet`.

    Each radix-tree branching contains 2^^radix pointers to the next
    sub-branching. In the RadixTreeSet case I want these pointers to also be
    able to contain special "codes" with the following meanings

    0x1: *only* value associated with sub-branching is set.

    0xFFFFFFFFFFFFFFFF: all values values in this sub-branch are set.
 */
module trie;

import std.traits : isIntegral, isSomeChar, isSomeString, isScalarType, isArray, allSatisfy, anySatisfy;
import std.range : isInputRange, ElementType;

import variant_pointer : VariantPointer;

version = benchmark;

import dbg : dln;

enum isFixedTrieableKeyType(T) = isScalarType!T;

enum isTrieableKeyType(T) = (isFixedTrieableKeyType!T ||
                             (isInputRange!T &&
                              isFixedTrieableKeyType!(ElementType!T)));

/** Defines how the entries in each `BranchM` are packed. */
enum NodePacking
{
    just1Bit,

    sparse2Bit,
    denseBit,

    sparse4Bit,
    dense4Bit,

    sparse8Bit,
    dense8Bit,
}

extern(C) pure nothrow @system @nogc
{
    void* malloc(size_t size);
    void* calloc(size_t nmemb, size_t size);
    void* realloc(void* ptr, size_t size);
    void free(void* ptr);
}

/** Radix Tree storing keys of type `Key`.

    In set-case (Value is Void) this containers is especially suitable for
    representing a set of 32 or 64 integers/pointers.

    See also: https://en.wikipedia.org/wiki/Radix_tree
 */
struct RadixTree(Key,
                 Value,
                 size_t radix = 4) // radix in number of bits, typically either 1, 2, 4 or 8
    if (allSatisfy!(isTrieableKeyType, Key))
{
    import std.meta : AliasSeq, staticMap;
    import std.typecons : ConstOf;

    static assert(radix <= 32, "Radix is currently limited to 32"); // TODO adjust?
    static assert(radix <= 8*Key.sizeof, "Radix must be less than or equal to Key bit-precision"); // TODO Use strictly less than: radix < ... instead?

    import std.algorithm : all;
    import bitop_ex : UnsignedOfSameSizeAs;

    enum isSet = is(Value == void); // `true` if this tree is a set
    enum isMap = !isSet;        // `true` if this tree is a map

    enum M = 2^^R;     // branch-multiplicity, typically either 2, 4, 16 or 256
    enum chunkMask = M - 1;

    alias order = M;   // tree order
    alias R = radix;

    /// Tree depth.
    enum maxDepth = 8*Key.sizeof / R;

    /// `true` if tree has fixed a key of fixed length and in turn a tree of fixed max depth.
    enum isFixed = isFixedTrieableKeyType!Key;

    /// `true` if tree has binary branch.
    enum isBinary = R == 2;

    /** Node types. */
    alias NodeTypes = AliasSeq!(BranchM, LeafM);

    /** Mutable node. */
    alias NodePtr = VariantPointer!(NodeTypes);
    /** Constant node. */
    alias ConstNodePtr = VariantPointer!(staticMap!(ConstOf, NodeTypes));

    alias Nexts = NodePtr[M];

    alias BranchUsageHistogram = size_t[M];

    /** Non-bottom branch node containing densly packed array of `M` number of
        pointers to sub-`BranchM`s or `Leaf`s.
    */
    static private struct BranchM
    {
        /// Indicates that only child at this index is occupied.
        static immutable oneSet = cast(typeof(this)*)1UL;

        /// Indicates that all children of `this` branch are occupied (fixed-sized Keys).
        static if (isFixed)
        {
            static immutable allSet = cast(typeof(this)*)size_t.max;
        }

        Nexts nexts;

        /** Returns: depth of tree at this branch. */
        // size_t linearDepth() @safe pure nothrow const
        // {
        //     // TODO replace with fold when switching to 2.071
        //     import std.algorithm : map, reduce, max;
        //     return reduce!max(0UL, nexts[].map!(next => (next.peek!(typeof(this)) == oneSet ? 1UL :
        //                                                  next ? 1 + next.linearDepth :
        //                                                  0UL)));
        // }

        /** Returns: depth of tree at this branch. */
        void calculate(ref BranchUsageHistogram hist) @safe pure nothrow const
        {
            import std.algorithm : count, filter;
            size_t nzcnt = 0; // number of non-zero branches
            foreach (next; nexts[].filter!(next => next))
            {
                ++nzcnt;
                if (const nextBranchM = next.peek!BranchM)
                {
                    nextBranchM.calculate(hist);
                }
                else if (const nextLeafM = next.peek!LeafM)
                {
                    nextLeafM.calculate(hist);
                }
                else if (next)
                {
                    assert(false, "Unknown type of non-null pointer");
                }
            }
            ++hist[nzcnt - 1];
        }

        static if (!isFixed)        // variable length keys only
        {
            LeafM nextOccupations; // if i:th bit is set key (and optionally value) associated with next[i] is also defined
            static if (isMap)
            {
                Value value;
            }
        }
    }

    /** Bottom-most leaf node of `RadixTree`-set storing `M` number of densly packed
        keys of fixed-length type `Key`.
    */
    static private struct LeafM
    {
        void calculate(ref BranchUsageHistogram hist) @safe pure const
        {
            import std.range : iota;
            foreach (const i; 0.iota(M))
            {
                ++hist[i];
            }
        }

        import bitset : BitSet;
        private BitSet!M _bits; // if i:th bit is set corresponding next is set

        alias _bits this;

        static if (isMap)
        {
            Value[M] values;
        }
    }

    /// Get depth of tree.
    // size_t depth() @safe pure nothrow const
    // {
    //     return _rootPtr !is null ? _rootPtr.linearDepth : 0;
    // }

    BranchUsageHistogram branchUsageHistogram() const
    {
        typeof(return) hist;
        // TODO reuse rangeinterface when made available
        if (const branchM = _rootPtr.peek!BranchM)
        {
            branchM.calculate(hist);
        }
        else if (const nextLeafM = _rootPtr.peek!LeafM)
        {
            assert(false, "TODO");
        }
        else if (_rootPtr)
        {
            assert(false, "Unknown type of non-null pointer");
        }
        return hist;
    }

    this(this)
    {
        if (!_rootPtr.ptr) return;
        auto oldRootPtr = _rootPtr;
        makeRoot;
        auto currPtr = oldRootPtr;
        while (currPtr)
        {
            // TODO iterative or recursive?
        }
        assert(false, "TODO calculate tree by branches and leafs and make copies of them");
    }

    ~this()
    {
        if (_rootPtr) { release(_rootPtr); }
        debug assert(_branchCount == 0);
    }

    /** Get chunkIndex:th chunk of `radix` number of bits. */
    auto bitsChunk(uint chunkIndex)(Key key) const @trusted pure nothrow
    {
        // calculate bit shift to current chunk
        static if (isIntegral!Key ||
                   isSomeChar!Key) // because top-most bit in ASCII coding (char) is often sparse
        {
            /* most signficant bit chunk first because integers are
               typically more sparse in more significant bits */
            enum shift = (maxDepth - 1 - chunkIndex)*R;
        }
        else
        {
            // default to most signficant bit chunk first
            enum shift = (maxDepth - 1 - chunkIndex)*R;
            // enum shift = chunkIndex*R; // least significant bit first
        }

        const u = *(cast(UnsignedOfSameSizeAs!Key*)(&key)); // TODO functionize and reuse here and in intsort.d
        const uint chunkBits = (u >> shift) & chunkMask; // part of value which is also an index
        static assert(radix <= 8*chunkBits.sizeof, "Need more precision in chunkBits");

        assert(chunkBits < M); // extra range check
        return chunkBits;
    }

    static if (isSet)
    {
        /** Insert `key`.
            Returns: `false` if key was previously already inserted, `true` otherwise.
        */
        bool insert(Key key)
        {
            makeRoot;

            auto currPtr = _rootPtr;
            foreach (ix; iota!(0, maxDepth)) // NOTE unrolled/inlined compile-time-foreach chunk index
            {
                const chunkBits = bitsChunk!(ix)(key);

                enum isLast = ix + 1 == maxDepth; // if this is the last chunk
                static if (!isLast) // this is not the last
                {
                    if (auto currBranchM = currPtr.peek!BranchM)
                    {
                        if (!currBranchM.nexts[chunkBits]) // if branch not yet visited
                        {
                            currBranchM.nexts[chunkBits] = allocateNode!BranchM; // create it
                        }
                        currPtr = currBranchM.nexts[chunkBits]; // and visit it
                    }
                    else if (auto currLeafM = currPtr.peek!LeafM)
                    {
                        assert(false, "TODO");
                    }
                    else if (currPtr)
                    {
                        assert(false, "Unknown type of non-null pointer");
                    }
                }
                else            // this is the last iteration
                {
                    if (auto currBranchM = currPtr.peek!BranchM)
                    {
                        if (!currBranchM.nexts[chunkBits])
                        {
                            currBranchM.nexts[chunkBits] = BranchM.oneSet; // tag this as last
                            return true; // a new value was inserted
                        }
                        else
                        {
                            static if (isFixedTrieableKeyType!Key)
                            {
                                assert(currBranchM.nexts[chunkBits].peek!BranchM == BranchM.oneSet);
                                return false; // value already set
                            }
                            else
                            {
                                dln("TODO");
                                // TODO test this
                                if (currPtr.isOccupied)
                                {
                                    return false;
                                }
                                else
                                {
                                    currPtr.isOccupied = false;
                                    return true;
                                }
                            }
                        }
                    }
                    else if (auto currLeafM = currPtr.peek!LeafM)
                    {
                        assert(false, "TODO");
                    }
                    else if (currPtr)
                    {
                        assert(false, "Unknown type of non-null pointer");
                    }
                }
            }
            assert(false, "End of function should be reached");
        }

        /** Returns: `true` if key is contained in set, `false` otherwise. */
        bool contains(Key key) const nothrow
        {
            if (!_rootPtr) { return false; }

            NodePtr currPtr = _rootPtr;
            foreach (ix; iota!(0, maxDepth)) // NOTE unrolled/inlined compile-time-foreach chunk index
            {
                const chunkBits = bitsChunk!(ix)(key);
                if (auto currBranchM = currPtr.peek!BranchM)
                {
                    if (!currBranchM.nexts[chunkBits])
                    {
                        return false;
                    }
                    else
                    {
                        static if (isFixedTrieableKeyType!Key)
                        {
                            if (currBranchM.nexts[chunkBits].peek!BranchM == BranchM.oneSet)
                            {
                                return true;
                            }
                        }
                        else
                        {
                            if (currBranchM.isOccupied)
                            {
                                return false;
                            }
                            else
                            {
                                currBranchM.isOccupied = false;
                                return true;
                            }
                        }
                        currPtr = currBranchM = currBranchM.nexts[chunkBits].peek!BranchM;
                    }
                }
                else if (const currLeafM = currPtr.peek!LeafM)
                {
                    assert(false, "TODO");
                }
                else if (currPtr)
                {
                    assert(false, "Unknown type of non-null pointer");
                }
            }
            return false;
        }

	/** Supports $(B `Key` in `this`) syntax. */
	bool opBinaryRight(string op)(Key key) const nothrow
            if (op == "in")
	{
            return contains(key);
	}

    }
    else
    {
        /** Insert `key`.
            Returns: `false` if key was previously already inserted, `true` otherwise.
        */
        bool insert(Key key, Value value)
        {
            makeRoot;
            return false;
        }

        /** Returns: pointer to value if `key` is contained in set, null otherwise. */
        Value* contains(Key key) const
        {
            return null;
        }
    }

    private:

    NodeType* allocateNode(NodeType)() @trusted
    {
        NodeType* node = cast(typeof(return))calloc(1, NodeType.sizeof);
        debug ++_branchCount;
        assert(node.nexts[].all!(x => !x));
        return node;
    }

    void release(BranchM* currPtr) pure nothrow
    {
        import std.algorithm : count, filter;
        foreach (next; currPtr.nexts[].filter!(next => next))
        {
            if (auto nextBranchM = next.peek!BranchM)
            {
                if (nextBranchM != BranchM.oneSet)
                {
                    release(nextBranchM);  // recurse
                }
            }
            else if (auto nextLeafM = next.peek!LeafM)
            {
                assert(false, "TODO");
            }
            else if (currPtr)
            {
                assert(false, "Unknown type of non-null pointer");
            }
        }
        deallocateNode(currPtr);
    }

    void release(NodePtr currPtr) pure nothrow
    {
        if (auto nextBranchM = currPtr.peek!BranchM)
        {
            if (nextBranchM != BranchM.oneSet)
            {
                release(nextBranchM);  // recurse
            }
        }
        else if (auto nextLeafM = currPtr.peek!LeafM)
        {
            assert(false, "TODO");
        }
        else if (currPtr)
        {
            assert(false, "Unknown type of non-null pointer");
        }
    }

    void deallocateNode(NodeType)(NodeType* branch) @trusted
    {
        debug --_branchCount;
        free(cast(void*)branch);  // TODO Allocator.free
    }

    void makeRoot()
    {
        if (!_rootPtr.ptr) { _rootPtr = allocateNode!BranchM; }
    }

    /// Returns: number of branches used in `this` tree.
    debug size_t branchCount() @safe pure nothrow @nogc { return _branchCount; }

    private NodePtr _rootPtr;
    debug size_t _branchCount = 0;
}
alias RadixTrie = RadixTree;
alias CompactPrefixTree = RadixTree;

/// Instantiator of radix tree set.
auto radixTreeSet(Key, size_t radix = 4)() { return RadixTree!(Key, void, radix)(); }

/// Instantiator of radix tree map.
auto radixTreeMap(Key, Value, size_t radix = 4)() { return RadixTree!(Key, Value, radix)(); }

auto check()
{
    import std.range : iota;
    foreach (const it; 0.iota(1))
    {
        import std.algorithm : equal;
        struct TestValueType { int i; float f; string s; }
        alias Value = TestValueType;
        import std.meta : AliasSeq;
        foreach (Key; AliasSeq!(uint))
        {
            auto set = radixTreeSet!(Key);

            static assert(set.isSet);

            foreach (Key k; 0.iota(512))
            {
                assert(!set.contains(k));

                assert(k !in set);

                assert(set.insert(k)); // insert new value returns `true`
                assert(!set.insert(k)); // reinsert same value returns `false`
                assert(!set.insert(k)); // reinsert same value returns `false`

                assert(set.contains(k));
                assert(k in set);
                // assert(set.depth == set.maxDepth);

                assert(!set.contains(k + 1)); // next is yet inserted
            }

            // debug assert(set.branchCount == 40);

            dln("DONE testing!");

            auto map = radixTreeMap!(Key, Value);
            static assert(map.isMap);

            map.insert(Key.init, Value.init);
        }
    }
}

@safe pure nothrow unittest
{
    check();
}

/// Performance benchmark
version(benchmark) unittest
{
    import core.thread : sleep;
    import std.range : iota;
    foreach (const it; 0.iota(1))
    {
        import std.algorithm : equal;
        struct TestValueType { int i; float f; string s; }
        alias Value = TestValueType;
        import std.meta : AliasSeq;
        foreach (Key; AliasSeq!(uint))
        {
            auto set = radixTreeSet!(Key);

            static assert(set.isSet);

            import std.conv : to;
            import std.datetime : StopWatch, AutoStart, Duration;
            enum n = 10_000_000;
            auto sw = StopWatch(AutoStart.yes);
            foreach (Key k; 0.iota(n))
            {
                assert(set.insert(k)); // insert new value returns `true`
            }

            dln("Added ", n, " ", Key.stringof, "s of size ", n*Key.sizeof/1e6, " megabytes in ", sw.peek().to!Duration, ". Sleeping...");
            dln("BranchUsageHistogram: ", set.branchUsageHistogram);
            sleep(5);
            dln("Sleeping done");

            auto map = radixTreeMap!(Key, Value);
            static assert(map.isMap);

            map.insert(Key.init, Value.init);
        }
    }
}

/** Static Iota.
    TODO Move to Phobos.
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
