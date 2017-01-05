module unique_range;

version(unittest)
{
    import dbgio : dln;
    import std.algorithm.comparison : equal;
}

import std.range.primitives : hasLength;

/** Unique range (slice) owning its source of `Source`.

    Copy construction is disabled, explicit copying is instead done through
    member `.dup`.
 */
struct UniqueRange(Source)
    if (hasLength!Source)       // TODO use traits `isArrayContainer` checking fo
{
    import std.range : ElementType;
    alias Slice = typeof(Source.init[]);
    alias E = ElementType!Slice;

    @disable this(this);        // not intended to be copied

    pragma(inline) @safe pure nothrow @nogc:

    /// Construct from `source`.
    this(Source source)
    {
        import std.algorithm.mutation : move;
        _frontIx = 0;
        _backIx = source.length;
        _source = move(source); // TODO remove `move` when compiler does it for us
    }

    /// Is `true` if range is empty.
    @property bool empty() const { return _frontIx == _backIx; }

    /// Front element.
    @property ref inout(E) front() inout return // TODO scope
    {
        assert(!empty);
        return _source[_frontIx];
    }

    /// Back element.
    @property ref inout(E) back() inout return // TODO scope
    {
        assert(!empty);
        return _source[_backIx - 1];
    }

    /// Pop front element.
    @property void popFront()
    {
        assert(!empty);
        _frontIx = _frontIx + 1;
    }

    /// Pop back element.
    @property void popBack()
    {
        assert(!empty);
        _backIx = _backIx - 1;
    }

    /// Returns: shallow duplicate of `this`.
    version(none)               // TODO make compile
    {
        @property UniqueRange dup() const
        {
            return typeof(this)(_frontIx, _backIx, _source.dup);
        }
    }

    /// Length.
    @property size_t length() const { return _backIx - _frontIx; }

private:
    size_t _frontIx;             // offset to front element
    size_t _backIx;
    Source _source; // typically a non-reference count container type with disable copy construction
}

/** Returns: A range of `Source` that owns its `source` (data container).
    Similar to Rust's `into_iter`.
 */
UniqueRange!Source intoUniqueRange(Source)(Source source)
    if (hasLength!Source)
{
    import std.algorithm.mutation : move;
    return typeof(return)(move(source)); // TODO remove `move` when compiler does it for us
}

/// A generator is a range which owns its state (typically a non-reference counted container).
alias intoGenerator = intoUniqueRange;

/// basics
@safe pure nothrow @nogc unittest
{
    import std.range.primitives : isInputRange, isIterable;
    import array_ex : SA = UncopyableArray;
    alias C = SA!int;

    auto cs = C.withElements(11, 13, 15, 17).intoUniqueRange;

    static assert(isInputRange!(typeof(cs)));
    static assert(isIterable!(typeof(cs)));

    assert(!cs.empty);
    assert(cs.length == 4);
    assert(cs.front == 11);
    assert(cs.back == 17);

    cs.popFront();
    assert(cs.length == 3);
    assert(cs.front == 13);
    assert(cs.back == 17);

    cs.popBack();
    assert(cs.length == 2);
    assert(cs.front == 13);
    assert(cs.back == 15);

    cs.popFront();
    assert(cs.length == 1);
    assert(cs.front == 15);
    assert(cs.back == 15);

    cs.popBack();
    assert(cs.length == 0);
    assert(cs.empty);
}

/// combined with Phobos ranges
@safe pure nothrow unittest
{
    import array_ex : SA = UncopyableArray;
    alias C = SA!int;
    assert(C.withElements(11, 13, 15, 17)
            .intoUniqueRange()
            .filterUnique!(_ => _ != 11)
            .mapUnique!(_ => 2*_)
            .equal([2*13, 2*15, 2*17]));
}

import std.functional : unaryFun;

template mapUnique(fun...) if (fun.length >= 1)
{
    import std.algorithm.mutation : move;
    import std.range.primitives : isInputRange, ElementType;
    import std.traits : Unqual;

    auto mapUnique(Range)(Range r) if (isInputRange!(Unqual!Range))
    {
        import std.meta : AliasSeq, staticMap;

        alias RE = ElementType!(Range);
        static if (fun.length > 1)
        {
            import std.functional : adjoin;
            import std.meta : staticIndexOf;

            alias _funs = staticMap!(unaryFun, fun);
            alias _fun = adjoin!_funs;

            // Once DMD issue #5710 is fixed, this validation loop can be moved into a template.
            foreach (f; _funs)
            {
                static assert(!is(typeof(f(RE.init)) == void),
                    "Mapping function(s) must not return void: " ~ _funs.stringof);
            }
        }
        else
        {
            alias _fun = unaryFun!fun;
            alias _funs = AliasSeq!(_fun);

            // Do the validation separately for single parameters due to DMD issue #15777.
            static assert(!is(typeof(_fun(RE.init)) == void),
                "Mapping function(s) must not return void: " ~ _funs.stringof);
        }

        return MapUniqueResult!(_fun, Range)(move(r));
    }
}

private struct MapUniqueResult(alias fun, Range)
{
    import std.traits : Unqual, isCopyable;
    import std.range.primitives : isInputRange, isForwardRange, isBidirectionalRange, isRandomAccessRange, isInfinite, hasSlicing;
    import std.algorithm.mutation : move;

    alias R = Unqual!Range;
    R _input;

    static if (isBidirectionalRange!R)
    {
        @property auto ref back()()
        {
            assert(!empty, "Attempting to fetch the back of an empty mapUnique.");
            return fun(_input.back);
        }

        void popBack()()
        {
            assert(!empty, "Attempting to popBack an empty mapUnique.");
            _input.popBack();
        }
    }

    this(R input)
    {
        _input = move(input); // TODO remove `move` when compiler does it for us
    }

    static if (isInfinite!R)
    {
        // Propagate infinite-ness.
        enum bool empty = false;
    }
    else
    {
        @property bool empty()
        {
            return _input.empty;
        }
    }

    void popFront()
    {
        assert(!empty, "Attempting to popFront an empty mapUnique.");
        _input.popFront();
    }

    @property auto ref front()
    {
        assert(!empty, "Attempting to fetch the front of an empty mapUnique.");
        return fun(_input.front);
    }

    static if (isRandomAccessRange!R)
    {
        static if (is(typeof(_input[ulong.max])))
            private alias opIndex_t = ulong;
        else
            private alias opIndex_t = uint;

        auto ref opIndex(opIndex_t index)
        {
            return fun(_input[index]);
        }
    }

    static if (hasLength!R)
    {
        @property auto length()
        {
            return _input.length;
        }

        alias opDollar = length;
    }

    static if (hasSlicing!R &&
               isCopyable!R)
    {
        static if (is(typeof(_input[ulong.max .. ulong.max])))
            private alias opSlice_t = ulong;
        else
            private alias opSlice_t = uint;

        static if (hasLength!R)
        {
            auto opSlice(opSlice_t low, opSlice_t high)
            {
                return typeof(this)(_input[low .. high]);
            }
        }
        else static if (is(typeof(_input[opSlice_t.max .. $])))
        {
            struct DollarToken{}
            enum opDollar = DollarToken.init;
            auto opSlice(opSlice_t low, DollarToken)
            {
                return typeof(this)(_input[low .. $]);
            }

            auto opSlice(opSlice_t low, opSlice_t high)
            {
                import std.range : takeExactly;
                return this[low .. $].takeExactly(high - low);
            }
        }
    }

    static if (isForwardRange!R &&
               isCopyable!R)    // TODO should save be allowed for non-copyable?
    {
        @property auto save()
        {
            return typeof(this)(_input.save);
        }
    }
}

// TODO Add duck-typed interface that shows that result is still sorted according to `predicate`
template filterUnique(alias predicate) if (is(typeof(unaryFun!predicate)))
{
    import std.algorithm.mutation : move;
    import std.range.primitives : isInputRange;
    import std.traits : Unqual;

    auto filterUnique(Range)(Range range) if (isInputRange!(Unqual!Range))
    {
        return FilterUniqueResult!(unaryFun!predicate, Range)(move(range));
    }
}

// TODO Add duck-typed interface that shows that result is still sorted according to `predicate`
private struct FilterUniqueResult(alias pred, Range)
{
    import std.algorithm.mutation : move;
    import std.range.primitives : isForwardRange, isInfinite;
    import std.traits : Unqual, isCopyable;
    alias R = Unqual!Range;
    R _input;

    this(R r)
    {
        _input = move(r);       // TODO remove `move` when compiler does it for us
        while (!_input.empty && !pred(_input.front))
        {
            _input.popFront();
        }
    }

    static if (isCopyable!Range)
    {
        auto opSlice() { return this; }
    }

    static if (isInfinite!Range)
    {
        enum bool empty = false;
    }
    else
    {
        @property bool empty() { return _input.empty; }
    }

    void popFront()
    {
        do
        {
            _input.popFront();
        } while (!_input.empty && !pred(_input.front));
    }

    @property auto ref front()
    {
        assert(!empty, "Attempting to fetch the front of an empty filterUnique.");
        return _input.front;
    }

    static if (isForwardRange!R &&
               isCopyable!R) // TODO should save be allowed for non-copyable?
    {
        @property auto save()
        {
            return typeof(this)(_input.save);
        }
    }
}

// TODO move these hidden behind template defs of takeUnique
import std.range : Take;
import std.typecons : Unqual;
import std.range.primitives : isInputRange, isInfinite, hasSlicing;

/// Unique take.
Take!R takeUnique(R)(R input, size_t n)
    if (is(R T == Take!T))
{
    import std.algorithm.mutation : move;
    import std.algorithm.comparison : min;
    return R(move(input.source), // TODO remove `move` when compiler does it for us
             min(n, input._maxAvailable));
}

/// ditto
Take!(R) takeUnique(R)(R input, size_t n)
    if (isInputRange!(Unqual!R) &&
        (isInfinite!(Unqual!R) ||
         !hasSlicing!(Unqual!R) &&
         !is(R T == Take!T)))
{
    import std.algorithm.mutation : move;
    return Take!R(move(input), n); // TODO remove `move` when compiler does it for us
}

import std.functional : binaryFun;

InputRange findUnique(alias pred = "a == b", InputRange, Element)(InputRange haystack, scope Element needle)
    if (isInputRange!InputRange &&
        is (typeof(binaryFun!pred(haystack.front, needle)) : bool))
{
    for (; !haystack.empty; haystack.popFront())
    {
        if (binaryFun!pred(haystack.front, needle))
            break;
    }
    import std.algorithm.mutation : move;
    return move(haystack);
}
