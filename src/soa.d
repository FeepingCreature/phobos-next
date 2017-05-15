/** Structure of arrays.
    See also: https://maikklein.github.io/post/soa-d/
    See also: TODO Add my forum post

    TODO add `x[0].name` that doesn't have to create a temporary.  See:
    http://forum.dlang.org/post/wvulryummkqtskiwrusb@forum.dlang.org
 */
module soa;

@safe /*pure*/:

/** Structure of arrays similar to members of `S`.
 */
struct SOA(S)
    if (is(S == struct))        // TODO extend to `isAggregate!S`?
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;

    import std.meta : staticMap;
    import std.traits : FieldNameTuple;

    alias toArray(S) = S[];
    alias toType(string s) = typeof(__traits(getMember, S, s));
    alias toPtrType(string s) = typeof(__traits(getMember, S, s));

    alias MemberNames = FieldNameTuple!S;
    enum memberCount = MemberNames.length;
    alias Types = staticMap!(toType, MemberNames);
    alias PtrTypes = staticMap!(toPtrType, MemberNames);

    /// Reference to element in `soaPtr` at index `elementIndex`.
    private struct ElementRef
    {
        SOA* soaPtr;
        size_t elementIndex;
        auto ref opDispatch(string name)()
            @trusted return scope
        {
            return (*soaPtr).name[elementIndex];
        }
    }

    @safe /*pure*/:

    this(size_t size_,
         IAllocator _alloc = allocatorObject(Mallocator.instance))
    {
        _alloc = _alloc;
        _capacity = size_;
        allocate(size_);
    }

    auto opDispatch(string name)()
    {
        import std.meta : staticIndexOf;
        alias index = staticIndexOf!(name, MemberNames);
        static assert(index >= 0);
        return getArray!index;
    }

    void pushBackMembers(Types types)
    {
        if (_length == _capacity) { grow(); }
        foreach (const index, _; MemberNames)
        {
            // TODO functionize
            static if (false)   // activate for non-Copyable membeers
            {
                import std.algorithm.mutation : move;
                move(types[index], getArray!index[_length]);
            }
            else
            {
                getArray!index[_length] = types[index];
            }
        }
        ++_length;
    }

    void pushBack(S e)
    {
        if (_length == _capacity) { grow(); }
        foreach (const index, _; MemberNames)
        {
            // TODO functionize
            static if (false)   // activate for non-Copyable membeers
            {
                import std.algorithm.mutation : move;
                move(__traits(getMember, e, MemberNames[index]), getArray!index[_length]);
            }
            else
            {
                getArray!index[_length] = __traits(getMember, e, MemberNames[index]);
            }
        }
        ++_length;
    }

    void opOpAssign(string op, S)(S e)
        if (op == "~")
    {
        import std.algorithm.mutation : move;
        pushBack(move(e));      // TODO remove when compile does this for us
    }

    size_t length() const @property
    {
        return _length;
    }

    ~this() @trusted
    {
        if (_alloc is null) { return; }
        foreach (const index, _; MemberNames)
        {
            _alloc.dispose(getArray!index);
        }
    }

    /** Index operator. */
    // TODO activate:
    // ref inout(ElementRef) opIndex(size_t elementIndex) inout return scope
    // {
    //     return ElementRef(this, elementIndex);
    // }

private:

    // TODO use when importing std.typecons doesn't cost to performance
    // import std.typecons : Tuple;
    // alias ArrayTypes = staticMap!(toArray, Types);
    // Tuple!ArrayTypes containers;

    static string generateContainers()
    {
        string defs;
        foreach (const index, Type; Types)
        {
            enum TypeName = Type.stringof;
            defs ~= TypeName ~ `[] container` ~ index.stringof ~ ";";
        }
        return defs;
    }
    mixin(generateContainers());

    ref inout(Types[index][]) getArray(size_t index)() inout return scope
    {
        mixin(`return container` ~ index.stringof ~ ";");
    }

    IAllocator _alloc;

    size_t _length = 0;
    size_t _capacity = 0;
    short growFactor = 2;

    void allocate(size_t newCapacity) @trusted
    {
        if (_alloc is null)
        {
            _alloc = allocatorObject(Mallocator.instance);
        }
        foreach (const index, _; MemberNames)
        {
            getArray!index = _alloc.makeArray!(Types[index])(newCapacity);
        }
    }

    void grow() @trusted
    {
        import std.algorithm: max;
        size_t newCapacity = max(1, _capacity * growFactor);
        size_t expandSize = newCapacity - _capacity;

        if (_capacity is 0)
        {
            allocate(newCapacity);
        }
        else
        {
            foreach (const index, _; MemberNames)
            {
                _alloc.expandArray(getArray!index, expandSize);
            }
        }
        _capacity = newCapacity;
    }
}

unittest
{
    struct S { int i; float f; }

    auto x = SOA!S();

    static assert(is(typeof(x.getArray!0()) == int[]));
    static assert(is(typeof(x.getArray!1()) == float[]));

    assert(x.length == 0);

    x.pushBack(S.init);
    assert(x.length == 1);

    x ~= S.init;
    assert(x.length == 2);

    x.pushBackMembers(42, 43f);
    assert(x.length == 3);
    assert(x.i[2] == 42);
    assert(x.f[2] == 43);

    auto x3 = SOA!S(3);
    assert(x3.length == 0);
}
