module moval;

E movedToRvalue(E)(ref E e)
{
    import std.algorithm.mutation : move;
    E value;
    move(e, value);             // this can be optimized
    return value;
}

@safe pure nothrow @nogc:

struct S
{
    @disable this(this);
    int x;
}

void consume(S x)
{
}

unittest
{

    auto s = S(13);
    static assert(!__traits(compiles, { consume(s); }));
    consume(s.movedToRvalue());
    // static assert(__traits(compiles, { consume(s.movedToRvalue()); }));
}
